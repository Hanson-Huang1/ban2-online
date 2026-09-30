const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*' } });
app.use(express.static(path.join(__dirname, 'public')));

const SUITS = ['♠', '♥', '♣', '♦'];
const RANKS = ['2','3','4','5','6','7','8','9','10','J','Q','K','A'];
const rooms = {};

// ---------- 工具函数 ----------
function createDeck() {
  const d = [];
  for (const s of SUITS) for (const r of RANKS) d.push({ suit: s, rank: r });
  d.push({ suit: 'joker', rank: '小王' });
  d.push({ suit: 'joker', rank: '大王' });
  return d;
}
function shuffle(a) {
  const d = [...a];
  for (let i = d.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [d[i], d[j]] = [d[j], d[i]];
  }
  return d;
}
function isTrump(c, ts) {
  if (!ts) return false;
  if (c.suit === 'joker') return true;
  if (c.rank === '2') return true;
  return c.suit === ts;
}
function getTrumpRank(c, ts) {
  if (c.suit === 'joker') return c.rank === '大王' ? 99 : 98;
  if (c.rank === '2') return c.suit === ts ? 97 : 96;
  if (c.suit === ts) {
    if (c.rank === '5') return 100;
    return RANKS.indexOf(c.rank);
  }
  return -1;
}
function getCardScore(c) {
  if (c.rank === '5') return 5;
  if (c.rank === '10') return 10;
  if (c.rank === 'K') return 10;
  return 0;
}
function sortHand(h, ts) {
  h.sort((a, b) => {
    const at = isTrump(a, ts), bt = isTrump(b, ts);
    if (at && !bt) return -1;
    if (!at && bt) return 1;
    if (at && bt) return getTrumpRank(b, ts) - getTrumpRank(a, ts);
    if (a.suit !== b.suit) return SUITS.indexOf(a.suit) - SUITS.indexOf(b.suit);
    return RANKS.indexOf(b.rank) - RANKS.indexOf(a.rank);
  });
}
function canBeat(card, winner, lead, ts) {
  const ct = isTrump(card, ts), wt = isTrump(winner, ts), lt = isTrump(lead, ts);
  if (lt) {
    if (!ct) return false;
    return getTrumpRank(card, ts) > getTrumpRank(winner, ts);
  }
  const ls = lead.suit;
  if (ct) {
    if (wt) return getTrumpRank(card, ts) > getTrumpRank(winner, ts);
    return true;
  }
  if (wt) return false;
  if (card.suit !== ls) return false;
  if (winner.suit !== ls) return true;
  return RANKS.indexOf(card.rank) > RANKS.indexOf(winner.rank);
}
function isValidPlay(hand, card, lead, ts) {
  if (!lead) return true;
  if (isTrump(lead, ts)) {
    const has = hand.some(c => isTrump(c, ts));
    if (has) return isTrump(card, ts);
    return true;
  }
  const ls = lead.suit;
  const has = hand.some(c => c.suit === ls && !isTrump(c, ts));
  if (has) return card.suit === ls && !isTrump(card, ts);
  return true;
}

function getNick(room, p) {
  const nk = (room.nicknames && room.nicknames[p]) || '';
  return nk ? `${p + 1}-${nk}` : `${p + 1}`;
}
function checkSweep(players, player, cards, ts, allTrump) {

  let min = cards[0];
  if (allTrump) {
    for (const c of cards) if (getTrumpRank(c, ts) < getTrumpRank(min, ts)) min = c;
    for (let p = 0; p < 4; p++) {
      if (p === player) continue;
      for (const c of players[p]) if (isTrump(c, ts) && getTrumpRank(c, ts) > getTrumpRank(min, ts)) return false;
    }
  } else {
    const suit = cards[0].suit;
    for (const c of cards) if (RANKS.indexOf(c.rank) < RANKS.indexOf(min.rank)) min = c;
    for (let p = 0; p < 4; p++) {
      if (p === player) continue;
      for (const c of players[p]) if (c.suit === suit && !isTrump(c, ts) && RANKS.indexOf(c.rank) > RANKS.indexOf(min.rank)) return false;
    }
  }
  return true;
}

// ---------- 初始化房间 ----------
function initRoom(room) {
  const prevState = room.state;
  const prevDealer = prevState ? prevState.dealer : -1;
  const prevPendingSupply = prevState ? prevState.pendingSupply : null;

  room.state = {
    deck: shuffle(createDeck()),
    players: [[], [], [], []],
    bottom: [],
    trumpSuit: null,
    dealer: prevDealer,
    currentPlayer: 0,
    dealCurrent: prevDealer >= 0 ? prevDealer : Math.floor(Math.random() * 4),
    dealtCounts: [0, 0, 0, 0],
    viceScore: 0,
    currentTrick: [],
    leadCard: null,
    phase: 'dealing',
    lastTrickWinner: -1,
    lastTrickWasTrump: false,
    trickNumber: 0,
    bottomScore: 0,
    supplyFrom: -1,
    supplyCount: 0,
    supplyCards: [],
    supplyAssign: [],
    pendingSupply: prevPendingSupply,
    supplyFromOverride: -1,
    returnDealerCount: 0,
    returnPartnerCount: 0,
    sweepInfo: null,
    flipBy: -1,
    declareBy: -1,
    revealIndex: 0,
    revealedBottom: [],
    nextRoundReady: [false, false, false, false],
    returnDealerSubmit: null,
    returnPartnerSubmit: null,
    
    trickPaused: false,
    surrenderVotes: [false, false, false, false],
    surrenderEnd: false,
  };
}

function broadcastState(roomId) {
  const room = rooms[roomId];
  if (!room || !room.state) return;
  room.players.forEach((p, idx) => {
    const s = io.sockets.sockets.get(p.socketId);
       if (s) s.emit('stateUpdate', { state: room.state, yourIndex: idx, roomId, nicknames: room.nicknames });
  });
}

// ---------- 游戏逻辑 ----------
function drawCard(room) {
  const s = room.state;
  if (s.phase !== 'dealing') return;
  const p = s.dealCurrent;
  if (s.dealtCounts[p] >= 12) return;
  s.players[p].push(s.deck.pop());
  s.dealtCounts[p]++;
  sortHand(s.players[p], s.trumpSuit);
  if (s.dealtCounts.every(c => c >= 12)) { finishDealing(room); return; }
  s.dealCurrent = (s.dealCurrent + 1) % 4;
  let g = 0;
  while (s.dealtCounts[s.dealCurrent] >= 12 && g < 4) { s.dealCurrent = (s.dealCurrent + 1) % 4; g++; }
}

function declareTwo(room, p, cardSuit) {
  const s = room.state;
  if (s.phase !== 'dealing' || s.trumpSuit !== null) return;

  // 找出玩家手里所有的 2
  const twos = [];
  for (let i = 0; i < s.players[p].length; i++) {
    const c = s.players[p][i];
    if (c.rank === '2') twos.push(c);
  }
  if (twos.length === 0) {
    io.to(room.id).emit('msg', '你手里没有 2');
    return;
  }

  let chosen = null;
  if (cardSuit && cardSuit.length > 0) {
    // 前端指定了花色
    chosen = twos.find(c => c.suit === cardSuit);
    if (!chosen) {
      io.to(room.id).emit('msg', '请选中一张 2');
      return;
    }
  } else if (twos.length === 1) {
    // 只有一张 2，自动选
    chosen = twos[0];
  } else {
    // 多张 2，必须指定
    io.to(room.id).emit('msg', '请选中要办的 2');
    return;
  }

  s.trumpSuit = chosen.suit;
  s.declareBy = p;
  if (s.dealer === -1) s.dealer = p;

  // 办2后，直接把剩余牌一次性发完（每人补到 12 张）
  while (s.dealtCounts.some(c => c < 12)) {
    const cur = s.dealCurrent;
    if (s.dealtCounts[cur] < 12) {
      s.players[cur].push(s.deck.pop());
      s.dealtCounts[cur]++;
    }
    s.dealCurrent = (s.dealCurrent + 1) % 4;
  }
  for (let k = 0; k < 4; k++) sortHand(s.players[k], s.trumpSuit);

  if (s.dealtCounts.every(c => c >= 12)) finishDealing(room);
}

function finishDealing(room) {
  const s = room.state;
  s.bottom = s.deck.splice(0, 6);
  if (s.trumpSuit === null) {
    if (s.dealer === -1) { initRoom(room); return; }
    s.phase = 'flipBottom'; return;
  }
  goToBottom(room);
}

function flipBottom(room, p) {
  const s = room.state;
  if (s.phase !== 'flipBottom' || s.dealer === -1) return;
  if (p % 2 === s.dealer % 2) return;
  s.flipBy = p;
  s.phase = 'flipReveal';
  s.revealIndex = 0;
  s.revealedBottom = [];
  s.trumpSuit = null;
}

function revealNext(room) {
  const s = room.state;
  if (s.phase === 'flipReveal') {
    if (s.revealIndex >= s.bottom.length) return;
    const card = s.bottom[s.revealIndex];
    s.revealedBottom.push(card);
    if (card.rank === '2' && s.trumpSuit === null) s.trumpSuit = card.suit;
    s.revealIndex++;
    if (s.revealIndex >= s.bottom.length) finishFlipReveal(room);
    return;
  }
  if (s.phase === 'bottomReveal') {
    if (s.revealIndex >= s.bottom.length) return;
    s.revealedBottom.push(s.bottom[s.revealIndex]);
    s.revealIndex++;
    if (s.revealIndex >= s.bottom.length) finishBottomReveal(room);
  }
}

function finishFlipReveal(room) {
  const s = room.state;
  if (s.trumpSuit === null) {
    const bs = new Set(s.bottom.map(c => c.suit));
    let found = false;
    for (const suit of SUITS) if (!bs.has(suit)) { s.trumpSuit = suit; found = true; break; }
    if (!found) {
      s.phase = 'flipNoTrump';
      return;
    }
  }
  for (let k = 0; k < 4; k++) sortHand(s.players[k], s.trumpSuit);
  s.revealedBottom = [];
  s.revealIndex = 0;
  goToBottom(room);
}

function goToBottom(room) {
  const s = room.state;
  s.players[s.dealer].push(...s.bottom);
  s.bottom = [];
  for (let k = 0; k < 4; k++) sortHand(s.players[k], s.trumpSuit);
  s.phase = 'bottom';
}

function confirmBottom(room) {
  const s = room.state;
  if (s.phase !== 'bottom') return;
  const dh = s.players[s.dealer];
  const idxs = (room.pendingBottomIndices || []).sort((a, b) => b - a);
  if (idxs.length !== 6) return;
  const nb = [];
  for (const i of idxs) nb.push(dh.splice(i, 1)[0]);
  s.bottom = nb;
  s.bottomScore = s.bottom.reduce((a, c) => a + getCardScore(c), 0);
  room.pendingBottomIndices = null;
  s.trickNumber = 0;
  s.sweepInfo = null;
  enterSupplyOrPlay(room);
}

function calcSupply(v) {
  if (v === 0) return { cards: 3, change: false };
  if (v <= 10) return { cards: 2, change: false };
  if (v <= 20) return { cards: 1, change: false };
  if (v < 35) return { cards: 0, change: false };
  if (v < 40) return { cards: 0, change: true };
  if (v < 50) return { cards: 1, change: true };
  if (v < 60) return { cards: 2, change: true };
  return { cards: 3, change: true };
}

function enterSupplyOrPlay(room) {
  const s = room.state;
  const ps = s.pendingSupply;
  if (ps && ps.cards > 0) {
    // 根据本局的办二者 / 翻底者确定上供者
    const dealerTeam = s.dealer % 2;
    let from;
    if (s.declareBy >= 0 && (s.declareBy % 2) !== dealerTeam) {
      // 副家有人办二 → 上供者 = 办二者的对家
      from = (s.declareBy + 2) % 4;
    } else if (s.flipBy >= 0 && (s.flipBy % 2) !== dealerTeam) {
      // 无人办二，副家某人翻底 → 上供者 = 翻底者的对家
      from = (s.flipBy + 2) % 4;
    } else {
      // 默认：庄家的下家
      from = (s.dealer + 1) % 4;
    }
    s.supplyFrom = from;
    s.supplyCount = ps.cards;

    // 自动选取最大的 N 张合法主牌（不含 10、K；5 可以上）
    const legal = [];
    for (let i = 0; i < s.players[from].length; i++) {
      const c = s.players[from][i];
      if (!isTrump(c, s.trumpSuit)) continue;
      if (c.rank === '10' || c.rank === 'K') continue;
      legal.push({ idx: i, rank: getTrumpRank(c, s.trumpSuit) });
    }
    legal.sort((a, b) => b.rank - a.rank);
    const chosen = legal.slice(0, s.supplyCount).map(x => x.idx);
    const idxs = [...chosen].sort((a, b) => b - a);
    s.supplyCards = [];
    for (const i of idxs) s.supplyCards.push(s.players[from].splice(i, 1)[0]);
    sortHand(s.players[from], s.trumpSuit);
        s.supplyAssign = s.supplyCards.map(() => 0);
    for (const c of s.supplyCards) c.tag = 'in';
    s.phase = 'supplyConfirm';
    io.to(room.id).emit('msg', `${getNick(room, from)} 上供 ${chosen.length} 张主牌，请确认`);
    return;
  }
  startPlay(room);
}

function startPlay(room) {
  const s = room.state;
  s.phase = 'play';
  s.currentPlayer = s.dealer;
  s.currentTrick = [];
  s.leadCard = null;
  s.supplyFrom = -1;
  s.supplyCount = 0;
  s.pendingSupply = null;
  s.supplyFromOverride = -1;
}

function confirmSupply(room) {
  const s = room.state;
  if (s.phase !== 'supplyConfirm') return;
  s.phase = 'supplyDistribute';
}

// 保留旧函数，不会触发（auto supply 后不再进入 supplySelect）
function confirmSupplySelect(room, indices) {
  const s = room.state;
  if (s.phase !== 'supplySelect') return;
  const from = s.supplyFrom;
  if (!indices || indices.length !== s.supplyCount) return;
  for (const i of indices) {
    const c = s.players[from][i];
    if (!isTrump(c, s.trumpSuit)) {
      io.to(room.id).emit('msg', '上供必须是主牌');
      return;
    }
    if (c.rank === '10' || c.rank === 'K') {
      io.to(room.id).emit('msg', '上供不能是 10、K');
      return;
    }
  }
  const idxs = [...indices].sort((a, b) => b - a);
  s.supplyCards = [];
  for (const i of idxs) s.supplyCards.push(s.players[from].splice(i, 1)[0]);
  sortHand(s.players[from], s.trumpSuit);
  s.supplyAssign = s.supplyCards.map(() => 0);
  s.phase = 'supplyDistribute';
}

function toggleAssign(room, i) {
  const s = room.state;
  if (s.phase !== 'supplyDistribute') return;
  s.supplyAssign[i] = s.supplyAssign[i] === 0 ? 1 : 0;
}

function confirmSupplyDistribute(room) {
  const s = room.state;
  if (s.phase !== 'supplyDistribute') return;
  const d = s.dealer, dp = (d + 2) % 4;
  const td = [], tp = [];
  for (let i = 0; i < s.supplyCards.length; i++) {
    if (s.supplyAssign[i] === 0) td.push(s.supplyCards[i]);
    else tp.push(s.supplyCards[i]);
  }
  s.players[d].push(...td);
  s.players[dp].push(...tp);
  sortHand(s.players[d], s.trumpSuit);
  sortHand(s.players[dp], s.trumpSuit);
  s.returnDealerCount = td.length;
  s.returnPartnerCount = tp.length;
  s.supplyCards = [];
  s.supplyAssign = [];
  s.returnDealerSubmit = null;
  s.returnPartnerSubmit = null;
  checkReturnFeasibility(room);
}

function checkReturnFeasibility(room) {
  const s = room.state;
  const d = s.dealer, dp = (d + 2) % 4, from = s.supplyFrom;
  const da = s.players[d].filter(c => !isTrump(c, s.trumpSuit) && getCardScore(c) === 0);
  const pa = s.players[dp].filter(c => !isTrump(c, s.trumpSuit) && getCardScore(c) === 0);
  const psuits = new Set(pa.map(c => c.suit));
  let msg = [];
    if (da.length < s.returnDealerCount && s.returnDealerCount > 0) {
    for (let i = 0; i < s.returnDealerCount; i++) {
      const c = s.players[d].pop();
      c.tag = 'out';
      s.players[from].push(c);
    }
    msg.push(`庄家无法还牌，退回${s.returnDealerCount}张`);
    s.returnDealerCount = 0;
  }
  if (psuits.size < s.returnPartnerCount && s.returnPartnerCount > 0) {
    for (let i = 0; i < s.returnPartnerCount; i++) {
      const c = s.players[dp].pop();
      c.tag = 'out';
      s.players[from].push(c);
    }
    msg.push(`庄家对家无法还牌，退回${s.returnPartnerCount}张`);
    s.returnPartnerCount = 0;
  }
  sortHand(s.players[d], s.trumpSuit);
  sortHand(s.players[dp], s.trumpSuit);
  sortHand(s.players[from], s.trumpSuit);
  if (msg.length) io.to(room.id).emit('msg', msg.join('\n'));
  if (s.returnDealerCount === 0 && s.returnPartnerCount === 0) { startPlay(room); return; }
  s.phase = 'supplyReturn';
}

function confirmReturn(room, dealerIndices, partnerIndices) {
  const s = room.state;
  if (s.phase !== 'supplyReturn') return;
  const d = s.dealer, dp = (d + 2) % 4, from = s.supplyFrom;

  if (s.returnDealerCount > 0 && (dealerIndices || []).length !== s.returnDealerCount) return;
  for (const i of dealerIndices) {
    const c = s.players[d][i];
    if (isTrump(c, s.trumpSuit)) { io.to(room.id).emit('msg', '庄家：不可以还主牌'); return; }
    if (getCardScore(c) > 0) { io.to(room.id).emit('msg', '庄家：不可以还 5、10、K'); return; }
  }

  if (s.returnPartnerCount > 0 && (partnerIndices || []).length !== s.returnPartnerCount) return;
  const usedSuits = new Set();
  for (const i of partnerIndices) {
    const c = s.players[dp][i];
    if (isTrump(c, s.trumpSuit)) { io.to(room.id).emit('msg', '庄家对家：不可以还主牌'); return; }
    if (getCardScore(c) > 0) { io.to(room.id).emit('msg', '庄家对家：不可以还 5、10、K'); return; }
    if (usedSuits.has(c.suit)) { io.to(room.id).emit('msg', '庄家对家：还牌必须不同花色'); return; }
    usedSuits.add(c.suit);
  }

    const di = [...(dealerIndices || [])].sort((a, b) => b - a);
  for (const i of di) {
    const c = s.players[d].splice(i, 1)[0];
    c.tag = 'out';
    s.players[from].push(c);
  }
  const pi = [...(partnerIndices || [])].sort((a, b) => b - a);
  for (const i of pi) {
    const c = s.players[dp].splice(i, 1)[0];
    c.tag = 'out';
    s.players[from].push(c);
  }

  sortHand(s.players[d], s.trumpSuit);
  sortHand(s.players[dp], s.trumpSuit);
  sortHand(s.players[from], s.trumpSuit);
  s.returnDealerSubmit = null;
  s.returnPartnerSubmit = null;
  startPlay(room);
}

function handleSurrender(room, p) {
  const s = room.state;
  const dealerTeam = s.dealer % 2;
  const viceTeam = 1 - dealerTeam;
  if (p % 2 !== viceTeam) return;
  const validPhases = ['flipBottom', 'flipReveal', 'bottom', 'supplyConfirm', 'supplyDistribute', 'supplyReturn', 'play'];
  if (!validPhases.includes(s.phase)) return;
  if (s.phase === 'play' && (s.trickNumber > 0 || s.currentTrick.length > 0)) return;
  if (s.surrenderVotes[p]) return;
  s.surrenderVotes[p] = true;
  const vicePlayers = [0,1,2,3].filter(i => i % 2 === viceTeam);
  const votedCount = vicePlayers.filter(i => s.surrenderVotes[i]).length;
  io.to(room.id).emit('msg', `${getNick(room, p)} 点了投降（${votedCount}/2）`);
  const bothVoted = vicePlayers.every(i => s.surrenderVotes[i]);
  if (bothVoted) {
    s.phase = 'surrenderEnd';
    s.surrenderEnd = true;
    s.viceScore = 0;
    s.pendingSupply = { cards: 3 };
    s.nextRoundReady = [false, false, false, false];
    io.to(room.id).emit('msg', '副家投降，本局结束。下把副家上供3张');
  }
}

// ---------- 出牌 ----------
function playCard(room, cardIndex) {

  const s = room.state;
  if (s.phase !== 'play' || s.sweepInfo || s.trickPaused) return;
  const p = s.currentPlayer;
  if (cardIndex === undefined || cardIndex < 0 || cardIndex >= s.players[p].length) return;
  const card = s.players[p][cardIndex];
  if (s.currentTrick.length > 0 && !isValidPlay(s.players[p], card, s.leadCard, s.trumpSuit)) {
    let need;
    if (!s.leadCard) need = '同花色';
    else if (isTrump(s.leadCard, s.trumpSuit)) need = '主牌';
    else need = s.leadCard.suit;
    io.to(room.id).emit('msg', `跟牌不合法：必须跟 ${need}`);
    return;
  }
  s.players[p].splice(cardIndex, 1);
  if (s.currentTrick.length === 0) s.leadCard = card;
  s.currentTrick.push({ player: p, card });
  if (s.currentTrick.length === 4) resolveTrick(room);
  else s.currentPlayer = (s.currentPlayer + 1) % 4;
}

function trySweep(room, indices) {
  const s = room.state;
  if (s.phase !== 'play' || s.currentTrick.length !== 0) return;
  const p = s.currentPlayer;
  if (!indices || indices.length < 2) {
    io.to(room.id).emit('msg', '甩牌至少需要 2 张');
    io.to(room.id).emit('clearSelection');
    return;
  }
  const cards = indices.map(i => s.players[p][i]);
  const allTrump = cards.every(c => isTrump(c, s.trumpSuit));
  let suit0 = null;
  if (!allTrump) {
    suit0 = cards[0].suit;
    if (!cards.every(c => c.suit === suit0 && !isTrump(c, s.trumpSuit))) {
      io.to(room.id).emit('msg', '甩牌必须同一花色或都是主牌');
      io.to(room.id).emit('clearSelection');
      return;
    }
  }
  if (!checkSweep(s.players, p, cards, s.trumpSuit, allTrump)) {
    if (allTrump) {
      io.to(room.id).emit('msg', '主牌甩牌失败，可自由出牌');
      io.to(room.id).emit('clearSelection');
      return;
    }
    let min = cards[0], mi = indices[0];
    for (let k = 0; k < cards.length; k++) {
      if (RANKS.indexOf(cards[k].rank) < RANKS.indexOf(min.rank)) { min = cards[k]; mi = indices[k]; }
    }
    const sorted = [...indices].sort((a, b) => b - a);
    for (const i of sorted) if (i !== mi) s.players[p].splice(i, 1);
    const newIdx = s.players[p].findIndex(c => c === min);
    s.players[p].splice(newIdx, 1);
    s.leadCard = min;
    s.currentTrick.push({ player: p, card: min });
    s.currentPlayer = (p + 1) % 4;
    io.to(room.id).emit('msg', `甩牌失败，出最小：${min.suit === 'joker' ? min.rank : min.suit + min.rank}`);
    return;
  }
  const sorted = [...indices].sort((a, b) => b - a);
  for (const i of sorted) s.players[p].splice(i, 1);
  s.leadCard = cards[0];
  s.currentTrick.push({ player: p, card: cards[0], cards, sweep: true });
  s.sweepInfo = { suit: allTrump ? null : suit0, isTrump: allTrump, count: cards.length, leader: p };
  s.currentPlayer = (p + 1) % 4;
  io.to(room.id).emit('msg', `甩牌成功！${cards.length}张`);
}

function playSweepFollow(room, indices) {
  const s = room.state;
  if (!s.sweepInfo || s.phase !== 'play' || s.trickPaused) return;
  const need = s.sweepInfo.count;
  if (!indices || indices.length !== need) return;
  const p = s.currentPlayer;
  const cards = indices.map(i => s.players[p][i]);
  const sw = s.sweepInfo;
  if (sw.isTrump) {
    const ht = s.players[p].filter(c => isTrump(c, s.trumpSuit));
    if (ht.length >= need && !cards.every(c => isTrump(c, s.trumpSuit))) return;
  } else {
    const hs = s.players[p].filter(c => c.suit === sw.suit && !isTrump(c, s.trumpSuit));
    if (hs.length >= need && !cards.every(c => c.suit === sw.suit && !isTrump(c, s.trumpSuit))) return;
  }
  const sorted = indices.sort((a, b) => b - a);
  for (const i of sorted) s.players[p].splice(i, 1);
  s.currentTrick.push({ player: p, cards });
  if (s.currentTrick.length === 4) resolveTrick(room);
  else s.currentPlayer = (s.currentPlayer + 1) % 4;
}

function resolveTrick(room) {
  const s = room.state;
  if (s.trickPaused) return;
  s.trickPaused = true;
  setTimeout(() => {
    s.trickPaused = false;
    resolveTrickFinalize(room);
    broadcastState(room.id);
  }, 1500);
}

function resolveTrickFinalize(room) {
  const s = room.state;
  const ts = s.trumpSuit;
  let winner;
  if (s.sweepInfo) {
    const sw = s.sweepInfo;
    if (sw.isTrump) winner = s.currentTrick[0];
    else {
      let killer = null, kb = -1;
      for (let i = 1; i < s.currentTrick.length; i++) {
        const play = s.currentTrick[i];
        const cards = play.cards || [play.card];
        if (cards.length === sw.count && cards.every(c => isTrump(c, ts))) {
          for (const c of cards) if (getTrumpRank(c, ts) > kb) { kb = getTrumpRank(c, ts); killer = play; }
        }
      }
      winner = killer || s.currentTrick[0];
    }
  } else {
    winner = s.currentTrick[0];
    for (let i = 1; i < s.currentTrick.length; i++) {
      if (canBeat(s.currentTrick[i].card, winner.card, s.leadCard, ts)) winner = s.currentTrick[i];
    }
  }
  const wc = winner.cards || [winner.card];
  const wasTrump = wc.every(c => isTrump(c, ts));
  let score = 0;
  for (const play of s.currentTrick) {
    const cs = play.cards || [play.card];
    for (const c of cs) score += getCardScore(c);
  }
  const dt = s.dealer % 2, vt = 1 - dt;
  if (winner.player % 2 === vt) s.viceScore += score;
  s.lastTrickWinner = winner.player;
  s.lastTrickWasTrump = wasTrump;
  s.trickNumber++;
  s.currentPlayer = winner.player;
  s.currentTrick = [];
  s.leadCard = null;
  s.sweepInfo = null;
  const total = s.players.reduce((a, h) => a + h.length, 0);
  if (total === 0) endGame(room);
}

function endGame(room) {
  const s = room.state;
  s.phase = 'bottomReveal';
  s.revealIndex = 0;
  s.revealedBottom = [];
}

function finishBottomReveal(room) {
  const s = room.state;
  s.phase = 'ended';
  const dt = s.dealer % 2, vt = 1 - dt;
  let msg = '';
  if (s.lastTrickWinner % 2 === vt && s.lastTrickWasTrump) {
    s.viceScore += s.bottomScore;
    msg = `副家以主赢最后一手，抠底成功！+${s.bottomScore}分`;
  } else if (s.lastTrickWinner % 2 === vt) {
    msg = `副家赢最后一手但不是主，不抠底。底牌${s.bottomScore}分作废`;
  } else {
    msg = `庄家赢最后一手，底牌${s.bottomScore}分作废`;
  }
  const info = calcSupply(s.viceScore);
  if (!info.change) {
    msg += `\n庄家不变，${info.cards > 0 ? `下把上供${info.cards}张` : '不上供'}`;
  } else {
    const nd = (s.dealer + 1) % 4;
    msg += `\n换庄！新庄家 ${getNick(room, nd)}，${info.cards > 0 ? `新副家上供${info.cards}张` : '不上供'}`;
    s.dealer = nd;
  }
  s.pendingSupply = { cards: info.cards };
  s.supplyFromOverride = -1;
  // 重置准备状态
  s.nextRoundReady = [false, false, false, false];
  io.to(room.id).emit('msg', msg);
}

// ---------- Socket.IO ----------
io.on('connection', (socket) => {
    socket.on('createRoom', ({ nickname } = {}) => {
    const id = Math.random().toString(36).substring(2, 6).toUpperCase();
    const token = Math.random().toString(36).substring(2, 12);
    const clean = (nickname || '').toString().trim().substring(0, 8);
    rooms[id] = { id, players: [], state: null, pendingBottomIndices: null,
      nicknames: [clean, '', '', ''] };
    rooms[id].players.push({ socketId: socket.id, token });
    initRoom(rooms[id]);
    socket.join(id);
    socket.emit('roomCreated', { roomId: id, playerIndex: 0, token, nicknames: rooms[id].nicknames });
  });

    socket.on('joinRoom', ({ roomId, nickname }) => {
    const room = rooms[roomId];
    if (!room) { socket.emit('err', '房间不存在'); return; }
    let idx = room.players.findIndex(p => !p.socketId);
    if (idx === -1 && room.players.length < 4) idx = room.players.length;
    if (idx === -1) { socket.emit('err', '房间已满'); return; }
    const token = Math.random().toString(36).substring(2, 12);
    if (idx >= room.players.length) {
      room.players.push({ socketId: socket.id, token });
    } else {
      room.players[idx] = { socketId: socket.id, token };
    }
    const clean = (nickname || '').toString().trim().substring(0, 8);
    if (clean) room.nicknames[idx] = clean;
    socket.join(roomId);
    socket.emit('joined', { roomId, playerIndex: idx, token, nicknames: room.nicknames });
    io.to(roomId).emit('roomUpdate', { count: room.players.filter(p => p.socketId).length, nicknames: room.nicknames });
    if (room.players.filter(p => p.socketId).length === 4) {
      initRoom(room);
      broadcastState(roomId);
    }
  });

  socket.on('reconnect', ({ roomId, token }) => {
    const room = rooms[roomId];
    if (!room) { socket.emit('err', '房间不存在'); return; }
    const idx = room.players.findIndex(p => p.token === token);
    if (idx === -1) { socket.emit('err', '重连失败'); return; }
    room.players[idx].socketId = socket.id;
    socket.join(roomId);
    socket.emit('reconnected', { roomId, playerIndex: idx, token });
    io.to(roomId).emit('roomUpdate', { count: room.players.filter(p => p.socketId).length });
    if (room.state) {
      socket.emit('stateUpdate', { state: room.state, yourIndex: idx, roomId });
    }
  });

  socket.on('requestState', ({ roomId, token }) => {
    const room = rooms[roomId];
    if (!room || !room.state) return;
    const idx = room.players.findIndex(p => p.token === token);
    if (idx === -1) return;
    socket.emit('stateUpdate', { state: room.state, yourIndex: idx, roomId });
  });

  socket.on('action', ({ roomId, type, ...params }) => {
    const room = rooms[roomId];
    if (!room || !room.state) return;
    const p = room.players.findIndex(x => x.socketId === socket.id);
    if (p < 0) return;
    const s = room.state;
    switch (type) {
      case 'assign':
        if (s.phase === 'supplyDistribute' && p === (s.supplyFrom + 2) % 4) {
          const idx = params.index;
          const tgt = params.target;
          if (idx >= 0 && idx < s.supplyAssign.length) s.supplyAssign[idx] = tgt;
        }
        break;
      case 'drawCard':
        if (s.phase === 'dealing' && p === s.dealCurrent) drawCard(room);
        break;
      case 'nextRound': {
        if (s.phase !== 'ended' && s.phase !== 'flipNoTrump' && s.phase !== 'surrenderEnd') break;
        s.nextRoundReady[p] = true;
        const readyCount = s.nextRoundReady.filter(x => x).length;
        io.to(room.id).emit('msg', `${getNick(room, p)} 已准备（${readyCount}/4），等待其他玩家...`);
        if (s.nextRoundReady.every(x => x)) initRoom(room);
        break;
      }
      case 'submitReturn': {
        if (s.phase !== 'supplyReturn') break;
        if (params.role === 'dealer' && p === s.dealer && s.returnDealerCount > 0) {
          s.returnDealerSubmit = params.indices;
        } else if (params.role === 'partner' && p === (s.dealer + 2) % 4 && s.returnPartnerCount > 0) {
          s.returnPartnerSubmit = params.indices;
        } else break;
        const dealerDone = s.returnDealerCount === 0 || s.returnDealerSubmit !== null;
        const partnerDone = s.returnPartnerCount === 0 || s.returnPartnerSubmit !== null;
        if (dealerDone && partnerDone) confirmReturn(room, s.returnDealerSubmit || [], s.returnPartnerSubmit || []);
        break;
      }

            case 'confirmSupply':
        if (s.phase === 'supplyConfirm' && p === s.supplyFrom) confirmSupply(room);
        break;
      case 'surrender':
        handleSurrender(room, p);
        break;
          case 'declareTwo':
        if (s.phase === 'dealing' && s.trumpSuit === null) declareTwo(room, p, params.cardSuit);
        break;

      case 'flipBottom':
        if (s.phase === 'flipBottom') flipBottom(room, p);
        break;
      case 'revealNext':
        if ((s.phase === 'flipReveal' && p === s.flipBy) || s.phase === 'bottomReveal') revealNext(room);
        break;
      case 'confirmBottom':
        if (s.phase === 'bottom' && p === s.dealer) {
          room.pendingBottomIndices = params.indices;
          confirmBottom(room);
        }
        break;
      case 'confirmSupplySelect':
        if (s.phase === 'supplySelect' && p === s.supplyFrom) confirmSupplySelect(room, params.indices);
        break;
      case 'toggleAssign':
        if (s.phase === 'supplyDistribute' && p === (s.supplyFrom + 2) % 4) toggleAssign(room, params.index);
        break;
      case 'confirmSupplyDistribute':
        if (s.phase === 'supplyDistribute' && p === (s.supplyFrom + 2) % 4) confirmSupplyDistribute(room);
        break;
      case 'confirmReturn':
        if (s.phase === 'supplyReturn') confirmReturn(room, params.dealerIndices, params.partnerIndices);
        break;
      case 'playCard':
        if (s.phase === 'play' && p === s.currentPlayer) playCard(room, params.cardIndex);
        break;
      case 'trySweep':
        if (s.phase === 'play' && p === s.currentPlayer) trySweep(room, params.indices);
        break;
      case 'playSweepFollow':
        if (s.phase === 'play' && p === s.currentPlayer) playSweepFollow(room, params.indices);
        break;
    }
    broadcastState(roomId);
  });

   socket.on('updateNickname', ({ roomId, nickname }) => {
    const room = rooms[roomId];
    if (!room) return;
    const idx = room.players.findIndex(x => x.socketId === socket.id);
    if (idx < 0) return;
    const clean = (nickname || '').toString().trim().substring(0, 8);
    room.nicknames[idx] = clean;
    io.to(roomId).emit('roomUpdate', { count: room.players.filter(p => p.socketId).length, nicknames: room.nicknames });
    broadcastState(roomId);
  });

  socket.on('disconnect', () => {

    for (const id in rooms) {
      const room = rooms[id];
      const player = room.players.find(x => x.socketId === socket.id);
      if (player) {
        player.socketId = null;
        if (room.players.every(p => !p.socketId)) delete rooms[id];
        break;
      }
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Server on ${PORT}`));