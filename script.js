const boardEl = document.getElementById('board');
const boardContainerEl = document.querySelector('.board-container');
const titleEl = document.querySelector('.title');
const levelEl = document.getElementById('levelNum');
const hintBtn = document.getElementById('hintBtn');
const newBtn = document.getElementById('newBtn');
const nextBtn = document.getElementById('nextBtn');
const overlay = document.getElementById('winOverlay');
const difficultyOverlay = document.getElementById('difficultyOverlay');
const diffButtons = document.querySelectorAll('.diff-btn');
const helpBtn = document.getElementById('helpBtn');
const helpOverlay = document.getElementById('helpOverlay');
const helpCloseBtn = document.getElementById('helpCloseBtn');
const statClicksEl = document.getElementById('statClicks');
const statMarksEl = document.getElementById('statMarks');
const statTimeEl = document.getElementById('statTime');

let size = 6;
let level = 1;
let state = null;
let dragging = false;
let dragMoved = false;
let dragStartIdx = -1;
let lastDragIdx = -1;
let dragVisited = new Set();
let dragMode = 'add';
let suppressClick = false;
let lastTap = { time: 0, idx: -1 };
let tapTimers = new Map();
let lastPointerType = 'mouse';

const SHOW_ILLEGAL_ON_KING = false;
let currentDifficulty = 'hard';
let clickCount = 0;
let dragMarkCount = 0;
let startTime = 0;
let timerId = null;

const SIZE_OPTIONS = [5, 6, 7, 8, 9];

function weightedSizeForLevel(lv) {
  const t = Math.min(1, Math.max(0, (lv - 1) / 20));
  const weights = SIZE_OPTIONS.map((_, i) => 1 + t * i * 1.2);
  const total = weights.reduce((a, b) => a + b, 0);
  let r = Math.random() * total;
  for (let i = 0; i < weights.length; i += 1) {
    r -= weights[i];
    if (r <= 0) return SIZE_OPTIONS[i];
  }
  return SIZE_OPTIONS[SIZE_OPTIONS.length - 1];
}

function randPick(arr) {
  return arr[Math.floor(Math.random() * arr.length)];
}

function idxOf(r, c) {
  return r * size + c;
}

function rcOf(idx) {
  return { r: Math.floor(idx / size), c: idx % size };
}

function neighbors8(idx) {
  const { r, c } = rcOf(idx);
  const list = [];
  for (let dr = -1; dr <= 1; dr += 1) {
    for (let dc = -1; dc <= 1; dc += 1) {
      if (dr === 0 && dc === 0) continue;
      const nr = r + dr;
      const nc = c + dc;
      if (nr >= 0 && nr < size && nc >= 0 && nc < size) {
        list.push(idxOf(nr, nc));
      }
    }
  }
  return list;
}

function illegalZone(idx) {
  const { r, c } = rcOf(idx);
  const list = new Set();
  for (let i = 0; i < size; i += 1) {
    list.add(idxOf(r, i));
    list.add(idxOf(i, c));
  }
  neighbors8(idx).forEach((n) => list.add(n));
  list.add(idx);
  return [...list];
}

function generateKings() {
  const total = size * size;
  const illegal = new Array(total).fill(false);
  const kings = [];
  let legal = [];

  function recomputeLegal() {
    legal = [];
    for (let i = 0; i < total; i += 1) {
      if (!illegal[i]) legal.push(i);
    }
  }

  recomputeLegal();
  while (legal.length > 0) {
    const pick = randPick(legal);
    kings.push(pick);
    illegalZone(pick).forEach((idx) => {
      illegal[idx] = true;
    });
    recomputeLegal();
  }

  return kings;
}

function generateRegions(kings) {
  const total = size * size;
  const region = new Array(total).fill(-1);
  const frontier = [];
  kings.forEach((k, id) => {
    region[k] = id;
    frontier.push(k);
  });

  const unassigned = new Set();
  for (let i = 0; i < total; i += 1) {
    if (region[i] === -1) unassigned.add(i);
  }

  function neighbors4(idx) {
    const { r, c } = rcOf(idx);
    const list = [];
    if (r > 0) list.push(idxOf(r - 1, c));
    if (r < size - 1) list.push(idxOf(r + 1, c));
    if (c > 0) list.push(idxOf(r, c - 1));
    if (c < size - 1) list.push(idxOf(r, c + 1));
    return list;
  }

  while (unassigned.size > 0) {
    const boundary = [];
    unassigned.forEach((idx) => {
      const neigh = neighbors4(idx);
      const regions = neigh.map((n) => region[n]).filter((v) => v !== -1);
      if (regions.length > 0) boundary.push({ idx, regions });
    });

    if (boundary.length === 0) break;
    const pick = randPick(boundary);
    const regionId = randPick(pick.regions);
    region[pick.idx] = regionId;
    unassigned.delete(pick.idx);
  }

  return region;
}

function colorsForRegions(count) {
  const colors = [];
  for (let i = 0; i < count; i += 1) {
    const hue = Math.round((i * 360) / count + 15) % 360;
    colors.push(`hsl(${hue} 68% 72%)`);
  }
  return colors;
}

function countSolutions(region, kingCount) {
  const total = size * size;
  const regions = Array.from({ length: kingCount }, () => []);
  for (let i = 0; i < total; i += 1) {
    const r = region[i];
    regions[r].push(i);
  }

  const order = regions
    .map((cells, id) => ({ id, cells }))
    .sort((a, b) => a.cells.length - b.cells.length);

  const usedRows = new Set();
  const usedCols = new Set();
  const occupied = new Set();
  let solutions = 0;

  function canPlace(idx) {
    const { r, c } = rcOf(idx);
    if (usedRows.has(r) || usedCols.has(c)) return false;
    for (const n of neighbors8(idx)) {
      if (occupied.has(n)) return false;
    }
    return true;
  }

  function backtrack(pos) {
    if (solutions > 1) return;
    if (pos === order.length) {
      solutions += 1;
      return;
    }
    const { cells } = order[pos];
    for (const idx of cells) {
      if (!canPlace(idx)) continue;
      const { r, c } = rcOf(idx);
      usedRows.add(r);
      usedCols.add(c);
      occupied.add(idx);
      backtrack(pos + 1);
      usedRows.delete(r);
      usedCols.delete(c);
      occupied.delete(idx);
      if (solutions > 1) return;
    }
  }

  backtrack(0);
  return solutions;
}

function generatePuzzle() {
  let attempt = 0;
  let result = null;
  while (attempt < 200) {
    const kings = generateKings();
    const region = generateRegions(kings);
    const solutions = countSolutions(region, kings.length);
    if (solutions === 1) {
      result = { kings, region };
      break;
    }
    attempt += 1;
  }
  if (!result) {
    const kings = generateKings();
    const region = generateRegions(kings);
    result = { kings, region };
  }
  return result;
}

function buildState() {
  const { kings, region } = generatePuzzle();
  const kingSet = new Set(kings);
  const colors = colorsForRegions(kings.length);
  const total = size * size;
  const cells = [];
  for (let i = 0; i < total; i += 1) {
    cells.push({
      color: colors[region[i]],
      isKing: kingSet.has(i),
      region: region[i],
      revealed: false,
      flagged: false,
      invalid: false,
    });
  }
  return { cells, kings, region, kingSet, revealedCount: 0 };
}

function renderBoard() {
  boardEl.style.setProperty('grid-template-columns', `repeat(${size}, 1fr)`);
  boardEl.innerHTML = '';
  state.cells.forEach((cell, idx) => {
    const div = document.createElement('div');
    div.className = 'cell';
    div.dataset.idx = String(idx);
    const colorClass = `color-${cell.region % 10}`;
    div.classList.add(colorClass);
    applyCellState(div, cell);
    boardEl.appendChild(div);
  });
}

function applyCellState(el, cell) {
  el.classList.toggle('flagged', cell.flagged && !cell.revealed);
  el.classList.toggle('invalid', cell.invalid && !cell.revealed);
  el.classList.toggle('king', cell.revealed);
}

function markIllegalFromKing(idx) {
  illegalZone(idx).forEach((i) => {
    if (!state.cells[i].revealed) {
      state.cells[i].invalid = true;
      state.cells[i].flagged = false;
    }
  });
}

function revealKing(idx) {
  const cell = state.cells[idx];
  if (cell.revealed) return;
  cell.revealed = true;
  cell.flagged = false;
  cell.invalid = false;
  state.revealedCount += 1;
  if (SHOW_ILLEGAL_ON_KING) {
    markIllegalFromKing(idx);
  }
}

function applyDifficultyReveal(diff) {
  const count = diff === 'easy' ? 2 : diff === 'medium' ? 1 : 0;
  if (count === 0) return;
  const hidden = state.kings.filter((k) => !state.cells[k].revealed);
  const revealCount = Math.min(count, hidden.length);
  for (let i = 0; i < revealCount; i += 1) {
    const pick = randPick(hidden);
    const index = hidden.indexOf(pick);
    if (index >= 0) hidden.splice(index, 1);
    revealKing(pick);
    updateBoardCell(pick);
  }
}

function checkCell(idx) {
  const cell = state.cells[idx];
  if (cell.revealed) return;
  if (cell.isKing) {
    revealKing(idx);
    if (SHOW_ILLEGAL_ON_KING) {
      illegalZone(idx).forEach((i) => updateBoardCell(i));
    }
  } else {
    cell.invalid = true;
    cell.flagged = false;
  }
  updateBoardCell(idx);
  checkWin();
}

function updateBoardCell(idx) {
  const el = boardEl.querySelector(`[data-idx="${idx}"]`);
  if (!el) return;
  applyCellState(el, state.cells[idx]);
}

function checkWin() {
  if (state.revealedCount === state.kings.length) {
    stopTimer();
    updateStatsUI();
    const kingEls = boardEl.querySelectorAll('.cell.king');
    kingEls.forEach((el) => el.classList.add('win-pop'));
    setTimeout(() => {
      kingEls.forEach((el) => el.classList.remove('win-pop'));
      overlay.hidden = false;
    }, 1000);
    if (titleEl) titleEl.classList.add('win-celebration');
    if (boardContainerEl) boardContainerEl.classList.add('win-celebration');
    setTimeout(() => {
      if (titleEl) titleEl.classList.remove('win-celebration');
      if (boardContainerEl) boardContainerEl.classList.remove('win-celebration');
    }, 800);
  }
}

function toggleFlag(idx) {
  const cell = state.cells[idx];
  if (cell.revealed || cell.invalid) return;
  cell.flagged = !cell.flagged;
  updateBoardCell(idx);
}

function setFlagWithCount(idx, desired, source) {
  const cell = state.cells[idx];
  if (cell.revealed || cell.invalid) return false;
  if (cell.flagged === desired) return false;
  cell.flagged = desired;
  updateBoardCell(idx);
  if (source === 'drag') dragMarkCount += 1;
  return true;
}

function setupEvents() {
  boardEl.addEventListener('click', (e) => {
    if (lastPointerType === 'touch') return;
    const target = e.target.closest('.cell');
    if (!target) return;
    if (suppressClick) {
      suppressClick = false;
      return;
    }
    const idx = Number(target.dataset.idx);
    clickCount += 1;
    toggleFlag(idx);
  });

  boardEl.addEventListener('dblclick', (e) => {
    const target = e.target.closest('.cell');
    if (!target) return;
    const idx = Number(target.dataset.idx);
    checkCell(idx);
    updateBoardCell(idx);
  });

  boardEl.addEventListener('pointerdown', (e) => {
    lastPointerType = e.pointerType || 'mouse';
    const target = e.target.closest('.cell');
    if (!target) return;
    dragging = true;
    dragMoved = false;
    dragStartIdx = Number(target.dataset.idx);
    lastDragIdx = dragStartIdx;
    dragVisited = new Set([dragStartIdx]);
    dragMode = state.cells[dragStartIdx].flagged ? 'remove' : 'add';
  });

  boardEl.addEventListener('pointerover', (e) => {
    if (!dragging) return;
    if (e.pointerType === 'touch') return;
    const target = e.target.closest('.cell');
    if (!target) return;
    const idx = Number(target.dataset.idx);
    if (idx === lastDragIdx) return;
    lastDragIdx = idx;
    if (!dragMoved) {
      dragMoved = true;
      if (!dragVisited.has(dragStartIdx)) {
        dragVisited.add(dragStartIdx);
      }
      setFlagWithCount(dragStartIdx, dragMode === 'add', 'drag');
    }
    if (!dragVisited.has(idx)) {
      dragVisited.add(idx);
      setFlagWithCount(idx, dragMode === 'add', 'drag');
    }
  });

  window.addEventListener('pointermove', (e) => {
    if (!dragging) return;
    if (e.pointerType !== 'touch') return;
    const el = document.elementFromPoint(e.clientX, e.clientY);
    if (!el) return;
    const target = el.closest && el.closest('.cell');
    if (!target) return;
    const idx = Number(target.dataset.idx);
    if (idx === lastDragIdx) return;
    lastDragIdx = idx;
    if (!dragMoved) {
      dragMoved = true;
      if (!dragVisited.has(dragStartIdx)) {
        dragVisited.add(dragStartIdx);
      }
      setFlagWithCount(dragStartIdx, dragMode === 'add', 'drag');
    }
    if (!dragVisited.has(idx)) {
      dragVisited.add(idx);
      setFlagWithCount(idx, dragMode === 'add', 'drag');
    }
  });

  function resetPointerState() {
    dragging = false;
    dragMoved = false;
    dragStartIdx = -1;
    lastDragIdx = -1;
    dragVisited.clear();
    dragMode = 'add';
  }

  window.addEventListener('pointerup', (e) => {
    const wasDragMoved = dragMoved;
    dragging = false;
    if (dragMoved) {
      suppressClick = true;
      setTimeout(() => {
        suppressClick = false;
      }, 0);
    }
    dragMoved = false;
    dragStartIdx = -1;
    lastDragIdx = -1;
    dragVisited.clear();
    if (e.pointerType === 'touch') {
      const target = e.target.closest && e.target.closest('.cell');
      if (!target) return;
      const idx = Number(target.dataset.idx);
      const now = Date.now();
      if (lastTap.idx === idx && now - lastTap.time < 350) {
        const timerId = tapTimers.get(idx);
        if (timerId) {
          clearTimeout(timerId);
          tapTimers.delete(idx);
        }
        checkCell(idx);
        updateBoardCell(idx);
        lastTap = { time: 0, idx: -1 };
      } else {
        lastTap = { time: now, idx };
        if (!wasDragMoved) {
          const timerId = setTimeout(() => {
            clickCount += 1;
            toggleFlag(idx);
            tapTimers.delete(idx);
          }, 300);
          tapTimers.set(idx, timerId);
        }
      }
    }
  });

  window.addEventListener('pointercancel', () => {
    resetPointerState();
    suppressClick = false;
  });

  hintBtn.addEventListener('click', () => {
    const hidden = state.kings.filter((k) => !state.cells[k].revealed);
    if (hidden.length === 0) return;
    const pick = randPick(hidden);
    revealKing(pick);
    updateBoardCell(pick);
    if (SHOW_ILLEGAL_ON_KING) {
      illegalZone(pick).forEach((i) => updateBoardCell(i));
    }
    checkWin();
  });

  newBtn.addEventListener('click', () => {
    overlay.hidden = true;
    difficultyOverlay.hidden = false;
  });

  nextBtn.addEventListener('click', () => {
    overlay.hidden = true;
    level += 1;
    startGame(currentDifficulty);
  });

  diffButtons.forEach((btn) => {
    btn.addEventListener('click', () => {
      const diff = btn.dataset.diff || 'hard';
      currentDifficulty = diff;
      difficultyOverlay.hidden = true;
      startGame(diff);
    });
  });

  helpBtn.addEventListener('click', () => {
    helpOverlay.hidden = false;
  });

  helpCloseBtn.addEventListener('click', () => {
    helpOverlay.hidden = true;
  });

  helpOverlay.addEventListener('click', (e) => {
    if (e.target === helpOverlay) {
      helpOverlay.hidden = true;
    }
  });
}

function startGame(difficulty = 'hard') {
  size = weightedSizeForLevel(level);
  levelEl.textContent = String(level);
  overlay.hidden = true;
  if (titleEl) titleEl.classList.remove('win-celebration');
  if (boardContainerEl) boardContainerEl.classList.remove('win-celebration');
  resetStats();
  state = buildState();
  renderBoard();
  applyDifficultyReveal(difficulty);
  startTimer();
}

function resetStats() {
  clickCount = 0;
  dragMarkCount = 0;
  updateStatsUI();
}

function startTimer() {
  stopTimer();
  startTime = Date.now();
  timerId = window.setInterval(() => {
    updateStatsUI();
  }, 1000);
}

function stopTimer() {
  if (timerId) {
    clearInterval(timerId);
    timerId = null;
  }
}

function formatTime(ms) {
  const total = Math.floor(ms / 1000);
  const m = String(Math.floor(total / 60)).padStart(2, '0');
  const s = String(total % 60).padStart(2, '0');
  return `${m}:${s}`;
}

function updateStatsUI() {
  const elapsed = startTime ? Date.now() - startTime : 0;
  if (statClicksEl) statClicksEl.textContent = String(clickCount);
  if (statMarksEl) statMarksEl.textContent = String(dragMarkCount);
  if (statTimeEl) statTimeEl.textContent = formatTime(elapsed);
}

setupEvents();
startGame();
