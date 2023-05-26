-- Sunfish

-- sunfish.lua, a human transpiler work of https://github.com/thomasahle/sunfish
-- embarassing and ugly translation done by Soumith Chintala
-- Code License: BSD

-- The table size is the maximum number of elements in the transposition table.
local TABLE_SIZE = 1e6

-- This constant controls how much time we spend on looking for optimal moves.
local NODES_SEARCHED = 1e4

-- Mate value must be greater than 8*queen + 2*(rook+knight+bishop)
-- King value is set to twice this value such that if the opponent is
-- 8 queens up, but we got the king, we still exceed MATE_VALUE.
local MATE_VALUE = 30000

-- Our board is represented as a 120 character string. The padding allows for
-- fast detection of moves that don't stay within the board.
local A1, H1, A8, H8 = 91, 98, 21, 28
local initial =
    '         \n' .. --   0 -  9
    '         \n' .. --  10 - 19
    ' rnbqkbnr\n' .. --  20 - 29
    ' pppppppp\n' .. --  30 - 39
    ' ........\n' .. --  40 - 49
    ' ........\n' .. --  50 - 59
    ' ........\n' .. --  60 - 69
    ' ........\n' .. --  70 - 79
    ' PPPPPPPP\n' .. --  80 - 89
    ' RNBQKBNR\n' .. --  90 - 99
    '         \n' .. -- 100 -109
    '          '     -- 110 -119

local __1 = 1 -- 1-index correction
-------------------------------------------------------------------------------
-- Move and evaluation tables
-------------------------------------------------------------------------------
local N, E, S, W = -10, 1, 10, -1
local directions = {
    P = {N, 2*N, N+W, N+E},
    N = {2*N+E, N+2*E, S+2*E, 2*S+E, 2*S+W, S+2*W, N+2*W, 2*N+W},
    B = {N+E, S+E, S+W, N+W},
    R = {N, E, S, W},
    Q = {N, E, S, W, N+E, S+E, S+W, N+W},
    K = {N, E, S, W, N+E, S+E, S+W, N+W}
}

local pst = {
    P = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 198, 198, 198, 198, 198, 198, 198, 198, 0,
        0, 178, 198, 198, 198, 198, 198, 198, 178, 0,
        0, 178, 198, 198, 198, 198, 198, 198, 178, 0,
        0, 178, 198, 208, 218, 218, 208, 198, 178, 0,
        0, 178, 198, 218, 238, 238, 218, 198, 178, 0,
        0, 178, 198, 208, 218, 218, 208, 198, 178, 0,
        0, 178, 198, 198, 198, 198, 198, 198, 178, 0,
        0, 198, 198, 198, 198, 198, 198, 198, 198, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    B = {
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 797, 824, 817, 808, 808, 817, 824, 797, 0,
        0, 814, 841, 834, 825, 825, 834, 841, 814, 0,
        0, 818, 845, 838, 829, 829, 838, 845, 818, 0,
        0, 824, 851, 844, 835, 835, 844, 851, 824, 0,
        0, 827, 854, 847, 838, 838, 847, 854, 827, 0,
        0, 826, 853, 846, 837, 837, 846, 853, 826, 0,
        0, 817, 844, 837, 828, 828, 837, 844, 817, 0,
        0, 792, 819, 812, 803, 803, 812, 819, 792, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    N = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 627, 762, 786, 798, 798, 786, 762, 627, 0,
        0, 763, 798, 822, 834, 834, 822, 798, 763, 0,
        0, 817, 852, 876, 888, 888, 876, 852, 817, 0,
        0, 797, 832, 856, 868, 868, 856, 832, 797, 0,
        0, 799, 834, 858, 870, 870, 858, 834, 799, 0,
        0, 758, 793, 817, 829, 829, 817, 793, 758, 0,
        0, 739, 774, 798, 810, 810, 798, 774, 739, 0,
        0, 683, 718, 742, 754, 754, 742, 718, 683, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    R = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    Q = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    K = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 60098, 60132, 60073, 60025, 60025, 60073, 60132, 60098, 0,
        0, 60119, 60153, 60094, 60046, 60046, 60094, 60153, 60119, 0,
        0, 60146, 60180, 60121, 60073, 60073, 60121, 60180, 60146, 0,
        0, 60173, 60207, 60148, 60100, 60100, 60148, 60207, 60173, 0,
        0, 60196, 60230, 60171, 60123, 60123, 60171, 60230, 60196, 0,
        0, 60224, 60258, 60199, 60151, 60151, 60199, 60258, 60224, 0,
        0, 60287, 60321, 60262, 60214, 60214, 60262, 60321, 60287, 0,
        0, 60298, 60332, 60273, 60225, 60225, 60273, 60332, 60298, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
}

-------------------------------------------------------------------------------
-- Chess logic
-------------------------------------------------------------------------------
local function isspace(s)
   if s == ' ' or s == '\n' then
      return true
   else
      return false
   end
end

local special = '. \n'

local function isupper(s)
   if special:find(s) then return false end
   return s:upper() == s
end

local function islower(s)
   if special:find(s) then return false end
   return s:lower() == s
end

-- super inefficient
local function swapcase(s)
   local s2 = ''
   for i=1,#s do
      local c = s:sub(i, i)
      if islower(c) then
s2 = s2 .. c:upper()
      else
s2 = s2 .. c:lower()
      end
   end
   return s2
end

local Position = {}

function Position.new(board, score, wc, bc, ep, kp)
   --[[  A state of a chess game
      board -- a 120 char representation of the board
      score -- the board evaluation
      wc -- the castling rights
      bc -- the opponent castling rights
      ep - the en passant square
      kp - the king passant square
   ]]--
   local self = {}
   self.board = board
   self.score = score
   self.wc = wc
   self.bc = bc
   self.ep = ep
   self.kp = kp
   for k,v in pairs(Position) do self[k] = v end
   return self
end

function Position:genMoves()
   local moves = {}
   -- For each of our pieces, iterate through each possible 'ray' of moves,
   -- as defined in the 'directions' map. The rays are broken e.g. by
   -- captures or immediately in case of pieces such as knights.
   for i = 1 - __1, #self.board - __1 do
      local p = self.board:sub(i + __1, i + __1)
      if isupper(p) and directions[p] then
for _, d in ipairs(directions[p]) do
   local limit = (i+d) + (10000) * d -- fake limit
   for j=i+d, limit, d do
      local q = self.board:sub(j + __1, j + __1)
      -- Stay inside the board
      if isspace(self.board:sub(j + __1, j + __1)) then break; end
      -- Castling
      if i == A1 and q == 'K' and self.wc[0 + __1] then
 table.insert(moves,  {j, j-2})
      end
      if i == H1 and q == 'K' and self.wc[1 + __1] then
 table.insert(moves,  {j, j+2})
      end
      -- print(p, q, i, d, j)
      -- No friendly captures
      if isupper(q) then break; end
      -- Special pawn stuff
      if p == 'P' and (d == N+W or d == N+E) and q == '.' and j ~= self.ep and j ~= self.kp then
 break;
      end
      if p == 'P' and (d == N or d == 2*N) and q ~= '.' then
 break;
      end
      if p == 'P' and d == 2*N and (i < A1+N or self.board:sub(i+N + __1, i+N + __1) ~= '.') then
 break;
      end
      -- Move it
      table.insert(moves, {i, j})
      -- print(i, j)
      -- Stop crawlers from sliding
      if p == 'P' or p == 'N' or p == 'K' then break; end
      -- No sliding after captures
      if islower(q) then break; end
   end
end
      end
   end
   return moves
end


function Position:rotate()
   return self.new(
      swapcase(self.board:reverse()), -self.score,
      self.bc, self.wc, 119-self.ep, 119-self.kp)
end

function Position:move(move)
   assert(move) -- move is zero-indexed
   local i, j = move[0 + __1], move[1 + __1]
   local p, q = self.board:sub(i + __1, i + __1), self.board:sub(j + __1, j + __1)
   local function put(board, i, p)
      return board:sub(1, i-1) .. p .. board:sub(i+1)
   end
   -- Copy variables and reset ep and kp
   local board = self.board
   local wc, bc, ep, kp = self.wc, self.bc, 0, 0
   local score = self.score + self:value(move)
   -- Actual move
   board = put(board, j + __1, board:sub(i + __1, i + __1))
   board = put(board, i + __1, '.')
   -- Castling rights
   if i == A1 then wc = {false, wc[0 + __1]}; end
   if i == H1 then wc = {wc[0 + __1], false}; end
   if j == A8 then bc = {bc[0 + __1], false}; end
   if j == H8 then bc = {false, bc[1 + __1]}; end
   -- Castling
   if p == 'K' then
      wc = {false, false}
      if math.abs(j-i) == 2 then
kp = math.floor((i+j)/2)
board = put(board, j < i and A1 + __1 or H1 + __1 , '.')
board = put(board, kp + __1, 'R')
      end
   end
   -- Special pawn stuff
   if p == 'P' then
      if A8 <= j and j <= H8 then
board = put(board, j + __1, 'Q')
      end
      if j - i == 2*N then
ep = i + N
      end
      if ((j - i) == N+W or (j - i) == N+E) and q == '.' then
board = put(board, j+S + __1, '.')
      end
   end
   -- We rotate the returned position, so it's ready for the next player
   return self.new(board, score, wc, bc, ep, kp):rotate()
end

function Position:value(move)
   local i, j = move[0 + __1], move[1 + __1]
   local p, q = self.board:sub(i + __1, i + __1), self.board:sub(j + __1, j + __1)
   -- Actual move
   local score = pst[p][j + __1] - pst[p][i + __1]
   -- Capture
   if islower(q) then
      score = score + pst[q:upper()][j + __1]
   end
   -- Castling check detection
   if math.abs(j-self.kp) < 2 then
      score = score + pst['K'][j + __1]
   end
   -- Castling
   if p == 'K' and math.abs(i-j) == 2 then
      score = score + pst['R'][math.floor((i+j)/2) + __1]
      score = score - pst['R'][j < i and A1 + __1 or H1 + __1]
   end
   -- Special pawn stuff
   if p == 'P' then
      if A8 <= j and j <= H8 then
score = score + pst['Q'][j + __1] - pst['P'][j + __1]
      end
      if j == self.ep then
score = score + pst['P'][j+S + __1]
      end
   end
   return score
end

-- the lamest possible and most embarassing namedtuple hasher ordered dict
-- I apologize to the world for writing it.
local tp = {}
local tp_index = {}
local tp_count = 0

local function tp_set(pos, val)
   local b1 = pos.bc[1] and 'true' or 'false'
   local b2 = pos.bc[2] and 'true' or 'false'
   local w1 = pos.bc[1] and 'true' or 'false'
   local w2 = pos.bc[2] and 'true' or 'false'
   local hash = pos.board .. ';' .. pos.score .. ';' .. w1 .. ';' .. w2 .. ';'
      .. b1 .. ';' .. b2 .. ';' .. pos.ep .. ';' .. pos.kp
   tp[hash] = val
   tp_index[#tp_index + 1] = hash
   tp_count = tp_count + 1
end

local function tp_get(pos)
   local b1 = pos.bc[1] and 'true' or 'false'
   local b2 = pos.bc[2] and 'true' or 'false'
   local w1 = pos.bc[1] and 'true' or 'false'
   local w2 = pos.bc[2] and 'true' or 'false'
   local hash = pos.board .. ';' .. pos.score .. ';' .. w1 .. ';' .. w2 .. ';'
      .. b1 .. ';' .. b2 .. ';' .. pos.ep .. ';' .. pos.kp
   return tp[hash]
end

local function tp_popitem()
   tp[tp_index[#tp_index]] = nil
   tp_index[#tp_index] = nil
   tp_count = tp_count - 1
end

-------------------------------------------------------------------------------
-- Search logic
-------------------------------------------------------------------------------

local nodes = 0

local function bound(pos, gamma, depth)
   --[[ returns s(pos) <= r < gamma    if s(pos) < gamma
        returns s(pos) >= r >= gamma   if s(pos) >= gamma ]]--
    nodes = nodes + 1

    -- Look in the table if we have already searched this position before.
    -- We use the table value if it was done with at least as deep a search
    -- as ours, and the gamma value is compatible.
    local entry = tp_get(pos)
    assert(depth)
    if entry ~= nil and entry.depth >= depth and (
            entry.score < entry.gamma and entry.score < gamma or
            entry.score >= entry.gamma and entry.score >= gamma) then
        return entry.score
    end

    -- Stop searching if we have won/lost.
    if math.abs(pos.score) >= MATE_VALUE then
        return pos.score
    end

    -- Null move. Is also used for stalemate checking
    local nullscore = depth > 0 and -bound(pos:rotate(), 1-gamma, depth-3) or pos.score
    --nullscore = -MATE_VALUE*3 if depth > 0 else pos.score
    if nullscore >= gamma then
        return nullscore
    end

    -- We generate all possible, pseudo legal moves and order them to provoke
    -- cuts. At the next level of the tree we are going to minimize the score.
    -- This can be shown equal to maximizing the negative score, with a slightly
    -- adjusted gamma value.
    local best, bmove = -3*MATE_VALUE, nil
    local moves = pos:genMoves()
    local function sorter(a, b)
       local va = pos:value(a)
       local vb = pos:value(b)
       if va ~= vb then
 return va > vb
       else
 if a[1] == b[1] then
    return a[2] > b[2]
 else
    return a[1] < b[1]
 end
       end
    end
    table.sort(moves, sorter)
    for _,move in ipairs(moves) do
       -- We check captures with the value function, as it also contains ep and kp
       if depth <= 0 and pos:value(move) < 150 then
 break
       end
       local score = -bound(pos:move(move), 1-gamma, depth-1)
       -- print(move[1] .. ' ' ..  move[2] .. ' ' .. score)
        if score > best then
  best = score
  bmove = move
end
        if score >= gamma then
  break
end
    end

    -- If there are no captures, or just not any good ones, stand pat
    if depth <= 0 and best < nullscore then
       return nullscore
    end
    -- Check for stalemate. If best move loses king, but not doing anything
    -- would save us. Not at all a perfect check.
    if depth > 0 and (best <= -MATE_VALUE) and nullscore > -MATE_VALUE then
       best = 0
    end

    -- We save the found move together with the score, so we can retrieve it in
    -- the play loop. We also trim the transposition table in FILO order.
    -- We prefer fail-high moves, as they are the ones we can build our pv from.
    if entry == nil or depth >= entry.depth and best >= gamma then
       tp_set(pos, {depth = depth, score = best, gamma = gamma, move = bmove})
       if tp_count > TABLE_SIZE then
 tp_popitem()
       end
    end
    return best
end

local function search(pos, maxn)
   -- Iterative deepening MTD-bi search
   maxn = maxn or NODES_SEARCHED
   nodes = 0 -- the global value "nodes"
   local score

   -- We limit the depth to some constant, so we don't get a stack overflow in
   -- the end game.
   for depth=1,98 do
      -- The inner loop is a binary search on the score of the position.
      -- Inv: lower <= score <= upper
      -- However this may be broken by values from the transposition table,
      -- as they don't have the same concept of p(score). Hence we just use
      -- 'lower < upper - margin' as the loop condition.
      local lower, upper = -3*MATE_VALUE, 3*MATE_VALUE
      while lower < upper - 3 do
local gamma = math.floor((lower+upper+1)/2)
score = bound(pos, gamma, depth)
-- print(nodes, gamma, score)
assert(score)
if score >= gamma then
   lower = score
end
if score < gamma then
   upper = score
end
      end
      assert(score)

      -- print(string.format("Searched %d nodes. Depth %d. Score %d(%d/%d)", nodes, depth, score, lower, upper))

      -- We stop deepening if the global N counter shows we have spent too
      -- long, or if we have already won the game.
      if nodes >= maxn or math.abs(score) >= MATE_VALUE then
break
      end
   end

   -- If the game hasn't finished we can retrieve our move from the
   -- transposition table.
   local entry = tp_get(pos)
   if entry ~= nil then
      return entry.move, score
   end
   return nil, score
end

local function parse(c)
   if not c then return nil end
   local p, v = c:sub(1,1), c:sub(2,2)
   if not (p and v and tonumber(v)) then return nil end

   local fil, rank = string.byte(p) - string.byte('a'), tonumber(v) - 1
   return A1 + fil - 10*rank
end







-- My logic

mode = "bot" -- either "bot" or "natural"

display_width = 0
display_height = 0
padding = 0
piece_interval = 0

turn = "white"
valid_move = true
selected_piece = nil
pieces = {"rook", "knight", "bishop", "queen", "king", "bishop", "knight", "rook"}
images = {}
board = {}
overlay_board = {}
white_graveyard = {}
black_graveyard = {}
position = Position.new(initial, 0, {true,true}, {true,true}, 0, 0)

function on.construction()
    for img_name, img_resource in pairs(_R.IMG) do
        images[img_name] = image.new(img_resource)
    end
   
    -- Initialize board matrix
    initialize_chess_board()
    initialize_overlay_board()
end

function isPawnValid(yInitial, xInitial, team, xDiff, yDiff)
    advance = 1
    oppositeTeam = "white"
    if string.lower(team) == "white" then
        advance = -1
        oppositeTeam = "black"
    end
   
    if math.abs(xDiff) == 1 and math.abs(yDiff) == 1 then
        if (yInitial + advance) > 0 and (yInitial + advance) < 8 then
            return ((xInitial + 1) < 8 and board[yInitial + advance][xInitial + 1] ~= nil and board[yInitial + advance][xInitial + 1].team == oppositeTeam) or ((xInitial - 1) > 0 and board[yInitial + advance][xInitial - 1] ~= nil and board[yInitial + advance][xInitial - 1].team == oppositeTeam)
        end
    end

    yMaxDiff = 2
    if (yInitial == 2 and string.lower(team) == "black") or (yInitial == 7 and string.lower(team) == "white") then
        yMaxDiff = 3
    end

    if xDiff == 0 then
        if turn == "white" then
            return yDiff < 0 and yDiff > (-1 * yMaxDiff)
        else
            return yDiff > 0 and yDiff < yMaxDiff
        end
    end
   
    return false
end

function isRookValid(xDiff, yDiff)
    return (xDiff == 0 and yDiff ~= 0) or (xDiff ~= 0 and yDiff == 0)
end

function isBishopValid(xDiff, yDiff)
    return math.abs(xDiff) == math.abs(yDiff)
end

function isKnightValid(xDiff, yDiff)
    return (math.abs(xDiff) == 2 * math.abs(yDiff)) or (math.abs(yDiff) == 2 * math.abs(xDiff))
end

function isKingValid(xDiff, yDiff)
    return math.abs(xDiff) < 2 and math.abs(yDiff) < 2
end

function is_valid_move(newX, newY, oldX, oldY, piece)
    if board[newY][newX] ~= nil and board[newY][newX].team == turn then
        return false
    end
   
    team = ""
    piece = splitStringByUnderscore(piece)
    for i, word in ipairs(piece) do
        if i == 2 then
            piece = word
        elseif i == 1 then
            team = word
        end
    end
   
    xDiff = newX - oldX
    yDiff = newY - oldY
   
    skippingOverPieces = false
    if yDiff == 0 and math.abs(xDiff) > 0 then
        i = 0
        while math.abs(i) < math.abs(xDiff) do
            i = i+sign(xDiff)
            if board[oldY][oldX + i] ~= nil then
                skippingOverPieces = true
                break
            end
        end
    elseif xDiff == 0 and math.abs(yDiff) > 0 then
        i = 0
        while math.abs(i) < math.abs(yDiff) do
            i = i+sign(yDiff)
            if board[oldY + i][oldX] ~= nil then
                skippingOverPieces = true
                break
            end
        end
    elseif math.abs(yDiff) == math.abs(xDiff) then
        i = 0
        j = 0
        while math.abs(i) < math.abs(xDiff) and math.abs(j) < math.abs(yDiff) do
            i = i+sign(xDiff)
            j = j+sign(yDiff)
            if board[oldY + j][oldX + i] ~= nil then
                skippingOverPieces = true
                break
            end
        end
       
        if board[oldY + j][oldX + i] ~= nil and board[oldY + j][oldX + i].team ~= turn then
            skippingOverPieces = false
        end
    end
       
    if piece == "pawn" then
        return isPawnValid(oldY, oldX, team, xDiff, yDiff) and skippingOverPieces == false
    elseif piece == "rook" then
        return isRookValid(xDiff, yDiff) and skippingOverPieces == false
    elseif piece == "bishop" then
        return isBishopValid(xDiff, yDiff) and skippingOverPieces == false
    elseif piece == "knight" then
        return isKnightValid(xDiff, yDiff)
    elseif piece == "king" then
        return isKingValid(xDiff, yDiff)
    elseif piece == "queen" then
        return (isRookValid(xDiff, yDiff) or isBishopValid(xDiff, yDiff)) and skippingOverPieces == false
    end
   
    return false
end

function sign(num)
    if num > 0 then
        return 1
    elseif num < 0 then
        return -1
    else
        return 0
    end
end

function splitStringByUnderscore(str)
  local result = {}
 
  for word in string.gmatch(str, "[^_]+") do
    table.insert(result, word)
  end
 
  return result
end

function draw_chess_pieces(gc)
    for i = 0, 7 do
        for j = 0, 7 do
            if board[i+1][j+1] ~= nil then
                piece = images[board[i+1][j+1].piece]
                piece = piece:copy(piece_interval - 2, piece_interval - 2)
                gc:drawImage(piece, padding + (j * piece_interval), i * piece_interval)
            end
        end
    end
end

function draw_overlay_chess_pieces(gc)
    for i = 0, 7 do
        for j = 0, 7 do
            if overlay_board[i+1][j+1] ~= nil then
                overlay_piece = overlay_board[i+1][j+1]
                if is_valid_move(j+1, i+1, overlay_piece.originalX, overlay_piece.originalY, overlay_piece.piece) then
                    gc:setColorRGB(0x00FF00)
                    gc:drawRect(padding + (j * piece_interval), i * piece_interval, piece_interval, piece_interval)
                    valid_move = true
                else
                    gc:setColorRGB(0xFF0000)
                    gc:drawRect(padding + (j * piece_interval), i * piece_interval, piece_interval, piece_interval)
                    valid_move = false
                end
                piece = images[overlay_board[i+1][j+1].piece]
                piece = piece:copy(piece_interval - 2, piece_interval - 2)
                gc:drawImage(piece, padding + (j * piece_interval), i * piece_interval)
            end
        end
    end
end

function initialize_chess_board()
    for i=1, 8 do
        board[i] = {}
        for j=1, 8 do
            if i == 1 then
                board[i][j] = {
                    team = "black",
                    piece = "Black_" .. pieces[j]
                }
            elseif i == 2 then
                board[i][j] = {
                    team = "black",
                    piece = "Black_pawn"
                }
            elseif i == 7 then
                board[i][j] = {
                    team = "white",
                    piece = "White_pawn"
                }
            elseif i == 8 then
                board[i][j] = {
                    team = "white",
                    piece = "White_" .. pieces[j]
                }
            else
                board[i][j] = nil
            end
        end
    end
end

function initialize_overlay_board()
    for i = 1, 8 do
        overlay_board[i] = {}
        for j = 1, 8 do
            overlay_board[i][j] = nil
        end
    end
end

function on.mouseDown(x, y)
    if selected_piece ~= nil then
        return
    end
    if x > padding and x < (padding + display_height) then
        if y > 0 and y < display_height then
            column = math.ceil((x - padding) / piece_interval)
            row = math.ceil(y / piece_interval)
            piece = nil
            if board[row][column] ~= nil then
                piece = board[row][column]
            end
            if piece == nil then
                return
            end
            if piece.team == turn then
                overlay_board[row][column] = {
                    team = piece.team,
                    piece = piece.piece,
                    originalX = column,
                    originalY = row
                }
                board[row][column] = nil
                if piece ~= nil then
                    selected_piece = { x = column, y = row }
                end
            end
        end
    end
end

function on.arrowUp(overlapHeight)
    if selected_piece ~= nil then
        overlay_piece = overlay_board[selected_piece.y][selected_piece.x]
        if selected_piece.y - 1 < 1 then
            return
        end
        overlay_board[selected_piece.y - 1][selected_piece.x] = overlay_piece
        overlay_board[selected_piece.y][selected_piece.x] = nil
        selected_piece.y = selected_piece.y - 1
    end
end

function on.arrowLeft(overlapHeight)
    if selected_piece ~= nil then
        overlay_piece = overlay_board[selected_piece.y][selected_piece.x]
        if selected_piece.x - 1 < 1 then
            return
        end
        overlay_board[selected_piece.y][selected_piece.x - 1] = overlay_piece
        overlay_board[selected_piece.y][selected_piece.x] = nil
        selected_piece.x = selected_piece.x - 1
    end
end

function on.arrowRight(overlapHeight)
    if selected_piece ~= nil then
        overlay_piece = overlay_board[selected_piece.y][selected_piece.x]
        if selected_piece.x + 1 > 8 then
            return
        end
        overlay_board[selected_piece.y][selected_piece.x + 1] = overlay_piece
        overlay_board[selected_piece.y][selected_piece.x] = nil
        selected_piece.x = selected_piece.x + 1
    end
end

function on.arrowDown(overlapHeight)
    if selected_piece ~= nil then
        overlay_piece = overlay_board[selected_piece.y][selected_piece.x]
        if selected_piece.y + 1 > 8 then
            return
        end
        overlay_board[selected_piece.y + 1][selected_piece.x] = overlay_piece
        overlay_board[selected_piece.y][selected_piece.x] = nil
        selected_piece.y = selected_piece.y + 1
    end
end

function on.escapeKey()
    overlay_piece = overlay_board[selected_piece.y][selected_piece.x]
    board[overlay_piece.originalY][overlay_piece.originalX] = {
        team = overlay_piece.team,
        piece = overlay_piece.piece
    }
    overlay_board[selected_piece.y][selected_piece.x] = nil
    selected_piece = nil
    valid_move = true
end

function getSelectedPiece()
    for i = 1, 8 do
        for j = 1, 8 do
            if overlay_board[i][j] ~= nil then
                return overlay_board[i][j].piece
            end
        end
    end
   
    return "none"
end

function on.enterKey()
    active_piece = overlay_board[selected_piece.y][selected_piece.x]
   
    if valid_move then
        move = {parse(translatePos(active_piece.originalX, active_piece.originalY)), parse(translatePos(selected_piece.x, selected_piece.y))}

        if board[selected_piece.y][selected_piece.x] ~= nil then
            currentPiece = board[selected_piece.y][selected_piece.x]
            if currentPiece.team == "white" and turn == "black" then
                table.insert(white_graveyard, currentPiece.piece)
                board[selected_piece.y][selected_piece.x] = nil
            elseif currentPiece.team == "black" and turn == "white" then
                table.insert(black_graveyard, currentPiece.piece)
                board[selected_piece.y][selected_piece.x] = nil
            end
        end
   
        board[selected_piece.y][selected_piece.x] = {
            piece = active_piece.piece,
            team = active_piece.team
        }
        overlay_board[selected_piece.y][selected_piece.x] = nil
       
        if turn == "white" then
            turn = "black"
        else
            turn = "white"
        end
       
        position = position:move(move)
        selected_piece = nil
    end
   
    if turn == "black" and mode == "bot" then
        local move, score = search(position)
        assert(score)
        assert(move)
        position = position:move(move)
        themove = translateMove(move)
        moving_piece = board[themove[1][2]][themove[1][1]]
        board[themove[1][2]][themove[1][1]] = nil
        new_position = board[themove[2][2]][themove[2][1]]
        if new_position ~= nil then
            if new_position.team == "white" and turn == "black" then
                table.insert(white_graveyard, new_position.piece)
                board[themove[1][2]][themove[1][1]] = nil
            end
        end
        board[themove[2][2]][themove[2][1]] = moving_piece
       
        turn = "white"
    end
end

function display_white_graveyard(gc)
    initial_x = 2
    initial_y = 50
    offset_x = 0
    offset_y = 0
    for i, v in ipairs(white_graveyard) do
        piece_img = images[v]
        piece_img = piece_img:copy(piece_interval - 4, piece_interval - 4)
        offset_x = 0
        offset_y = math.ceil(i / 2) * piece_interval
        if i % 2 ~= 0 then
            offset_x = piece_interval
        end
        gc:drawImage(piece_img, initial_x + offset_x, initial_y + offset_y)
    end
end

function display_black_graveyard(gc)
    initial_x = 265
    initial_y = 50
    offset_x = 0
    offset_y = 0
    for i, v in ipairs(black_graveyard) do
        piece_img = images[v]
        piece_img = piece_img:copy(piece_interval - 4, piece_interval - 4)
        offset_x = 0
        offset_y = math.ceil(i / 2) * piece_interval
        if i % 2 == 0 then
            offset_x = piece_interval
        end
        gc:drawImage(piece_img, initial_x + offset_x, initial_y + offset_y)
    end
end

-- Trying to get it to update every move
function on.timer(gc)
    print("hello")
    update(gc)
    timer.start(0.015)
end

function on.paint(gc)
    update(gc)
end

function update(gc)
    -- Meta calculations
    display_width = platform.window:width()
    display_height = platform.window:height()
    padding = (display_width - display_height) / 2
    piece_interval = display_height / 8    
   
    -- Display chessboard
    chessboard = images["Chessboard"]
    height = chessboard:height()
    chessboard = chessboard:copy(display_height, display_height)
    gc:drawImage(chessboard, padding, 0)
       
    -- Display chess pieces according to board matrix
    draw_chess_pieces(gc)
   
    -- Display overlay chess pieces according to overlay matrix
    draw_overlay_chess_pieces(gc)
   
    -- Display information
    gc:setFont("sansserif", "r", 7)
    gc:drawString("Turn: " .. turn, 0, 0)
    gc:drawString("Selected\npiece: \n" .. getSelectedPiece(), 0, 30)
   
    -- Display graveyards
    display_white_graveyard(gc)
    display_black_graveyard(gc)
   
end

function indexOf(element, arr)
    for i, ele in ipairs(arr) do
        if element == ele then
            return i
        end
    end
end

translator = {"a", "b", "c", "d", "e", "f", "g", "h"}

function translatePos(x, y)
    return translator[x] .. tostring(9 - y)
end

function translateBackPos(pos)
    x = pos.sub(1, 2)
    y = pos.sub(2, 3)
    return { indexOf(x, translator), tonumber(math.abs(y - 9)) }
end

function translateMove(move)
    initial_pos = move[1]
    final_pos = move[2]
    initial_x = initial_pos % 10
    initial_y = math.floor(initial_pos / 10)
    final_x = final_pos % 10
    final_y = math.floor(final_pos / 10)
    return { { initial_x, 9 - (initial_y - 1) }, { final_x, 9 - (final_y - 1) } }
end

