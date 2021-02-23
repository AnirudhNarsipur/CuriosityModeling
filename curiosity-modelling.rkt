#lang forge

-- Modelling the 2 Knight endgame.
-- White winning with pawnless double Knight and Black defending with single King.

-------- Signatures --------
-- Colors for the sides
abstract sig Color { otherColor: one Color }
one sig White, Black extends Color {}

-- Files (columns) and left and right adjacencies
abstract sig File {
    left: lone File,
    right: lone File
}
one sig A, B, C, D, E, F, G, H extends File {}

-- Ranks (rows) and top bottom adjacencies
abstract sig Rank {
    above: lone Rank,
    below: lone Rank
}
one sig R1, R2, R3, R4, R5, R6, R7, R8 extends Rank {}

-- Colored pieces
abstract sig Piece { clr : one Color }
sig King, Knight extends Piece {}

-- Board/State
sig Board {
    next: lone Board,
    places: set File -> Rank -> Piece,
    toMove: one Color
}

-------- Helper Functions --------
fun getFile[b: Board, p: Piece]: File {
    -- Returns the File of Piece p on Board b
    (b.places.p).Rank
}
/*
places = Board0->A0->R10->Knight0
getFile[Board0,Knight0] = A0
*/


fun getRank[b: Board, p: Piece]: Rank {
    -- Returns the Rank of Piece p on Board b
    b.places.p[File]
}
/*
places = Board0->A0->R10->Knight0
getRank[Board0,Knight0] = R10
*/


fun getPos[b: Board, p: Piece]: File->Rank {
    b.places.p
}

/*
places = Board0->A0->R10->Knight0
getRank[Board0,Knight0] = A0->R10

*/
fun kingMoves[b: Board, p: King]: set File -> Rank {
    (getFile[b, p] + getFile[b, p].left + getFile[b, p].right) -- File
    ->(getRank[b, p] + (getRank[b, p]).above + (getRank[b, p]).below) -- Rank
    - (getFile[b, p]->getRank[b, p])
}
/*
places =((Board0 A0 R80 King0) (Board0 B0 R20 Knight1) (Board0 B0 R60 King1) (Board0 D0 R70 Knight0))
kingMoves  = ((A0 R50) (A0 R70) (B0 R50) (B0 R60) (B0 R70))


*/

fun knightMoves[b: Board, p: Knight]: set File -> Rank {
    -- One square to left/right and two to above/below
    (getFile[b, p].left + getFile[b, p].right) -- File
    ->(getRank[b, p].above.above + getRank[b, p].below.below) -- Rank
    -- One square to above/below and two to left/right
    + (getFile[b, p].left.left + getFile[b, p].right.right) -- File
    ->(getRank[b, p].above + getRank[b, p].below) -- Rank
}

/*
places =((Board0 A0 R80 King0) (Board0 B0 R20 Knight1) (Board0 B0 R60 King1) (Board0 D0 R70 Knight0))
knightMoves[Board0,Knight0] = ((B0 R60) (B0 R80) (C0 R50) (E0 R50) (F0 R60) (F0 R80))
*/

-------- Statefulness --------
pred initBoard[b: Board] {
   not(Checkmate[b,Black]) and
   not(Stalemate[b,Black])
}

pred canMove[pre: Board, post: Board] {
    one p: Piece | {
        -- This piece is the piece that moves
        p.clr = pre.toMove
        -- The post board has the other color moving
        pre.toMove.otherColor = post.toMove
        -- The piece has indeed moved
        pre.places.p != post.places.p
        -- If p is a King
        (p in King) => {
            post.places.p in kingMoves[pre, p]
        }
        -- If p is Knight
        (p in Knight) => {
            post.places.p in knightMoves[pre, p]
        }
        all other : Piece - p {
            -- None of the other pieces have moved
            pre.places.other = post.places.other
        }
    }
}

pred KingCanMove[b: Board, c: Color] {
    -- The King of Color c has a legal move
    one k: King | {
        k.clr = c
        b.toMove = c
        -- Some position
        some f: File, r: Rank | {
            -- That the king can move to
            f->r in kingMoves[b, k]
            -- That is not in the other colored king's moves
            not f->r in kingMoves[b, King & clr.(c.otherColor)]
            -- That is not in the other colored knight's moves
            all n: Knight | n in clr.(c.otherColor) => {
                not f->r in knightMoves[b, n]
            }
        }
    }
}

pred Check[b: Board, c: Color] {
    -- The King of Color c is in check
    one k : King | {
        k.clr = c
        b.toMove = c
        -- Some position
        some f: File, r: Rank | {
            f->r = getPos[b, k]
            -- That is in the other colored knight's moves
            some n: Knight | n in clr.(c.otherColor) => {
                f->r in knightMoves[b, n]
            }
        }
    }
}

pred Checkmate[b: Board, c: Color] {
    -- When c is to move and is in check and has no moves to prevent checkmate
    b.toMove = c
    Check[b, c]
    not KingCanMove[b, c]
}

inst validCheckmate {
    Piece = King0 + King1 + Knight0 + Knight1
    King = King0 + King1
    Knight = Knight0 + Knight1
    Board = Board0
    Rank = R10 + R20 + R30 + R40 + R50 + R60 + R70 + R80
    R1 = R10
    R2 = R20
    R3 = R30
    R4 = R40
    R5 = R50
    R6 = R60
    R7 = R70
    R8 = R80
    File = A0 + B0 + C0 + D0 + E0 + F0 + G0 + H0
    A = A0
    B = B0
    C = C0
    D = D0
    E = E0
    F = F0
    G = G0
    H = H0
    Color = White0 + Black0
    White = White0
    Black = Black0
    below = R20->R10 + R30->R20 + R40->R30 + R50->R40 + R60->R50 + R70->R60 + R80->R70
    right = A0->B0 + B0->C0 + C0->D0 + D0->E0 + E0->F0 + F0->G0 + G0->H0
    above = R10->R20 + R20->R30 + R30->R40 + R40->R50 + R50->R60 + R60->R70 + R70->R80
    left = B0->A0 + C0->B0 + D0->C0 + E0->D0 + F0->E0 + G0->F0 + H0->G0
    places = Board0->F0->R60->Knight1 + Board0->F0->R80->King1 + Board0->F0->R70->Knight0 + Board0->H0->R80->King0
    clr = King0->Black0 + King1->White0 + Knight0->White0 + Knight1->White0
    otherColor = White0->Black0 + Black0->White0
    toMove = Board0->Black0
}

pred Stalemate[b: Board, c: Color] {
    -- When c is to move, 
    b.toMove = c
    clr.c in King // There is only the king left
    not Check[b, c]
    not KingCanMove[b, c]
}

inst isStalemate {
        Piece = King0 + King1 + Knight0 + Knight1
    King = King0 + King1
    Knight = Knight0 + Knight1
    Board = Board0
    Rank = R10 + R20 + R30 + R40 + R50 + R60 + R70 + R80
    R1 = R10
    R2 = R20
    R3 = R30
    R4 = R40
    R5 = R50
    R6 = R60
    R7 = R70
    R8 = R80
    File = A0 + B0 + C0 + D0 + E0 + F0 + G0 + H0
    A = A0
    B = B0
    C = C0
    D = D0
    E = E0
    F = F0
    G = G0
    H = H0
    Color = White0 + Black0
    White = White0
    Black = Black0
    below = R20->R10 + R30->R20 + R40->R30 + R50->R40 + R60->R50 + R70->R60 + R80->R70
    right = A0->B0 + B0->C0 + C0->D0 + D0->E0 + E0->F0 + F0->G0 + G0->H0
    above = R10->R20 + R20->R30 + R30->R40 + R40->R50 + R50->R60 + R60->R70 + R70->R80
    left = B0->A0 + C0->B0 + D0->C0 + E0->D0 + F0->E0 + G0->F0 + H0->G0
    places =  Board0->A0->R50->Knight1 + Board0->A0->R80->King0 + Board0->C0->R40->King1 + Board0->C0->R60->Knight0 
    clr = King0->Black0 + King1->White0 + Knight0->White0 + Knight1->White0
    otherColor = White0->Black0 + Black0->White0
    toMove = Board0->Black0
}

pred finalBoard[b: Board] {
    -- A color is in checkmate
    some c: Color {
        Checkmate[b, c] or Stalemate[b, c] // Ending position
    }
}

pred transitionBoards {
    all st, nx: Board | st->nx in next => {
        canMove[st, nx]
    }
    all bd: Board | {
        -- Each board has at most one in-edge
        lone next.bd
    }
    -- One initial board
    one bd: Board | {
        -- No in board leads to this board
        no next.bd
        -- It is a valid initial board
        initBoard[bd]
        -- Every other board comes in some progression after this board
        Board = bd.*next
    }
    -- One final board
    one bd: Board | {
        -- Final board has no next board
        no bd.next
        -- It is a valid final board
        finalBoard[bd]
        -- Every board eventually reaches the final board
        Board = *next.bd
    }
}

-------- Validity --------

pred validBoard {
    -- Color inverses
    otherColor = Black->White + White->Black
    -- File and Rank ordering defined
    left = H->G + G->F + F->E + E->D + D->C + C->B + B->A
    right = A->B + B->C + C->D + D->E + E->F + F->G + G->H
    below = R8->R7 + R7->R6 + R6->R5 + R5->R4 + R4->R3 + R3->R2 + R2->R1
    above = R1->R2 + R2->R3 + R3->R4 + R4->R5 + R5->R6 + R6->R7 + R7->R8
    no k : King, y : King - k {
        k.clr = y.clr
    }
    all b: Board {
        all p: Piece {
            -- Each piece has a unique location on the board
            one (b.places).p
        }
        all f: File, r: Rank | {
            -- Only one piece on each square
            lone b.places[f][r]
        }
        -- The color that just moved before did not move into check
        all k: King | k.clr = b.toMove.otherColor implies {
            all n: Knight | n in clr.(k.clr.otherColor) implies {
                not getPos[b, k] in knightMoves[b, n]
            }
            all kg: King | kg in clr.(k.clr.otherColor) implies {
                not getPos[b, k] in kingMoves[b, kg]
            }
        }
    }
}

run {
    validBoard
    transitionBoards
    all b: Board | {
        -- White is the side with Knight pair
        Knight.clr = White
    }
 --   some b: Board, c: Color | Checkmate[b, c] // Comment out to reach Stalemate ending. This forces a search for checkmate sequences.
} for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int

-------- Tests (requires 5 Int bitwidth from run) --------
example CanCheckmate is Checkmate[Board, Black] for validCheckmate

example CanStalemate is Stalemate[Board,Black] for isStalemate

test expect {
    only1Move: {(validBoard and transitionBoards) => {some x,y : Board | { canMove[x,y] => one(y.places - x.places) }}} for exactly 8 File, exactly 8 Rank, exactly 5 Board is theorem
    onlysinglenextBoard: {(validBoard and transitionBoards) => {next.~next in iden} }  for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is theorem
    eachPieceHasOnlyPosition: {(validBoard and transitionBoards) => {all b : Board | { all p : Piece { one(b.places.p)}}}}  for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is theorem
    onlyPieceOnEachSquare: {(validBoard and transitionBoards) => {all b : Board | {  all f: File, r: Rank | {
            -- Only one piece on each square
            lone b.places[f][r]
        }   }}}  for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is theorem
     --   endsWithCheckOrStalemateForBlack: {(validBoard and transitionBoards) => {one b : Board {  some c : Color { Checkmate[b, c] or Stalemate[b, c] }}}}  for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is theorem
 /*   startingPositionDoesNotHaveCheckmate: {(validBoard and transitionBoards) => { one b : Board{
        some c : Color { 
        initBoard[b]
        not(Checkmate[b,c]) and
        not(Stalemate[b,c])}}}} for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is theorem */
    MoveHastToOccur: {some x,y : Board { canMove[x,y] and x.places = y.places}}for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is unsat

   MoveOnlyToValidLocWhenTurn: {all x,y : Board { canMove[x,y] =>
  { one p : Piece {
       p.clr = x.toMove
       x.places.p != y.places.p
       (p = Knight) => y.places.p in knightMoves[x,p]
       (p = King) => y.places.p in kingMoves[x,p]
   }}}} for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight, exactly 2 Color, 5 Int is theorem
}

