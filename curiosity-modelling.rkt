#lang forge

-- Modelling the Bishop and Knight endgame.
-- White winning with pawnless Bishop/Knight and Black defending with single King.

-------- Signatures --------
abstract sig Color {}
one sig White extends Color {}
one sig Black extends Color {}

abstract sig File {
    left: lone File,
    right: lone File
}
one sig A, B, C, D, E, F, G, H extends File {}

abstract sig Rank {
    above: lone Rank,
    below: lone Rank
}
one sig R1, R2, R3, R4, R5, R6, R7, R8 extends Rank {}

abstract sig Piece {clr : one Color}

sig King extends Piece {}
sig Knight extends Piece {}
--sig Bishop extends Piece {}

sig Board {
    next: lone Board,
    places: set File -> Rank -> Piece,
    toMove: one Color
}

-------- Statefulness --------
fun getFile[b: Board, p: Piece]: File {
    -- Returns the File of Piece p on Board b
    (b.places.p).Rank
}

fun getRank[b: Board, p: Piece]: Rank {
    -- Returns the Rank of Piece p on Board b
    b.places.p[File]
}

fun kingMoves[b: Board, p: King]: set File -> Rank {
    (getFile[b, p] + getFile[b, p].left + getFile[b, p].right) -- File
    ->(getRank[b, p] + (getRank[b, p]).above + (getRank[b, p]).below) -- Rank
    - (getFile[b, p]->getRank[b, p])
}


fun knightMoves[b: Board, p: Knight]: set File -> Rank {
    -- One square to left/right and two to above/below
    (getFile[b, p].left + getFile[b, p].right) -- File
    ->(getRank[b, p].above.above + getRank[b, p].below.below) -- Rank
    -- One square to above/below and two to left/right
    + (getFile[b, p].left.left + getFile[b, p].right.right) -- File
    ->(getRank[b, p].above + getRank[b, p].below) -- Rank
}
pred initBoard[b: Board] {
   one k : King {
       k.clr = Black
       all p : Piece - k {
           no(b.places.p & kingMoves[b,k])
       }
   }
}

pred canMove[pre: Board, post: Board] {
    one p : Piece | {
        p.clr = pre.toMove
        pre.places.p != post.places.p
        not(post.places.p in pre.places.Piece)
        (p = King) => {
            not(post.places.p in (kingMoves[post,King - p] + knightMoves[post,Knight]))
        }
        (p = King) => (post.places.p in kingMoves[pre,p])
        (p = Knight) => (post.places.p in knightMoves[pre,p])
        all other : Piece - p {
            pre.places.other = post.places.other
        }
    }
   
         
            
}

pred BlackKingCanMove[b : Board] {
    one p : King | {
        p.clr = Black
        some(kingMoves[b,p]  - (kingMoves[b,King - p] + knightMoves[b,Knight]))
    }
}
pred Check[b : Board] {
     one p : King | {
        p.clr = Black
        some(kingMoves[b,p]  & (kingMoves[b,King - p] + knightMoves[b,Knight]))
    }
}
pred CheckMate[b : Board] {
    Check[b]
    not(BlackKingCanMove[b])
}
pred Stalemate[b : Board]{
    not(Check[b])
    not(BlackKingCanMove[b])
}
pred finalBoard[b: Board] {
   Check[b] or Stalemate[b]
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
      
    }
    
}



/*
fun bishopMoves[b: Board, bi: Bishop]: set File -> Rank {
    none
}
*/

run {
    validBoard
    transitionBoards
    all b: Board {
        -- White is the side with Bishop and Knight pair
          Knight.clr = White
        
    }
} for exactly 8 File, exactly 8 Rank, exactly 5 Board, exactly 2 King, exactly 2 Knight,exactly 2 Color, 5 Int