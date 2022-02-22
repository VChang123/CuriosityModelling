#lang forge/bsl
//DUE MARCH 3rd

one sig Game {
    // turnNumber: one Int,
    initialState: one State
}

abstract sig Player {
    rightHand: one Int,
    leftHand: one Int
}

one sig Player1,Player2 extends Player{}

sig State {
    turnNumber: one Int,
    player1: one Player1,
    player2: one Player2,
    next : lone State
}

//--------------------------------------- PREDICATES -------------------------------------------//

pred validStates {
    // all s: State | all p: Player | (p.rightHand >= 0 or p.rightHand <= 4) and (p.leftHand >= 0 or p.leftHand <= 4)
    
    all s1, s2: State | s2 = s1.next => s2.turnNumber = add[s1.turnNumber, 1]

}
pred initState[s: State] {
    s.turnNumber = 0
    s.player1.rightHand = 1 and s.player1.leftHand = 1 and s.player2.rightHand = 1 and s.player2.leftHand = 1
    Game.initialState = s
}

pred finalState[s: State] {
    // winningState[s]
    no s.next
}

pred winningState[s: State]{
    (s.player1.rightHand = 0 and s.player1.leftHand = 0) or 
    (s.player2.rightHand = 0 and s.player2.leftHand = 0)
}

pred Player1Turn[s: State] {
    remainder[s.turnNumber, 2] = 0
    // add[s.turnNumber, 1]
}

pred Player2Turn[s: State] {
    remainder[s.turnNumber, 2] = 1
    // add[s.turnNumber, 1]
}

pred attack[attacker: Player, opponent: Player, s: State] {
    (attacker = Player1 and opponent = Player2) implies Player1Turn[s]
    (attacker = Player2 and opponent = Player1) implies Player2Turn[s]

    // (attacker.rightHand > attacker.leftHand) => {
    //     (opponent.rightHand > opponent.leftHand) =>{
    //         opponent.leftHand = remainder[attacker.rightHand, opponent.leftHand]
    //     } else {
    //          opponent.rightHand = remainder[attacker.rightHand, opponent.rightHand]
    //     }
    // } else {
    //     (opponent.rightHand > opponent.leftHand) =>{
    //         opponent.leftHand = remainder[attacker.leftHand, opponent.leftHand]
    //     } else {
    //         opponent.rightHand = remainder[attacker.leftHand, opponent.rightHand]
    //     }
    // }

    // opponent.leftHand = remainder[add[attacker.rightHand, opponent.leftHand], 5]
}

pred transfer[p: Player, s: State]{
    p = Player1 implies Player1Turn[s]
    p = Player2 implies Player2Turn[s]
    
    // (p.rightHand > p.leftHand) => {
    //     p.leftHand = remainder[add[p.leftHand, 1], 5]
    //     p.rightHand = subtract[p.rightHand, 1]
    // } else {
    //     p.rightHand = remainder[add[p.rightHand, 1], 5]
    //     p.leftHand = subtract[p.leftHand, 1]
    // }
}

pred canMove[pre: State, post: State] {
    remainder[pre.turnNumber, 2] != remainder[post.turnNumber, 2]

    // Player1's turn 
    remainder[pre.turnNumber, 2] = 0 => {
        // attacking
        remainder[pre.turnNumber, 4] = 0 => { 
            attack[pre.player1, pre.player2, pre]
        } else { // transfer
            transfer[pre.player1, pre]
        }
    } else {
        remainder[pre.turnNumber, 4] = 1 => {
            attack[pre.player2, pre.player1, pre]
        } else { // transfer
            transfer[pre.player2, pre]
        }
    }
    // for player 1: if turn number mod 4 = 0, attack; otherwise transfer
    // if attacking: 
    // the values on at least one of the opponent's hands should change

    // the amount that it changes by should be the same as the hand that is attacking


}

pred transitionStates{
    some init, final: State {
        initState[init]

        all s: State | (s != init) implies (s.next != init)

        finalState[final]
        reachable[final, init, next]
        -- valid transitions
        all s: State | some s.next => canMove[s, s.next]
    }
}

pred traces{

}

//------------------------------------- TESTING/EXAMPLES--------------------------------//

test expect {

}

//examples for the move, state, different attacks



run {
    validStates
    transitionStates
    // winningState
} for 6 State, exactly 2 Player, exactly 1 Player1, exactly 1 Player2
for {next is linear}