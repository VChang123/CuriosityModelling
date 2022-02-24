#lang forge/bsl
//DUE MARCH 3rd

one sig Game {
    // turnNumber: one Int,
    initialState: one State
}

abstract sig Player {}

one sig Player1, Player2 extends Player {}

sig State {
    turnNumber: one Int,
    leftHandP1: one Int,
    rightHandP1: one Int,
    leftHandP2: one Int,
    rightHandP2: one Int,
    // player1: one Player1,
    // player2: one Player2,
    next : lone State
}

//--------------------------------------- PREDICATES -------------------------------------------//

pred validStates {
    all s: State | (s.rightHandP1 >= 0 and s.rightHandP1 <= 4) and (s.leftHandP1 >= 0 and s.leftHandP1 <= 4) and (s.rightHandP2 >= 0 and s.rightHandP2 <= 4) and (s.leftHandP2 >= 0 and s.leftHandP2 <= 4)
    
    all s1, s2: State | s2 = s1.next => s2.turnNumber = add[s1.turnNumber, 1]

}
pred initState[s: State] {
    s.turnNumber = 0
    s.rightHandP1 = 1 
    s.leftHandP1 = 1 
    s.rightHandP2 = 1 
    s.leftHandP2 = 1 
    Game.initialState = s
}

pred finalState[s: State] {
    // winningState[s]
    no s.next
}

pred winningState[s: State]{
    (s.rightHandP1 = 0 and s.leftHandP1 = 0) or 
    (s.rightHandP2 = 0 and s.leftHandP2 = 0)
}

pred doNothing[pre: State, post: State] {
    winningState[pre]
    pre.rightHandP1 = post.rightHandP1
    pre.leftHandP1 = post.leftHandP1
    pre.rightHandP2 = post.rightHandP2
    pre.leftHandP2 = post.leftHandP2
}

pred Player1Turn[s: State] {
    remainder[s.turnNumber, 2] = 0
    // add[s.turnNumber, 1]
}

pred Player2Turn[s: State] {
    remainder[s.turnNumber, 2] = 1
    // add[s.turnNumber, 1]
}

pred attack[pre: State, post: State] {
    // (attacker = Player1 and opponent = Player2) implies Player1Turn[s]
    // (attacker = Player2 and opponent = Player1) implies Player2Turn[s]

    Player1Turn[pre] => {post.rightHandP2 = remainder[add[pre.rightHandP1, pre.rightHandP2], 5]} or
                    {post.leftHandP2 = remainder[add[pre.rightHandP1, pre.leftHandP2], 5]} or
                    {post.rightHandP2 = remainder[add[pre.leftHandP1, pre.rightHandP2], 5]} or 
                    {post.leftHandP2 = remainder[add[pre.leftHandP1, pre.leftHandP2], 5]}
    
    Player2Turn[pre] => {post.rightHandP1 = remainder[add[pre.rightHandP2, pre.rightHandP1], 5]} or
                    {post.leftHandP1 = remainder[add[pre.rightHandP2, pre.leftHandP1], 5]} or
                    {post.rightHandP1 = remainder[add[pre.leftHandP2, pre.rightHandP1], 5]} or 
                    {post.leftHandP1 = remainder[add[pre.leftHandP2, pre.leftHandP1], 5]}
    // (attacker.rightHand > attacker.leftHand) => {
    //     (opponent.rightHand > opponent.leftHand) =>{
    //         opponent.leftHand = remainder[add[attacker.rightHand, opponent.leftHand], 5]
    //     } else {
    //          opponent.rightHand = remainder[add[attacker.rightHand, opponent.rightHand], 5]
    //     }
    // } else {
    //     (opponent.rightHand > opponent.leftHand) =>{
    //         opponent.leftHand = remainder[add[attacker.leftHand, opponent.leftHand], 5]
    //     } else {
    //         opponent.rightHand = remainder[add[attacker.leftHand, opponent.rightHand], 5]
    //     }
    // }

    // opponent.leftHand = remainder[add[attacker.rightHand, opponent.leftHand], 5]
}

pred transfer[pre: State, post: Post]{
    // p = Player1 implies Player1Turn[s]
    // p = Player2 implies Player2Turn[s]
    
    Player1Turn[pre] => {post.rightHandP1 = remainder[add[pre.rightHandP1, 1], 5] and post.leftHandP1 = subtract[pre.leftHandP1, 1]} or 
                        {post.leftHandP1 = remainder[add[pre.leftHandP1, 1], 5] and post.rightHandP1 = subtract[pre.rightHandP1, 1]} or 
    Player2Turn[pre] => {post.rightHandP2 = remainder[add[pre.rightHandP2, 1], 5] and post.leftHandP2 = subtract[pre.leftHandP2, 1]} or
                        {post.leftHandP2 = remainder[add[pre.leftHandP2, 1], 5] and post.rightHandP2 = subtract[pre.rightHandP2, 1]}  

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
    attack[ pre, post] or transfer[pre, post]
    // Player1's turn 
    // remainder[pre.turnNumber, 2] = 0 => {
    //     // attacking
    //     //remainder[pre.turnNumber, 4] = 0 => { 
       
    //     //} else { // transfer
            
    //     //}
    // } else {
    //     //remainder[pre.turnNumber, 4] = 1 => {
    //         attack[pre.player2, pre.player1, pre]
    //     } else { // transfer
    //         transfer[pre.player2, pre]
    //     }
    // }
    // for player 1: if turn number mod 4 = 0, attack; otherwise transfer
    // if attacking: 
    // the values on at least one of the opponent's hands should change

    // the amount that it changes by should be the same as the hand that is attacking


}

pred transitionStates{
    some init, final: State {
        initState[init]

        all s: State | (s != init) implies (s.next != init)

        // finalState[final]
        // reachable[final, init, next]
        -- valid transitions
        all s: State | some s.next => canMove[s, s.next] or doNothing[s, s.next]
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
} for 9 State
for {next is linear}