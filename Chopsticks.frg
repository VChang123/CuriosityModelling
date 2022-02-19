#lang forge/bsl
//DUE MARCH 3rd

sig Game {
    turnNumber: one Int,
    initialState : one State,
   
}
abstract sig Player {
    rightHand: one Int,
    leftHand: one Int
}

sig Player1,Player2 extends Player{}

sig State{
    turnNumber: one Int,
    player1: one Player1,
    player2: one Player2,
    next : lone State
}

//--------------------------------------- PREDICATES -------------------------------------------//

pred validState {
    all s: State | all p: Player | (p.rightHand >= 0 or p.rightHand >= 4) and (p.leftHand >= 0 or p.leftHand >= 4)

}
pred initialState[s: State]{
    s.player1.rightHand = 1 and s.player1.leftHand = 1 and s.player2.rightHand = 1 and s.player2.leftHand = 1
}

pred finalState[s: State] {
    winningState[s]
    s.next = none

}

pred winningState[s: State]{
    (s.player1.rightHand = 0 and s.player1.leftHand = 0) or 
    (s.player2.rightHand = 0 and s.player2.leftHand = 0)
}

pred Player1Turn{
    reminder[Game.turnNumber, 2] = 0
    add[Game.turnNumber, 1]
}

pred Player2Turn{
    reminder[Game.turnNumber, 2] = 1
    add[Game.turnNumber, 1]
}

pred attack[atacker: Player, opponent: Player] {
    attacker = Player1 implies Player1Turn
    attacker = Player2 implies Player2Turn
    (attacker.rightHand > attacker.lefthand) =>{
        (opponent.rightHand > opponent.leftHand) =>{
            opponent.leftHand = reminder[attacker.rightHand, opponent.leftHand]
        } else {
             opponent.rightHand = reminder[attacker.rightHand, opponent.rightHand]
        }
    } else {
        (opponent.rightHand > opponent.leftHand) =>{
            opponent.leftHand = reminder[attacker.leftHand, opponent.leftHand]
        } else {
            opponent.rightHand = reminder[attacker.leftHand, opponent.rightHand]
        }
    }

}

pred transfer[p: Player]{
    p = Player1 implies Player1Turn
    p = Player2 implies Player2Turn
    (p.rightHand > p.leftHand){
        p.leftHand = reminder[add[p.leftHand, 1], 5]
        p.rightHand = subtract[p.rightHand, 1]
    } else {
        p.rightHand = reminder[add[p.rightHand, 1], 5]
        p.leftHand = subtract[p.leftHand, 1]
    }
}

pred canMove[pre: State, post: State]{

}

pred transitionStates{
    some init, final: State {
        initState[init]
        all s: tate | (s != init) implies (s.next != init)
        finalState[final]
        -- link init to final state via gwnext
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



run{
    validStates
    transitionStates
    winningState
} for 9 States, exactly 2 Player, exactly 1 Player1, exactly 1 Player2