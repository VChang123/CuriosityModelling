#lang forge/bsl
//DUE MARCH 3rd

one sig Game {
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
}

pred Player2Turn[s: State] {
    remainder[s.turnNumber, 2] = 1
}

pred attack[pre: State, post: State] {
    Player1Turn[pre] => {
        post.rightHandP2 = remainder[add[pre.rightHandP1, pre.rightHandP2], 5]
        post.leftHandP2 = pre.leftHandP2
        post.rightHandP1 = pre.rightHandP1
        post.leftHandP1 = pre.leftHandP1
    
    } or {
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = remainder[add[pre.rightHandP1, pre.leftHandP2], 5]
        post.rightHandP1 = pre.rightHandP1
        post.leftHandP1 = pre.leftHandP1
    } or {
        post.rightHandP2 = remainder[add[pre.leftHandP1, pre.rightHandP2], 5]
        post.leftHandP2 = pre.leftHandP2
        post.rightHandP1 = pre.rightHandP1
        post.leftHandP1 = pre.leftHandP1
    } or {
        post.leftHandP2 = remainder[add[pre.leftHandP1, pre.leftHandP2], 5]
        post.rightHandP2 = pre.rightHandP2
        post.rightHandP1 = pre.rightHandP1
        post.leftHandP1 = pre.leftHandP1
    }

    Player2Turn[pre] => {
        post.rightHandP1 = remainder[add[pre.rightHandP2, pre.rightHandP1], 5]
        post.leftHandP1 = pre.leftHandP1
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = pre.leftHandP2
    } or {
        post.leftHandP1 = remainder[add[pre.rightHandP2, pre.leftHandP1], 5]
        post.rightHandP1 = pre.rightHandP1
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = pre.leftHandP2
    } or {
        post.rightHandP1 = remainder[add[pre.leftHandP2, pre.rightHandP1], 5]
        post.leftHandP1 = pre.leftHandP1
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = pre.leftHandP2
    } or {
        post.leftHandP1 = remainder[add[pre.leftHandP2, pre.leftHandP1], 5]
        post.rightHandP1 = pre.rightHandP1
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = pre.leftHandP2
    }
}

pred transfer[pre: State, post: Post]{
    Player1Turn[pre] => {
        post.rightHandP1 = remainder[add[pre.rightHandP1, 1], 5]
        post.leftHandP1 = subtract[pre.leftHandP1, 1]
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = pre.leftHandP2
    } or {
        post.leftHandP1 = remainder[add[pre.leftHandP1, 1], 5]
        post.rightHandP1 = subtract[pre.rightHandP1, 1]
        post.rightHandP2 = pre.rightHandP2
        post.leftHandP2 = pre.leftHandP2
    } 

    Player2Turn[pre] => {
        post.rightHandP2 = remainder[add[pre.rightHandP2, 1], 5]
        post.leftHandP2 = subtract[pre.leftHandP2, 1]
        post.rightHandP1 = pre.rightHandP1
        post.leftHandP1 = pre.leftHandP1
    } or {
        post.leftHandP2 = remainder[add[pre.leftHandP2, 1], 5]
        post.rightHandP2 = subtract[pre.rightHandP2, 1]
        post.rightHandP1 = pre.rightHandP1
        post.leftHandP1 = pre.leftHandP1
    }  
}

pred canMove[pre: State, post: State] {
    remainder[pre.turnNumber, 2] != remainder[post.turnNumber, 2]
    not winningState[pre] => { attack[ pre, post] or transfer[pre, post] } else doNothing[pre, post]
}

pred transitionStates{
    some init, final: State {
        initState[init]

        all s: State | (s != init) implies (s.next != init)

        -- valid transitions
        all s: State | some s.next => canMove[s, s.next]
    }
}

//------------------------------------- TESTING/EXAMPLES--------------------------------//

test expect {

}

//examples for the move, state, different attacks

// sig State {
//     turnNumber: one Int,
//     leftHandP1: one Int,
//     rightHandP1: one Int,
//     leftHandP2: one Int,
//     rightHandP2: one Int,
//     next : lone State
// }
// initial state
// example validInitialState is initState for {
//     State = `S0
//     turnNumber = `S0 -> 0
// }

// winning state
example isWinningState is {some s: State | winningState[s]} for {
    State = `S5
    
    turnNumber = `S5 -> 5
    leftHandP1 = `S5-> 0 
    rightHandP1 = `S5-> 0 
    leftHandP2 = `S5-> 1 
    rightHandP2 = `S5-> 1
    

}
example isNotWinningState is not {some s: State | winningState[s]} for {
    State = `S5
    
    turnNumber = `S5 -> 5
    leftHandP1 = `S5-> 2
    rightHandP1 = `S5-> 3 
    leftHandP2 = `S5-> 1 
    rightHandP2 = `S5-> 1
    

}

// transitions 

// valid state

example isValidState is validStates for  {
    State = `S0 

    turnNumber = `S0 -> 0
    leftHandP1 = `S0-> 2
    rightHandP1 = `S0-> 2
    leftHandP2 = `S0-> 1 
    rightHandP2 = `S0-> 1 
  
}
//missing right hand
example isNotValidState is not validStates for  {
    State = `S0 
    turnNumber = `S0 -> 0 
    leftHandP1 = `S0-> 1 
    rightHandP1 = `S0-> 3
    leftHandP2 = `S0-> 1
    rightHandP2 = `S0 ->7
   
}

//negative numbers for the count on the hands
example isNotValidState2 is not validStates for  {
    State = `S0 
    turnNumber = `S0 -> 0 
    leftHandP1 = `S0-> 1 
    rightHandP1 = `S0-> -1 
    leftHandP2 = `S0-> 5 
    rightHandP2 = `S0-> 1  
    
}
// attack 

// transfer

example validTransfer is {some pre, post : State | transfer[pre, post]} for  {
    State = `S0 + `S1
    turnNumber = `S0 -> 0 + `S1 -> 1
    next = `S0 -> `S1
    leftHandP1 = `S0-> 1  + `S1 -> 2
    rightHandP1 = `S0-> 1 + `S1 -> 0
    leftHandP2 = `S0-> 1 + `S1 -> 1
    rightHandP2 = `S0-> 1 + `S1 -> 1
}

//transferred more than 1
example invalidTransfer is not {some pre, post : State | transfer[pre, post]} for {
    State = `S0 + `S1
    turnNumber = `S0 -> 0 + `S1 -> 1
    next = `S0 -> `S1
    leftHandP1 = `S0-> 1  + `S1 -> 3
    rightHandP1 = `S0-> 1 + `S1 -> 0
    leftHandP2 = `S0-> 1 + `S1 -> 1
    rightHandP2 = `S0-> 1 + `S1 -> 1
}

//both hands transfer
example invalidTransfer2 is not {some pre, post : State | transfer[pre, post]} for {
    State = `S0 + `S1
    turnNumber = `S0 -> 0 + `S1 -> 1
    next = `S0 -> `S1
    leftHandP1 = `S0-> 1  + `S1 -> 2
    rightHandP1 = `S0-> 1 + `S1 -> 0
    leftHandP2 = `S0-> 1 + `S1 -> 2
    rightHandP2 = `S0-> 1 + `S1 -> 0
}

//did not subtract properly
example invalidTransfer3 is not {some pre, post : State | transfer[pre, post]} for {
    State = `S0 + `S1
    turnNumber = `S0 -> 0 + `S1 -> 1
    next = `S0 -> `S1
    leftHandP1 = `S0-> 1  + `S1 -> 2
    rightHandP1 = `S0-> 1 + `S1 -> 1
    leftHandP2 = `S0-> 1 + `S1 -> 1
    rightHandP2 = `S0-> 1 + `S1 -> 1
}


run {
    validStates
    transitionStates
} for 15 State
for {next is linear}