# CuriosityModelling

**Chopsticks**

DESCRIPTION OF MODEL:
    We have chosen to model the game Chopsticks for this project. The game starts of with 2 players and
    each player has 1 finger extended on each hand. The players transfer those scores by taking turns to tap one hand against another. For example player 1 has 1 on their right hand and player 2 has 2 on their left hand. Player 1 taps their right hand on Player 2 left hand, so now Player 2 left hand has a score of 4. Each hand cannot hold more than 4, therefore when a Players rigthand and lefthand are at a score of 0 the opposing player wins. 


DESIGN CHOICES:
Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by Sterling. How should we look at and interpret an instance created by your spec?

Some ot the model design choices that we made was to allow the model to choose either to attack or transfer. We did not specifically designate when to attack or when to transfer in order to replicate human behavior as close as possible. In the run statement we ensure that all the states are valid and we run the traces/transitionStates to get a full game. We specified our model to run for 15 states although it may take more than 15 states for a player to win. The instance generated by Sterling will model the game and how each hand of a player changes. It would be easier to look at the table version of the instance. When a players lefthand and righthand both have a value of zero, that is when the game ends and then all the scores after it would stay the same if they win before 15 states

PREDICATES AND SIGS:

