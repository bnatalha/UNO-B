MACHINE Players 

CONSTANTS
	PLAYERS

PROPERTIES

	PLAYERS <: NAT1 &
	PLAYERS = {1,2}

VARIABLES
	players_order,
	curr_player,
	winner

INVARIANT
	players_order	: iseq(PLAYERS) &
	players_order /= [] &
	ran(players_order) = PLAYERS &

	winner : PLAYERS \/ {0} &
	
	// proof obligation
	curr_player: dom(players_order)

INITIALISATION
	winner := 0 ||
	ANY pp WHERE pp : PLAYERS THEN curr_player := pp END ||
	players_order := [1,2]

OPERATIONS
	pp <-- current_player = pp := players_order(curr_player);

	pp <-- get_winner = pp := winner

END