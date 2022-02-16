MACHINE PlayersStatus 

SEES
	Players

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

	pp <-- get_winner = pp := winner;

	set_winner(pp) =
	PRE pp : PLAYERS & winner = 0
	THEN winner := pp 
	END;

	revert_players_order =
	players_order := rev(players_order);

	set_curr_player(pp) =
	PRE pp : PLAYERS & pp : ran(players_order)
	THEN curr_player := pp 
	END


END