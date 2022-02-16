MACHINE PlayersStatus 

SEES
	Players

VARIABLES
	players_order,
	curr_player,
	winner

INVARIANT
	players_order : PLAYERS >-> PLAYERS &
	players_order /= {} &

	winner : PLAYERS \/ {0} &
	
	// proof obligation
	curr_player: dom(players_order)

INITIALISATION
	winner := 0 ||
	ANY pp WHERE pp : PLAYERS THEN curr_player := pp END ||
	players_order := (%xx.(xx : PLAYERS | xx))

OPERATIONS
	pp <-- current_player = pp := players_order(curr_player);

	pp <-- get_winner = pp := winner;

	set_winner(pp) =
	PRE pp : PLAYERS & winner = 0
	THEN winner := pp 
	END;

	revert_players_order =
	players_order := rev(players_order);

	next_turn =
	IF 	(curr_player + 1) mod card(PLAYERS) = 0 
	THEN	curr_player := card(PLAYERS)
	ELSE	curr_player := (curr_player) mod card(PLAYERS) + 1
	END

	
END