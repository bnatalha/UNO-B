/**
TODO: 
	- [x] initialize the discard_stack with 2 cards taken from the draw_stack;
	- [x] initialize with 7 cards for each player;
	- [x] plays_card only if it's the player's turn;
		- implement turns;
	- [x] play a game with only the cards with number's as values;
	- add more players;
	- [x] add effect cards rules to the game;
		- +2
		- reverse
		- skip
		- +4
		- wild
	- add other rules;
		- play +1 effect per turn
		- play +1 card per turn if its a double
	- refact project;
  	- [x] win a game;
  	- [x] draw when needed;
 	- [x] custom INITIALIZATION for a more randomized hand
*/

MACHINE Uno

SEES
	Cards,
	Players,
	CardStacks

VARIABLES
	drawing,
	skipping,
	set_wild_color
	
INVARIANT
	drawing : NAT &
	skipping : NAT &
	set_wild_color : {0,1}

INITIALISATION
	drawing := 0 ||
	skipping := 0 ||
	set_wild_color := 0


OPERATIONS
	play(pp, cc) =
	PRE 	pp : PLAYERS & 
		pp = players_order(curr_player) &
		players_hands(pp) /= {} &
		cc : players_hands(pp) &
		drawing = 0 &
		skipping = 0 &
		winner = 0 &
		set_wild_color = 0 &
		// rules
		(CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
		 CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
		 CARD_COLOR(cc) = BLACK)	
	THEN
		players_hands(pp) := players_hands(pp) - {cc} ||	// remove the card from the players_hand
		discard_stack := discard_stack <- cc	|| // add card to discard_stack

		// played an effect card
		CASE CARD_VAL(cc) OF
			EITHER 	eDRAW_2 THEN drawing := 2  
			OR	eSKIP	THEN skipping := 1
			OR 	eREVERSE	THEN players_order := rev(players_order)
			OR	eWILD	THEN set_wild_color := 1
			OR	eWILD_DRAW_4 THEN drawing:= 4 || set_wild_color := 1
			ELSE skip
			END
		END ||

		// set a winner, if there is any
		IF	card(players_hands(pp)) - 1 = 0
		THEN	winner := pp
		ELSE	skip
		END ||

		// calculate next turn
		IF 	(curr_player + 1) mod card(PLAYERS) = 0 
		THEN	curr_player := card(PLAYERS)
		ELSE	curr_player := (curr_player) mod card(PLAYERS) + 1
		END
		
		
	END;

	set_color(cl) =
	PRE	set_wild_color = 1 & cl : sCOLOR - {BLACK}
	THEN	CASE CARD_VAL(last(discard_stack)) OF
			EITHER 	eWILD 	THEN 
				CASE cl	OF
					EITHER	RED	THEN	discard_stack := front(discard_stack) <- 109 
					OR	GREEN	THEN	discard_stack := front(discard_stack) <- 110
					OR	BLUE	THEN	discard_stack := front(discard_stack) <- 111
					OR	YELLOW	THEN	discard_stack := front(discard_stack) <- 112
					ELSE skip
					END
				END
			OR	eWILD_DRAW_4	THEN
				CASE cl	OF
					EITHER	RED	THEN	discard_stack := front(discard_stack) <- 113 
					OR	GREEN	THEN	discard_stack := front(discard_stack) <- 114
					OR	BLUE	THEN	discard_stack := front(discard_stack) <- 115
					OR	YELLOW	THEN	discard_stack := front(discard_stack) <- 116
					ELSE skip
					END
				END
			ELSE skip
			END
		END ||
		set_wild_color := 0
	END;

	skip_turn =
	PRE	skipping > 0 & drawing = 0 & set_wild_color = 0
	THEN	IF 	(curr_player + 1) mod card(PLAYERS) = 0 
		THEN	curr_player := card(PLAYERS)
		ELSE	curr_player := (curr_player) mod card(PLAYERS) + 1
		END ||
		skipping := skipping - 1
	END;
	
	draw(pp) =
	PRE 	pp : PLAYERS & 
		pp = players_order(curr_player) &
		card(draw_stack) > 0 &
		winner = 0 &
		skipping = 0 &
		set_wild_color = 0 &
		(drawing > 0 or
		!(cc).(cc: players_hands(pp) => //rules
			not((CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
		 	CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
			CARD_COLOR(cc) = BLACK))
		))
	THEN
		ANY cc WHERE cc : draw_stack 
		THEN	draw_stack := draw_stack - {cc} ||	// remove the card from draw_stack
			players_hands(pp) := players_hands(pp) \/ {cc} || // add card to player's hand	
			IF drawing > 0
				THEN drawing := drawing - 1
				ELSE skip
			END
		END
	END
END
