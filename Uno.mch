MACHINE Uno

SEES
	Cards,
	Players,
	GameState

INCLUDES
	PlayersStatus,
	Stacks,
	Game

PROMOTES
	hand, hand_desc 	// Stacks

VARIABLES
	state

INVARIANT
	state : GAME_STATE

INITIALISATION
	state := INITIALIZING

OPERATIONS

	init_game =
	PRE	state = INITIALIZING
	THEN shuffle_deck ||
		 state := PLAYING
	END;

	//	play(pp, cc) =
	//	PRE 	pp : PLAYERS & 
	//		pp = players_order(curr_player) &
	//		players_hands(pp) /= {} &
	//		cc : players_hands(pp) &
	//		state = PLAYING
	//		// rules
	//		(CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
	//		 CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
	//		 CARD_COLOR(cc) = BLACK)	
	//	THEN
	//		players_hands(pp) := players_hands(pp) - {cc} ||	// remove the card from the players_hand
	//		discard_stack := discard_stack <- cc	|| // add card to discard_stack
//	
	//		// played an effect card
	//		CASE CARD_VAL(cc) OF
	//			EITHER 	eDRAW_2 THEN drawing := 2  
	//			OR	eSKIP	THEN skipping := 1
	//			OR 	eREVERSE	THEN players_order := rev(players_order)
	//			OR	eWILD	THEN setting_wild_color := 1
	//			OR	eWILD_DRAW_4 THEN drawing:= 4 || setting_wild_color := 1
	//			ELSE skip
	//			END
	//		END ||
//	
	//		// set a winner, if there is any
	//		IF	card(players_hands(pp)) - 1 = 0
	//		THEN	winner := pp
	//		ELSE	skip
	//		END ||
//	
	//		// calculate next turn
	//		IF 	(curr_player + 1) mod card(PLAYERS) = 0 
	//		THEN	curr_player := card(PLAYERS)
	//		ELSE	curr_player := (curr_player) mod card(PLAYERS) + 1
	//		END
	//		
	//		
	//	END;

	play(pp, cc) =
	PRE state = PLAYING	&
		pp = players_order(curr_player) &
		players_hands(pp) /= {} &
		cc : players_hands(pp) &
		// rules
		(CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
			CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
			CARD_COLOR(cc) = BLACK)	
	THEN
		play_card(pp, cc) ||

		// set a winner, if there is any
		IF	card(players_hands(pp)) - 1 = 0
		THEN	set_winner(pp) ||
				state := DONE
		ELSE	state := FINISHING_PLAY
		END
	END;

	finishing_play =
	PRE state = FINISHING_PLAY
	THEN 
		// played an effect card
		CASE CARD_VAL(cc) OF
			EITHER 	eDRAW_2 THEN drawing := 2  
			OR	eSKIP	THEN skipping := 1
			OR 	eREVERSE	THEN players_order := rev(players_order)
			OR	eWILD	THEN setting_wild_color := 1
			OR	eWILD_DRAW_4 THEN drawing:= 4 || setting_wild_color := 1
			ELSE skip
			END
		END ||
	
		// calculate next player
		IF 	(curr_player + 1) mod card(PLAYERS) = 0 
		THEN	curr_player := card(PLAYERS)
		ELSE	curr_player := (curr_player) mod card(PLAYERS) + 1
		END
	END;


	set_color(cl) =
	PRE	state = SETTING_COLOR & cl : sCOLOR - {BLACK}
	THEN	CASE CARD_VAL(last(discard_stack)) OF
			EITHER 	eWILD 	THEN 
				CASE cl	OF
					EITHER	RED	THEN	push_discard_stack(109) 
					OR	GREEN	THEN	push_discard_stack(110)
					OR	BLUE	THEN	push_discard_stack(111)
					OR	YELLOW	THEN	push_discard_stack(112)
					ELSE skip
					END
				END
			OR	eWILD_DRAW_4	THEN
				CASE cl	OF
					EITHER	RED	THEN	push_discard_stack(113) 
					OR	GREEN	THEN	push_discard_stack(114)
					OR	BLUE	THEN	push_discard_stack(115)
					OR	YELLOW	THEN	push_discard_stack(116)
					ELSE skip
					END
				END
			ELSE skip
			END
		END ||
		state := PLAYING
	END

	//	skip_turn =
	//	PRE	skipping > 0 & drawing = 0 & setting_wild_color = 0
	//	THEN	IF 	(curr_player + 1) mod card(PLAYERS) = 0 
	//		THEN	set_curr_player(card(PLAYERS))
	//		ELSE	set_curr_player((curr_player) mod card(PLAYERS) + 1)
	//		END ||
	//		set_skipping(skipping - 1)
	//	END
	
	//	draw(pp) =
	//	PRE 	pp : PLAYERS & 
	//		pp = players_order(curr_player) &
	//		card(draw_stack) > 0 &
	//		winner = 0 &
	//		skipping = 0 &
	//		setting_wild_color = 0 &
	//		(drawing > 0 or
	//		!(cc).(cc: players_hands(pp) => //rules
	//			not((CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
	//		 	CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
	//			CARD_COLOR(cc) = BLACK))
	//		))
	//	THEN
	//		ANY cc WHERE cc : draw_stack 
	//		THEN	draw_stack := draw_stack - {cc} ||	// remove the card from draw_stack
	//			players_hands(pp) := players_hands(pp) \/ {cc} || // add card to player's hand	
	//			IF drawing > 0
	//				THEN drawing := drawing - 1
	//				ELSE skip
	//			END
	//		END
	//	END
END
