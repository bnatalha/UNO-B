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
	hand, hand_desc, hand_qty, last_discard, last_discard_desc, // Stacks
	get_winner	// PlayersStatus

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

		// set the next state
		IF	card(players_hands(pp)) - 1 = 0
		THEN	set_winner(pp) ||
				state := DONE
		ELSE	state := SETTING_EFFECTS
		END;

		next_turn
	END;

	set_effects =
	PRE state = SETTING_EFFECTS
	THEN CASE CARD_VAL(last(discard_stack)) OF
			EITHER 	eDRAW_2		THEN 	set_drawing(2)  || state := DRAWING
			OR	eSKIP			THEN 	state := SKIPPING
			OR 	eREVERT			THEN 	revert_players_order	|| state := PLAYING
			OR	eWILD			THEN 	state := SETTING_COLOR
			OR	eWILD_DRAW_4	THEN 	set_drawing(4) || state := SETTING_COLOR
			ELSE state := PLAYING
			END
		END
	END;

	set_color(cl) =
	PRE	state = SETTING_COLOR &
		cl : sCOLOR - {BLACK} & 
		CARD_VAL(last(discard_stack)) : {eWILD, eWILD_DRAW_4}
	THEN	
		set_discard_color(cl) ||
		IF drawing > 0
		THEN	state := DRAWING
		ELSE	state := PLAYING	
		END
	END;
	
	draw(pp) =
	PRE pp : PLAYERS & 
		pp = players_order(curr_player) &
		card(draw_stack) > 0 &	// there are cards to draw from the stack
		// state is DRAWING
		((state = DRAWING &
		drawing > 0) or
		// or state is PLAYING and has no card to play in hand
		(state = PLAYING &
		!(cc).(cc: players_hands(pp) => //rules
			not((CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
			CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
			CARD_COLOR(cc) = BLACK)))))
	THEN
		draw_card(pp) ||	
		set_drawing(drawing - 1) ||
		IF (drawing - 1) = 0
			THEN state := PLAYING
			ELSE skip
		END
	END;

	skip_turn = 
	PRE state = SKIPPING
	THEN
		next_turn ||
		state := PLAYING
	END
END
