
MACHINE Stacks

SEES
	Cards,
	Players,
	PlayersStatus

VARIABLES
	draw_stack,
	discard_stack,
	players_hands
	
INVARIANT
	draw_stack <: DECK &
	discard_stack : seq(CARDS) &	// because of wild cards strategy, may have repeated numbers
	players_hands : PLAYERS >-> POW(DECK) &

	// no intersections between player's hands, or any stack
	draw_stack /\ ran(discard_stack) = {} &
	draw_stack /\ union({hh | hh : ran(players_hands)}) =  {} &
	ran(discard_stack) /\ union({hh | hh : ran(players_hands)}) = {} &

	// always have all 108 cards on game
	card(draw_stack) + size(discard_stack) + card(union({hh | hh : ran(players_hands)})) = 108
	
INITIALISATION
	draw_stack := DECK ||
	discard_stack := [] ||
	players_hands := []

OPERATIONS

	//	shuffle_deck =
	//	// shuffle initial hands, discards 2 cards
	//	ANY 	hand1, hand2, initial_discard
	//	WHERE	hand1 <: DECK & hand2 <: DECK & initial_discard : iseq(DECK) &
	//		card(hand1) = 7 & card(hand2) = 7 & size(initial_discard) = 2 &
	//		// can't have an intersection between the draws
	//		hand1 /\ hand2 = {} &
	//		hand1 /\ ran(initial_discard) = {} &
	//		hand2 /\ ran(initial_discard) = {}
	//	THEN 	draw_stack := DECK - (hand1 \/ hand2 \/ ran(initial_discard)) ||
	//		players_hands := {(1 |-> hand1), (2 |-> hand2)} ||
	//		discard_stack := initial_discard
	//	END;

	shuffle_deck =
	ANY hand1, hand2, initial_discard
	WHERE 
		hand1 = {1,8,40,32,103,106} & 
		hand2 = {2,9,41,33,102,107} &
		// initial_discard = {(1 |-> 90), (2 |-> 91)}
		initial_discard = {(1 |-> 105)}	// +4
	THEN
		draw_stack := DECK - (hand1 \/ hand2 \/ ran(initial_discard)) ||
		players_hands := {(1 |-> hand1), (2 |-> hand2)} ||
		discard_stack := initial_discard
	END;

	hh <-- hand(pp) =
	PRE	pp : PLAYERS
	THEN 	hh := players_hands(pp)
	END;

	cc <-- last_discard =
	PRE discard_stack /= {}
	THEN cc := last(discard_stack)
	END;

	cc <-- last_discard_desc =
	PRE discard_stack /= {} & last(discard_stack) : CARDS
	THEN cc := CARD_DESC(last(discard_stack))
	END;

	hh <-- hand_desc(pp) = 
	PRE 	pp : PLAYERS
	THEN	hh := { bb | bb : players_hands(pp) <| CARD_DESC} 
	END;

	// player_draw_card(pp,cc) =

	play_card(pp, cc) =
	PRE pp = players_order(curr_player) &
		players_hands(pp) /= {} &
		cc : players_hands(pp) &
		// rules
		(CARD_VAL(cc) = CARD_VAL(last(discard_stack)) or
			CARD_COLOR(cc) = CARD_COLOR(last(discard_stack)) or
			CARD_COLOR(cc) = BLACK)	
	THEN
		players_hands(pp) := players_hands(pp) - {cc} ||	// remove the card from the players_hand
		discard_stack := discard_stack <- cc // add card to discard_stack
	END;

	push_discard_stack(cc) =
	PRE cc : CARDS & cc /: ran(discard_stack)
	THEN discard_stack := discard_stack <- cc 
	END

END
