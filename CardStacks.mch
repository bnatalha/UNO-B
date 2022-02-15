
MACHINE CardStacks

SEES
	Cards,
	Players

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
	// shuffle initial hands, discards 2 cards
	ANY 	hand1, hand2, initial_discard
	WHERE	hand1 <: DECK & hand2 <: DECK & initial_discard : iseq(DECK) &
		card(hand1) = 7 & card(hand2) = 7 & size(initial_discard) = 2 &
		// can't have an intersection between the draws
		hand1 /\ hand2 = {} &
		hand1 /\ ran(initial_discard) = {} &
		hand2 /\ ran(initial_discard) = {}
	THEN 	draw_stack := DECK - (hand1 \/ hand2 \/ ran(initial_discard)) ||
		players_hands := {(1 |-> hand1), (2 |-> hand2)} ||
		discard_stack := initial_discard
	END

OPERATIONS
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
	END

END
