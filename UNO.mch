MACHINE UNO
SETS
	COLORS = {GREEN, BLUE, YELLOW, RED, BLACK};
	CARD_VALUES = {
		N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,
		eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERSE}
CONSTANTS 
	/* main sets */
	VALID_CARDS,
	NUMBER_CARDS,
	EFFECT_CARDS,
	MAIN_COLORS,
	NUMBERS,
	EFFECTS,

	// EMPTY_HAND,

	/* effect cards */
	WILD,
	WILD_DRAW_4,
	// effect cards set
	DRAW_2_SET,
	SKIP_SET,
	REVERSE_SET,

	/* game */
	PLAYERS,
	DECK	// 4 x WILD_DRAW_4, WILD
		// 4 x N0 == card(COLOR - {BLACK})
		// 2 x other cards == 2 * card(COLOR - {BLACK})
PROPERTIES

	MAIN_COLORS <: COLORS &
	MAIN_COLORS = 		COLORS - {BLACK} &

	// EFFECTS
	EFFECTS <: CARD_VALUES &
	EFFECTS =	{eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERSE} &
	// EFFECT CARDS
	WILD = 		(eWILD |-> BLACK) &
	WILD_DRAW_4 = 		(eWILD_DRAW_4 |-> BLACK) &
	DRAW_2_SET = 		{eDRAW_2} * MAIN_COLORS &
	SKIP_SET = 		{eSKIP} * MAIN_COLORS &
	REVERSE_SET = 		{eREVERSE} * MAIN_COLORS &
	EFFECT_CARDS = 	{WILD, WILD_DRAW_4} \/ 
			DRAW_2_SET \/ 
			SKIP_SET \/ 
			REVERSE_SET &

	// NUMBERS
	NUMBERS <: CARD_VALUES & 
	NUMBERS = {N0,N1,N2,N3,N4,N5,N6,N7,N8,N9} &
	// NUMBER CARDS
	NUMBER_CARDS = NUMBERS * MAIN_COLORS &


	VALID_CARDS = NUMBER_CARDS \/ EFFECT_CARDS &


	/*DECK = [WILD, WILD, WILD, WILD, //4x
		WILD_DRAW_4, WILD_DRAW_4, WILD_DRAW_4, WILD_DRAW_4, // 4x
		// 0 CARD
		(N0 |-> RED), (N0 |-> GREEN), (N0 |-> YELLOW), (N0 |-> BLUE),
		// NUMBER_CARDS 2x
		(N1 |-> RED), (N1 |-> GREEN), (N1 |-> YELLOW), (N1 |-> BLUE),
		(N2 |-> RED), (N2 |-> GREEN), (N2 |-> YELLOW), (N2 |-> BLUE),
		(N3 |-> RED), (N3 |-> GREEN), (N3 |-> YELLOW), (N3 |-> BLUE),
		(N4 |-> RED), (N4 |-> GREEN), (N4 |-> YELLOW), (N4 |-> BLUE),
		(N5 |-> RED), (N5 |-> GREEN), (N5 |-> YELLOW), (N5 |-> BLUE),
		(N6 |-> RED), (N6 |-> GREEN), (N6 |-> YELLOW), (N6 |-> BLUE),
		(N7 |-> RED), (N7 |-> GREEN), (N7 |-> YELLOW), (N7 |-> BLUE),
		(N8 |-> RED), (N8 |-> GREEN), (N8 |-> YELLOW), (N8 |-> BLUE),
		(N9 |-> RED), (N9 |-> GREEN), (N9 |-> YELLOW), (N9 |-> BLUE),
		(N1 |-> RED), (N1 |-> GREEN), (N1 |-> YELLOW), (N1 |-> BLUE),
		(N2 |-> RED), (N2 |-> GREEN), (N2 |-> YELLOW), (N2 |-> BLUE),
		(N3 |-> RED), (N3 |-> GREEN), (N3 |-> YELLOW), (N3 |-> BLUE),
		(N4 |-> RED), (N4 |-> GREEN), (N4 |-> YELLOW), (N4 |-> BLUE),
		(N5 |-> RED), (N5 |-> GREEN), (N5 |-> YELLOW), (N5 |-> BLUE),
		(N6 |-> RED), (N6 |-> GREEN), (N6 |-> YELLOW), (N6 |-> BLUE),
		(N7 |-> RED), (N7 |-> GREEN), (N7 |-> YELLOW), (N7 |-> BLUE),
		(N8 |-> RED), (N8 |-> GREEN), (N8 |-> YELLOW), (N8 |-> BLUE),
		(N9 |-> RED), (N9 |-> GREEN), (N9 |-> YELLOW), (N9 |-> BLUE),
		// EFFECT_CARDS
		(eDRAW_2 |-> RED), (eDRAW_2 |-> GREEN), (eDRAW_2 |-> YELLOW), (eDRAW_2 |-> BLUE),
		(eDRAW_2 |-> RED), (eDRAW_2 |-> GREEN), (eDRAW_2 |-> YELLOW), (eDRAW_2 |-> BLUE),
		(eSKIP |-> RED), (eSKIP |-> GREEN), (eSKIP |-> YELLOW), (eSKIP |-> BLUE),
		(eSKIP |-> RED), (eSKIP |-> GREEN), (eSKIP |-> YELLOW), (eSKIP |-> BLUE),
		(eREVERSE |-> RED), (eREVERSE |-> GREEN), (eREVERSE |-> YELLOW), (eREVERSE |-> BLUE),
		(eREVERSE |-> RED), (eREVERSE |-> GREEN), (eREVERSE |-> YELLOW), (eREVERSE |-> BLUE)] &*/

	DECK = [(N1 |-> RED), (N1 |-> GREEN), (N1 |-> YELLOW), (N1 |-> BLUE)] &

	PLAYERS <: NAT1 &
	PLAYERS = {1,2}

	// EMPTY_HAND

	/*DECK = ({1,2,3,4} * {WILD, WILD_DRAW_4}) \/
		({1} * ( {N0} * MAIN_COLORS )) \/
		({1,2} * ({N0} <<| NUMBER_CARDS)) \/
		({1,2} * (DRAW_2_SET \/ SKIP_SET \/ REVERSE_SET) )*/
		
VARIABLES
	draw_stack,
	discard_stack,
	player_order,
	players_hands
INVARIANT 
	player_order : perm(PLAYERS) &
	draw_stack <: DECK &
	discard_stack <: DECK &
	players_hands : PLAYERS --> seq(CARD_VALUES*COLORS) &
	
	/* deck size invariants */
	size(draw_stack) + size(discard_stack) = size(DECK)

INITIALISATION
 	player_order := [1,2] ||
	draw_stack := DECK ||
	discard_stack := [] ||
	players_hands := COLORS * []
	
OPERATIONS
	cc <-- draw_card =
		PRE draw_stack /= []
		THEN
			ANY idx WHERE idx : dom(draw_stack)
			THEN 
				cc := draw_stack(idx) ||	
				draw_stack := front(draw_stack /|\ idx) ^ (draw_stack \|/ idx) ||	// remove the card from the draw_stack
				discard_stack := discard_stack <- draw_stack(idx)	// add card to discard_stack
			END
		END;

	cc <-- draw_card_hand(pp) =
		PRE draw_stack /= [] & pp : PLAYERS
		THEN
			ANY idx , cd WHERE idx : dom(draw_stack) & cd : draw_stack[{idx}]
			THEN 
				cc := draw_stack(idx) ||	
				draw_stack := front(draw_stack /|\ idx) ^ (draw_stack \|/ idx) ||	// remove the card from the draw_stack
				players_hands(pp) := players_hands(pp) <- cd	// add card to players_hand
			END
		END
		
END

