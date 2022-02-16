MACHINE Cards

SETS
	// The black color is used for the trap cards without a color
	sCOLOR = {GREEN, BLUE, YELLOW, RED, BLACK};

	sVALUE = {
		N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,  // the numbers 0,1,...9
		eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERT}	// effects

CONSTANTS
	DECK,
	CARDS, 
	CARD_COLOR,
	CARD_VAL,
	CARD_DESC
	// HAND1, HAND2, INITIAL_DISCARD

PROPERTIES
	// building deck definitions...
	DECK = 1..108 &
	CARDS = DECK \/ 109..116 &	// 109..116 are special colors for effects
	CARD_COLOR : CARDS -->> sCOLOR &
	!ca.((ca : CARDS & ca <= 25) => (ca, RED) : CARD_COLOR) &
	!ca.((ca : CARDS & ca > 25 & ca <= 50) => (ca, GREEN) : CARD_COLOR) &
	!ca.((ca : CARDS & ca > 50 & ca <= 75) => (ca, BLUE) : CARD_COLOR) &
	!ca.((ca : CARDS & ca > 75 & ca <= 100) => (ca, YELLOW) : CARD_COLOR) &
	!ca.((ca : CARDS & ca > 100 & ca <= 108) => (ca, BLACK) : CARD_COLOR) &
	// especial wild
	!ca.((ca : CARDS & (ca = 109 or ca = 113)) => (ca, RED) : CARD_COLOR) &
	!ca.((ca : CARDS & (ca = 110 or ca = 114)) => (ca, GREEN) : CARD_COLOR) &
	!ca.((ca : CARDS & (ca = 111 or ca = 115)) => (ca, BLUE) : CARD_COLOR) &
	!ca.((ca : CARDS & (ca = 112 or ca = 116)) => (ca, YELLOW) : CARD_COLOR) &

	CARD_VAL : CARDS -->> sVALUE &
	!ca.((ca : CARDS & ca >= 101 & ca < 105) => {ca |-> eWILD} <: CARD_VAL) &
	!ca.((ca : CARDS & ca >= 105 & ca < 109) => {ca |-> eWILD_DRAW_4} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 1 or ca mod 25 = (12 + 1))) => {ca |-> N1} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 2 or ca mod 25 = (12 + 2))) => {ca |-> N2} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 3 or ca mod 25 = (12 + 3))) => {ca |-> N3} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 4 or ca mod 25 = (12 + 4))) => {ca |-> N4} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 5 or ca mod 25 = (12 + 5))) => {ca |-> N5} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 6 or ca mod 25 = (12 + 6))) => {ca |-> N6} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 7 or ca mod 25 = (12 + 7))) => {ca |-> N7} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 8 or ca mod 25 = (12 + 8))) => {ca |-> N8} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 9 or ca mod 25 = (12 + 9))) => {ca |-> N9} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 10 or ca mod 25 = (12 + 10))) => {ca |-> eDRAW_2} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 11 or ca mod 25 = (12 + 11))) => {ca |-> eSKIP} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 12 or ca mod 25 = (12 + 12))) => {ca |-> eREVERT} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & ca mod 25 = 0) => {ca |-> N0} <: CARD_VAL) &
	// especial wild
	!ca.((ca : CARDS & ca >= 109 & ca < 113) => {ca |-> eWILD} <: CARD_VAL) &
	!ca.((ca : CARDS & ca >= 113 & ca < 117) => {ca |-> eWILD_DRAW_4} <: CARD_VAL) &

	CARD_DESC : CARDS --> (sCOLOR * sVALUE) &
	!ca.(ca : CARDS => (ca |-> (CARD_COLOR(ca) |-> CARD_VAL(ca))) : CARD_DESC)

	// MOCK
	// HAND1 = {1,8,40,32,103,106} &
	// HAND2 = {2,9,41,33,102,107} &
	// INITIAL_DISCARD = {(1 |-> 90), (2 |-> 91)}

//	OPERATIONS
//		cc <-- card_color(ca) =
//		PRE 	ca : CARDS
//		THEN 	cc := CARD_COLOR(ca)
//		END;
//	
//		cc <-- card_val(ca) =
//		PRE 	ca : CARDS
//		THEN 	cc := CARD_VAL(ca)
//		END;
//	
//		cc <-- card_desc(ca) =
//		PRE 	ca : CARDS
//		THEN 	cc := CARD_DESC(ca)
//		END;
//	
//		bb <-- can_play_card(c1, c2) = 
//		PRE c1 : CARDS & c2 : CARDS
//		THEN 	IF CARD_VAL(c1) = CARD_VAL(c2) or CARD_COLOR(c1) = CARD_COLOR(c2)
//			THEN bb := true
//			ELSE bb := false
//			END
//		END;

END