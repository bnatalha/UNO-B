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

MACHINE BETTER_UNO

SETS
	// The black color is used for the trap cards without a color
	sCOLOR = {GREEN, BLUE, YELLOW, RED, BLACK};

	sVALUE = {
		N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,  // the numbers 0,1,...9
		eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERSE}	// effects

CONSTANTS
	DECK,
	CARDS, 
	CARD_COLOR,
	CARD_VAL,
	CARD_DESC,
	PLAYERS,
	HAND1, HAND2, INITIAL_DISCARD

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
	!ca.((ca : CARDS & ca <= 100 & (ca mod 25 = 12 or ca mod 25 = (12 + 12))) => {ca |-> eREVERSE} <: CARD_VAL) &
	!ca.((ca : CARDS & ca <= 100 & ca mod 25 = 0) => {ca |-> N0} <: CARD_VAL) &
	// especial wild
	!ca.((ca : CARDS & ca >= 109 & ca < 113) => {ca |-> eWILD} <: CARD_VAL) &
	!ca.((ca : CARDS & ca >= 113 & ca < 117) => {ca |-> eWILD_DRAW_4} <: CARD_VAL) &

	CARD_DESC : CARDS --> (sCOLOR * sVALUE) &
	!ca.(ca : CARDS => (ca |-> (CARD_COLOR(ca) |-> CARD_VAL(ca))) : CARD_DESC) &

	PLAYERS <: NAT1 &
	PLAYERS = {1,2} &

	// MOCK
	HAND1 = {1,8,40,32,103,106} &
	HAND2 = {2,9,41,33,102,107} &
	INITIAL_DISCARD = {(1 |-> 90), (2 |-> 91)}

VARIABLES
	draw_stack,
	discard_stack,
	players_hands,
	players_order,
	curr_player,
	winner,
	drawing,
	skipping,
	set_wild_color
	
INVARIANT
	draw_stack <: DECK &
	discard_stack : seq(CARDS) &	// because of wild cards strategy, may have repeated numbers
	players_hands : PLAYERS >-> POW(DECK) &
	winner : PLAYERS \/ {0} &
	drawing : NAT &
	skipping : NAT &
	set_wild_color : {0,1} &

	// no intersections between player's hands, or any stack
	draw_stack /\ ran(discard_stack) = {} &
	draw_stack /\ union({hh | hh : ran(players_hands)}) =  {} &
	ran(discard_stack) /\ union({hh | hh : ran(players_hands)}) = {} &

	// always have all 108 cards on game
	card(draw_stack) + size(discard_stack) + card(union({hh | hh : ran(players_hands)})) = 108 &
	
	players_order	: iseq(PLAYERS) &
	players_order /= [] &
	ran(players_order) = PLAYERS &
	
	// proof obligation
	curr_player: dom(players_order)

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
		discard_stack := initial_discard ||
		players_order 	:= [1,2] || 
		//ANY pseq WHERE pseq : iseq(PLAYERS) & ran(pseq) = PLAYERS THEN players_order := pseq END ||
		ANY pp WHERE pp : PLAYERS THEN curr_player := pp END ||
		//curr_player := 1 ||
		winner := 0 ||
		drawing := 0 ||
		skipping := 0 ||
		set_wild_color := 0
	END

	// CUSTOM INITIALIZATION
//	draw_stack := DECK - (HAND1 \/ HAND2 \/ ran(INITIAL_DISCARD)) ||
//	players_hands := {(1 |-> HAND1), (2 |-> HAND2)} ||
//	discard_stack := INITIAL_DISCARD ||
//	players_order 	:= [1,2] || 
//	curr_player := 1 ||
//	winner := 0 ||
//	drawing := 0 ||
//	skipping := 0 ||
//	set_wild_color := 0

OPERATIONS
//	cc <-- card_color(ca) =
//	PRE 	ca : CARDS
//	THEN 	cc := CARD_COLOR(ca)
//	END;
//
//	cc <-- card_val(ca) =
//	PRE 	ca : CARDS
//	THEN 	cc := CARD_VAL(ca)
//	END;
//
//	cc <-- card_desc(ca) =
//	PRE 	ca : CARDS
//	THEN 	cc := CARD_DESC(ca)
//	END;
//
//	bb <-- can_play_card(c1, c2) = 
//	PRE c1 : CARDS & c2 : CARDS
//	THEN 	IF CARD_VAL(c1) = CARD_VAL(c2) or CARD_COLOR(c1) = CARD_COLOR(c2)
//		THEN bb := true
//		ELSE bb := false
//		END
//	END;

	pp <-- current_player = pp := players_order(curr_player);

	pp <-- get_winner =
	pp := winner;
	
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
