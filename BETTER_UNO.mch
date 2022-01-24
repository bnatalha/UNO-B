/**
TODO: 
	- [x] initialize the discard_stack with 2 cards taken from the draw_stack;
	- [x] initialize with 7 cards for each player;
	- [/] plays_card only if it's the player's turn;
		- implement turns;
	- [x] play a game with only the cards with number's as values;
	- add more players;
	- add effect cards rules to the game;
	- add other rules;
	- refact project;
  - win a game;
  - draw when needed;
*/

MACHINE BETTER_UNO

SETS
	// The black color is used for the trap cards without a color
	sCOLOR = {GREEN, BLUE, YELLOW, RED, BLACK};

	sVALUE = {
		N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,  // the numbers 0,1,...9
		eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERSE};	// effects

	sBOOLEAN = { false, true }

CONSTANTS 
	CARDS, CARD_COLOR, CARD_VAL,
	CARD_DESC, //HAND_DESC,
	CAN_PLAY_CARD, CAN_PLAY,
	PLAYERS

PROPERTIES
	// building deck definitions...
	CARDS = 1..108 &
	CARD_COLOR : CARDS -->> sCOLOR &
	!ca.((ca : CARDS & ca > 100) => {ca |-> BLACK} <: CARD_COLOR) &
	!ca.((ca : CARDS & ca <= 25) => {ca |-> RED} <: CARD_COLOR) &
	!ca.((ca : CARDS & ca > 25 & ca <= 50) => {ca |-> GREEN} <: CARD_COLOR) &
	!ca.((ca : CARDS & ca > 50 & ca <= 75) => {ca |-> BLUE} <: CARD_COLOR) &
	!ca.((ca : CARDS & ca > 75 & ca <= 100) => {ca |-> YELLOW} <: CARD_COLOR) &

	CARD_VAL : CARDS --> sVALUE &
	!ca.((ca : CARDS & ca > 104) => {ca |-> eWILD_DRAW_4} <: CARD_VAL) &
	!ca.((ca : CARDS & ca > 100 & ca < 104) => {ca |-> eWILD} <: CARD_VAL) &
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

	CARD_DESC : CARDS --> (sCOLOR * sVALUE) &
	!ca.(ca : CARDS => (ca |-> (CARD_COLOR(ca) |-> CARD_VAL(ca))) : CARD_DESC) &

	// TODO: error (infinite possibilities)
	// HAND_DESC : iseq(CARDS) --> (CARDS * (sCOLOR * sVALUE)) &
	//!hh.(hh : iseq(CARDS) => (!idx.(idx : dom(hh) => (hh |-> (idx |-> CARD_DESC(hh(idx)))) : HAND_DESC))) &
	//!hh.(hh : iseq(CARDS) =>
	//	(#des.(des : ran(CARD_DESC) => 
	//	(#idx.(idx : dom(hh) => 
	//	(CARD_DESC(hh(idx)) = des &
	//	(hh |-> (idx |-> des)) : HAND_DESC)))))) &

	// (c1 |-> c2) : CAN_PLAY_CARD implies that c1 can be played after c2
	CAN_PLAY_CARD = (CARDS * CARDS) &
	!(c1, c2).(
	  (c1 : CARDS & c2 : CARDS & 
           (CARD_VAL(c1) = CARD_VAL(c2) or // have the same value
	    // CARD_COLOR(c1) = BLACK or	// the card being played is black
            CARD_COLOR(c1) = CARD_COLOR(c2)) => // have the same color
	 ((c1 |-> c2) : CAN_PLAY_CARD))) &

	// TODO: condição não ta funcionando
	CAN_PLAY = (iseq(CARDS) * CARDS) & //CANNOT
	!(hh, cc).(
		(hh : iseq(CARDS) & cc : CARDS => 
        		(!ca.((ca : ran(hh) & (ca |-> cc) /: CAN_PLAY_CARD) =>
		((hh |-> cc) : CAN_PLAY)
		)))) &

	PLAYERS <: NAT1 &
	PLAYERS = {1,2}

INVARIANT
	draw_stack <: CARDS &
	discard_stack : iseq(CARDS) &
	players_hands : PLAYERS >-> iseq(CARDS) &
	players_order	: iseq(PLAYERS) &
	turn: PLAYERS

VARIABLES
	draw_stack,
	discard_stack,
	players_hands,
	players_order,
	turn

INITIALISATION
	// shuffle initial hands, discards 2 cards
	ANY 	hand1, hand2, initial_discard
	WHERE	hand1 : iseq(CARDS) & hand2 : iseq(CARDS) & initial_discard : iseq(CARDS) &
		size(hand1) = 7 & size(hand2) = 7 & size(initial_discard) = 2 &
		// can't have an intersection between the draws
		ran(hand1) /\ ran(hand2) = {} &
		ran(hand1) /\ ran(initial_discard) = {} &
		ran(hand2) /\ ran(initial_discard) = {}
		//card(union({ran(hand1), ran(hand2), ran(initial_discard)})) = (14 + 2)
	THEN 	draw_stack := CARDS - (ran(hand1) \/ ran(hand2) \/ ran(initial_discard)) ||
		players_hands := {(1 |-> hand1), (2 |-> hand2)} ||
		discard_stack := initial_discard ||
		players_order 	:= [1,2] || 
		turn := 1
	END

	// TODO: generalized version for any number of players timing out
	//ANY 	hand
	//WHERE	hand : PLAYERS >-> iseq(CARDS) &
	//	!pp.(pp : PLAYERS => size(hand(pp)) = 7) &
	//	!(p1, p2).(p1 : PLAYERS & p2 : PLAYERS => 
	//		ran(hand(p1)) /\ ran(hand(p2)) = {})
	//THEN 	draw_stack := CARDS - ran(union(ran(hand))) ||
	//	players_hands := hand ||
	//	discard_stack := []
	//END

OPERATIONS
	cc <-- card_color(ca) =
	PRE 	ca : CARDS
	THEN 	cc := CARD_COLOR(ca)
	END;

	cc <-- card_val(ca) =
	PRE 	ca : CARDS
	THEN 	cc := CARD_VAL(ca)
	END;

	cc <-- card_desc(ca) =
	PRE 	ca : CARDS
	THEN 	cc := CARD_DESC(ca)
	END;

	hh <-- player_hand(pp) =
	PRE	pp : PLAYERS
	THEN 	hh := players_hands(pp)
	END;

	// TODO: is matching only when theres is only 1 card left at the hand
	hh <-- player_hand_with_desc(pp) = 
	PRE 	pp : PLAYERS
	THEN	hh := {ee | !idx.(idx : dom(players_hands(pp)) => ((idx |-> CARD_DESC((players_hands(pp))(idx))) = ee))}
	//THEN	hh := { ee | ee : (CARDS * (sCOLOR * sVALUE)) & 
	//	(#des.(des : ran(CARD_DESC) => 
	//	(#idx.(idx : dom(players_hands(pp)) => 
	//	(CARD_DESC(hh(idx)) = des &
	//	(idx |-> des) = ee)))))}
	END;

	play(pp, cc) =
	PRE 	pp : PLAYERS & 
		pp = players_order(turn) &
		cc : ran(players_hands(pp)) &
		(cc |-> last(discard_stack)) : CAN_PLAY_CARD //&
		//(players_hands(pp) |-> last(discard_stack)) : CAN_PLAY
	THEN
		ANY hand, idx WHERE hand = players_hands(pp) & idx : dom((players_hands(pp)) |> {cc}) THEN
			players_hands(pp) := front(hand /|\ idx) ^ (hand \|/ idx) ||	// remove the card from the players_hand
			discard_stack := discard_stack <- hand(idx)	|| // add card to discard_stack
			// TODO : transformar em propriedade
			IF 	((turn + 1) mod card(PLAYERS) = 0)
			THEN	turn := card(PLAYERS)
			ELSE	turn := ((turn + 1) mod card(PLAYERS))
			END
		END
	END
END
