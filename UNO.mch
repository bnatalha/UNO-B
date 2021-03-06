/**
TODO: 
	- initialize with 7 cards for each player;
	- initialize the discard_stack with 2 cards taken from the draw_stack;
	- plays_card only if it's the player's turn;
		- implement turns;
	- play a game with only the cards with number's as values;
	- add more players;
	- add Effect cards rules to the game;
	- add more other rules;
	- refact project;

*/

MACHINE UNO
SETS
	// The black color is used for the trap cards without a color
	COLORS = {GREEN, BLUE, YELLOW, RED, BLACK};

	CARD_VALUES = {
		N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,  // the numbers 0,1,...9
		eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERSE};	// effects

	BOOLEANS = {true, false}
CONSTANTS 
	/* main sets */
	VALID_CARDS,
	NUMBER_CARDS,
	EFFECT_CARDS,
	MAIN_COLORS,
	NUMBERS,
	EFFECTS,

	/* effect cards */
	WILD,
	WILD_DRAW_4,
	// effect cards set
	DRAW_2_SET,
	SKIP_SET,
	REVERSE_SET,

	/* game */
	PLAYERS,
	DECK,	// 4 x WILD_DRAW_4, WILD
		// 4 x N0 == card(COLOR - {BLACK})
		// 2 x other cards == 2 * card(COLOR - {BLACK})
	CAN_PLAY_CARD
PROPERTIES

	MAIN_COLORS <: COLORS &
	MAIN_COLORS = COLORS - {BLACK} &

	// EFFECTS
	EFFECTS <: CARD_VALUES &
	EFFECTS =	{eWILD, eWILD_DRAW_4, eDRAW_2, eSKIP, eREVERSE} &
	// EFFECT CARDS
	WILD = (eWILD |-> BLACK) &
	WILD_DRAW_4 = (eWILD_DRAW_4 |-> BLACK) &
	DRAW_2_SET = {eDRAW_2} * MAIN_COLORS &
	SKIP_SET = {eSKIP} * MAIN_COLORS &
	REVERSE_SET = {eREVERSE} * MAIN_COLORS &
	EFFECT_CARDS = {WILD, WILD_DRAW_4} \/ 
			DRAW_2_SET \/ 
			SKIP_SET \/ 
			REVERSE_SET &

	// NUMBERS
	NUMBERS <: CARD_VALUES & 
	NUMBERS = {N0,N1,N2,N3,N4,N5,N6,N7,N8,N9} &
	// NUMBER CARDS
	NUMBER_CARDS = NUMBERS * MAIN_COLORS &

	VALID_CARDS = NUMBER_CARDS \/ EFFECT_CARDS &

	DECK = [WILD, WILD, WILD, WILD, //4x
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
		(eREVERSE |-> RED), (eREVERSE |-> GREEN), (eREVERSE |-> YELLOW), (eREVERSE |-> BLUE)] &

	// DECK = [(N1 |-> RED), (N1 |-> GREEN), (N1 |-> YELLOW), (N1 |-> BLUE)] &
	/*DECK = ({1,2,3,4} * {WILD, WILD_DRAW_4}) \/
		({1} * ( {N0} * MAIN_COLORS )) \/
		({1,2} * ({N0} <<| NUMBER_CARDS)) \/
		({1,2} * (DRAW_2_SET \/ SKIP_SET \/ REVERSE_SET) )*/

	PLAYERS <: NAT1 &
	PLAYERS = {1,2} &

	/* 
	 *  where (val1 |-> col1) is the card to be played and
	 *  (val2 |-> col2) is the last discarded card
	 */

	CAN_PLAY_CARD : VALID_CARDS <-> VALID_CARDS &
	
	!(val1 , val2, col1, col2).(
		(val1 : dom(VALID_CARDS) & val2 : dom(VALID_CARDS) &
		 col1 : VALID_CARDS[{val1}] & col2 : VALID_CARDS[{val2}]) & 
		((col1 = BLACK) or (col2 = BLACK) or (col1 = col2) or (val1 = val2)) =>
   	 	((val1 |-> col1) |-> (val2 |-> col2)) : CAN_PLAY_CARD)
		
  		
	

VARIABLES
	draw_stack,
	discard_stack,
	player_order,
	players_hands
INVARIANT 
	player_order : perm(PLAYERS) &
	ran(draw_stack) <: ran(DECK) &
	ran(discard_stack) <: ran(DECK) &
	players_hands : PLAYERS --> seq(CARD_VALUES*COLORS) &
	
	/* deck size invariants */
	size(draw_stack) + size(discard_stack) + SIGMA(zz).(zz : ran(players_hands) | size(zz)) = size(DECK)

INITIALISATION
 	player_order := [1,2] ||
	
	// initialize the draw_stack with DECK, but discards 1 card
	ANY idx1, idx2 WHERE idx1 : dom(DECK) & idx2 : dom(DECK) & idx1 /= idx2
		THEN
			draw_stack := front(DECK /|\ idx1) ^ (DECK \|/ idx1) ||	// remove the card from the draw_stack
			discard_stack := [DECK(idx1)]	// add card to discard_stack
		END ||
	
	players_hands := PLAYERS * seq({})
	
OPERATIONS
	
	// test operation:
	// draw a card from de stack and discards it
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

	// player pp will try to play the card cc
	/*play(pp, cc) =
		PRE pp : PLAYERS & cc : ran(players_hands(pp)) & (cc |-> last(discard_stack)) : CAN_PLAY_CARD // & it's pp's turn to play
		THEN 
			ANY hand, idx WHERE hand = players_hands(pp) & idx : dom((players_hands(pp)) |> {cc}) THEN
				players_hands(pp) := front(hand /|\ idx) ^ (hand \|/ idx) ||	// remove the card from the players_hand
				discard_stack := discard_stack <- hand(idx)	// add card to discard_stack
			END
		END;*/

	// player pp will draw a random card from the draw_stack to it's hand
	cc <-- draw_card_hand(pp) =
		PRE draw_stack /= [] & pp : PLAYERS
		THEN
			ANY idx WHERE idx : dom(draw_stack)
			THEN 
				cc := draw_stack(idx) ||	
				draw_stack := front(draw_stack /|\ idx) ^ (draw_stack \|/ idx) ||	// remove the card from the draw_stack
				players_hands(pp) := players_hands(pp) <- draw_stack(idx)	// add card to players_hand
			END
		END
		
END

