MACHINE GameState

SEES
	Stacks,
	Cards

VARIABLES
	drawing,
	skipping,
	setting_wild_color
	
INVARIANT
	drawing : NAT &
	skipping : NAT &
	setting_wild_color : {0,1}

INITIALISATION
	drawing := 0 ||
	skipping := 0 ||
	setting_wild_color := 0


OPERATIONS
	nn <-- get_drawing = nn := drawing;

	nn <-- get_skipping = nn := skipping;

	nn <-- get_setting_wild_color = nn := setting_wild_color;

	//set_drawing(nn) =
	//PRE 	nn : NAT
	//THEN	drawing := nn
	//END; 

	set_skipping(nn) =
	PRE 	nn : NAT
	THEN	skipping := nn
	END; 

	set_wild_color(cc) =
	PRE 	setting_wild_color = 0 &
			(CARD_VAL(cc) = eWILD or CARD_VAL(cc) = eWILD_DRAW_4) &
			CARD_COLOR(cc) = BLACK
	THEN	setting_wild_color := 1
	END;

	unset_wild_color =
	PRE setting_wild_color = 1
	THEN	setting_wild_color := 0
	END
	
	// set_setting_wild_color(nn) =
	// PRE 	nn : {0,1}
	// THEN	setting_wild_color := nn
	// END

END
