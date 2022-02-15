MACHINE Game

SEES
	Stacks,
	Cards

VARIABLES
	drawing,
	skipping
	
INVARIANT
	drawing : NAT &
	skipping : NAT

INITIALISATION
	drawing := 0 ||
	skipping := 0


OPERATIONS

	nn <-- get_drawing = nn := drawing;

	nn <-- get_skipping = nn := skipping;

	//set_drawing(nn) =
	//PRE 	nn : NAT
	//THEN	drawing := nn
	//END; 

	set_skipping(nn) =
	PRE 	nn : NAT
	THEN	skipping := nn
	END

END
