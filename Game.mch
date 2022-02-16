MACHINE Game

SEES
	Cards

VARIABLES
	drawing
	
INVARIANT
	drawing : NAT

INITIALISATION
	drawing := 0

OPERATIONS

	nn <-- get_drawing = nn := drawing;

	set_drawing(nn) =
	PRE 	nn : NAT
	THEN	drawing := nn
	END

END
