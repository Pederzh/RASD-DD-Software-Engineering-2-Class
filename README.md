# SafeStreets project: Cavadini, Molinari, Pederzani

DD (Design Document): https://bit.ly/3CD5APc

## RASD (Requirement Analysis and Specification Document)
The	Requirements	analysis	and	specification	document	(RASD) contains	the	description	of	the	scenarios,	
the	use	cases	 that	describe	 them,	and	 the	models	describing	requirements	and	specification	 for	 the	
problem	under	consideration.	You	are	to use	a	suitable	mix	of	natural	language,	UML, and	Alloy.

## DD (Design Document)
The Design	document	(DD) must	contain	a	functional	description	of	the	system,	and	any	other	view	you	
find	useful	to	provide.	You	should	use	all	the	UML	diagrams	you	need	to	provide	a	full	description	of	
the	 system.

## Deliverables
RASD (Requirement Analysis and Specification Document): https://bit.ly/3qYutCU

DD (Design Document): https://bit.ly/3CD5APc

## Assignment:
SafeStreets	is	a	crowd-sourced	application	that	intends	to	provide	users	with	the	possibility	to	notify	
authorities	when traffic violations	occur,	and in	 particular	 parking	violations.	The	application	allows	
users	to	send	pictures	of	violations,	including	their	date,	time,	and	position,	to	authorities.	Examples	of	
violations	 are	 vehicles	 parked	 in	 the	 middle	 of	 bike	 lanes	 or	 in	 places	 reserved	 for	 people	 with	
disabilities,	double	parking,	and	so	on.
Basic	service:	SafeStreets	stores	the	information	provided	by	users,	completing	it	with	suitable	metadata.	In	particular,	when	it	receives	a	picture,	it	runs	an	algorithm	to	read	the	license	plate	(one	can	
also	think	of	mechanisms	with	which	the	user	can	help	with	the	recognition),	and	stores	the	retrieved	
information	with	the	violation,	including	also	the	type	of	the	violation	(input	by	the	user)	and	the	name	
of	the	street	where	the	violation	occurred (which	can	be	retrieved	from	the	geographical	position of	
the	violation).	In	addition,	the	application	allows both	end	users	and authorities	to	mine	the	information
that	has	been	received,	for	example	by	highlighting	the	streets	(or	the	areas)	with	the	highest	frequency	
of	violations,	or	 the	vehicles	 that	commit	 the	most	violations. Of	course,	different	levels	of	visibility	
could	be	offered	to	different	roles.	
Advanced	function 1:	If	the	municipality	offers	a	service	that	allows	users	to	retrieve	the	information	
about	the	accidents	that	occur	on	the	territory	of	the	municipality,	SafeStrees	can	cross	this	information	
with	its	own	data	to	identify	potentially unsafe	areas,	and	suggest	possible	interventions	(e.g.,	add	a	
barrier between	 the	 bike	 lane	 and	 the	 part	 of	 the	 road	 for	 motorized	 vehicles	 to	 prevent	 unsafe	
parking).
Advanced	functions 2:	In	addition,	the	municipality	(and, in	particular, the	local	police)	could	offer	a	
service	that	takes	the	information	about	the	violations	coming	from	SafeStreets,	and	generates	traffic	
tickets	from	it. In	this	case,	mechanisms	should	be	put	in	place	to	ensure	that	the	chain	of	custody	of	
the	information	coming	from	the	users	is	never	broken,	and	the	information	is	never	altered	(e.g.,	if a	
manipulation	occurs	at	any	point	of	the	image	showing	the	violation,	for	example	to	alter	the	license	
plate,	the	application	should	discard	the	information). In	addition,	the	information	about	issued	tickets	
can	be	used	by	SafeStreets	to	build	statistics,	for	example	about	the	most	egregious	offenders,	or	the	
effectiveness	of	the	SafeStreets	initiative (e.g.,	by	looking	for	trends	in	the	issuing	of	tickets).




