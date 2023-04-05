sig Person {
var loc: City,
pass: some City,
var visited_cities: set City,
var status: Status
}

enum Status {Travelling, AtDestination}

sig City {
linkedWith: some City,
name: disj one EuropeanCities
}

enum EuropeanCities {Milan, Berlin, Paris, London, Vienna, Prague, Stockholm, Amsterdam, Copenaghen}

fact BidirectionalConnection{
all c1, c2: City | c1 in c2.linkedWith iff c2 in c1.linkedWith and !(c1 = c2) and c1.*linkedWith = City}

fact NoVisitedCitiesAtTheBeginning {
all p:Person | no p.visited_cities}

fact StartingFromMilanAndComingBack {
all p:Person | p.loc.name = Milan and p.status = Travelling and after (eventually (always p.loc.name = Milan and p.status=AtDestination))}

fact VisitingIsForever {
all p: Person, c: City | always (c in p.visited_cities implies always c in p.visited_cities)}

pred move[p: Person, c: City] {
c in p.loc.linkedWith and c in p.pass and c not in p.visited_cities and c not in p.loc
p.loc' = c
c in p.visited_cities'
}

pred moved[p: Person] { some c: City | move[p,c]}

pred unmoved[p: Person] {  p.loc = p.loc'}


fact NeverVisitedCities{ 
all c: City, p: Person |always( c not in p.visited_cities implies historically c not in p.visited_cities) 
}

fact VisitedCities{ 
all c: City, p: Person | always (c in p.visited_cities implies once move[p, c])
}

fact VisitingAllCities{ 
all p: Person, c: City | (c in p.pass and !(c.name = Milan)) implies (always (after !(p.loc.name = Milan) until (c in p.visited_cities)))
}

--fact OneDayVisitingOneDayTraveling{ 
	--all p: Person | always ((moved[p] and p.status = Travelling implies after unmoved[p]) || 
	--(unmoved[p] and p.status = Travelling  implies after moved[p])
--}

fact MovingOrNot {
all p: Person | always (moved[p] or unmoved[p])}

fact NoLongerTraveling{ 
all p: Person | after (p.loc.name = Milan releases p.status = Travelling)}

fact Departure { 
	all p: Person | always (moved[p] implies (p.status = Travelling since p.loc.name = Milan))
}

assert Departure2{ 
	all p: Person | always (p.status = Travelling implies (p.loc.name = Milan triggered p.status = Travelling)) 
}

pred world1{#City = 6 and #Person = 2 #Person.visited_cities' = 2 ; #Person.visited_cities' = 4 ;  #Person.visited_cities' = 6}
run world1 for 10 
