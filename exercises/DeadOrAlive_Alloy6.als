sig Person {
var liveness: Liveness
}

assert DeadSinceDeath2 {
always (all p: Person | p.liveness = Dead implies (p.liveness=Dead since Die[p]))}

assert IfAliveBeforeAlive {
after (always (all p:Person | p.liveness = Alive implies before p.liveness = Alive) )}

enum Liveness {Alive, Dead}

pred Die [p: Person] {
p.liveness = Alive
p.liveness' = Dead }

fact AliveUntilDeath {
always ( all p:Person | p.liveness = Alive implies (Die[p] releases p.liveness = Alive))}

assert DeadSinceDeath3 {
always (all p: Person | Die[p] implies ( p.liveness = Dead triggered p.liveness = Alive))}

fact NoResurrection {
always (all p:Person| p.liveness = Dead implies after p.liveness = Dead)}

fact NoImmortality  {
always (all p:Person | p.liveness = Alive implies after (eventually p.liveness = Dead))}

fact NoDeadThenAlive {
always (all p:Person | p.liveness = Alive implies historically p.liveness = Alive)}

fact DeadSinceDeath {
always (all p:Person | p.liveness = Dead implies once Die [p])}

check DeadSinceDeath3

run{#Person = 4 and some p: Person | (p.liveness = Alive ; p.liveness = Alive ; p.liveness = Dead)} for 5
