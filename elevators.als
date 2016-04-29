//basic scenario with two separate elevators
open util/ordering [Floor] as f
open util/ordering[State] as s

abstract sig Direction {}
one sig Up extends Direction {}
one sig Down extends Direction {}

abstract sig Floor {}

sig Person {
	start: one Floor,
	destination: one Floor
}
{
	start != destination
}

abstract sig Elevator {
	direction: one Direction,
	passengers: set Person,
	calls: set Floor
}

one sig e1 extends Elevator {}
one sig e2 extends Elevator {}

sig State {
	locations: set Elevator -> one Floor,
	people: set Person -> one Floor
}

sig Trace {
	pre, post: State
}


fact transitions {
	all s: State - last |
		let s' = s.next | s'.locations in next[s.locations] + prev[s.locations] + s.locations and
			one e: Trace | e.pre = s and e.post = s'
}

fact initial_state {
	no (s/first.locations).Floor.passengers and
	s/first.people = start	
	

}

run{} for 6 Floor, 1 Up, 1 Down, exactly 1 Person, 2 State, 1 Trace


