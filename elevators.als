//basic scenario with two separate elevators
open util/ordering [Floor] as f
open util/ordering[State] as s

abstract sig Direction {}
one sig Up extends Direction {}
one sig Down extends Direction {}

abstract sig Floor {} //should this even be abstract??

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
}

one sig e1 extends Elevator {}
one sig e2 extends Elevator {}

sig State {
	locations: set Elevator -> one Floor,
	people: set Person -> one Floor,
	calls: set Elevator -> set Floor
}

abstract sig Event{
	pre, post: State
}

sig boarding extends Event {}
{
	pre.locations = post.locations
}

sig moveElevator extends Event {}
{
	//elevators only move one floor per transition
	post.locations in next[pre.locations] + prev[pre.locations] + pre.locations
}

fact transitions {
	all s: State - last |
		let s' = s.next | 
			//every two states connected by one trace
			one e: Event | e.pre = s and e.post = s'

}

fact init {
	//no passengers on elevators
	no (s/first.locations).Floor.passengers
	// all people on starting floors
	s/first.people = start
	//all people have called both elevators
	Elevator -> Person.(s/first.people) = s/first.calls
}


run{} for 6 Floor, 1 Up, 1 Down, exactly 1 Person, 2 State, 1 Trace


