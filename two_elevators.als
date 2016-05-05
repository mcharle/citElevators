open util/ordering [Floor] as f
open util/ordering [State] as st

// floor - there should be 6 of these in order
sig Floor{}

sig Elevator{}

sig Person {
	destination: one Floor
}

sig State{
	e: set Elevator -> one Floor,
	passengers : set Elevator -> set Person,
	p: set Person -> one Floor
} {
	passengers.p in e
}

// valid_move - checks if the elevator moved up or down one floor
// not every transition is a "move"
pred move_transition[pre: State, post: State] {
	all elev : Elevator | {elev.(post.e) = elev.(pre.e).next or elev.(post.e) = elev.(pre.e).prev}
	//is it implied that all people are in p?
	post.passengers = pre.passengers and
	all per: Person | !(per in Elevator.(pre.passengers)) implies pre.p = post.p
}

// transition where elevator stays on same floor (not a "move")
pred load_transition[pre: State, post: State] {
	pre.p = post.p and
	pre.e = post.e and
	all elev : Elevator | elev.(post.passengers) = elev.(pre.passengers) +
		{pass : Person | pass.(pre.p) = elev.(pre.e) and pass.(pre.p) != pass.destination and
		post.passengers.pass = elev}
}

// transition where elevator stays on same floor (not a "move")
pred unload_transition[pre: State, post:State] {
	pre.p = post.p and
	pre.e = post.e and
	all elev : Elevator | elev.(post.passengers) = elev.(pre.passengers) - {pass: Person | elev.(pre.e) = pass.destination}
}

fact pickup {
	// forces both elevators to visit all floors that people end on
	//Elevator -> Person.destination in State.e
	// forces both elevators to visit all floors that people start on
	Elevator -> Person.(st/first.p) in State.e
}

//all people and elevators have to be in a State - not sure this is necessary at all?
fact all_in_state {
	all person :Person |
		person in State.p.Floor	
	all elev : Elevator | 
		elev in State.e.Floor
}

//in the beginning, the passenger isn't on their desired floor or on any elevator
fact init {
	all pass: Person | pass.(st/first.p) != pass.destination
	no st/first.passengers
	// forces people to end two floors apart
	some pass1: Person | some pass2: Person | pass2.destination = pass1.destination.next.next
	// forces people to start two floors apart
	some pass1: Person | some pass2: Person | pass2.(st/first.p) = pass1.(st/first.p).next.next
}

//transition - checks that the elevator moves, loads or unloads
fact transition {
	all s : State - st/last |
		let s' = s.next |
			move_transition[s, s'] or
			load_transition[s, s'] or
			unload_transition[s,s']
}

//end_state - ensures that all people are at their destination floor in the last state
fact end_state {
	st/last.p = destination and
	no st/last.passengers
}

run{} for exactly 6 Floor, 5 State, exactly 2 Elevator, exactly 2 Person
