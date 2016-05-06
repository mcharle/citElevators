open util/ordering [Floor] as f
open util/ordering [State] as st

// there should be 6 of these in order
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
pred move_transition[pre: State, post: State, elev : Elevator] {
	elev.(post.e) = elev.(pre.e).next or elev.(post.e) = elev.(pre.e).prev
	elev.(post.passengers) = elev.(pre.passengers) //and
//	all per: Person | !(per in Elevator.(pre.passengers)) implies pre.p = post.p //??
}

// transition where elevator stays on same floor (not a "move")
pred load_transition[pre: State, post: State, elev: Elevator] {
	elev.(post.passengers) <: pre.p = elev.(post.passengers) <: post.p and
	elev.(pre.e) = elev.(post.e) and
	elev.(post.passengers) = elev.(pre.passengers) +
		{pass : Person | pass.(pre.p) = elev.(pre.e) and pass.(pre.p) != pass.destination and
		post.passengers.pass = elev}
}

// transition where elevator stays on same floor (not a "move")
pred unload_transition[pre: State, post:State, elev: Elevator] {
	elev.(pre.passengers) <: pre.p = elev.(pre.passengers) <: post.p and
	elev.(pre.e) = elev.(post.e) and
	elev.(post.passengers) = elev.(pre.passengers) - {pass: Person | elev.(pre.e) = pass.destination}
}

// forces both elevators to visit all floors that people start on in order to simulate always
// calling both elevators
pred original_elevators {
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
}

// forces people to end two floors apart
pred end_apart {
	some pass1: Person | some pass2: Person | pass2.destination = pass1.destination.next.next
}

// forces people to start two floors apart
pred start_apart {
	some pass1: Person | some pass2: Person | pass2.(st/first.p) = pass1.(st/first.p).next.next
}

pred below_fourth {
	some e1: Elevator | all st: State | e1.(st.e) in f/prevs[f/last.prev.prev]
}

pred diff_floors {
	some p1, p2: Person | p1.destination != p2.destination
}

pred start_on_first {
	Elevator.(st/first.e) = f/first.next
}

pred all_floors_used {
	Person.destination + Person.(st/first.p) = Floor
}

//transition - checks that the elevator moves, loads or unloads
fact transition {
	all s : State - st/last |
		let s' = s.next |
			(Person - Elevator.(s.passengers + s'.passengers)) <: s.p = ( Person - Elevator.(s.passengers + s'.passengers)) <: s'.p and
			all elev: Elevator |
				move_transition[s, s', elev] or
				load_transition[s, s', elev] or
				unload_transition[s,s',elev]
}

//end_state - ensures that all people are at their destination floor in the last state
fact end_state {
	st/last.p = destination and
	no st/last.passengers
}

assert no_jump {
	all s : State - st/last |
		let s' = s.next |
			all per : Person |
				per.(s.p) != per.(s'.p) implies per in Elevator.(s.passengers) and move_transition[s, s', s.passengers.per]
}
check no_jump for exactly 6 Floor, 5 State, exactly 2 Elevator, exactly 2 Person


run{diff_floors and start_on_first and below_fourth} for exactly 6 Floor, 4 State, exactly 2 Elevator, exactly 2 Person
run{start_apart and original_elevators and end_apart} for exactly 6 Floor, 5 State, exactly 2 Elevator, exactly 2 Person
run two_apart {start_apart and end_apart and below_fourth and start_on_first} for exactly 6 Floor, 5 State, exactly 2 Elevator, exactly 2 Person
run{start_apart and below_fourth and end_apart} for exactly 6 Floor, 4 State, exactly 2 Elevator, exactly 2 Person
run all_floors {all_floors_used and below_fourth and start_on_first} for exactly 6 Floor, 9 State, exactly 2 Elevator, exactly 3 Person
