//PART ONE: THE BASIC MODEL

open util/ordering [Floor] as f
open util/ordering [State] as st

// there should be 6 floors, to represent the CIT (specified in the run command)
sig Floor{}
sig Elevator{}

sig Person {
	destination: one Floor
}

sig State{
	//each elevator is on one floor
	e: set Elevator -> one Floor,
	//each elevator has a set of passengers
	passengers : set Elevator -> set Person,
	//each person is on one floor
	p: set Person -> one Floor
} {
	//if a person is on an elevator, they have to be on the same floor as the elevator
	passengers.p in e
}

//in the beginning, the passenger isn't on their desired floor or on any elevator
fact init {
	all pass: Person | pass.(st/first.p) != pass.destination
	no st/first.passengers
}

//checks that each elevator moves, loads or unloads, and that people who aren't passengers don't move (frame condition)
fact transition {
	all s : State - st/last |
		let s' = s.next |
			//frame condition
			let non_pass = (Person - Elevator.(s.passengers & s'.passengers)) | 
				{non_pass <: s.p = non_pass <: s'.p} and
			//all elevators move, load, or unload
			all elev: Elevator |
				{move_transition[s, s', elev] or
				load_transition[s, s', elev] or
				unload_transition[s,s',elev]}
}

//ensures that all people are at their destination floor in the last state
fact end_state {
	st/last.p = destination and
	no st/last.passengers
}

//transition for one elevator moving up or down one floor
pred move_transition[pre: State, post: State, elev : Elevator] {
	elev.(post.e) = elev.(pre.e).next or elev.(post.e) = elev.(pre.e).prev
	elev.(post.passengers) = elev.(pre.passengers) 
}

// transition where people get off the elevator
pred load_transition[pre: State, post: State, elev: Elevator] {
	//the elevator stays on the same floor
	elev.(pre.e) = elev.(post.e) and
	//everyone on the same floor as the elevator gets on who isn't at their destination or on another elevator
	elev.(post.passengers) = elev.(pre.passengers) +
		{pass : Person | pass.(pre.p) = elev.(pre.e) and pass.(pre.p) != pass.destination and
		post.passengers.pass = elev}
}

// transition where people get on the elevator
pred unload_transition[pre: State, post:State, elev: Elevator] {
	//the elevator stays on the same floor
	elev.(pre.e) = elev.(post.e) and
	//everyone who is at their destination gets off the elevator
	elev.(post.passengers) = elev.(pre.passengers) - {pass: Person | elev.(pre.e) = pass.destination}
}


//checks that people don't jump floors without being on moving elevators (the frame condition)
assert no_jump {
	all s : State - st/last |
		let s' = s.next |
			all per : Person |
				per.(s.p) != per.(s'.p) implies per in Elevator.(s.passengers) and move_transition[s, s', s.passengers.per]
}
check no_jump for exactly 6 Floor, 5 State, exactly 2 Elevator, exactly 3 Person


//PART TWO: RESTRICTIONS FOR DIFFERENT SCENARIOS

//ELEVATOR RESTRICTIONS

// forces both elevators to visit all floors that people start on in order to simulate always
// calling both elevators
pred call_both {
    Elevator -> Person.(st/first.p) in State.e
}

//one elevator always stays below fourth floor
pred below_fourth {
	some e1: Elevator | all st: State | e1.(st.e) in f/prevs[f/last.prev.prev]
}

//elevators must start on the "first"/ground floor
pred start_on_first {
	Elevator.(st/first.e) = f/first.next
}

//PASSENGER RESTRICTIONS

//forces two people to have different destination floors
pred diff_floors {
	some p1, p2: Person | p1.destination != p2.destination
}

// forces two people to end two floors apart
pred end_apart {
	some pass1: Person | some pass2: Person | pass2.destination = pass1.destination.next.next
}

// forces two people to start two floors apart
pred start_apart {
	some pass1: Person | some pass2: Person | pass2.(st/first.p) = pass1.(st/first.p).next.next
}

//forces all the floors to be either the starting or ending floors of at least one person in the model
pred all_floors_used {
	Person.destination + Person.(st/first.p) = Floor
}




//PART 3: RUNNING DIFFERENT SCENARIOS
//have to add in which elevator scenario you want by hand
run different_destinations {diff_floors} for exactly 6 Floor, 4 State, exactly 2 Elevator, exactly 2 Person
run two_apart {start_apart and end_apart} for exactly 6 Floor, 4 State, exactly 2 Elevator, exactly 2 Person
run all_floors {all_floors_used} for exactly 6 Floor, 8 State, exactly 2 Elevator, exactly 3 Person
