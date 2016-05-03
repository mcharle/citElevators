open util/ordering [Floor] as f
open util/ordering [State] as st

// floor - there should be 6 of these in order
sig Floor{}

//elevator instances - in this model there is only one distinct elevator (in real life)
//but many instances of this sig (in the model) to account for different states
sig Elevator{
	floor: one Floor,
	passengers: set Person
}

//person instances - in this model, there is only one distinct person being modeled ->
// destination should never change between states 
sig Person {
	destination: one Floor
}

//each state has one elevator on a specific floor and one person
sig State{
	e: one Elevator,
	p: set Person -> one Floor
} {
	//e.passengers in p.Floor
	all pass: p.Floor | pass in e.passengers implies pass.p = e.floor
}

// valid_move - checks if the elevator moved up or down one floor
// not every transition is a "move"
pred move_transition[pre: State, post: State] {
	(post.e.floor = pre.e.floor.next or
	post.e.floor = pre.e.floor.prev) and
	post.p.Floor = pre.p.Floor and
	post.e.passengers = pre.e.passengers and
	let non_pass = Person - pre.e.passengers | non_pass <: pre.p = non_pass <: post.p
}

// transition where elevator stays on same floor (not a "move")
pred load_transition[pre: State, post: State] {
	pre.e.floor = post.e.floor and
	post.e.passengers = pre.e.passengers +
		{pass : Person | pass.(pre.p) = pre.e.floor and pass.(pre.p) != pass.destination}
	and pre.p = post.p
}

// transition where elevator stays on same floor (not a "move")
pred unload_transition[pre: State, post:State] {
	pre.e.floor = post.e.floor and
	post.e.passengers = pre.e.passengers - {pass: Person | pre.e.floor = pass.destination} and
	pre.p = post.p
}

//all people and elevators have to be in a State
fact all_in_state {
	all person :Person |
		person in State.p.Floor	
	all elev : Elevator | 
		elev in State.e
}

//in the beginning, the passenger isn't on their desired floor or on any elevator
fact init {
	all pass: Person | pass.(st/first.p) != pass.destination
	no st/first.e.passengers
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
	no st/last.e.passengers
}


run{some p1, p2: Person | p1.destination != p2.destination} for exactly 6 Floor,  8 State, 8 Elevator, exactly 2 Person
