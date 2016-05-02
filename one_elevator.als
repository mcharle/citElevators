open util/ordering [Floor] as f
open util/ordering [State] as st

// floor - there should be 6 of these in order
sig Floor{}

//elevator instances - in this model there is only one distinct elevator (in real life)
//but many instances of this sig (in the model) to account for different states
sig Elevator{
	floor: one Floor,
	passengers: lone Person
}
{
	passengers.curr_floor = floor or no passengers 
}

//person instances - in this model, there is only one distinct person being modeled ->
// destination should never change between states 
sig Person {
	curr_floor: one Floor,
	destination: one Floor
}

//each state has one elevator on a specific floor and one person
sig State{
	e: one Elevator,
	p: one Person
} {
	e.passengers in p
}

// valid_move - checks if the elevator moved up or down one floor
pred valid_move[pre: State, post: State] {
	(post.e.floor = pre.e.floor.next or
	post.e.floor = pre.e.floor.prev) and
	post.p.destination = pre.p.destination and
	(!(pre.p in  pre.e.passengers) implies post.p = pre.p) and
	#{post.e.passengers} = #pre.e.passengers
}

pred load [pre: State, post: State] {
	pre.e.floor = post.e.floor and
	post.e.passengers = pre.e.passengers +
		{pass : Person | pass in pre.p and pass.curr_floor = pre.e.floor and pass.curr_floor != pass.destination}
	and pre.p = post.p
}

pred unload[pre: State, post:State] {
	pre.e.floor = post.e.floor and
	post.e.passengers = pre.e.passengers - {pass: Person | pre.e.floor = pass.destination} and
	pre.p = post.p
}

//all people and elevators have to be in a State
fact all_in_state {
	all person :Person |
		person in State.p	
	all elev : Elevator | 
		elev in State.e
}

//in the beginning, the passenger isn't on their desired floor or on any elevator
fact init{
	st/first.p.curr_floor != st/first.p.destination and
	no st/first.e.passengers
}

//transition - checks if the elevator has moved up or down one floor
fact transition {
	all s : State - st/last |
		let s' = s.next |
			valid_move[s, s'] or
			load[s, s'] or
			unload[s,s']
}

//end_state - ensures that all people are at their destination floor in the last state
fact end_state {
	let people = st/last.p | 
		people <: curr_floor = people <: destination and
		no st/last.e.passengers
}


run{} for exactly 6 Floor,  4 State, 4 Elevator, 4 Person
