open util/ordering [Floor] as f
open util/ordering [State] as st

sig Elevator{
	curr_floor: one Floor
}

sig Floor{}

sig State{
	e: one Elevator
}

pred valid_move[pre: Elevator, post: Elevator] {
	post.curr_floor = pre.curr_floor.next or
	post.curr_floor = pre.curr_floor.prev
}

fact transition {
	all s : State - st/last |
		let s' = s.next |
			valid_move[s.e, s'.e]
}


run{} for exactly 6 Floor, exactly 2 State, 2 Elevator
