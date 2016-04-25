//basic scenario with two separate elevators
open util/ordering [Floor]

abstract sig Direction {}
one sig Up extends Direction {}
one sig Down extends Direction {}

abstract sig Floor {}

//sig basement extends Floor {}
//sig f1 extends Floor {}
//sig f2 extends Floor {}
//sig f3 extends Floor {}
//sig f4 extends Floor {}
//sig f5 extends Floor {}

sig Person {
	start: one Floor,
	destination: one Floor,
	current: one Floor
}

abstract sig Elevator {
	direction: one Direction,
	currentFloor: one Floor,
	passengers: set Person,
	calls: set Floor
}

one sig e1 extends Elevator {}
one sig e2 extends Elevator {}

run{} for 6 Floor, 1 Up, 1 Down, 1 Person


