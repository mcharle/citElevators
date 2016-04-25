//basic scenario with two separate elevators

abstract sig Direction {}
sig Up extends Direction {}
sig Down extends Direction {}

abstract sig Floor {}
sig basement extends Floor {}
sig f1 extends Floor {}
sig f2 extends Floor {}
sig f3 extends Floor {}
sig f4 extends Floor {}
sig f5 extends Floor {}

sig Person {
	start: one Floor,
	destination: one Floor
}

abstract sig Elevator {
	direction: one Direction,
	currentFloor: one Floor,
	passengers: set Person
}

sig e1 extends Elevator {}

sig e2 extends Elevator {}
