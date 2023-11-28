sig Road {
    direct: one Direction
}

abstract sig Color {}
abstract sig Direction {}

one sig Red, Yellow, Green extends Color {}
one sig NS, EW extends Direction {}


abstract sig Light {
    isAbove: one Road
}

// Adding left turn light
abstract sig LeftTurnColor {}
one sig YellowLeft, GreenLeft extends LeftTurnColor {}

sig TrafficLight extends Light{
    isColor: one Color
}

sig LeftTurnLight extends Light{
    leftState: one LeftTurnColor + Red
}


// Adding pedestrian light
abstract sig PedestrianWalkState {}
one sig Walk, DontWalk extends PedestrianWalkState {}

sig PedestrianLight extends Light{
    walkState: one PedestrianWalkState
}


//lights on different streets can't be green or yellow or green and yellow at the same time
fact {
    all disj r1, r2: Road | 
        (r1.direct != r2.direct) => 
            (all l1: r1.~isAbove, l2: r2.~isAbove | 
                (l1 in TrafficLight && l2 in TrafficLight) => 
                    !(l1.isColor in Green + Yellow && l2.isColor in Green + Yellow))
}

//all traffic lights on the same road should be the same color
fact {
    all r: Road, c: Color | 
        (some l: r.~isAbove | l in TrafficLight && l.isColor = c) => 
            (all l: r.~isAbove | l in TrafficLight => l.isColor = c)
}

//There should be 2 roads
fact {
    #Road = 2
}

//streets can't go the same direction
fact {
    no disj r1, r2: Road | r1.direct = r2.direct
}

// If traffic light is green or yellow, pedestrian light should be 'DontWalk'
fact {
    all r: Road, t: TrafficLight, p: PedestrianLight | 
        (t.isAbove = r && p.isAbove = r && t.isColor in Green + Yellow) => p.walkState = DontWalk
}

//there should only be one left turn light above each road
fact {
    all r: Road | #(r.~isAbove & LeftTurnLight) = 1
}


//a leftturnlight can only be greenleft if all the normal lights on both roads are red
fact {
    all l: LeftTurnLight | 
        (l.leftState = GreenLeft) => 
            (all r: Road, t: (r.~isAbove & TrafficLight) | t.isColor = Red)
}


//each road need at least one traffic light above it
fact {
    all r: Road | #(r.~isAbove & TrafficLight) >= 1
}

//each road should have only one ped light
fact {
    all r: Road | #(r.~isAbove & PedestrianLight) >= 1
}

//each road should have only one leftturn light
fact {
    all r: Road | #(r.~isAbove & LeftTurnLight) >= 1
}

//there shouldn't be a walk light on any road if there is a greenleft or yellowleft on any road
fact {
    all l: LeftTurnLight | 
        (l.leftState in GreenLeft + YellowLeft) => 
            (all r: Road, p: (r.~isAbove & PedestrianLight) | p.walkState = DontWalk)
}

pred show {

}
pred showGreenLeftLight {
    some l: PedestrianLight | l.walkState = Walk
}

pred showTwoGreenLeftLights {
    some disj l1, l2: LeftTurnLight | l1.leftState = Red and l2.leftState = Red

}


run showTwoGreenLeftLights for exactly 2 Road, exactly 2 TrafficLight, exactly 2 LeftTurnLight, exactly 2 PedestrianLight

run showGreenLeftLight for exactly 2 Road, exactly 2 TrafficLight, exactly 2 LeftTurnLight, exactly 2 PedestrianLight

run show for exactly 2 Road, 6 Light