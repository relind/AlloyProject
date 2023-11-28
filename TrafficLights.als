//road sig
sig Road {
    direct: one Direction
}

//parent sigs
abstract sig Color {}
abstract sig Direction {}

//sigs for object states
one sig Red, Yellow, Green extends Color {}
one sig NS, EW extends Direction {}

//parent sig for lights
abstract sig Light {
    isAbove: one Road
}

// Adding left turn light
abstract sig LeftTurnColor {}
one sig YellowLeft, GreenLeft extends LeftTurnColor {}

//light to tell cars when to go
sig TrafficLight extends Light{
    isColor: one Color
}

//adding protected lefts
sig LeftTurnLight extends Light{
    leftState: one LeftTurnColor + Red
}


// Adding pedestrian light
abstract sig PedestrianWalkState {}
one sig Walk, DontWalk extends PedestrianWalkState {}

//light to tell people when to walk
sig PedestrianLight extends Light{
    walkState: one PedestrianWalkState
}


//lights on different streets can't be green, yellow or green and yellow at the same time
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



//a leftturnlight can only be yellowleft or greenleft if all other traffic lights and left lights are red
fact {
    all l: LeftTurnLight |
        (l.leftState in YellowLeft + GreenLeft) =>
            (all r: Road, t: (r.~isAbove & TrafficLight) | t.isColor = Red) 
}

//a left turn light can only be greenleft or yellowleft is all other lefttrunlights are red
fact {
    all l: LeftTurnLight |
        (l.leftState in YellowLeft + GreenLeft) =>
            (all l2: LeftTurnLight - l | l2.leftState = Red)
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

//random intersection
pred show {

}

//intersection with a protected left
pred showGreenLeftLight {
    some l: LeftTurnLight | l.leftState = GreenLeft
}

//intersection with 2 protected left **just realized this shouldn't exist**
pred showTwoGreenLeftLights {
    some disj l1, l2: LeftTurnLight | l1.leftState = GreenLeft and l2.leftState = GreenLeft

}

//show a intersection where 2 lights on the same street are different colors (shouldn't exist)
pred diffColor {
    some r: Road | some disj t1, t2: (r.~isAbove & TrafficLight) | t1.isColor != t2.isColor
}

run diffColor for 4 TrafficLight, 2 Road, 8 Light

run showTwoGreenLeftLights for exactly 2 Road, exactly 2 TrafficLight, exactly 2 LeftTurnLight, exactly 2 PedestrianLight

run showGreenLeftLight for exactly 2 Road, exactly 2 TrafficLight, exactly 2 LeftTurnLight, exactly 2 PedestrianLight

run show for exactly 2 Road, 6 Light