//road sig
sig Road {
    direct: one Direction
}

//get lights above roads
fun lightsAbove(r: Road): set Light {
  r.~isAbove & Light
}

//check if lights on the same roads have different colors
fun lightsOnSameRoadDifferentColors[r: Road, t1, t2: TrafficLight]: set Color {
  { c: Color | (t1.isAbove = r && t2.isAbove = r && t1.isColor = c && t2.isColor != c) }
}

//get pedestrian light above a road
fun pedestrianLightAbove(r: Road): set PedestrianLight {
  r.~isAbove & PedestrianLight
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

//check if two left turn lights on the same road have different states
fun leftTurnLightsOnSameRoadDifferentStates[r: Road, l1, l2: LeftTurnLight]: set LeftTurnColor {
  { state: LeftTurnColor | 
    (l1.isAbove = r && l2.isAbove = r && l1.leftState = state && l2.leftState != state)
  }
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
      (all l1: lightsAbove[r1], l2: lightsAbove[r2] | 
        (l1 in TrafficLight && l2 in TrafficLight) => 
          !(l1.isColor in Green + Yellow && l2.isColor in Green + Yellow))
}

// all traffic lights on the same road should be the same color
fact {
  all r: Road, c: Color | 
    (some l: lightsAbove[r] | l in TrafficLight && l.isColor = c) => 
      (all l: lightsAbove[r] | l in TrafficLight => l.isColor = c)
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
  all r: Road, t: lightsAbove[r], p: pedestrianLightAbove[r] | 
    (t in TrafficLight && t.isColor in Green + Yellow) => p.walkState = DontWalk
}

// there should only be one left turn light above each road
fact {
    all r: Road | #(r.~isAbove & LeftTurnLight) = 1
}



// a left turn light can only be greenleft or yellowleft if all other left turn lights are red
fact {
    all l: LeftTurnLight |
        (l.leftState in YellowLeft + GreenLeft) =>
            (all l2: LeftTurnLight - l | l2.leftState = Red)
}



// each road need at least one traffic light above it
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

assert allTrafficLightsSameColor {
  all r: Road, t1, t2: TrafficLight |
    (t1.isAbove = r && t2.isAbove = r && t1 != t2) =>
      t1.isColor = t2.isColor
}

assert twoRoadsExist {
  #Road = 2
}

assert noSameDirectionStreets {
  no disj r1, r2: Road | r1.direct = r2.direct
}

assert pedestrianLightMatchesTrafficLight {
  all r: Road, t: TrafficLight, p: PedestrianLight |
    (t.isAbove = r && p.isAbove = r && t.isColor in Green + Yellow) => p.walkState = DontWalk
}

//random intersection
pred show {

}

//intersection with a protected left that's green
pred showGreenLeftLight {
    some l: LeftTurnLight | l.leftState = GreenLeft
}

//intersection with 2 protected left (shouldn't exist)
pred showTwoGreenLeftLights {
    some disj l1, l2: LeftTurnLight | l1.leftState = GreenLeft and l2.leftState = GreenLeft

}

//show a intersection where 2 lights on the same street are different colors (shouldn't exist)
pred diffColor {
    some r: Road | some disj t1, t2: (r.~isAbove & TrafficLight) | t1.isColor != t2.isColor
}

//intersection with a green light
pred oneGreen {
    some l: TrafficLight | l.isColor = Green
}


//DYNAMIC PREDICATES

// Dynamic Predicate 1: Traffic light changes its color
pred trafficLightChangesColor[t, t1: TrafficLight, c: Color] {
    t.isColor = c and t1 = t
}

// Dynamic Predicate 2: Pedestrian light changes its state
pred pedestrianLightChangesState[p, p1: PedestrianLight, s: PedestrianWalkState] {
    p.walkState = s and p1 = p
}

// Dynamic Predicate 3: Left turn light changes its state
pred leftTurnLightChangesState[l, l1: LeftTurnLight, ls: LeftTurnColor] {
    l.leftState = ls and l1 = l
}

// Dynamic Predicate 4: Road changes its direction
pred roadChangesDirection[r, r1: Road, d: Direction] {
    r.direct = d and r1 = r
}

// Run Dynamic Predicate 1: Traffic light changes its color
//run trafficLightChangesColor for exactly 2 Road, exactly 4 TrafficLight, exactly 2 PedestrianLight, exactly 8 Light

// Run Dynamic Predicate 2: Pedestrian light changes its state
//run pedestrianLightChangesState for exactly 2 Road, exactly 4 TrafficLight, exactly 2 PedestrianLight, exactly 8 Light

// Run Dynamic Predicate 3: Left turn light changes its state
//run leftTurnLightChangesState for exactly 2 Road, exactly 4 TrafficLight, exactly 2 PedestrianLight, exactly 2 LeftTurnLight

// Run Dynamic Predicate 4: Road changes its direction
run roadChangesDirection for exactly 2 Road, exactly 2 Direction, exactly 4 TrafficLight, exactly 2 PedestrianLight, exactly 8 Light

//run diffColor for 4 TrafficLight, 2 Road, 8 Light

//run showTwoGreenLeftLights for exactly 2 Road, exactly 2 TrafficLight, exactly 2 LeftTurnLight, exactly 2 PedestrianLight

//run showGreenLeftLight for exactly 2 Road, exactly 2 TrafficLight, exactly 2 LeftTurnLight, exactly 2 PedestrianLight

//run show for exactly 2 Road, 6 Light

//run oneGreen for exactly 2 Road, 8 Light
