sig road{
    direct: one direction
}

abstract sig color{}
abstract sig direction{}

one sig Red, Yellow, Green extends color{}
one sig NS, EW extends direction{}

sig light{
    isAbove: one road,
    isColor: one color

}

// Roads can't go the same direction
fact {
    all r1, r2: road | r1 != r2 implies r1.direct != r2.direct
}

// Lights can't both be green or yellow or green and yellow
fact {
    no l1, l2: light | l1 != l2 and ((l1.isColor = Green and l2.isColor = Green) or (l1.isColor = Yellow and l2.isColor = Yellow) or (l1.isColor = Green and l2.isColor = Yellow) or (l1.isColor = Yellow and l2.isColor = Green))
}

// Lights on same road can't be different colors
fact {
    all r: road | one c: color | all l: light | l.isAbove = r implies l.isColor = c
}



pred show{}

run show for exactly 2 road, exactly 4 light