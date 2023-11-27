sig road{}

abstract sig color{}

one sig Red, Yellow, Green extends color{}

sig light{
    isAbove: one road,
    isColor: one color

}

//lights can't both be green
fact {}

//lights on same road can't be different colors
fact {}



pred show{}

run show for exactly 2 road, exactly 2 light