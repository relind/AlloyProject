sig road{}

abstract sig color{}

one sig Red, Yellow, Green extends color{}

sig light{
    isAbove: one road,
    isColor: one color

}

fact {}


pred show{}

run show for exactly 2 road, exactly 2 light