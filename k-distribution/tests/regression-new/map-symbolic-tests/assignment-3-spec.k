// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-3-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (MAP:Map X:MyId |-> 1) [ Y:MyId <- 2 ] [ Z:MyId <- 3 ] ) => assignmentResult ( ( MAP [ Y <- 2 ]  X |-> 1 ) [ Z <- 3 ] )   </k> requires Y =/=K X

endmodule
