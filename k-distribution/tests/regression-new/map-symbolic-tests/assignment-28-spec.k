// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-28-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (X:MyId |-> 3 y |-> 4) [ x <- 5 ] ) => assignmentResult ( X |-> 3 [ x <- 5 ] y |-> 4 ) </k> requires X =/=K y

endmodule
