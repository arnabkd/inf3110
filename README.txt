INF3110
Mandatory 2
H2012


Project group:
 * arnabkd Arnab Datta
 * marill  Mari Lindeng Larsen
 * henrste Henrik Steen


The implementation shall work as intended.
Three of the examples from mandatory 1 is included.

The file is run by:
$ sml mandatory2.sml

You can then run the tests by for example:
- t4();

The test will then run, show a prettyprint and show the resulting board.


The testing starts when interpret is called. Interpret first runs a prettyprint on the
var-decls and statements. Then it does the actual interpret and calculations. Finally
when it reaches the stop statement, it stops interpreting (if e.g. any more statements)
and displays the position and the board showing which tiles are drawed.


The board is stored in a multidimentional array with booleans keeping track of which
tiles are drawed.


When the interpretation runs, it runs through all statements recursively, "adding" new
statements (as in while) as neccessary.