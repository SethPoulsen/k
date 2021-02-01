require "unification.k"

module LOGIK-COMMON
  imports DOMAINS-SYNTAX

  syntax PredicateName
  syntax Predicate ::= PredicateName | PredicateName "(" Predicates ")"
  syntax Predicates ::= List{Predicate,","}
  syntax Clause ::= Predicate ":-" Predicates "." | Predicate "."
  syntax Query ::= "?-" Predicates "."
  syntax Pgm ::= Query | Clause Pgm
endmodule

module LOGIK-SYNTAX
  imports LOGIK-COMMON
  imports BUILTIN-ID-TOKENS
  syntax #KVariable ::= r"[A-Z_][A-Za-z0-9_]*"   [token, prec(2)]
                      | #UpperId                 [token]
  syntax Predicate ::= #KVariable [klabel(#SemanticCastToPredicate)]
  syntax PredicateName ::= r"[a-z][a-zA-Z0-9_]*"                 [token]
                   | #LowerId                              [token]
endmodule

module LOGIK
  imports LOGIK-COMMON
  imports DOMAINS
  imports UNIFICATION

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <fresh color="orange"> .K </fresh>
                  <clauses color="red">
                    <clause color="pink" multiplicity="*"> .K </clause>
                  </clauses>
                  <mgu> .K </mgu>
                </T>
                <solution multiplicity="?"> .K </solution>


  rule <k> C:Clause Pgm => Pgm </k>
       (.Bag => <clause> #renameVariables(C) </clause>)

  rule <k> ?- Ls:Predicates. => Ls ...</k>
       <mgu> _ => #variablesMap(#variables(Ls)) </mgu>

  rule L:Predicate, Ls:Predicates => L ~> Ls
  rule .Predicates => .

rule <T>... <k> . </k> <mgu> Theta </mgu> ...</T>
  => <solution> Theta </solution>

  rule <fresh> . => #renameVariables(C) </fresh> <clause> C </clause>
       <k> T:Predicate ...</k>
  requires #unifiable(T,head(C))
    [transition]

  syntax Predicate ::= head(Clause) [function]
  rule head(L.) => L
  rule head(L:-_.) => L


  rule <k> L:Predicate => . ...</k>
       <fresh>  L:Predicate . => . </fresh>

  rule <k> L:Predicate => Ls ...</k>
       <fresh>  L:Predicate :- Ls:Predicates. => . </fresh>

endmodule
