require "unification.k"

module LOGIK-COMMON
  imports DOMAINS-SYNTAX

  syntax OperationName
  syntax Term ::= OperationName
                | OperationName "(" Terms ")"                    [strict(2)]
                | Int
                | String
                | "(" Term ")"                                   [bracket]
                > Term "*" Term                                  [strict,left]
                > left:
                  Term "+" Term                                  [strict]
                | Term "-" Term                                  [strict]
                | "[" Terms "]"                                  [strict]
                | "[" Terms "|" Term "]"
  syntax Terms ::= List{Term,","}

  syntax Val ::= OperationName "(" Vals ")"
  syntax Vals ::= List{Val,","}

  syntax PredicateName
  syntax Predicate ::= PredicateName
                     | PredicateName "(" Terms ")"
                     > Term "<=" Term                            [strict]
                     | Term ">"  Term                            [strict]
                     | Term "is" Term                            [strict(2)]
                     | "write" "(" Term ")"                      [strict]
                     | Bool
  syntax Predicates ::= List{Predicate,","}

  syntax Clause ::= Predicate ":-" Predicates "."
                 | Predicate "."
  syntax Query ::= "?-" Predicates "."
  syntax Pgm ::= Query | Clause Pgm

  rule [T1:Term,T2:Term,Ts:Terms|T':Term] => [T1|[T2,Ts|T']]      [macro]
  rule [T:Term,Ts:Terms] => [T,Ts|[.Terms]]                      [macro]


  // syntax OperationName ::= "cons"
  // syntax Term ::= "nil"
  // rule [Ts:Terms | T:Term] => cons(Ts, T)    [macro]
  // rule [T:Terms ] => cons(T, nil)           [macro]
  // rule [ .Terms ] => nil                          [macro]
  // TODO; desugar this to just be Cons?
  
  // syntax KResult
endmodule

module LOGIK-SYNTAX
  imports LOGIK-COMMON
  imports BUILTIN-ID-TOKENS

  syntax #KVariable ::= r"[A-Z_][A-Za-z0-9_]*"   [token, prec(2)]
                      | #UpperId                 [token]
  syntax Term ::= #KVariable [klabel(#SemanticCastToTerm)]
  syntax OperationName ::= r"[a-z][a-zA-Z0-9_]*"                 [token]
                         | #LowerId                              [token]
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
                  <output color="Orchid" stream="stdout"> .List </output> 
                </T>
                <solution multiplicity="?"> .K </solution>

  syntax KResult ::= Int | Bool | String

  // syntax KResult ::= Val 
  // syntax Val ::= Int | Bool | String

  // Binary operations
  rule I1 * I2 => I1 *Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 - I2 => I1 -Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 <= I2 => I1 <=Int I2

  // Booleans 
  rule true => .  


  context HOLE > HOLE

  // Variable assignment/lookup
  context X is HOLE

  syntax KItem ::= Term "=" Term
  rule X is Y => X = Y
  rule T = T => .

  // Output 
  rule <k> write(P) => . ... </k>
       <output>... .List => ListItem(P) </output>  [print]

  // Preprocessing
  rule <k> C:Clause Pgm => Pgm </k>
       (.Bag => <clause> #renameVariables(C) </clause>)

  rule <k> ?- Ls:Predicates. => Ls ...</k>
       <mgu> _ => #variablesMap(#variables(Ls)) </mgu>

  rule L:Predicate, Ls:Predicates => L ~> Ls
  rule .Predicates => .

  rule <T>... <k> . </k> <mgu> Theta </mgu> ...</T>
    => <solution> Theta </solution>

  // Actual rules

  rule <fresh> . => #renameVariables(C) </fresh> <clause> C </clause>
       <k> T:Predicate ...</k> 
       requires #unifiable(T,head(C))  [transition]

  syntax Predicate ::= head(Clause) [function]
  rule head(L.) => L
  rule head(L:-_.) => L

  rule <k> L:Predicate => . ...</k>
       <fresh>  L:Predicate . => . </fresh>

  rule <k> L:Predicate => Ls ...</k>
       <fresh>  L:Predicate :- Ls:Predicates. => . </fresh>


  // rule T1 is T2 => T1 :- T2

endmodule
