// Copyright (c) 2014-2019 K Team. All Rights Reserved.

/*!
\title{SIMPLE --- Untyped}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This is the \K semantic definition of the untyped SIMPLE language.
SIMPLE is intended to be a pedagogical and research language that captures
the essence of the imperative programming paradigm, extended with several
features often encountered in imperative programming languages.
A program consists of a set of global variable declarations and
function definitions.  Like in C, function definitions cannot be
nested and each program must have one function called \texttt{main},
which is invoked when the program is executed.  To make it more
interesting and to highlight some of \K's strengths, SIMPLE includes
the following features in addition to the conventional imperative
expression and statement constructs:
\begin{itemize}
\item Multidimensional arrays and array references.  An array evaluates
to an array reference, which is a special value holding a location (where
the elements of the array start) together with the size of the array;
the elements of the array can be array references themselves (particularly
when the array is multi-dimensional).  Array references are ordinary values,
so they can be assigned to variables and passed/received by functions.
\item Functions and function values.  Functions can have zero or
more parameters and can return abruptly using a \texttt{return} statement.
SIMPLE follows a call-by-value parameter passing style, with static scoping.
Function names evaluate to function abstractions, which hereby become ordinary
values in the language, same like the array references.
\item Blocks with locals.  SIMPLE variables can be declared
anywhere, their scope being from the place where they are declared
until the end of the most nested enclosing block.
\item Input/Output.  The expression \texttt{read()} evaluates to the
next value in the input buffer, and the statement \texttt{write(e)}
evaluates \texttt{e} and outputs its value to the output buffer.  The
input and output buffers are lists of values.
\item Exceptions.  SIMPLE has parametric exceptions (the value thrown as
an exception can be caught and bound).
\item Concurrency via dynamic thread creation/termination and
synchronization.  One can spawn a thread to execute any statement.
The spawned thread shares with its parent its environment at creation time.
Threads can be synchronized via a join command which blocks the current thread
until the joined thread completes, via re-entrant locks which can be acquired
and released, as well as through rendezvous commands.
\end{itemize}
Like in many other languages, some of SIMPLE's constructs can be
desugared into a smaller set of basic constructs.  We do that at the end
of the syntax module, and then we only give semantics to the core constructs.
*/

module SIMPLE-UNTYPED-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Id ::= "main" [token]

  syntax Decl ::= "var" Exps ";"
                | "function" Id "(" Ids ")" Block

  syntax Exp ::= Int | Bool | String | Id
               | "(" Exp ")"             [bracket]
               | "++" Exp
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict]
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
               | "read" "(" ")"
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

  syntax Ids  ::= List{Id,","}
  syntax Exps ::= List{Exp,","}          [strict]  // automatically hybrid now
  syntax Exps ::= Ids
  syntax Val
  syntax Vals ::= List{Val,","}
  syntax Bottom
  syntax Bottoms ::= List{Bottom,","}
  syntax Ids ::= Bottoms

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "for" "(" Stmts Exp ";" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "break" ";"
                | "continue" ";"
                | "print" "(" Exps ")" ";"              [strict]
// NOTE: print strict allows non-deterministic evaluation of its arguments
// Either keep like this but document, or otherwise make Exps seqstrict.
// Of define and use a different expression list here, which is seqstrict.
                | "try" Block "catch" "(" Id ")" Block
                | "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]

/*@ \section{Desugared Syntax} */

  rule if (E) S => if (E) S else {}                                 [macro]
  rule while (E) S => for (1; E; 1) S                               [macro]
  // rule while (E) S => if (E) {S while(E)S}  [structural]
  // rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  // rule for(Start Cond; Step) {} => {Start while (Cond) {Step;}}     [macro]
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1; var E2, Es;          [macro-rec]
  rule var X:Id = E; => var X; X = E;                               [macro]


endmodule


module SIMPLE-UNTYPED
  imports SIMPLE-UNTYPED-SYNTAX
  imports DOMAINS

  syntax Val ::= Int | Bool | String
               | array(Int,Int)
               | lambda(Ids,Stmt)
  syntax Exp ::= Val
  syntax Exps ::= Vals
  syntax Vals ::= Bottoms
  syntax KResult ::= Val
                   | Vals  // TODO: should not need this

  syntax ControlCell
  syntax ControlCellFragment

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> $PGM:Stmts ~> execute </k>
                    //<br/> // TODO(KORE): support latex annotations #1799
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <lstack color="violet"> .List </lstack>
                      </control>
                    //<br/> // TODO(KORE): support latex annotations #1799
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                //<br/> // TODO(KORE): support latex annotations #1799
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan"> .Set </busy>
                  <terminated color="red"> .Set </terminated>
                //<br/> // TODO(KORE): support latex annotations #1799
                  <input color="magenta" stream="stdin"> .List </input>
                  <output color="brown" stream="stdout"> .List </output>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

/*@ \section{Declarations and Initialization}
We start by defining the semantics of declarations (for variables,
arrays and functions). */

/*@ \subsection{Variable Declaration}*/

  syntax KItem ::= "undefined"  [latex(\bot)]

  rule <k> var X:Id; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> undefined ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

/*@ \subsection{Array Declaration} */

  context var _:Id[HOLE];

  rule <k> var X:Id[N:Int]; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> array(L +Int 1, N)
                          (L +Int 1) ... (L +Int N) |-> undefined ...</store>
       <nextLoc> L => L +Int 1 +Int N </nextLoc>
    requires N >=Int 0

  syntax Id ::= "$1" | "$2"
  rule var X:Id[N1:Int, N2:Int, Vs:Vals];
    => var X[N1];
       {
         for(var $1 = 0; $1 <= N1 - 1; ++$1) {
           var $2[N2, Vs];
           X[$1] = $2;
         }
       }
    [structural]

/*@ \subsection{Function declaration} */

  rule <k> function F(Xs) S => . ...</k>
       <env> Env => Env[F <- L] </env>
       <store>... .Map => L |-> lambda(Xs, S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

  syntax KItem ::= "execute"
  rule <k> execute => main(.Exps); </k>
       <env> Env </env>
       <genv> .Map => Env </genv>  [structural]

/*@ \section{Expressions} */

/*@ \subsection{Variable lookup} */

  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

/*@ \subsection{Variable/Array increment} */

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store>  [increment]

/*@ \subsection{Arithmetic operators} */

  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 requires I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 requires I2 =/=K 0
  rule - I => 0 -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2

/*@ The equality and inequality constructs reduce to syntactic comparison
of the two argument values (which is what the equality on $K$ terms does). */

  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2

/*@ The logical negation is clear, but the logical conjunction and disjunction
are short-circuited: */

  rule ! T => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E

/*@ \subsection{Array lookup} */

// The [anywhere] feature is underused, because it would only be used
// at the top of the computation or inside the lvalue wrapper. So it
// may not be worth, or we may need to come up with a special notation
// allowing us to enumerate contexts for [anywhere] rules.
  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
    [structural, anywhere]

  rule array(L,_)[N:Int] => lookup(L +Int N)
    [structural, anywhere]

/*@ \subsection{Size of an array} */

  rule sizeOf(array(_,N)) => N

/*@ \subsection{Function call} */

  syntax KItem ::=  (Map,K,ControlCellFragment)

  rule <k> lambda(Xs,S)(Vs:Vals) ~> K => mkDecls(Xs,Vs) S return; </k>
       <control>
         <fstack> .List => ListItem((Env,K,C)) ...</fstack>
         C
       </control>
       <env> Env => GEnv </env>
       <genv> GEnv </genv>

  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <control>
         <fstack> ListItem((Env,K,C)) => .List ...</fstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

  syntax Val ::= "nothing"
  rule return; => return nothing;   [macro]

/*@ \subsection{Read} */

  rule <k> read() => I ...</k> <input> ListItem(I:Int) => .List ...</input>  [read]

/*@ \subsection{Assignment}
In SIMPLE, like in C, assignments are expression constructs and not statement
constructs.  To make it a statement all one needs to do is to follow it by a
semi-colon ``\texttt{;}'' (see the semantics for expression statements below).
Like for the increment, we want to allow assignments not only to variables but
also to array elements, e.g., \texttt{e1[e2] = e3} where \texttt{e1} evaluates
to an array reference, \texttt{e2} to a natural number, and \texttt{e3} to any
value.  Thus, we first compute the lvalue of the left-hand-side expression
that appears in an assignment, and then we do the actual assignment to the
resulting location: */

  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (_ => V) ...</store>
    [assignment]

/*@ \section{Statements} */

/*@ \subsection{Blocks}
Empty blocks are simply discarded, as shown in the first rule below.
For non-empty blocks, we schedule the enclosed statement but we have to
make sure the environment is recovered after the enclosed statement executes.
Recall that we allow local variable declarations, whose scope is the block
enclosing them.  That is the reason for which we have to recover the
environment after the block.  This allows us to have a very simple semantics
for variable declarations, as we did above.  One can make the two rules below
computational if one wants them to count as computational steps. */

  rule {} => .  [structural]
  rule <k> { S } => S ~> setEnv(Env) ...</k>  <env> Env </env>  [structural]

/*@ The basic definition of environment recovery is straightforward and
given in the section on auxiliary constructs at the end of the file. */

/*@ There are two common alternatives to the above semantics of blocks.
One is to keep track of the variables which are declared in the block and only
recover those at the end of the block.  This way one does more work for
variable declarations but conceptually less work for environment recovery; we
say ``conceptually'' because it is not clear that it is indeed the case that
one does less work when AC matching is involved.  The other alternative is to
work with a stack of environments instead of a flat environment, and push the
current environment when entering a block and pop it when exiting it.  This
way, one does more work when accessing variables (since one has to search the
variable in the environment stack in a top-down manner), but on the other hand
uses smaller environments and the definition gets closer to an implementation.
Based on experience with dozens of language semantics and other \K definitions,
we have found that our approach above is the best trade-off between elegance
and efficiency (especially since rewrite engines have built-in techniques to
lazily copy terms, by need, thus not creating unnecessary copies),
so it is the one that we follow in general. */

/*@ \subsection{Sequential composition}
Sequential composition is desugared into \K's builtin sequentialization
operation (recall that, like in C, the semi-colon ``\texttt{;}'' is not a
statement separator in SIMPLE---it is either a statement terminator or a
construct for a statement from an expression).  The rule below is
structural, so it does not count as a computational step.  One can make it
computational if one wants it to count as a step.  Note that \K allows
to define the semantics of SIMPLE in such a way that statements eventually
dissolve from the top of the computation when they are completed; this is in
sharp contrast to (artificially) ``evaluating'' them to a special
\texttt{skip} statement value and then getting rid of that special value, as
it is the case in other semantic approaches (where everything must evaluate
to something).  This means that once $S_1$ completes in the rule below, $S_2$
becomes automatically the next computation item without any additional
(explicit or implicit) rules. */

  rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]

/*@ A subtle aspect of the rule above is that $S_1$ is declared to have sort
$\it Stmts$ and not $\it Stmt$.  That is because desugaring macros can indeed
produce left associative sequential composition of statements.  For example,
the code $\texttt{var\,x=0;\,x=1;}$ is desugared to
$\texttt{(var\,x;\,x=0;)\,x=1;}$, so although originally the first term of
the sequential composition had sort $\it Stmt$, after desugaring it became
of sort $\it Stmts$.  Note that the attribute \texttt{[right]} associated
to the sequential compositon production is an attribute of the syntax, and not
of the semantics: e.g., it tells the parser to parse
$\texttt{var\,x;\,x=0;\,x=1;}$ as $\texttt{var\,x;\,(x=0;\,x=1;)}$, but it
does not tell the rewrite engine to rewrite $\texttt{(var\,x;\,x=0;)\,x=1;}$ to
$\texttt{var\,x;\,(x=0;\,x=1;)}$. */

/*@ \subsection{Expression statements}
Expression statements are only used for their side effects, so their result
value is simply discarded.  Common examples of expression statements are ones
of the form \texttt{++x;}, \texttt{x=e;}, \texttt{e1[e2]=e3;}, etc. */

  rule _:Val; => .

/*@ \subsection{Conditional}
Since the conditional was declared with the \texttt{strict(1)} attribute, we
can assume that its first argument will eventually be evaluated.  The rules
below cover the only two possibilities in which the conditional is allowed to
proceed (otherwise the rewriting process gets stuck). */

  rule if ( true) S else _ => S
  rule if (false) _ else S => S

/*@ \subsection{While loop}
The simplest way to give the semantics of the while loop is by unrolling.
Note, however, that its unrolling is only allowed when the while loop reaches
the top of the computation (to avoid non-termination of unrolling).  We prefer
the rule below to be structural, because we don't want the unrolling of the
while loop to count as a computational step; this is unavoidable in
conventional semantics, but it is possible in \K thanks to its distinction
between structural and computational rules.  The simple while loop semantics
below works because our while loops in SIMPLE are indeed very basic.  If we
allowed break/continue of loops then we would need a completely different
semantics, which would also involve the \textsf{control} cell. */

  // rule while (E) S => if (E) {S while(E)S}  [structural]

  rule for(Start Cond; Step) S => {Start if (Cond) {S Step; for (1; Cond; Step) S } }  [structural]

  // rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  // rule for(Start Cond; Step) {} => {Start if (Cond) {Step for ( Cond; Step) {} }}  [structural]
  // rule for(Start Cond; Step) {} => {Start while (Cond) {Step;}}     [macro]

/*@ \subsection{Print}
The \texttt{print} statement was strict, so all its arguments are now
evaluated (recall that \texttt{print} is variadic).  We append each of
its evaluated arguments to the output buffer, and discard the residual
\texttt{print} statement with an empty list of arguments. */

  rule <k> print(V:Val, Es => Es); ...</k> <output>... .List => ListItem(V) </output>
    [print]
  rule print(.Vals); => .  [structural]

/*@ \subsection{Exceptions} */

  syntax KItem ::= (Id,Stmts,K,Map,ControlCellFragment)

  syntax KItem ::= "popx"

  rule <k> (try S1 catch(X) {S2} => S1 ~> popx) ~> K </k>
       <control>
         <xstack> .List => ListItem((X, S2, K, Env, C)) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> ListItem(_) => .List ...</xstack>

  rule <k> throw V:Val; ~> _ => { var X = V; S2 } ~> K </k>
       <control>
         <xstack> ListItem((X, S2, K, Env, C)) => .List ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

/*@ \subsection{Threads}
SIMPLE's threads can be created and terminated dynamically, and can
synchronize by acquiring and releasing re-entrant locks and by rendezvous.
We discuss the seven rules giving the semantics of these operations below. */

/*@ \subsubsection{Thread creation}
Threads can be created by any other threads using the ``\texttt{spawn $S$}''
construct.  The spawn expression construct evaluates to the unique identifier
of the newly created thread and, at the same time, a new thread cell is added
into the configuration, initialized with the $S$ statement and sharing the
same environment with the parent thread.  Note that the newly created
\textsf{thread} cell is torn.  That means that the remaining cells are added
and initialized automatically as described in the definition of SIMPLE's
configuration.  This is part of \K's configuration abstraction mechanism. */

  rule <thread>...
         <k> spawn S => !T:Int ...</k>
         <env> Env </env>
       ...</thread>
       (.Bag => <thread>...
               <k> S </k>
               <env> Env </env>
               <id> !T </id>
             ...</thread>)

/*@ \subsubsection{Thread termination}
Dually to the above, when a thread terminates its assigned computation (the
contents of its \textsf{k} cell) is empty, so the thread can be dissolved.
However, since no discipline is imposed on how locks are acquired and released,
it can be the case that a terminating thread still holds locks.  Those locks
must be released, so other threads attempting to acquire them do not deadlock.
We achieve that by removing all the locks held by the terminating thread in its
\textsf{holds} cell from the set of busy locks in the \textsf{busy} cell
(\texttt{keys($H$)} returns the domain of the map $H$ as a set, that is, only
the locks themselves ignoring their multiplicity).  As seen below, a lock is
added to the \textsf{busy} cell as soon as it is acquired for the first time
by a thread.  The unique identifier of the terminated thread is also collected
into the \textsf{terminated} cell, so the \texttt{join} construct knows which
threads have terminated. */

  rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .Bag)
       <busy> Busy => Busy -Set keys(H) </busy>
       <terminated>... .Set => SetItem(T) ...</terminated>

/*@ \subsubsection{Thread joining}
Thread joining is now straightforward: all we need to do is to check whether
the identifier of the thread to be joined is in the \textsf{terminated} cell.
If yes, then the \texttt{join} statement dissolves and the joining thread
continues normally; if not, then the joining thread gets stuck. */

  rule <k> join T:Int; => . ...</k>
       <terminated>... SetItem(T) ...</terminated>

/*@ \subsubsection{Acquire lock}
There are two cases to distinguish when a thread attempts to acquire a lock
(in SIMPLE any value can be used as a lock):\\
(1) The thread does not currently have the lock, in which case it has to
take it provided that the lock is not already taken by another thread (see
the side condition of the first rule).\\
(2) The thread already has the lock, in which case it just increments its
counter for the lock (the locks are re-entrant).  These two cases are captured
by the two rules below: */

  rule <k> acquire V:Val; => . ...</k>
       <holds>... .Map => V |-> 0 ...</holds>
       <busy> Busy (.Set => SetItem(V)) </busy>
    requires (notBool(V in Busy))  [acquire]

  rule <k> acquire V; => . ...</k>
       <holds>... V:Val |-> (N => N +Int 1) ...</holds>

/*@ \subsubsection{Release lock}
Similarly, there are two corresponding cases to distinguish when a thread
releases a lock:\\
(1) The thread holds the lock more than once, in which case all it needs to do
is to decrement the lock counter.\\
(2) The thread holds the lock only once, in which case it needs to remove it
from its \textsf{holds} cell and also from the the shared \textsf{busy} cell,
so other threads can acquire it if they need to. */

  rule <k> release V:Val; => . ...</k>
       <holds>... V |-> (N => N -Int 1) ...</holds>
    requires N >Int 0

  rule <k> release V; => . ...</k> <holds>... V:Val |-> 0 => .Map ...</holds>
       <busy>... SetItem(V) => .Set ...</busy>

/*@ \subsubsection{Rendezvous synchronization}
In addition to synchronization through acquire and release of locks, SIMPLE
also provides a construct for rendezvous synchronization.  A thread whose next
statement to execute is \texttt{rendezvous($V$)} gets stuck until another
thread reaches an identical statement; when that happens, the two threads
drop their rendezvous statements and continue their executions.  If three
threads happen to have an identical rendezvous statement as their next
statement, then precisely two of them will synchronize and the other will
remain blocked until another thread reaches a similar rendezvous statement.
The rule below is as simple as it can be.  Note, however, that, again, it is
\K's mechanism for configuration abstraction that makes it work as desired:
since the only cell which can multiply containing a \textsf{k} cell inside is
the \textsf{thread} cell, the only way to concretize the rule below to the
actual configuration of SIMPLE is to include each \textsf{k} cell in a
\textsf{thread} cell. */

  rule <k> rendezvous V:Val; => . ...</k>
       <k> rendezvous V; => . ...</k>  [rendezvous]

/*@ \section{Auxiliary declarations and operations}
In this section we define all the auxiliary constructs used in the
above semantics. */

/*@ \subsection{Making declarations}
The \texttt{mkDecls} auxiliary construct turns a list of identifiers
and a list of values in a sequence of corresponding variable
declarations. */

  syntax Stmts ::= mkDecls(Ids,Vals)  [function]
  rule mkDecls((X:Id, Xs:Ids), (V:Val, Vs:Vals)) => var X=V; mkDecls(Xs,Vs)
  rule mkDecls(.Ids,.Vals) => {}

/*@ \subsection{Location lookup}
The operation below is straightforward.  Note that we tag it with the same
\texttt{lookup} tag as the variable lookup rule defined above.  This way,
both rules will be considered transitions when we include the \texttt{lookup}
tag in the transition option of \texttt{kompile}. */

  syntax Exp ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

/*@ \subsubsection{Environment recovery}
We have already discussed the environment recovery auxiliary operation in the
IMP++ tutorial: */

// TODO: eliminate the env wrapper, like we did in IMP++

  syntax KItem ::= setEnv(Map)
  rule <k> setEnv(Env) => . ...</k> <env> _ => Env </env>  [structural]

/*@  While theoretically sufficient, the basic definition for environment
recovery alone is suboptimal.  Consider a loop \texttt{while (E)S},
whose semantics (see above) was given by unrolling.  \texttt{S}
is a block.  Then the semantics of blocks above, together with the
unrolling semantics of the while loop, will yield a computation
structure in the \textsf{k} cell that increasingly grows, adding a new
environment recovery task right in front of the already existing sequence of
similar environment recovery tasks (this phenomenon is similar to the ``tail
recursion'' problem).  Of course, when we have a sequence of environment
recovery tasks, we only need to keep the last one.  The elegant rule below
does precisely that, thus avoiding the unnecessary computation explosion
problem: */

  rule (setEnv(_) => .) ~> setEnv(_)  [structural]

/* In fact, the above follows a common convention in \K for recovery
operations of cell contents: the meaning of a computation task of the form
\texttt{cell($C$)} that reaches the top of the computation is that the current
contents of cell \textsf{cell} is discarded and gets replaced with $C$.  We
did not add support for these special computation tasks in our current
implementation of \K, so we need to define them as above. */

/*@ \subsection{lvalue and loc}
For convenience in giving the semantics of constructs like the increment and
the assignment, that we want to operate the same way on variables and on
array elements, we used an auxiliary \texttt{lvalue($E$)} construct which was
expected to evaluate to the lvalue of the expression $E$.  This is only
defined when $E$ has an lvalue, that is, when $E$ is either a variable or
evaluates to an array element.  \texttt{lvalue($E$)} evaluates to a value of
the form \texttt{loc($L$)}, where $L$ is the location where the value of $E$
can be found; for clarity, we use \texttt{loc} to structurally distinguish
natural numbers from location values.  In giving semantics to \texttt{lvalue}
there are two cases to consider.  (1) If $E$ is a variable, then all we need
to do is to grab its location from the environment.  (2) If $E$ is an array
element, then we first evaluate the array and its index in order to identify
the exact location of the element of concern, and then return that location;
the last rule below works because its preceding context declarations ensure
that the array and its index are evaluated, and then the rule for array lookup
(defined above) rewrites the evaluated array access construct to its
corresponding store lookup operation. */

// For parsing reasons, we prefer to allow lvalue to take a K

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)

// Local variable

  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

// Array element: evaluate the array and its index;
// then the array lookup rule above applies.

  context lvalue(_::Exp[HOLE::Exps])
  context lvalue(HOLE::Exp[_::Exps])

// Finally, return the address of the desired object member

  rule lvalue(lookup(L:Int) => loc(L))  [structural]

/*@ \subsection{Initializing multiple locations}
The following operation initializes a sequence of locations with the same
value: */

  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  requires N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  requires N <=Int M

/*@ The semantics of SIMPLE is now complete.  Make sure you kompile the
definition with the right options in order to generate the desired model.
No kompile options are needed if you only only want to execute the definition
(and thus get an interpreter), but if you want to search for a different
program behaviors then you need to kompile with the transition option
including rule tags such as lookup, increment, acquire, etc.  See the
IMP++ tutorial for what the transition option means how to use it. */
endmodule
