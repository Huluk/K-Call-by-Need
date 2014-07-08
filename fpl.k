/*execute 
\title{FPL}

Problem: all base operations may be executed, /bc they don't check reading

Trying out <thunk> execute


current thoughts:

if I create call-by-need lists,
then these lists may contain arbitrary VExp.
When one of these elements is evaluated (by calling hd),
then it must be overridden in the original list,
which may be anywhere in any variable.
so, each list must contain a backlink in order to signify,
part of which list it is.
possible solution: make new list object:
list_reference_starting_at_index_i,
which solves this problem.

\author{Lars Hansen}
*/
require "ans_rules.k"

module FPL-SYNTAX
  syntax PgmExp ::= VExp
                  | Let
                  | Funct
                  | "halt"
                  | PgmExp ";" PgmExp [left]

  syntax VExp ::= Exp | Val
  syntax Exp ::= Id
               > "empty" "(" VExp ")"
               | "head" "(" VExp ")"
               | "tail" "(" VExp ")"
               > VExp "(" VExps ")"
               | "if" VExp "then" Block "else" Block
               > AOp VExp VExp
               > "$arg" VExp
               | "(" VExp ")" [bracket]

  syntax Let ::= "let" Id "=" "(" VExp ")"

  syntax Funct ::= "def" Id "(" Ids ")" Block

  syntax Lambda ::= "\\" Ids "->" Block

  syntax Li ::= "[" VExps "]"
              | "[" VExps "|" Lambda "]"

  syntax Block ::= "{" PgmExp "}"

  syntax Predef ::= "empty"
                  | "head"
                  | "tail"

  syntax Ids ::= List{Id,","}
  syntax VExps ::= List{VExp,","}

  syntax AOp ::= "*" | "/" > "+" | "-" | "<"

  syntax Val ::= Int | Bool | Lambda | Li
endmodule

module FPL-CONFIG
  imports FPL-SYNTAX
  imports ANS-RULES

  syntax KResult ::= Val

  syntax K ::= "execute" | "ans"
             | (Map,K)
             | "continue" "(" Map "," K ")"

  configuration
    <T>
      <k color="green"> $PGM:K ~> execute </k>
      <genv color="orange"> .Map </genv>
      <env color="yellow"> .Map </env>
      <store color="red"> .Map </store>
      <fstack color="blue"> .List </fstack>
      <reading color="cyan"> true </reading>
      <ans> false </ans>
    </T>
endmodule

module FPL
  imports FPL-CONFIG

  // halting
  rule <k> halt => HOLE ... </k>
       <fstack> .=>ListItem("halt") ... </fstack>
  
  // sequential composition
  rule X:PgmExp ; Y:PgmExp => X ~> Y [structural]

  // end of reading program
  rule <k> execute => A ... </k>
       <ans> A </ans>
       <reading> true => false </reading>

  // base case integer rules
  rule (+ X:Int Y:Int) => X +Int Y
  rule (- X:Int Y:Int) => X -Int Y
  rule (* X:Int Y:Int) => X *Int Y
  rule (/ X:Int Y:Int) => X /Int Y
    when Y =/=Int 0
  // comparison
  rule < X:Int Y:Int => X <Int Y

  // conditional
  rule if true then {E:PgmExp} else _ => E
  rule if false then _ else {E:PgmExp} => E

  // lambda partial application
  rule \ X:Id,Xs:Ids -> {B} ( E:VExp,Es:VExps ) =>
       \ Xs -> { let X = ($arg E) ; B } (Es)
  // lambda application
  rule <k> \ .Ids -> {B} ( .VExps ) ~> K => B ~> execute </k>
       <env> Env => .Map </env>
       <fstack> .=>ListItem((Env,K)) ... </fstack>
       <reading> false => true </reading>

  // lambda - end of execution
  rule <k> .K => V ~> K </k>
       <env> _=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>
       <ans> V </ans>

  // predef functions
  // TODO test
  rule empty ( [.VExps] ) => true
  rule empty ( [E:VExp,Es:VExps] ) => false
  rule empty ( [_ | R] ) => false
  rule head ( [E:VExp,Es:VExps] ) => E
  rule head ( [E:VExp,Es:VExps | _] ) => E
  rule head ( [.VExps | R] ) => head ( R )
  rule tail ( [E:VExp,Es:VExps] ) => [Es]
  rule tail ( [E:VExp,Es:VExps | R ] ) => [Es | R]

  // write ans
  rule <k> (V:Val ~> E) => E ... </k>
       <ans> _ => V </ans>

  // skip over all expressions while reading program
  rule <k> X:Exp ~> Y => Y ... </k>
       <ans> _=>X </ans>
       <reading> true </reading>
  
  // get value from different scope
  rule <k> $arg E:VExp => E:VExp ~> continue(CurEnv,K) ... </k>
       <env> CurEnv=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>

  // return to scope
  rule <k> continue(Env,K) =>. ... </k>
       <env> CurEnv=>Env </env>
       <fstack> .=>ListItem((CurEnv,K)) ... </fstack>

  // variable definition
  rule <k> let N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> E) </store>
    when fresh(L)

  // function definition
  rule <k> def N:Id ( Args:Ids ) B:Block => . ... </k>
       <genv> ... .=>(N |-> L) </genv>
       <store> ... .=>(L |-> \ Args -> B) </store>
    when fresh(L)

  // thunk variable lookup
  // remove rule to change to call-by-name
  syntax K ::= Id "<-" VExp
  rule <k> N:Id => E ~> N <- ans ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> E:Exp ... </store>
       <reading> false </reading>

  // thunk variable override
  // remove rule to change to call-by-name
  rule <k> N:Id <- ans => V ... </k>
       <ans> V </ans>
       <env> ... N |-> L ... </env>
       <store> ... L |-> (_=>V) ... </store>

  // base variable lookup
  // remove :Val for V to change to call-by-name
  rule <k> N:Id => V ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> V:Val ... </store>
       <reading> false </reading>

  // global variable lookup
  rule <k> N:Id => E ... </k>
       <genv> ... N |-> L ... </genv>
       <store> ... L |-> E ... </store>
       <reading> false </reading>

endmodule
