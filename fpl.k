/*execute 
\title{FPL}

Trying out <thunk> execute

\author{Lars Hansen}
*/

module FPL-SYNTAX
  syntax PgmExp ::= VExp
                  | Let
                  | "halt"
                  | PgmExp ";" PgmExp [left]

  syntax VExp ::= Exp | Val
  syntax Exp ::= Id
               | VExp "(" VExps ")"
               | "if" VExp "then" Block "else" Block
               > AOp VExp VExp
               | "(" VExp ")" [bracket]

  syntax Let ::= "let" Id "=" "(" VExp ")"

  syntax Lambda ::= "\\" Ids "->" Block

  syntax Block ::= "{" PgmExp "}"

  syntax Ids ::= List{Id,","}
  syntax VExps ::= List{VExp,","}

  syntax AOp ::= "*" | "/" > "+" | "-" | "<"

  syntax Val ::= Int | Bool | Lambda
endmodule

module FPL-CONFIG
  imports FPL-SYNTAX

  syntax KResult ::= Val

  syntax K ::= "execute" | "ans"

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
       \ Xs -> { let X = (E) ; B } (Es)
  // lambda application
  syntax K ::= (Map,K)
  rule <k> \ .Ids -> {B} ( .VExps ) ~> K => B ~> execute </k>
       <genv> GEnv </genv>
       <env> Env => GEnv </env>
       <fstack> .=>ListItem((Env,K)) ... </fstack>
       <reading> false => true </reading>

  // lambda - end of execution
  rule <k> .K => V ~> K </k>
       <env> _=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>
       <ans> V </ans>

  // arithmetic derivation rules
  rule <k> O:AOp X:Exp Y:VExp => X ~> O ans Y ... </k>
       <reading> false </reading>
  rule <k> O:AOp X:VExp Y:Exp => Y ~> O X ans ... </k>
       <reading> false </reading>
  // arithmetic read ans
  rule <k> O X ans => O X V ... </k>
       <ans> V </ans>
  rule <k> O ans X => O V X ... </k>
       <ans> V </ans>

  // conditional derivation rules
  rule <k> if X:Exp then T else F => X ~> if ans then T else F ... </k>
       <reading> false </reading>
  // conditional read ans
  rule <k> if ans then T else F => if V then T else F ... </k>
       <ans> V </ans>

  // lambda derivation rules
  rule <k> X:Exp ( Args:VExps ) => X ~> ans (Args) ... </k>
       <reading> false </reading>
  // lambda read ans
  rule <k> ans ( Args ) => V (Args) ... </k>
       <ans> V </ans>

  // write ans
  rule <k> (V:Val ~> E) => E ... </k>
       <ans> _ => V </ans>

  // skip over all expressions while reading program
  rule <k> X:Exp ~> Y => Y ... </k>
       <ans> _=>X </ans>
       <reading> true </reading>

  // variable definition
  rule <k> let N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> E) </store>
    when fresh(L)

  // thunk variable lookup
  syntax K ::= Id "<-" VExp
  rule <k> N:Id => E ~> N <- ans ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> E:Exp ... </store>
       <reading> false </reading>

  // thunk variable override
  rule <k> N:Id <- ans => V ... </k>
       <ans> V </ans>
       <env> ... N |-> L ... </env>
       <store> ... L |-> (_=>V) ... </store>

  // base variable lookup
  rule <k> N:Id => V ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> V:Val ... </store>
       <reading> false </reading>

endmodule
