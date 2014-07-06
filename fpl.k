/*execute 
\title{FPL}

Trying out <thunk> execute

\author{Lars Hansen}
*/

module FPL-SYNTAX
  syntax PgmExp ::= VExp
                  | Let
                  | PgmExp ";" PgmExp [left]

  syntax VExp ::= Exp | Val
  syntax Exp ::= Id
               /* > VExp "*" VExp [left] */
               /* | VExp "/" VExp [left] */
               /* > VExp "+" VExp [left] */
               > VExp AOp VExp
               | "(" VExp ")" [bracket]

  syntax Let ::= "let" Id "=" "(" VExp ")"
               > "let" Id "=" Id
               > "let" Id "=" Val

  syntax Ids ::= List{Id,","}

  syntax AOp ::= "*" | "/" > "+" | "-"

  syntax Val ::= Int
endmodule

module FPL-CONFIG
  imports FPL-SYNTAX

  syntax KResult ::= Val

  syntax K ::= "execute" | "ans"

  configuration
    <T>
      <k color="green"> $PGM:K ~> execute </k>
      <env color="yellow"> .Map </env>
      <store color="red"> .Map </store>
      <fstack color="blue"> .List </fstack>
      <reading color="orange"> true </reading>
      <ans> false </ans>
    </T>
endmodule

module FPL
  imports FPL-CONFIG
  
  // sequential composition
  rule X:PgmExp ; Y:PgmExp => X ~> Y [structural]

  // end of reading program
  rule <k> execute => A </k>
       <ans> A </ans>
       <reading> true => false </reading>

  // base case integer rules
  rule X:Int + Y:Int => X +Int Y
  rule X:Int * Y:Int => X *Int Y
  rule X:Int / Y:Int => X /Int Y
    when Y =/=Int 0

  // arithmetic rules
  rule <k> X:Exp O:AOp Y => X ~> ans O X ... </k>
       <reading> false </reading>
  rule <k> X O:AOp Y:Exp => Y ~> X O ans ... </k>
       <reading> false </reading>
  
  // read ans
  rule <k> X O ans => X O V ... </k>
       <ans> V </ans>
  rule <k> ans O X => V O X ... </k>
       <ans> V </ans>

  // write ans
  rule <k> (V:Val ~> E) => E ... </k>
       <ans> _ => V </ans>

  // run through all expressions while reading program
  rule <k> X:Exp ~> Y => Y ... </k>
       <ans> _=>X </ans>
       <reading> true </reading>

  // variable definition
  rule <k> let N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> E) </store>
    when fresh(L)

  // variable definition - shorthand for values
  rule <k> let N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> E) </store>
    when fresh(L)

  // variable copy
  rule <k> let N:Id = M:Id => . ... </k>
       <env> ... K |-> L ... .=>(N |-> L) </env>

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
