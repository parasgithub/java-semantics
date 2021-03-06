module STATEMENTS
    imports CORE-SORTS
    imports SUBTYPING
    imports CORE-EXEC     //for sl
    imports VAR-LOOKUP
    imports METHOD-INVOKE // for initParams
    imports STMT-SYNTAX

//@ \subsection{isStmt}
rule isStmt('For(_)) => true
rule isStmt('Switch(_)) => true
rule isStmt('Block(_)) => true

//@ \subsection{Call of main method}

//For now main class may only be placed in the default package.
rule [ExecutionPhase-Start]:
    <k>
      //K-AST for new <MainClass>().main(new String[0]);
      . =>  getClassType(packageId(String2Id("")), String2Id(MainClassS))
              .String2Id("main")

              //workaround: we have to use toExps because 'NewArray is not a native expression but a hacked one
              ( toExps(['NewArray(classString,, ['Dim(0 :: int)],, [.KList])]) );
    </k>
    <env> . </env>
    <mainClass> ListItem(MainClassS:String) </mainClass>
    <globalPhase> UnfoldingPhase => ExecutionPhase  </globalPhase>

//@ \subsection{Blocks} JLS \$14.2

rule [Block]:
    <k> 'Block(S:K) => S ~> env(Env:Map) ...</k>
    <env> Env </env>
        [structural]

rule [BlockStmList]:
    'BlockStmList(A:K,, B:K) => A ~> B

rule [BlockStmListEmpty]:
    .BlockStmList => .K

//@ \texttt{env} Restore the env cell content from env(...) statement argument
syntax KItem ::= env ( Map )

rule [env]:
    <k> env(Env:Map) => . ...</k>
    <env> _ => Env </env>
        [structural]

rule [env-double-Discard]:
    (env(_) => .) ~> env(_)
        [structural]

/*@ \subsection{Local Variable Declaration Statements} JLS \$14.4
    Not only local but fields also*/

rule [LocalVarDec]:
    <k> T:Type X:Id; => . ...</k>
    <env> Env:Map => Env[L/X] </env>
    <store>... . => L |-> default(T) ...</store>
    <storeMetadata>... . => L |-> LocalLocMetadata ...</storeMetadata>
    <nextLoc> L:Int => L +Int 1 </nextLoc>

//rule [matches]:
//    'LocalVarDec(_,, T:Type,, [ 'VarDec(X) ]:KListWrap) => Debug ~> X [anywhere]
//    'LocalVarDec(_,, T:Type,, [ 'VarDec(X:Id) ]:KListWrap) => Debug ~> X [anywhere]
//    'LocalVarDec(_,, T:Type,, [ X:VarDecId ]:KListWrap) => Debug ~> X [anywhere]
//    'LocalVarDec(_,, T:Type,, [ X:VarDec ]:KListWrap) => Debug ~> X [anywhere]
//   T:Type X:Id; => Debug ~> X [anywhere]

//@ \subsection{Empty statement} JLS \$14.6

rule [Empty]:
    ;<:EmptyStmt => .

//@ \subsection{Labeled statements} JLS \$14.7

rule [Labeled]:
    X:Id : S:Stmt => S ~> labeledImpl(X)

//@ Processed version of the labeled statement
syntax KItem ::= labeledImpl ( Id )

rule [labeledImpl-Discard]:
    labeledImpl(_) => .K

//@ \subsection{Expression statements} JLS \$14.8

rule _:TypedVal; => .K

//@ \subsection{If statement}
rule [If-True]:
    if (true::bool) S:Stmt else _:Stmt => S
        [symbolic-rule]

rule [If-False]:
    if (false::bool) _:Stmt else S:Stmt => S
        [symbolic-rule]

rule [If-True]:
    if (true::bool) S:Stmt => S
        [symbolic-rule]

rule [If-False]:
    if (false::bool) _:Stmt => .
        [symbolic-rule]

//@ \subsection{Assert statement}
//short version:    assert exp1;
rule [AssertStm-True-OneArg]:
        assert true::bool; => .

rule [AssertStm-False-OneArg]:
        assert false::bool;
        => throw new class String2Id("java.lang.AssertionError") (null::classString);

//full version:    assert exp1:exp2;
rule [AssertStm-FirstTrue-SecondDiscarded]:
        assert true::bool : _ ; => .

context assert false::bool : HOLE;

rule [AssertStm-FirstFalse]:
        assert (false::bool) : (TV:TypedVal);
        => throw new class String2Id("java.lang.AssertionError") (toString(TV));

//@ \subsection{Switch statement}

syntax KItem ::= switchImpl (
             Exp, // switch argument
             SwitchGroupList, // switch body - list of 'SwitchGroup labels
             BlockStmList, // DefaultStm - default block, if any
             SwitchGroupList // everything following default block
             ) [strict(1(result(TypedVal)))]

context switchImpl( _, ('SwitchGroup('Case(HOLE) _:SwitchLabelList,, _:BlockStmList) _:SwitchGroupList), _ , _ )
context switchImpl( _, ('SwitchGroup('Default(HOLE) _:SwitchLabelList,, _:BlockStmList) _:SwitchGroupList), _ , _ )

syntax KItem ::= "switchEnd"
syntax KItem ::= "Debug"
syntax KItem ::= addToEnd (SwitchGroupList, SwitchGroup) [function]

rule [AddToEndSwitchGroupList]:
    addToEnd(Hd:SwitchGroup Tl:SwitchGroupList, S:SwitchGroup) => (Hd addToEnd(Tl, S))

rule [AddToEndSwitchGroupList2]:
    addToEnd(.SwitchGroupList, S:SwitchGroup) => (S .SwitchGroupList)

// goes from switch to switchImpl, taking the trailing labels and adding them as an empty switch group
// the default block is for now empty and will be filled when we go through the switch groups and find one that has a default label
//@ The switchEnd in the right-hand side of => is required to properly interact with break.
rule [Switch]:
    (switch(T:TypedVal) { S:SwitchGroupList TrailingLabels:SwitchLabelList })
    => switchImpl(T, addToEnd(S, 'SwitchGroup(TrailingLabels,, .BlockStmList)), .BlockStmList, .SwitchGroupList)
    ~> switchEnd

/*@ The type associated to V and V2 is not important for match, only the value.
JLS3 \$14.11, page 377: Every case constant expression associated with
a switch statement must be assignable (�5.2) to the type of the switch Expression.*/
rule [switchImpl-CaseNotMatch]:
    switchImpl(V :: _,
               'SwitchGroup( (('Case(V2 :: _) OtherLabels:SwitchLabelList) => (OtherLabels)) ,, _:BlockStmList)
               Rest:SwitchGroupList, _ , _ )
    when V =/=K V2

/*@Once case of first switch group matches, the whole switch is replaced
by it's block. The execution rules for switch will discard switch-related
constructs and will execute the statements. */

rule [executeBlockStmList]:
    'BlockStmList(Hd,,Tl:BlockStmList) => (Hd ~> Tl)

rule [executeSwitchGroupList]:
    'SwitchGroupList(Hd,,Tl:SwitchGroupList) => (Hd ~> Tl)

rule [executeBlockStmList2]:
    '.List`{""`}(.KList) => .K

rule [switchImpl-CaseMatch]:
    switchImpl(V:RawVal :: _,
               'SwitchGroup('Case(V :: _) OtherLabels:SwitchLabelList ,, S:BlockStmList)
               Rest:SwitchGroupList, _ , _ ) => ('Block(S) ~> Rest)

// moves the default to the third argument of switchImpl
// moves all remaining stuff to fourth argument of switchImpl
rule [switchImpl-DefaultSave]:
    switchImpl(TV:TypedVal,
              'SwitchGroup((('Default(_) OtherLabels:SwitchLabelList) => (OtherLabels)),, S:BlockStmList)
              Rest:SwitchGroupList,
              (.BlockStmList => S),
              (.SwitchGroupList => Rest))

rule [switchImpl-SwitchGroup-Discard]:
    switchImpl(TV:TypedVal,
               (('SwitchGroup(.SwitchLabelList ,, _:BlockStmList) Rest:SwitchGroupList) => (Rest)), _, _)

rule [switchImpl-Default-Exec]:
    switchImpl( _, .SwitchGroupList, DefaultStm:BlockStmList, AfterDef:SwitchGroupList) => (DefaultStm ~> AfterDef)

rule [SwitchGroup-Exec]:
    'SwitchGroup(_:SwitchLabelList,, S:BlockStmList) => S

rule [switchEnd-Discard]:
    switchEnd => .K

//@ \subsection{While statement} and loop infrastructure.

rule [while]:
    while(E:Exp)S:Stmt => whileImpl(E, S)                              [structural]

syntax KItem ::=  whileImpl (
                K,  // E - test expression. In For loop, it is UpdClause ~> testExp
                K   // S - while body
              )

rule [whileImpl]:
    whileImpl(E:K, S:K) => ifAux(E, S ~> whileImpl(E, S), .K)           [structural]

//@ \subsection{Do statement}
rule [do-while]:
    do S:Stmt while(E:Exp); => S ~> whileImpl(E, S)                     [structural]

//@ \subsection{For statement}
//macros
rule 'For(_,,_,,([Exps:KList] => toExps([Exps])),,_)   [macro]
rule 'For(([Exps:KList] => toExps([Exps])),,_)         [macro]

//wrapper of certain clauses of for statement, adds ; to cast expressions
syntax Exps ::= stm (Exps)

rule [stm-empty]:
    stm(.Exps) => .                                                         [structural]

rule [stm-exp]:
    stm(E,Es) => E; ~> stm(Es)
when
    getKLabel(E) ==KLabel 'cast                                             [structural]

rule [stm-LocalVarDec]:
    stm(K,Ks) => K ~> stm(Ks)
when
    notBool ( getKLabel(K) ==KLabel 'cast )                                 [structural]

rule [For-FirstArgV1Red]:
    for((InitExps => stm(InitExps));_;_) _
    when notBool ( getKLabel(InitExps) ==KLabel 'stm )                      [structural]

rule [For-SecondArgRed]:
    for(stm(_);('None(.KList) => 'Some(true));_) _                          [structural]

rule [For-ThirdArgRed]:
    for(stm(_);_;(UpdExps => stm(UpdExps))) _
    when notBool ( getKLabel(UpdExps) ==KLabel 'stm )                       [structural]

rule [For]:
    for(stm(InitClause); 'Some(TestExp); stm(UpdClause)) S
    => 'Block(stm(InitClause)
    ~> ifAux(TestExp, ('Block(S) ~> whileImpl(stm(UpdClause) ~> TestExp,S)), .)) [structural]

//totest model check - the argument of 'return and 'Throw must be evaluated. Otherwise some side effects during
// evaluation might be evaluated too late
/*@ Stack consumer stm - Return, Throw, Break or Continue reaches tryFinallySL layer*/
rule [StackConsumerStmt-in-TryFinally]:
    StackCons:StackConsumerStmt ~> finallyBlock(FinallyS:K)
    => FinallyS ~> StackCons

rule [StackConsumerStmt-RestoreEnv]:
    StackCons:StackConsumerStmt ~> env(Env:Map)
    => env(Env:Map) ~> StackCons

//@ \subsection{Break statement}

rule [Break-UnlabeledPropagate]:
    break 'None(_); ~> (KL:KLabel(_) => .)
when
            KL =/=KLabel 'env
    andBool KL =/=KLabel 'finallyBlock
    andBool KL =/=KLabel 'whileImpl
    andBool KL =/=KLabel 'switchEnd

rule [Break-Unlabeled]:
    break 'None(_); ~> KL:KLabel(_) => .
when
           KL ==KLabel 'whileImpl
    orBool KL ==KLabel 'switchEnd

rule [Break-LabeledPropagate]:
    break 'Some(X:Id); ~> (KL:KLabel(_) => .)
when
            KL =/=KLabel 'env
    andBool KL =/=KLabel 'finallyBlock
    andBool KL =/=KLabel 'labeledImpl

rule [BreakLabeledNotMatch]:
    break 'Some(X1:Id); ~> (labeledImpl(X2:Id) => .)
when
    X1 =/=K X2

rule [Break-LabeledMatch]:
    break 'Some(X:Id); ~> labeledImpl(X:Id) => .

//@ \subsection{Continue statement}

rule [Continue-Propagate]:
    continue _; ~> (KL:KLabel(_) => .)
when
            KL =/=KLabel 'env
    andBool KL =/=KLabel 'finallyBlock
    andBool KL =/=KLabel 'whileImpl

rule [Continue-Unlabeled]:
   (continue 'None(_); => .) ~> whileImpl(_,_)

rule [Continue-LabeledMeetsWhile]:
    <k>
      (. => getWhileLabel(Rest)) ~> continue 'Some(X:Id); ~> whileImpl(_,_) ~> Rest:K
    </k>

rule [Continue-LabeledNotMatch]:
    (whileLabel(LabelK:K) => .) ~> continue 'Some(X:Id); ~> (whileImpl(_,_) => .)
when
    LabelK =/=K X

rule [Continue-LabeledMatch]:
    whileLabel(X) ~> continue 'Some(X:Id); => .

/*@ Auxiliary constructs used in the semantics of continue.
Search for the label associated with the last encountered while statement*/
syntax KItem ::= getWhileLabel ( K )
           | whileLabel ( K )

rule getWhileLabel((env(_) => .) ~> _)
rule getWhileLabel(.K) => whileLabel(.K)
rule getWhileLabel(labeledImpl(X:Id) ~> _) => whileLabel(X)

rule getWhileLabel(KL:KLabel(_) ~> _) => whileLabel(.K)
when
            KL =/=KLabel 'env
    andBool KL =/=KLabel 'labeledImpl

/*@\subsection{Return} At method return, we have to check that the type
of the returned
value is a subtype of the expected return type.  Moreover, if that is
the case, then we also up-cast the returned value to one of the
expected type. */

//context 'Return('Some(HOLE))
context return 'Some(HOLE);

rule [Return-None-Desugar]:
    return 'None(_); => return 'Some(nothing :: void);
        [structural]

rule [Return-Propagate]:
    return 'Some(TV:TypedVal); ~> (KL:KLabel(Ks:KList) => .K)
when
            KL =/=KLabel 'env
    andBool KL =/=KLabel 'finallyBlock

rule [Return-MethodEnd]:
    <k> return 'Some(TV:TypedVal); => TV ~> K </k>
    <stack> ListItem( sl(K:K, MethContext:Bag) ) => . ...</stack>
    <methodContext> _:Bag => MethContext </methodContext>

/*@ \subsection{Throw statement}
Exceptions are propagated now until a catch that can bind them is
encountered. */
rule [Throw]:
    (. => checkCatch(subtype(typeOf(TV), T)))
    ~> throw TV:TypedVal;
    ~> catchBlocks(catchImpl(_ T:Type X:Id,_) _:CatchClauses)

syntax KItem ::= checkCatch ( K )
context checkCatch(HOLE)

rule [Throw-checkCatch-True]:
    checkCatch(true::bool)
    ~> throw TV:TypedVal;
    ~> catchBlocks(catchImpl(Param:Param, CatchS:K) _:CatchClauses)
    => 'Block([initParams(Param, TV),, CatchS])

rule [Throw-checkCatch-False]:
    (checkCatch(false::bool) => .)
    ~> throw TV:TypedVal;
    ~> catchBlocks(catchImpl(_,_) C:CatchClauses => C)

rule [Throw-catchBlocks-EmptyDiscard]:
    throw TV:TypedVal; ~> (catchBlocks(.CatchClauses) => .)

rule [Throw-Propagate]:
    throw TV:TypedVal; ~> (KL:KLabel(_) => .)
when
            KL =/=KLabel 'env
    andBool KL =/=KLabel 'finallyBlock
    andBool KL =/=KLabel 'catchBlocks

rule [Throw-MethodEnd]:
    <k>
      throw TV:TypedVal; ~> (. => K)
    </k>
    <stack> ListItem( sl(K:K, MethContext:Bag) ) => . ...</stack>
    <methodContext> _ => MethContext </methodContext>

rule [Throw-CausesThreadTermination]:
    <k>
      throw TV:TypedVal;
      =>  'Field( class String2Id("java.lang.System"),, String2Id("out") )
            .String2Id("println")
            (cast(classObject, 'Plus( "Thread terminated with exception: ",, TV )));
    </k>
    <stack> .List </stack>

//@ \subsection{Try statement}

// Why are there two trys?
rule [Try-Catch-Finally-Desugar]:
    try TryS:K Catches finally FinallyS:K
    => try 'Block(try TryS Catches) .CatchClauses finally FinallyS
    when Catches =/=K .CatchClauses
        [structural]

/*@ \subsubsection{Execution of try-catch} JLS \$14.20.1
*/
//resolve the catch clauses of try statement
context try _ HOLE

rule catch(KR:Param)S => catchImpl(KR,S)

//@ Internal representation of a preprocessed catch clause
syntax CatchImpl ::=  catchImpl (
                      Param,  //'Param(...),
                      K   //the code block
                   )
syntax KResult ::= CatchImpl
// after this statements there will be two types of catch clauses
// CatchImpl(ParamImpl, Block) and 'Catch(Param, Block)
syntax CatchClause ::= CatchImpl

rule [Try-Catch]:
    (try TryS:K KRs:CatchClauses => TryS ~> catchBlocks(KRs))
    when isKResult(KRs)

/*@ The auxiliary construct that holds catch clauses
after try clause has been moved to the top of computation*/
syntax KItem ::= catchBlocks ( CatchClauses ) //arg - list of catchImpl

/*@ If try clause executed without raising an exception, this construct will reach the top of computation.
    In this case it should be discarded.
*/
rule [catchBlocks-Discard]:
    catchBlocks(_) => .K

/*@ \subsubsection{Execution of try-finally} JLS \$14.20.2
*/

rule [Try-Finally]:
    try TryS:K .CatchClauses finally FinallyS:K => TryS ~> finallyBlock(FinallyS)

/*@ The auxiliary construct that holds finally clause
after try clause has been moved to the top of computation*/
syntax KItem ::= finallyBlock ( K )      //arg - finally block

rule [finallyBlock-NormalEnd]:
    finallyBlock(FinallyS:K) => FinallyS

endmodule
