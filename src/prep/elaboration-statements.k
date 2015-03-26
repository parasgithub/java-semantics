module ELABORATION-STATEMENTS
    imports CORE-SORTS
    imports ELABORATION-CORE
    imports ELABORATION-METHOD-INVOKE //for lookupMethod
    imports PROCESS-LOCAL-CLASSES //for localClassGetExtraArgs

//@ Elaboration of 'KListWrap, 'Block, 'For or 'Catch - nodes that may contain variable declarations.

//K bug: support for KListWrap. This rule was replaced by a special section for elaboration of KListWrap.
// See other K-bug-s.
/* 'KListWrap nodes need to be elaborated left-to-right. Required when direct child elements might contain variable
declarations.
*/
//rule customElabHeating('KListWrap, HeadKs:KList,, K:K) => isElabKList(HeadKs)

syntax KItem ::= isVarDecHolderLabel ( KLabel )                 [function]
rule isVarDecHolderLabel('Block) => true
rule isVarDecHolderLabel('For) => true
rule isVarDecHolderLabel('Catch) => true

/*@ In addition to what defaul elab heating does, when we heat the first argument of 'Block, 'For or 'Catch
we need to save a copy of elaboration environment - e.g. the last entry of <elabEnv> <localTypes>.
This is because these statements are blocks that might declare local variables.
*/
rule [elab-Block-For-Catch-heat-FirstSubterm]:
    <k> elab(KL:KLabel(K:K,, Ks:KList)) => elab(K) ~> elab(KL(CHOLE,, Ks:KList)) ...</k>
    <elabEnv> (. => ElabEnvLI) ElabEnvLI:ListItem ...</elabEnv>
    <localTypes> (. => LocalTypesLI) LocalTypesLI:ListItem ...</localTypes>
when
    isVarDecHolderLabel(KL) ==K true andBool notBool isElabKResult(K) ==K true

rule [testing]:
//    elab('Block(K:K,, Ks:KList)) => 'Block(K:K,, Ks:KList) ~> Debugs)
    <k> elab('Block(K:K,, Ks:KList)) => elab(K) ~> elab('Block(CHOLE,, Ks:KList))...</k>
    <elabEnv> (. => ElabEnvLI) ElabEnvLI:ListItem ...</elabEnv>
    <localTypes> (. => LocalTypesLI) LocalTypesLI:ListItem ...</localTypes>
    <debug> (. => ('Block(K,, Ks))) ...</debug>
//    elab('Block(K:K,, Ks:KList)) => (Debugs ~> 'Block(K:K,, Ks:KList) ~> Debugs)
when
    notBool isElabKResult(K) ==K true [macro]

//Seqstrict starting from 2-nd argument.
// Having three terms in the KList in the second argument ensures that
// the list is at least of length 2.
rule [customElabHeating-For-next-children]:
    customElabHeating('For, [HeadKs:KList,, KPrec:K,, KHole:K]) => isElabKList([HeadKs,,KPrec])

//Seqstrict starting from 2-nd argument.
rule [customElabHeating-For-next-children]:
    customElabHeating('Catch, [K1:K,, KHole:K]) => isElabKResult(K1)

rule [elabEnd-Block-For-Catch]:
    elabEnd(KL:KLabel(ElabResL:KList)) => removeLastElabEnv ~> elabRes(KL(ElabResL))
when
    isVarDecHolderLabel(KL) ==K true

syntax KItem ::= "Debugs"

rule [sequentialHeating]:
    customElabHeating('BlockStmList, [B:KList,, KHole:K]) => isElabKList([B])

//@ Resolve the local var type, required to register the var in <elabEnv>
//context elab('LocalVarDecStm('LocalVarDec(_:K,, HOLE,, _:K)))
context elab('LocalVarDec(_:K,, HOLE,, _:K))

rule [desugar-LocalVarDec-with-init-macro]:
        'BlockStmList('LocalVarDecStm('LocalVarDec(K:K,, T:K,, ['VarDec(X:Id,,InitExp:K)])),, 'BlockStmList(El:K,, Rest:K))
      =>
        'BlockStmList('LocalVarDecStm('LocalVarDec(K,, T,, ['VarDec(X)])),, 'BlockStmList('ExprStm('Assign('ExprName(X),, InitExp)),, 'BlockStmList(El,, Rest)))
when
    getKLabel(InitExp) =/=KLabel 'ArrayInit             [macro]
    
rule [desugar-LocalVarDec-multi-macro]:
        'BlockStmList('LocalVarDecStm('LocalVarDec(K:K,, T:K,, [Var1:K,, Var2:K,, VarDecs:KList])),, 'BlockStmList(El:K,, Rest:K))
      =>
        'BlockStmList('LocalVarDecStm('LocalVarDec(K,, T,, [Var1])),, 'BlockStmList('LocalVarDecStm('LocalVarDec(K,, T,, [Var2,, VarDecs])),, 'BlockStmList(El,, Rest)))
        [macro]

rule [desugar-For-LocalVarDec-macro]:
        'For('LocalVarDec(K:K,, T:K,, [Init:KList]),, A,, B,, C)
      =>
        'Block('BlockStmList('LocalVarDecStm('LocalVarDec(K:K,, T:K,, [Init])),, 'BlockStmList('For(.Exps,, A,, B,, C),, .BlockStmList)))
      [macro]


rule [elab-LocalVarDec]:
    <k>
      elab('LocalVarDec(K:K,, T:Type,, ['VarDec(X:Id)]))
      => elabRes('LocalVarDec(K,, T,, ['VarDec(X)]))
      ...
    </k>
    <elabEnv> ListItem(mapWrap((. => X |-> T) _)) ...</elabEnv>

//@\subsection{Elaboration of SuperConstrInv, QSuperConstrInv, AltConstrInv}

// 'SuperConstrInv( _:K,, [ Args:KList ] )
//@ Desugaring unqualified superclass constructor invocation into a qualified one
rule [elab-SuperConstrInv-desugar]:
    <k>
      elab(
        'SuperConstrInv(K:K,, [ Args:KList ])
        =>  'QSuperConstrInv(
              #if CT ==K instanceCT
                #then findQualifierOfType(EnclosingClass, BaseEnclosingClass)
                #else noValue
              #fi,,
              K,,
              [Args]
            )
      )
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>
    <class>
      <classType> Class </classType>
      <extends> BaseClass:ClassType </extends>
      <enclosingClass> EnclosingClass:ClassType </enclosingClass>
      ...
    </class>
    <class>
      <classType> BaseClass </classType>
      <enclosingClass> BaseEnclosingClass:ClassType </enclosingClass>
      <classContextType> CT:ContextType </classContextType>
      ...
    </class>

rule customElabEnd('QSuperConstrInv) => true

rule [elabEnd-QSuperConstrInv-local-augment-arguments]:
    <k>
      (. => localClassGetExtraArgs(BaseClass))
      ~> elabEnd('QSuperConstrInv(Qual:K,, Arg2:K,, [ Args:KList ]))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>
    <classType> Class </classType>
    <extends> BaseClass:ClassType </extends>

//@ QSuperConstrInv lookup is always unqualified
rule [elabEnd-QSuperConstrInv-to-lookupMethod]:
    <k>
      ( elabRes([ExtraArgs:KList])
        => lookupMethod(BaseClass, true, getConsName(BaseClass), [Args,,ExtraArgs])
      )
      ~> elabEnd('QSuperConstrInv(Qual:K,, Arg2:K,, [ Args:KList ]))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>
    <classType> Class </classType>
    <extends> BaseClass:ClassType </extends>

rule [elabEnd-QSuperConstrInv]:
    methodLookupResult(_, [ExpectedArgExps:KList], instanceCT)
    ~> elabEnd('QSuperConstrInv(Qual:K,, Arg2:K,, [_]))
    => elabRes('QSuperConstrInv(Qual,, Arg2,, [ ExpectedArgExps ]))

rule customElabEnd('AltConstrInv) => true

rule [elabEnd-AltConstrInv-local-augment-arguments]:
    <k>
      (. => localClassGetExtraArgs(Class))
      ~> elabEnd('AltConstrInv(Arg1:K,, [ Args:KList ]))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>

//@ AltConstrInv lookup is always unqualified
rule [elabEnd-AltConstrInv-to-lookupMethod]:
    <k>
      ( elabRes([ExtraArgs:KList])
        => lookupMethod(Class, true, getConsName(Class), [Args,,ExtraArgs])
      )
      ~> elabEnd('AltConstrInv(Arg1:K,, [ Args:KList ]))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>

rule [elab-AltConstrInv]:
    methodLookupResult(_, [ExpectedArgExps:KList], instanceCT)
    ~> elabEnd('AltConstrInv(Arg1:K,, [_]))
    => elabRes('AltConstrInv(Arg1:K,, [ ExpectedArgExps ]))

endmodule
