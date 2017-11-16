(*  Title:      gASPFutures
    Author:     Ludovic Henrio 
                2017

    Note:      A new type system for futures
*)
(*Conventions:
  l = location in store
  x,y=varname
  locs = local variables
  l_\<alpha> = location in the local store of the active object of \<alpha>
 Stl = statement list
 EContext is an execution context, ie a thread 
 EcL = EContext list*)

chapter {* Syntax and Semantics *}

theory gASPFutures imports Main AuxiliaryFunctions begin
 
subsection {* Syntax *}
type_synonym VarName =  string
datatype VarOrThis = This | Id VarName
type_synonym ClassName = string
type_synonym MethodName = string

type_synonym ActName = nat
type_synonym FutName = nat
type_synonym Location = nat

datatype BasicType = Integer | Boolean | TObj ClassName  | AnyObject
datatype ASPType = BType BasicType | FutType BasicType 

abbreviation BasicTypeinASPType where
"BasicTypeinASPType fT \<equiv> case fT of BType T\<Rightarrow>T | FutType T\<Rightarrow>T"

datatype Signature = Method ASPType MethodName  "(ASPType * VarName) list" 
  (* signature = Method returnType MethodName (list of parameters)*)

datatype Value = null | ASPInt nat | ASPBool bool (* static values *)
                | ActRef ActName (* runtime values *)
                | FutRef FutName
type_synonym  Object = "(VarName\<rightharpoonup>Value) * ASPType"
abbreviation GetObject:: "Object \<Rightarrow>VarName=>Value option" ("_.[_]")
  where "GetObject ob x \<equiv> (fst ob) x"
abbreviation SetObject:: "Object \<Rightarrow>VarName=>Value\<Rightarrow>Object" ("_.[_]:=_")
  where "SetObject ob x v\<equiv> ((fst ob)(x\<mapsto>v),snd ob)"

datatype Atom = Val Value
             | Var VarOrThis 


datatype Expression = At Atom
             | Plus Atom Atom ("_+\<^sub>A_" [120,120] 200) 

datatype Rhs = Expr Expression
             | Call Atom MethodName "Expression list" ("_.\<^sub>A_'(_')" [440,0,50] 500) (*e.m(e list) *)
             | NewActive ClassName "Expression list" ("newActive _'(_')" [300,0] 500) (*newActive C(e list) *)
             | Get Atom

datatype Statement =   Assign VarName Rhs  (infix "=\<^sub>A"  400) (*x=z*)
      | Return Expression ("return _" [300] 300)(*return E *)
       | If Atom "Statement list" "Statement list" ("IF _ THEN _ ELSE _ " [300,0,0] 300)(*if E then s else s *)
(* skip |  NB: skip and seq are not necessary thanks to the use of statement list
| Seq Statement Statement (infix ";;"  100)*)
abbreviation MakeStatementList:: "Statement \<Rightarrow>Statement list\<Rightarrow>Statement list" (infix ";;" 100)
  where "MakeStatementList s Stl\<equiv> s#Stl"
abbreviation MakeStatementList2:: "Statement \<Rightarrow>Statement\<Rightarrow>Statement list" (infix ";;;" 120)
  where "MakeStatementList2 s s'\<equiv> s#[s']"


(*primrec RedContext:: "Statement\<Rightarrow> Statement \<times>Statement" (* returns basic instruction,context , i.e. the rest of the sequence*)
where
  "RedContext Skip = (Skip,Skip)" |
  "RedContext (x=\<^sub>Az) =  ((x=\<^sub>Az),Skip)" |
  "RedContext (return e) =  (return e,Skip)" |
  "RedContext (IF e THEN s ELSE s') =  (IF e THEN s ELSE s',Skip)" |
  "RedContext ( s ;; s') =  (fst (RedContext s),(snd (RedContext s);;s'))"
*)
(*abbreviation BuildContext::"Statement\<Rightarrow>Statement\<Rightarrow> Statement \<times>Statement" ("_[[_]]" [300, 0] 300)
where "BuildContext R s \<equiv> (s,R)"
*)
record Method = 
MethSignature:: Signature 
LocalVariables::"(ASPType * VarName) list" 
Body::"Statement list"
(*MethDefinition methodname (local variables) body*)

abbreviation MName:: "Method \<Rightarrow> MethodName"
where "MName m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>MethName"

abbreviation MRType:: "Method \<Rightarrow> ASPType"
where "MRType m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>returnType"

abbreviation MParams:: "Method \<Rightarrow>(ASPType * VarName) list"  
where "MParams m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>listparameters"

record Class = 
 Name::ClassName 
 ClassParameters::"((ASPType * VarName) list)"
 Methods::"(Method list)"
             (*ASPclass name (classparameters)  (listofmethodbodies) *)

datatype Program = Prog  "Class list" "(ASPType * VarName) list" "Statement list"


(*        --- runtime notions --- *)
type_synonym EContext = " (VarName\<rightharpoonup>Value) * (Statement list)" 
                          (*execution context = location of this, local variables, and statements *)
type_synonym Request = "FutName * MethodName * (Value list)"
abbreviation EC_locs:: "EContext \<Rightarrow>(VarName\<rightharpoonup>Value)"
where "EC_locs Ec \<equiv> fst ( Ec)"
abbreviation EC_Stl:: "EContext \<Rightarrow>Statement list"
where "EC_Stl Ec \<equiv> snd (Ec)"
(*datatype Process = Proc Request "Context list" *)

datatype ActiveObject = AO  ClassName "(VarName\<rightharpoonup>Value)"  "Request option" EContext "Request list"
    (* active object object's state , curr request id (None if idle), current request statement, request queue*)

datatype FutValue = Undefined | FutVal Value  

datatype Configuration = Cn "ActName\<rightharpoonup>ActiveObject" "FutName\<rightharpoonup>(BasicType*FutValue)"
abbreviation Conf_AOs
where "Conf_AOs conf \<equiv> case conf of Cn ao fut \<Rightarrow> ao"
abbreviation Conf_futs
where "Conf_futs conf \<equiv> case conf of Cn ao fut \<Rightarrow> fut"

text{* Binding and fetching elements *}
definition  fetchClass
where
"fetchClass P C \<equiv> 
case P of (Prog  CL Vars Stl) \<Rightarrow> (List.find  (\<lambda>class.(Name class) = C) CL) 
"
definition fetchMethodInClass
where
"fetchMethodInClass  class m \<equiv> 
List.find (\<lambda>method. (MName method = m)) (Methods class)
"

(*definition fetchMethodInClassOLD
where
"fetchMethodInClassOLD  class m \<equiv> 
Option.bind 
(List.find (\<lambda>method. (MName method = m)) (Methods class))
(\<lambda>method. Some (map fst (MParams method),map snd (MParams method), map snd (LocalVariables method), Body method))
" *)

definition Initialisation_from_BasicType
where 
"Initialisation_from_BasicType T \<equiv> case T of
Integer \<Rightarrow> (ASPInt 0)| Boolean \<Rightarrow> ASPBool False | TObj ClassName \<Rightarrow> null | AnyObject \<Rightarrow> null
"
definition Initialisation_from_ASPType
where 
"Initialisation_from_ASPType fT \<equiv> 
Initialisation_from_BasicType (BasicTypeinASPType fT)
"

definition Bind::"Program\<Rightarrow>ClassName\<Rightarrow>MethodName\<Rightarrow>Value list\<Rightarrow> EContext option"
where
 "Bind P  C m value_list\<equiv>
(case fetchClass P C of
  Some class \<Rightarrow>
    (case  fetchMethodInClass class m  of 
       Some Meth \<Rightarrow> 
         let param_list=MParams Meth in
         let param_names = map snd param_list in
         let param_types= map fst param_list in
         let locs = map snd (LocalVariables Meth) in
         if length param_list = length value_list then
           ( let locales=  (map_of (zip locs (map Initialisation_from_ASPType param_types)))
                    ++ (map_of (zip param_names value_list)) in
                Some (  locales,Body Meth))
           else None
       | None \<Rightarrow> None)
  | _\<Rightarrow> None)"
definition  fields:: "Program\<Rightarrow>ClassName \<Rightarrow>VarName list"
where
  "fields P C \<equiv>
     case (fetchClass P C) of
  Some class \<Rightarrow>(map snd (ClassParameters class))"

abbreviation DefinedClassNames
where "DefinedClassNames prog \<equiv>set (case prog of Prog  CL vl xtl \<Rightarrow>map Name CL)"

definition ReturnType
where
"ReturnType P m C=(case fetchClass P C of
  Some class \<Rightarrow> (case  fetchMethodInClass class m  of 
       Some Meth \<Rightarrow> Some (MRType Meth) |
       None \<Rightarrow> None)
  |
  None \<Rightarrow> None)"

definition MakeFutureType:: "ASPType \<Rightarrow> ASPType"
where
"MakeFutureType T = (case T of
  FutType T' \<Rightarrow> FutType T' |
  BType T' \<Rightarrow> FutType T')"

definition GetBasicType:: "ASPType \<Rightarrow> BasicType"
where
"GetBasicType T = (case T of
  FutType T' \<Rightarrow>  T' |
  BType T' \<Rightarrow>  T')"

section{*SOS*}

(*datatype EvaluatedExpr = Undefined | EVal Value | EObj Object | EFutRef FutName*)

inductive_set EvalValue:: "(Value  \<times> Value) set"
where
  Valnull[simp,intro]: "(null,   null)\<in>EvalValue" |
  Valint[simp,intro]: "(ASPInt i,  (ASPInt i) )\<in>EvalValue" |
  valbool[simp,intro]: "(ASPBool b,  (ASPBool b) )\<in>EvalValue" |
  valact[simp,intro]: "(ActRef \<alpha>,  ActRef \<alpha> )\<in>EvalValue" 

lemma EvalValue_is_deterministic[rule_format,intro]: "(e,v)\<in>EvalValue \<Longrightarrow>(e,v')\<in>EvalValue \<longrightarrow>v=v'"
apply (erule EvalValue.induct)
apply auto
apply (erule EvalValue.cases,simp+)+
done

inductive_set EvalAtom:: "(Atom  \<times>ActName  \<times> (VarName\<rightharpoonup>Value) \<times> (VarName\<rightharpoonup>Value) \<times> Value) set"
(* (e1,\<alpha>,state,locs,v) is true if e1 EVALUATES to v  in a setting where local variables are locs, state are fields and \<alpha> is the current AO*)
 where
   atomval[simp,intro]: "(v,ev)\<in>EvalValue \<Longrightarrow>(Val v, \<alpha>, state,locs, ev)\<in>EvalAtom" |
   atomlocs[simp,intro]: "\<lbrakk>locs(x)=Some v;(v,ev)\<in>EvalValue\<rbrakk> \<Longrightarrow>(Var (Id x),\<alpha>, state,locs, ev)\<in>EvalAtom" |
   atomThis[simp,intro]: "(Var This,\<alpha>,  state, locs,  ActRef \<alpha>)\<in>EvalAtom" |
   atomfield[simp,intro]:
   "\<lbrakk>locs(x)=None;  state x = Some v;(v,ev)\<in>EvalValue\<rbrakk> 
                      \<Longrightarrow>(Var (Id x),\<alpha>, state, locs, ev)\<in>EvalAtom" 

lemma EvalAtom_is_deterministic[rule_format]: 
      " (e,\<alpha>,state,locs,v)\<in>EvalAtom \<Longrightarrow> (\<forall> v'. (e,\<alpha>,state,locs,v')\<in>EvalAtom \<longrightarrow>v=v')"
apply (erule EvalAtom.induct)
apply (case_tac v,auto)
apply (erule EvalAtom.cases,auto)+
done

inductive_set EvalExpr:: "(Expression  \<times>ActName  \<times> (VarName\<rightharpoonup>Value) \<times> (VarName\<rightharpoonup>Value) \<times> Value) set"
(* (e1,\<alpha>,state,locs,v) is true if e1 EVALUATES to v  in a setting where local variables are locs, state are fields and \<alpha> is the current AO*)
 where
   expratom[simp,intro]: "(v,\<alpha>,state,locs,ev)\<in>EvalAtom \<Longrightarrow>(At v, \<alpha>, state,locs, ev)\<in>EvalExpr" |
   expradd[simp,intro]:"\<lbrakk>(v,\<alpha>,state,locs,ASPInt i)\<in>EvalAtom;(v',\<alpha>,state,locs, ASPInt i')\<in>EvalAtom\<rbrakk> 
                      \<Longrightarrow>(v +\<^sub>A v',\<alpha>,state, locs,  ASPInt (i+i'))\<in>EvalExpr" 


lemma EvalExpr_is_deterministic[rule_format]: 
      " (e,\<alpha>,state,locs,v)\<in>EvalExpr \<Longrightarrow> (\<forall> v'. (e,\<alpha>,state,locs,v')\<in>EvalExpr \<longrightarrow>v=v')"
apply (erule EvalExpr.induct)
apply auto
apply (erule EvalExpr.cases,auto)
apply (erule EvalAtom_is_deterministic,auto)
apply (erule EvalExpr.cases,auto)
apply (subgoal_tac "ASPInt i=ASPInt ia")
apply (subgoal_tac "ASPInt i'=ASPInt i'a")
apply force
apply (erule EvalAtom_is_deterministic,force)
apply (erule EvalAtom_is_deterministic,force)
done

abbreviation emptyEC::EContext
where "emptyEC == (empty,[])"
abbreviation ExprAORef where
"ExprAORef \<gamma>\<equiv>Expr (At(Val (ActRef \<gamma>)))"
abbreviation ExprFutRef where
"ExprFutRef f\<equiv>Expr (At(Val (FutRef f)))"

inductive reduction :: "Program\<Rightarrow>[Configuration, Configuration] => bool"  ("_\<turnstile>_\<leadsto>_" 50)
  where
    Serve [simp, intro!]: 
      "\<lbrakk>(Activities \<alpha>) = Some (AO C state None s (R#Rq)) ; 
      R= (f,m,vl);
        Bind P  C m vl = Some Ec\<rbrakk> 
          \<Longrightarrow> P\<turnstile>Cn Activities Futures 
                \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C state (Some R) Ec Rq))) Futures" 
|
    AssignLocal  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some(AO C state (Some R) Ec Rq); 
       Ec= (locs,(x=\<^sub>AExpr e);;Stl);
       x\<in>dom locs ; (e,\<alpha>,state, locs,v)\<in>EvalExpr
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C state (Some R) (locs(x\<mapsto>v),Stl) Rq)))  Futures" 
|
AssignField  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some(AO C state (Some R) Ec Rq); 
        Ec= (locs,(x=\<^sub>AExpr e);;Stl);
       x\<notin>dom locs;     x\<in>dom(state);  
       (e,\<alpha>,state, locs,v)\<in>EvalExpr
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C (state(x\<mapsto>v)) (Some R) (locs,Stl) Rq))) Futures"
 |
     NewActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some(AO C state (Some R) Ec Rq); 
        Ec= (locs,(x=\<^sub>AnewActive C'(el));;Stl); 
       fields P C=field_list; 
       \<gamma>\<notin>dom Activities;       
       length field_list = length el;   length field_list = length value_list; 
       \<forall> i<length value_list . (el!i,\<alpha>,state, locs,value_list!i)\<in>EvalExpr  ;
      state'=(map_of (zip field_list value_list))
     \<rbrakk>   
        \<Longrightarrow> P\<turnstile>Cn Activities Futures 
             \<leadsto>Cn (Activities(\<alpha>\<mapsto>(AO C state (Some R) (locs,x=\<^sub>A(ExprAORef \<gamma>);;Stl) Rq))
                             (\<gamma>\<mapsto> (AO C' state' None emptyEC [])))  
                  Futures" 
       (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)

|

   InvkActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO C state (Some R) (locs,(x=\<^sub>A(e.\<^sub>Am(el));;Stl)) Rq); 
       Activities \<beta> = Some (AO C\<^sub>\<beta> state\<^sub>\<beta>  R\<^sub>\<beta> Ec\<^sub>\<beta> Rq\<^sub>\<beta>); 
       \<alpha>\<noteq>\<beta>;
       (e,\<alpha>,state, locs,ActRef \<beta>)\<in>EvalAtom;
       f\<notin>dom Futures;   
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,\<alpha>,state, locs,value_list!i)\<in>EvalExpr) ;
       Some T=ReturnType P m C\<^sub>\<beta>
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C state (Some R) (locs,(x=\<^sub>AExprFutRef f);;Stl) Rq))
                             (\<beta>\<mapsto> (AO C\<^sub>\<beta> state\<^sub>\<beta> R\<^sub>\<beta> Ec\<^sub>\<beta> (Rq\<^sub>\<beta>@[(f,m,value_list)])) )) 
              (Futures(f\<mapsto>(GetBasicType T,Undefined)))"
       (* new term to evaluate is artificially complex because fut ref has to be encapsulated in a value and an expression*)
|
   InvkActive_Self [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO C state (Some R) Ec Rq); 
        Ec= (locs,(x=\<^sub>A(e.\<^sub>Am(el));;Stl));
       (e,\<alpha>,state, locs,ActRef \<alpha>)\<in>EvalAtom;
       f\<notin>dom Futures;   
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,\<alpha>,state, locs,value_list!i)\<in>EvalExpr)  ;
       Some T=ReturnType P m C
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C state (Some R) (locs,(x=\<^sub>AExprFutRef f);;Stl) (Rq@[(f,m,value_list)]))) ) 
              (Futures(f\<mapsto>(GetBasicType T,Undefined)))"
       (* new term to evaluate is artificially complex because fut ref has to be encapsulated in a value and an expression*)
|
   ReturnRequest [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some  (AO C state (Some R) Ec Rq); 
        Ec= (locs,(return e;;Stl));   R=(f,m,vl);
       (e,\<alpha>,state, locs,v)\<in>EvalExpr ;
       Futures f =Some (T,Undefined)
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto>(AO C state None emptyEC Rq))) (Futures(f\<mapsto>(T,FutVal v) ))" 

(************************** AUTOMATIC UPDATE **************************************)
(*|
  UpdateFuture_state [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some  (AO C state R Ec Rq);
     Futures f = Some (T,FutVal v); 
     state x = Some (FutRef f)
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C (state(x\<mapsto>v)) R Ec Rq))) Futures" 
|
  UpdateFuture_locs [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some  (AO C state R (locs, Stl) Rq);
     Futures f = Some (T,FutVal v); 
     locs x = Some (FutRef f)
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C state  R (locs(x\<mapsto>v),Stl) Rq))) Futures" *)

(***************** GET ***************************)
|
  GetRetrieve  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some  (AO C state (Some R) Ec Rq);
      Ec= (locs,(x=\<^sub>AGet z);;Stl); 
      (z,\<alpha>,state, locs,(FutRef f))\<in>EvalAtom;
     Futures f = Some (T,FutVal v)
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto>(AO C state (Some R) (locs,(x=\<^sub>AGet ( (Val v)));;Stl) Rq))) Futures" 
|
  GetResolved  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some  (AO C state (Some R) Ec Rq);
      Ec= (locs,(x=\<^sub>AGet e);;Stl); 
      (Var (Id y),\<alpha>,state, locs,v)\<in>EvalAtom;
      \<not> (\<exists> f. (v=FutRef f))
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto>(AO C state (Some R) (locs,(x=\<^sub>AExpr(At(Val v)));;Stl) Rq))) Futures" 
|
    IfThenElseTrue [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some(AO C state (Some R) Ec Rq); 
        Ec= (locs,(IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl);
       (e,\<alpha>,state, locs,ASPBool True)\<in>EvalAtom
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C (state(x\<mapsto>v)) (Some R) (locs,s\<^sub>t@Stl) Rq))) Futures"

|
     IfThenElseFalse [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some(AO C state (Some R) Ec Rq); 
        Ec= (locs,(IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl);
       (e,\<alpha>,state, locs,ASPBool False)\<in>EvalAtom
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO C (state(x\<mapsto>v)) (Some R) (locs,s\<^sub>e@Stl) Rq))) Futures" 

definition emptyObjClass  where
"emptyObjClass \<equiv> 
\<lparr>Name = ''EmptyObjectClass'',
 ClassParameters=[],
 Methods=[]
\<rparr>"

definition MainMethodEmptyBody where (* for typing *)
" MainMethodEmptyBody Vars \<equiv>
\<lparr>MethSignature= Method (BType Integer) ''main'' [] ,
LocalVariables= Vars ,
Body =[]
\<rparr>
"

definition MainObjClass  where
"MainObjClass Vars\<equiv> 
\<lparr>Name = ''MainClass'',
 ClassParameters=[],
 Methods=[(MainMethodEmptyBody Vars)]
\<rparr>"

abbreviation "EmptyConfig \<equiv> Cn empty empty"

definition BuildInitialConfigurationfromVarsStl:: "((ASPType * VarName) list) \<Rightarrow>Statement list\<Rightarrow> Configuration"
where
  "BuildInitialConfigurationfromVarsStl vl stl \<equiv> Cn (empty(0\<mapsto>(AO (''MainClass'') (empty) 
                  (Some(0,''main'',[])) (map_of (map (\<lambda> v. (snd v,Initialisation_from_ASPType (fst v))) vl),stl) [])))
                  (empty(0\<mapsto>(Integer,Undefined)))"

definition InitialConfiguration:: "Program \<Rightarrow>Configuration"
where  
" InitialConfiguration prog \<equiv> case prog of (Prog  CL Vars Stl) \<Rightarrow> BuildInitialConfigurationfromVarsStl (Vars) Stl" 


end
