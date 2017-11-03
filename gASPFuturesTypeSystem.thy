theory gASPFuturesTypeSystem imports gASPFutures begin
(* there is a type Any for null*)
definition BuildTypeEnv ::"(ASPType * VarName) list \<Rightarrow> VarName \<Rightarrow>ASPType option"
where
"BuildTypeEnv VarDeclList =  (map_of (map prod.swap (VarDeclList)))"

inductive Subtype :: "Program\<Rightarrow>ASPType \<Rightarrow>ASPType \<Rightarrow>bool "  (" _\<turnstile>_\<sqsubseteq>_" 50)
 where
 "P\<turnstile>T\<sqsubseteq>T"
|
 "P\<turnstile>BType T\<sqsubseteq>FutType T"
|
 "P\<turnstile>BType (TObj C)\<sqsubseteq>BType AnyObject"
|
 "P\<turnstile>FutType (TObj C)\<sqsubseteq>FutType AnyObject"

inductive TypeValue :: "Program\<Rightarrow>Configuration\<Rightarrow>Value \<Rightarrow> ASPType \<Rightarrow> bool"  ("_,_\<turnstile>\<^sub>V_:_" 50)
where
 "P,Conf \<turnstile>\<^sub>V ASPInt n: BType Integer"
|
 "P,Conf \<turnstile>\<^sub>V ASPBool b: BType Boolean"
|
 "P,Conf \<turnstile>\<^sub>V null :  BType (AnyObject)"
|
 "Acts \<alpha>= Some(AO C' state R Ec Rq)
\<Longrightarrow> P,Cn Acts Futs \<turnstile>\<^sub>V ActRef \<alpha>:  BType (TObj C')"  (*dynamic obj*)
|
 "Futs f = Some(T,V)
\<Longrightarrow> P,Cn Acts Futs \<turnstile>\<^sub>V FutRef f: FutType T"  (*dynamic fut*)

inductive TypeAtom :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Atom \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>A_:_" 50)
 where
 " P,Config \<turnstile>\<^sub>V v:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>A Val v:T"
|
" P,Config,\<Gamma> in C \<turnstile>\<^sub>A Var This:  BType (TObj C)  (*This*)
  " 
|
" \<Gamma> x = Some T \<Longrightarrow>P,Config,\<Gamma>  in C\<turnstile>\<^sub>A Var (Id x) : T (* Var or field reference *)
  "
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>A e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>A e:T' " (* subtype*)

inductive TypeExpression :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Expression \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>E_:_" 50)
 where
 " P,Config,\<Gamma> in C \<turnstile>\<^sub>A  v:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>E At v:T"
|
"\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>A e:BType Integer; P,Config,\<Gamma> in C \<turnstile>\<^sub>A e':BType Integer
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>Ee+\<^sub>Ae':BType Integer"
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T' " (* subtype*)


inductive TypeRhs  :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow> Rhs \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>R_:_" 50)
 where
  (* Expression *)
 " P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (Expr e):T"
|  (* method call*)
 "\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>A z:BType (TObj C') ; fetchClass P C' = Some Class;
   fetchMethodInClass Class m = Some Meth;
   param_types= map fst (MParams Meth) ; length param_types = length el ; \<forall> i<length el. (P,Config,\<Gamma> in C \<turnstile>\<^sub>E el!i:(param_types!i)) \<rbrakk>
\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (z.\<^sub>Am(el)):MakeFutureType (MRType Meth)"
|  (* new active *)
"\<lbrakk>  fetchClass P C' = Some Class;
   Class_param_types = map fst (ClassParameters Class);
   length Class_param_types = length el ; \<forall> i<length el. (P,Config,\<Gamma> in C \<turnstile>\<^sub>E el!i:(Class_param_types!i)) \<rbrakk>
\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (newActive C'(el)):BType (TObj C')"
| (* Get *)
" P,Config,\<Gamma> in C \<turnstile>\<^sub>A a:(FutType T)    \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (Get a):BType (T)"
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>R e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R e:T' "   (* subtype*)

inductive TypeStatement  :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Statement\<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>S _ " 50)
and TypeStatementList ::"Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Statement list\<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>L _ " 50)
 where
 "\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>R a:T; 
    \<Gamma> x = Some T' ; P\<turnstile>T\<sqsubseteq>T'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S (x=\<^sub>A a) "
|
 "\<lbrakk> fetchClass P C = Some Class;
   fetchMethodInClass Class m = Some Meth;
   MRType Meth = T';
   P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T; 
    \<Gamma> x = Some T' ; P\<turnstile>T\<sqsubseteq>T'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S return e "
|
 "\<lbrakk>
   P,Config,\<Gamma> in C \<turnstile>\<^sub>A z:BType Boolean; 
   P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl;  P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S IF z THEN sl ELSE sl' "
|
"P,Config,\<Gamma> in C \<turnstile>\<^sub>L [] "
|
"P,Config,\<Gamma> in C \<turnstile>\<^sub>S s\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl\<Longrightarrow>P,Config,\<Gamma> in C \<turnstile>\<^sub>L s;;sl "


fun TypeClass :: "Program \<Rightarrow> Class \<Rightarrow>bool" ("_ \<turnstile>\<^sub>C _ " 50)
where
" (P\<turnstile>\<^sub>CClass) = (let C_param_env = (map_of (map prod.swap (ClassParameters Class))) in
               (\<forall> M\<in> set (Methods Class). 
               let \<Gamma> = C_param_env ++ (map_of (map prod.swap (LocalVariables M))) ++ (map_of (map prod.swap (MParams M))) in
               (P,EmptyConfig,\<Gamma> in (Name Class) \<turnstile>\<^sub>L (Body M) ) ) ) "

primrec TypeProgram :: "Program \<Rightarrow>bool" ("\<turnstile>\<^sub>P _ " 50)
where
" (\<turnstile>\<^sub>PProg CL MainVars MainBody) = (
                   (\<forall> C\<in>set CL. (Prog CL MainVars MainBody\<turnstile>\<^sub>CC)) \<and>
                   (let \<Gamma> = (map_of (map prod.swap (MainVars))) in
                           (Prog ((MainObjClass MainVars)#CL) MainVars MainBody,EmptyConfig,\<Gamma> in (''MainClass'') \<turnstile>\<^sub>L MainBody )  )  )
"

inductive TypeRequest :: "Program \<Rightarrow> Configuration\<Rightarrow> ClassName \<Rightarrow>Request \<Rightarrow> bool"  ("_,_ in _ \<turnstile>\<^sub>Q _" 50)
where 
" \<lbrakk> fetchClass P C =   Some Class ;
    fetchMethodInClass Class m = Some Meth; 
    param_types= map fst (MParams Meth);
    length vl = length param_types ;  \<forall> i <length vl . (P, Cn Acts Futs\<turnstile>\<^sub>V(vl!i):(param_types!i));
    Futs f = Some (T, Undefined); T=GetBasicType (MRType Meth)
\<rbrakk>
\<Longrightarrow>P,Cn Acts Futs in C\<turnstile>\<^sub>Q(f,m,vl)"

primrec TypeConfig :: "Program \<Rightarrow>Configuration \<Rightarrow>bool" ("_ \<turnstile> _ " 50)
where
" (P\<turnstile>Cn AOs Futures) =
((\<forall> Act\<in> ran AOs. case Act of (AO C state R Ec Rq) \<Rightarrow>
   (\<exists> CL . (fetchClass P C = Some CL \<and>
    (
     (* check state *)
     ( (  \<forall> x v. (state(x) =Some  v \<longrightarrow> (\<exists> T . (T,x)\<in> set (ClassParameters CL) \<and> (P,Cn AOs Futures\<turnstile>\<^sub>V v: T))) ) )
     (* check request queue*)
     \<and> (\<forall> R'\<in>set Rq. (P, (Cn AOs Futures) in C \<turnstile>\<^sub>Q R' ) )
     (* check current request*)
     \<and> 
     (case R of Some  (f,m,vl) \<Rightarrow>
         (\<exists> Meth. fetchMethodInClass CL m = Some Meth \<and>
           (P, Cn AOs Futures in C \<turnstile>\<^sub>Q (f,m,vl)) 
           \<and> (case Ec of (locs,Stl) \<Rightarrow> ( \<forall> s\<in>set Stl. 
             (P,Cn AOs Futures,
             (BuildTypeEnv (ClassParameters CL))++(BuildTypeEnv (LocalVariables Meth))++(BuildTypeEnv (MParams Meth)) 
                in C \<turnstile>\<^sub>S s)
        )) ) ) )))) \<and>
   (* Futures *)
(\<forall> futs\<in> ran Futures. case futs of
      (T,Undefined) \<Rightarrow> True |
      (T,FutVal v) \<Rightarrow> (P,Cn AOs Futures \<turnstile>\<^sub>V v: (FutType T))))
"


end