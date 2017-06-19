theory gASPFuturesTypeSystem imports gASPFutures begin

inductive Subtype :: "Program\<Rightarrow>ASPType \<Rightarrow>ASPType \<Rightarrow>bool "  (" _\<turnstile>_\<sqsubseteq>_" 50)
 where
 "P\<turnstile>T\<sqsubseteq>T"
|
 "P\<turnstile>BType T\<sqsubseteq>FutType T"
|
 "P\<turnstile>BType (TObj C)\<sqsubseteq>BType AnyObject"
|
 "P\<turnstile>FutType (TObj C)\<sqsubseteq>FutType AnyObject"

inductive TypeExpression :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Expression \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>E_:_" 50)
 where
 "P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Val (ASPInt n): BType Integer"
|
 "P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Val (ASPBool b): BType Boolean"
|
 "P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Val (null) :  BType (AnyObject)"
|
 "Acts \<alpha>= Some(AO C' state R Ec Rq)
\<Longrightarrow> P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Val (ActRef \<alpha>):  BType (TObj C')"  (*dynamic obj*)
|
 "Futs f = Some(T,V)
\<Longrightarrow> P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Val (FutRef f):   FutType T  (*dynamic fut*)
" 
|
" P,Cn Acts Futs,\<Gamma> in C \<turnstile>\<^sub>E Var This:  BType (TObj C)  (*This*)
  " 
|
" \<Gamma> x = Some T \<Longrightarrow>P,Cn Acts Futs,\<Gamma>  in C\<turnstile>\<^sub>E Var (Id x) : T (* Var or field reference *)
  "
|
"\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:BType Integer; P,Config,\<Gamma> in C \<turnstile>\<^sub>E e':BType Integer
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>Ee+\<^sub>Ae':BType Integer"
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T' " (* subtype*)


inductive TypeRhs  :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow> Rhs \<Rightarrow>ASPType \<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>R_:_" 50)
 where
 " P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (Expr e):T"
|
 "\<lbrakk> P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:BType (TObj C') ; fetchClass P C' = Some Class;
   fetchMethodInClass Class m = Some Meth;
   param_types= map fst (MParams Meth) ; length param_types = length el ; \<forall> i<length el. (P,Config,\<Gamma> in C \<turnstile>\<^sub>E el!i:(param_types!i)) \<rbrakk>
\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (e.\<^sub>Am(el)):MakeFutureType (MRType Meth)"
|
"\<lbrakk>  fetchClass P C' = Some Class;
   Class_param_types = map fst (ClassParameters Class);
   length Class_param_types = length el ; \<forall> i<length el. (P,Config,\<Gamma> in C \<turnstile>\<^sub>E el!i:(Class_param_types!i)) \<rbrakk>
\<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R (newActive C'(el)):BType (TObj C')"
|
"P\<turnstile>T\<sqsubseteq>T' \<Longrightarrow>  P,Config,\<Gamma> in C \<turnstile>\<^sub>R e:T \<Longrightarrow> P,Config,\<Gamma> in C \<turnstile>\<^sub>R e:T' "   (* subtype*)

inductive TypeStatement  :: "Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Statement\<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>S _ " 50)
and TypeSTatementList ::"Program\<Rightarrow>Configuration\<Rightarrow> (VarName \<rightharpoonup>ASPType)\<Rightarrow> ClassName\<Rightarrow>Statement list\<Rightarrow> bool"  ("_,_,_ in _\<turnstile>\<^sub>L _ " 50)
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
   P,Config,\<Gamma> in C \<turnstile>\<^sub>E e:BType Bool; 
   P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl;  P,Config,\<Gamma> in C \<turnstile>\<^sub>L sl'
\<rbrakk> \<Longrightarrow>
P,Config,\<Gamma> in C \<turnstile>\<^sub>S IF e THEN sl ELSE sl' "
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
" (\<turnstile>\<^sub>PProg CL MainVars MainBody) = (let P = Prog CL MainVars MainBody in
                          ( (\<forall> C\<in>set CL. (P\<turnstile>\<^sub>CC)) \<and>
                            (let \<Gamma> = (map_of (map prod.swap (MainVars))) in
                              (P,EmptyConfig,\<Gamma> in (Name emptyObjClass) \<turnstile>\<^sub>L MainBody )  ) ) )
"

primrec TypeConfig :: "Program \<Rightarrow>Configuration \<Rightarrow>bool" ("_ \<turnstile>\<^sub>R _ " 50)
where
" (P\<turnstile>\<^sub>RCn AOs Futures) = (\<forall> Act\<in> ran AOs. case Act of (AO C state R Ec Rq) \<Rightarrow> True )
"
