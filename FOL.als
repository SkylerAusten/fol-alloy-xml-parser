module FOLSeparator

abstract sig Variable {}
abstract sig Element {}
abstract sig Relation {}

abstract sig Formula {}

sig Atom extends Formula {
    relation: one Relation,
    vars: seq Variable
} {
	#vars = 2
}

abstract sig Quantifier extends Formula {
    bound_var: one Variable,
    body: one Formula
}

sig Forall extends Quantifier {}
sig Exists extends Quantifier {}

abstract sig UnaryConnective extends Formula {
    child: one Formula
}
sig Not extends UnaryConnective {}

abstract sig BinaryConnective extends Formula {
    left: one Formula,
    right: one Formula
} {
    left != right
}
sig And extends BinaryConnective {}
sig Or extends BinaryConnective {}
sig Implies extends BinaryConnective {}

// environment maps variable to a constant
abstract sig Environment {
    mapping: Variable -> lone Element
}

one sig EmptyEnvironment extends Environment {} {
    no mapping
}



abstract sig Structure {
    elements: set Element,
    interpretation: Relation -> set (Element -> Element),
    satisfies: Environment -> set Formula
}

abstract sig PositiveStructure extends Structure {}
abstract sig NegativeStructure extends Structure {}

fun all_children : Formula -> Formula {
    (Quantifier <: body) + (UnaryConnective <: child) + 
    (BinaryConnective <: left) + (BinaryConnective <: right)
}

//add extra relation to environment
fun extendEnv[env: Environment, v: Variable, e: Element]: Environment {
    // Find the pre-generated environment that has the right mapping
    {env': Environment | env'.mapping = env.mapping ++ (v -> e)}
}


fact Semantics {
    all s: Structure {
        // Atom semantics
        all env: Environment, a: Atom |
            (env -> a) in s.satisfies iff (
                a.relation = E and
                all v: a.vars[Int] | v in env.mapping.Element and
                (env.mapping[a.vars[0]] -> env.mapping[a.vars[1]] ) in s.interpretation[a.relation]
            )
        
        // Not semantics
        all env: Environment, n: Not |
            (env -> n) in s.satisfies iff 
            (env -> n.child) not in s.satisfies
        
        // And semantics
        all env: Environment, a: And |
            (env -> a) in s.satisfies iff 
            ((env -> a.left) in s.satisfies and (env -> a.right) in s.satisfies)
        
        // Or semantics
        all env: Environment, o: Or |
            (env -> o) in s.satisfies iff 
            ((env -> o.left) in s.satisfies or (env -> o.right) in s.satisfies)
        
        // Implies semantics
        all env: Environment, i: Implies |
            (env -> i) in s.satisfies iff 
            ((env -> i.left) not in s.satisfies or (env -> i.right) in s.satisfies)
        
        // Forall semantics
        all env: Environment, f: Forall |
            (env -> f) in s.satisfies iff 
            (all e: s.elements | 
                let env' = extendEnv[env, f.bound_var, e] |
                one env' implies (env' -> f.body) in s.satisfies)
        
        // Exists semantics
        all env: Environment, e: Exists |
            (env -> e) in s.satisfies iff 
            (some elem: s.elements | 
                let env' = extendEnv[env, e.bound_var, elem] |
                one env' and (env' -> e.body) in s.satisfies)
    }
}

// makes  a DAG
fact FormulaStructure {
    no f: Formula | f in f.^all_children
    all f: Formula - Separator.root | one all_children.f
    Formula = Separator.root.*all_children
}

// al vars must be bound
fact WellFormedness {
    all a: Atom | all v: a.vars[Int] |
        some q: Quantifier | q.bound_var = v and a in q.^all_children
    
    all q1, q2: Quantifier | 
        q2 in q1.^all_children implies q1.bound_var != q2.bound_var
}

// no duplicate atom and no double negation
fact AvoidDegenerateFormulas {
    no n1, n2: Not | n2 = n1.child
    no disj a1, a2: Atom | 
        a1.relation = a2.relation and a1.vars = a2.vars
}

one sig Separator {
    root: one Formula
}

one sig V0, V1 extends Variable {}
one sig E extends Relation {}
one sig N1, N2, N3 extends Element {}

one sig Pos_Edge extends PositiveStructure {} {
    elements = N1 + N2 + N3
    interpretation[E] = (N1->N2) + (N2->N1) + (N2->N3) + (N3->N1)
}

one sig Neg_NoEdge extends NegativeStructure {} {
    elements = N1 + N3
    interpretation[E] = (N1->N3) + (N3->N1)
}

one sig Neg_NoEdge2 extends NegativeStructure {} {
    elements = N2 + N3  
    interpretation[E] = (N2->N3) + (N3->N2)
}

one sig Env_V0_N1 extends Environment {} {
    mapping = V0->N1
}
one sig Env_V0_N2 extends Environment {} {
    mapping = V0->N2
}
one sig Env_V0_N3 extends Environment {} {
    mapping = V0->N3
}
one sig Env_V1_N1 extends Environment {} {
    mapping = V1->N1
}
one sig Env_V1_N2 extends Environment {} {
    mapping = V1->N2
}
one sig Env_V1_N3 extends Environment {} {
    mapping = V1->N3
}

one sig Env_V0_N1_V1_N1 extends Environment {} {
    mapping = V0->N1 + V1->N1
}
one sig Env_V0_N1_V1_N2 extends Environment {} {
    mapping = V0->N1 + V1->N2
}
one sig Env_V0_N1_V1_N3 extends Environment {} {
    mapping = V0->N1 + V1->N3
}
one sig Env_V0_N2_V1_N1 extends Environment {} {
    mapping = V0->N2 + V1->N1
}
one sig Env_V0_N2_V1_N2 extends Environment {} {
    mapping = V0->N2 + V1->N2
}
one sig Env_V0_N2_V1_N3 extends Environment {} {
    mapping = V0->N2 + V1->N3
}
one sig Env_V0_N3_V1_N1 extends Environment {} {
    mapping = V0->N3 + V1->N1
}
one sig Env_V0_N3_V1_N2 extends Environment {} {
    mapping = V0->N3 + V1->N2
}
one sig Env_V0_N3_V1_N3 extends Environment {} {
    mapping = V0->N3 + V1->N3
}


pred findSeparator {
    all p: PositiveStructure | (EmptyEnvironment -> Separator.root) in p.satisfies
    all n: NegativeStructure | (EmptyEnvironment -> Separator.root) not in n.satisfies

}

run findSeparator for 6 Formula, 2 Atom, 2 Quantifier, 2 Variable
