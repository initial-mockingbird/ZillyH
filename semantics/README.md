# Extended Semantics

## BNF Grammar

We try to stick with a very standard grammar for a lambda calculus with variable assignment. With a couple of minor differences:

- Every argument in a lambda expression is explicitly typed.
- We denote the set of basic types as $B$.
- We add Type Variables, Abstractions and Applications. Although not currently employed, it allows us to write the one existential triplet the language uses to model the `Lazy*` type.
- We add an existential triplet to model `Lazy*`. It contains the type witness, the value, and a function to forcefully evaluate the value.
- We have 3 environments: Gamma (names to types), E (names to memory locations) and S (memory locations to expressions). As a shorthand, we write $\varphi_{i,j,k}$ for $E_i,S_j,\Gamma_k$.
- Every expression can result in a closure $<e,\varphi>$

## Lazy* 

One of the features of Zilly, is that big steps can change the type of expressions. After one big step, an expression of type $Lazy<a>$, is reduced to an expression of type $a$.

Since Zilly is a strict language, we force one single big step at every definition, assignment, function application and function return. This has the sudden implication that the assignment operator is not idempotent:

```
Int x := 5;
Lazy<Int> lx := 'x'; // lx -> x;
lx := lx // lx -> RValue(lx) = RValue(x) = 5;
```

Although this is the expected behavior, it is somewhat surprising since now `lx` no longer holds the deferred value `x`, but rather the basic value `5`.

Another implication of such a model, is that it disallows certain valid function applications:

```
Lazy<Int> -> Int f := /. x : Lazy<Int> => x.
Int x0 := f(5);       // Allowed by subtyping
Int x1 := f('5');     // Allowed
_   x2 := f('''5'''); // Disallowed!
```

In this example, although `f` only returns `x` after applying one big step to it, our type system is not rich enough to enforce this constraint. Thus we have to provide a more specific type which is incompatible with lazier arguments.

One way to mitigate both issues, is by introducing a $Lazy^*<b>$ type, that represents an operation which takes 0 or more big steps to arrive at a basic value of type $b$. This would immediately solve our function problem, and also make reassignments more explicit, since now the contract implies a change of state.

$Lazy^*$ plays well with reductions, rule $L^*-RT$ states that whenever we make one big step over a $Lazy^*$ expression, we get another expression of the same type. This makes sense since any expression in the language, including the resulting expression, will take 0 or more evaluation steps to reach a basic type. 

$Lazy^*$ also plays well with subtyping, from its definition follows that:

- $Int <: Lazy^*<Int>$ 
- $Lazy<Int> <: Lazy^*<Int>$
- $Lazy<Lazy<Int>> <: Lazy^*<Int>$

More generally, typing Rule $LL^*-ST$ formalizes this subtyping pattern for any type: If $\tau_1$ contains a basic type $\tau_2$, then $\tau_1 <: Lazy^*<\tau_2>$. This is because:

- If $\tau_1$ is a basic type, it's trivially a subtype of $Lazy^*<\tau_1>$
- If $\tau_1 = Lazy<Lazy<...<Lazy<b>>>>, then we have to do $n$ big steps to arrive to a basic type $b$, and thus, by definition $\tau_1 <: Lazy^*<b>$.
- If $\tau_1 = Lazy^*<b>$, then it's trivially a subtype by reflexivity.

Thus, we are able to express `f` as:

```
Lazy*<Int> -> Lazy*<Int> f := /. x : Lazy*<Int> => x.
Lazy*<Int> x0 := f(5);   // Allowed by subtyping
Lazy*<Int> x1 := f('5'); // Allowed by subtyping
Lazy*<Int> x2 := f(x1);  // Allowed!
```

As seen in these examples, $Lazy^*$ effectively hides everything but the basic type of an expression. In this way, it behaves as an existential type. Because of this, we include the rules $E-Pack-1$ and $E-Pack-2$, which  builds an existential triple from an expression a la Pierce. The triplet holds the wrapped value, the type of the wrapped value, and a way of forcefully evaluate the value to its basic type.

Due to the lack of existential types in Zilly. We do not provide a way to unpack values, rather, we rely on $feval-3$ to apply the wrapped force-evaluation function.

Finally, $E-Eval$ rule shows us that reducing an existential triplet is equivalent to unpacking it, applying one reduction, and packing it with the respective $feval$. 

There is one final detail to address. A $Lazy^*$ value is a triplet, thus, formally it cannot be a super-type of $5 : Int$, nor $'x' : Lazy<Int>$. Nevertheless, since both the type of the wrapped value and the force-eval function are uniquely determined by the value, we can safely work with subtyping by automatically injecting this values behind the scenes. This detail is not present in the operational semantics due to simplicity.


## Typing Rules


- EL: Provides a syntactic sugar to evaluating the 3 environments. We read $\varphi_{i,j,k} \vdash x : \tau [e]$, as:  the variable $x$ holds the expression $e$ of type $\tau$ in the context $\varphi_{i,j,k}$
- E-Abs: Classical lamba abstraction
- T-App: Classical type level lamba application.
- Defer: acts as a constructor for the $Lazy$ type, which models unreduced expressions.
- Formula: Formula only works on variables. Gets the contents of the variable WITHOUT applying any big steps to it.
- BT: The function $bt$ is used only on the formal semantics as a helper. It's a type-level function which returns the basic type of the argument.
- STR/STT/STA: Defines a **S**ub**T**ype relation which is **R**eflexive, **T**transitive, and **A**ntisimetric.
- F-ST: States the subtyping relation for functions as per usual: contra-variant over the argument and co-variant over the return.
- VL-ST: Any Basic type $\tau$ is subtype of  $Lazy<\tau>$. That is, any reduced expression can also be thought as a non-necessarily reduced expression.
- LL-ST: Every Lazy expression, is subtype of an even more lazy expression. That is, if a lazy expression $l$, can be reduced to a basic type in $n$ big steps, it can also be reduced to the same basic type in $n+1$ big steps.
- LL*-ST: Any type is a subtype of the $Lazy*$. We'll discuss what $Lazy*$ stands for in the next section.
- E-App: Classic function application.
- $\bot$: Zilly provides a bottom value which inhabits evert type for errors.
- Closure: All closures have the same type as the value they wrap.
- F-RT: Functions expressions are reduced to function expressions.
- I-RT: Integer values are reduced to integer values
- LN-RT: A value of type $Lazy<Lazy<\tau>>$ which can be reduced to a basic value in $n+1$ big steps, is reduced to a value of type $Lazy<\tau>$ which can be reduced to a basic type in $n$ big steps.
- L-RT: A value of type $Lazy<B>$ can be reduced to a basic type $B$ in exactly one big step.
- L*-RT: A value of type $Lazy*<\tau>$, which can originally be reduced to a basic type in zero or more steps, is reduced to a value of the same type.
- FE: $feval$ forcefully evaluates any expression to its basic type.

## Operational semantics of expressions

- BT-B:  The basic type of a basic type is itself.
- BT-LB: The basic type of $Lazy<B>$, is $B$.
- BT-LL: If we know that the basic type of $\tau_1$ is $\tau_2$, then it must also be the basic type for $Lazy<\tau_1>$.
- E-Int: Number literals are reduced to themselves.
- E-Fun: Function literals are reduced to a closure that contains themselves.
- E-FClosure: Function closures are reduced to themselves.
- feval-1: force evaluating an expression of a basic type, is the same as applying one big step to it.
- feval-2: force evaluating an unreduced expression is the same as applying one big step to it, and then force evaluating its result. Since there is no way of producing infinite-depth lazy expressions without falling into infinite recursion. $feval$ always ends on its input.
- Var-RValue: Notice that every variable is actually a reference. And notice that applying one big step to an expression can chance its result. Thus we define variable evaluation as looking up its content, and applying one big step to it.
- D-Eval: Evaluating a deferred expression yields a closure with its body. This is necessary due to possible scoping issues.
- C-Eval: Evaluating any NON-FUNCTION closure results in evaluating the wrapped expression over the wrapped contexts.
- F-eval: We defined the formula function as a lookup in the 3 environments.
- E-App: Function application is the same as in strict languages with object-reference passing: We apply one big step to both the function (to get a function closure) and the argument. And then, after allocating a new memory location, and assigning the variable argument to the formal argument, we apply one big step to the function body.
- Minus: Denotationally takes the difference of its arguments.
- Less-True, Less-False: Less returns 1 if the first value is less than the second one, else it returns -1.
- If-True, If-False: False classically defined.
- Subtype-Replace: Subtyping replacement classically defined.
 

## Operational semantics of actions


- Decl: Given that we can allocate a new memory location in our current environment, and bind the variable to the declared type, then we can reduce the body of the assignment using the new variable environment and typing environment, and the resulting expression in the Store environment. Notice that in order to accommodate recursion, we use the new variable and typing environment, thus bringing into scope $x$.
- Assign: Assignment works as declaration, without the need to evaluate its body using a new environment. This is because our LHS is already into scope.
- Seq: Sequencing is done carrying the newly generated contexts thought the whole program.