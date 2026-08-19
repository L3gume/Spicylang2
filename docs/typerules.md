# Type Unification Algorithm

```
unify(a: Monotype, b: Monotype) => Substitution:
    if a is typevar:
        if b is same typevar:
            return {}
        if b contains a:
            Error("infinite type")
        return {a |-> b}

    if b is typevar:
        return unify(b, a)

    if a & b both typefunvappl:
        if a & b have different type funcs:
            Error("Different functions")
        let S = {}
        for i in range(num of type func arguments):
            S = combine(S, unify(S(a.args[i]), S(b.args[i])))
        return S

    Error(?)
```

# Typing Rules

## Variable

```
    x : σ ∈ Γ      if variable x of polytype σ is in the typing context
  --------------   then
    Γ ⊢ x : σ      from Γ it follows that (⊢) x is of type σ
```

## Application

```
    Γ ⊢ e₀ : τₐ → τᵦ    Γ ⊢ e₁ : τₐ
  -----------------------------------
            Γ ⊢ e₀ e₁ : τᵦ
```

If it follows from Γ that e₀ is of polytype τₐ → τᵦ and e₁ is of polytype τₐ, then from Γ it follows that application of e₀ and e₁ is of polytype τᵦ.

## Abstraction

```
    Γ, x : τₐ ⊢ e : τᵦ
  ----------------------
    Γ ⊢ λx → e : τₐ → τᵦ
```

If it follows from the context plus a variable x of type τₐ that expression e has type τᵦ, then from the context it follows that function definition \x -> e defines a function of type τₐ → τᵦ.

## Let-binding

```
    Γ ⊢ e₀ : σ   Γ, x : σ ⊢ e₁ : τ
   --------------------------------
        Γ ⊢ let x = e₀ in e₁ : τ
```

If it follows from context that e₀ has type σ and if it also follows from context plus a variable x of type σ that expression e₁ has type τ, then it follows from context that expression `let x = e₀ in e₁` has type τ.

Let bindings have the type of the last expression.

Merlin's `let` is recursive: `x` is bound to a fresh type variable while `e₀` is checked, so `e₀` may itself reference `x`. The inferred type is then generalised and bound for `e₁` (see Generalisation).

## If-Then-Else

```
    Γ ⊢ e₀ : Bool    Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ
   ---------------------------------------------
           Γ ⊢ if e₀ then e₁ else e₂ : τ
```

If it follows from context Γ that e₀ has type Bool and that e₁ and e₂ have type τ, then it follows from context that expression `if e₀ then e₁ else e₂` has type τ.

## Literal

```
    ─────────────
    Γ ⊢ lit : τ(lit)
```

Where τ(lit) is the literal's fixed type — Int, Float, Bool, Str, or Unit. Literals are axioms: they contribute no premises and type independently of Γ. They constrain other rules by forcing unification with their concrete type.

## Arithmetic

```
    Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ
  ----------------------------
    Γ ⊢ e₁ ⊕ e₂ : τ   (⊕ ∈ {+, -, *, /, %})
```

Both operands unify to a common type τ, which is also the result type. For `+`, τ must be Int, Float, or Str (string `+` is concatenation); for `-`, `*`, `/`, `%`, τ must be Int or Float.

## Comparison

```
    Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ
  -----------------------------
    Γ ⊢ e₁ ⨝ e₂ : Bool   (⨝ ∈ {==, !=, <, >, <=, >=})
```

Both operands unify to a common type τ. For `==` and `!=`, τ must be Int, Float, Str, or Bool, and must not be a function type; for the ordering comparisons, τ must be Int or Float. The result is always Bool.

## Logical

```
    Γ ⊢ e₁ : Bool    Γ ⊢ e₂ : Bool
  -----------------------------------
    Γ ⊢ e₁ ∧ e₂ : Bool   (∧ ∈ {&&, ||})
```

Both operands must be Bool; the result is Bool.

## Unary

```
    Γ ⊢ e : τ
  --------------
    Γ ⊢ -e : τ    (τ is Int or Float)

    Γ ⊢ e : Bool
  ----------------
    Γ ⊢ !e : Bool
```

Unary negation `-` preserves the operand's numeric type (Int or Float); logical negation `!` requires and returns Bool.

## Block

```
    Γ₁ ⊢ s₁  Γ₂ ⊢ s₂  …  Γₙ ⊢ sₙ    Γₙ₊₁ ⊢ e : τ
  -------------------------------------------------
                 Γ₁ ⊢ { s₁ … sₙ e } : τ
```

A block is a sequence of statements followed by a final bare expression; its type is the type of that final expression. Each `let x = e` declaration is type-checked in order, binding the generalised type of `x` in the context for the rest of the block; plain expression statements are checked for their side effects and discard their type. Type declarations are not allowed inside blocks.

## List

```
    Γ ⊢ e₁ : τ  …  Γ ⊢ eₙ : τ
  ------------------------------
    Γ ⊢ [e₁, …, eₙ] : List τ

    ─────────────
    Γ ⊢ [] : List α    (α fresh)
```

A non-empty list's elements must all unify to a single element type τ, giving `List τ`. The empty list is polymorphic: it has type `List α` for a fresh type variable α, unified with whatever the context demands.

## Cons

```
    Γ ⊢ e₁ : τ    Γ ⊢ e₂ : List τ
  ----------------------------------
    Γ ⊢ e₁ :: e₂ : List τ
```

The cons operator `::` prepends an element of type τ to a list of type `List τ`, producing `List τ`.

## Match

```
  Γ ⊢ e : τ    Γ, p₁ ⊢ e₁ : σ    …    Γ, pₙ ⊢ eₙ : σ
  ------------------------------------------------------
    Γ ⊢ match e with p₁ => e₁ | … | pₙ => eₙ : σ
```

The scrutinee `e` is checked against τ, which is refined as the cases are matched (a `Cons` case pins τ to `List τ'`, a `List` case to its element type, a constructor application to its enum type). Each branch binds its pattern variables under the types induced by unifying the pattern with the current match type. All branches must unify to a single result type σ, and the patterns must be exhaustive over τ.

### Patterns

```
    ─────────────
    Γ ⊢ lit : τ    (pattern binds nothing)

    Γ ⊢ x : τ    (pattern binds x : τ)

    Γ ⊢ e₁ : τ    Γ ⊢ e₂ : List τ
  ----------------------------------
    Γ ⊢ e₁ :: e₂ : List τ

    Γ ⊢ C e₁ … eₙ : τ   (C is a constructor applied to patterns)

    Γ ⊢ e₁ : τ  …  Γ ⊢ eₙ : τ
  ------------------------------
    Γ ⊢ [e₁, …, eₙ] : List τ
```

A pattern is type-checked against the scrutinee's (refined) type τ. A literal pattern binds nothing and must unify with τ; a variable pattern binds the variable to τ; cons, list, and constructor-application patterns decompose τ structurally, binding their sub-pattern variables accordingly. Constructor patterns must apply a known constructor to the right number of pattern arguments.

## Instantiation

```
    Γ ⊢ e : σₐ    σₐ ⊑ σᵦ
  -----------------------
       Γ ⊢ e : σᵦ
```

If it follows from context that e has type σₐ and σₐ is more general than σᵦ, then it follows from context that e has type σᵦ.

For example: if e has type σₐ : ∀α. λInt → α and σᵦ : λInt → Bool, then e also has type λInt → Bool.

## Generalisation

```
    Γ ⊢ e : σ   α ∉ FV(Γ)
  -----------------------
       Γ ⊢ e : ∀α. σ
```

If it follows from context that expression e is of polytype σ and that type var α is not a free variable in the context, then it follows from context that expression e is of polytype ∀α. σ (this means α can be anything).
