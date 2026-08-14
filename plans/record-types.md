# Record type plan

## Syntax

Declaration of record type looks like this:

```
record <name>[( <type vars> )] = {
    <field1> : <type>,
    ...
    <fieldn> : <type>
};
```

Initialization and access to record field looks like:

```
let rec = record { foo: 1 };
let field = rec.foo;
```

Record fields are ALWAYS immutable, to get a modified record, use with-expression:

```
let rec = recname { foo: 1, bar: "baz" };
let mod_rec = rec with { foo: 42 };
```

Pattern matching over records must be done on all fields:

```
match rec
| { foo: 1, bar: val } => val # structural match with optional binding on fields
# ~or~
| boundrec => boundrec.bar # bind whole struct to variable
```

## Polymorphic Records

Type variables can be used in record declarations to make polymorphic records:

```
record poly_option_box('a) = {
    boxed : Option 'a
};
```
