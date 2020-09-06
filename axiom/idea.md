## Samples

#### Data type instance representation

- [0], [1;2]...
- negative samples cannot be represented in this form.

#### Predicate representation

- the predicates representation of [0] is
  + member([0], u) = if u = 0 then true else false
  + order([0], u, v) = if u = 0 && v = 0 then true else false
- a counter-example generated from the SMT solver could be represented in this form

#### Quantifier-free vector representation

Assign value to $u$ and $v$, to make it as vector.

```
                         member(u)   member(v)   order(u, v)   order(v, u)   u = v
(l = [0], u = 0, v = 0)    true        true        true          true        true
(l = [0], u = 0, v = 1)    true        false       false         false       false
(l = [0], u = 1, v = 0)    false       true        false         false       false
(l = [0], u = 1, v = 1)    false       false       false         false       true
...
```

- One predicate representation can be converted to multiple vector representations.
- The counter-example generated from the SMT solver should indicate it satisfies the negation of post-condition under which $u$ and $v$.

- Assume the VC is:

```
(forall u v, 0 < u < 10 => l0: u -> (u + 1)) => (forall u, 0 < u < 10 => l --> u).
```

- Negation of the VC is:

```
(forall u v, 0 < u < 10 => l0: u -> (u + 1)) => exists u, 0 < u < 10 /\ ~ (l --> u).
```

- Then the SMT solver will provide the $u$ and corresponding $l$(in predicate representation).

```
u = 5;
l --> u:= if u = 5 then false else true
l: u -> v := true
```

- The vector representation:

```
                         member(u)   member(v)   order(u, v)   order(v, u)   u = v
(l = _, u = 5, v = 0)      false       true        true            ture      false
```

- Verctor representation is used as classification.
