Thank you for your detailed comments.  We will incorporate
your suggestions regarding problem setup, related work, and
evaluation in our revision.

- Dealing with incorrect programs. (Reviewer-A)

As with other abductive mechanisms, our approach
seeks a lemma consistent with the library definitions
sufficient to imply a client post-condition.  Programs
with bugs, either in the library or client code, will
likely result in the algorithm exploring a potentially
infinite hypothesis space, since it cannot distinguish
whether a postulated lemma failed because it was too
weak, or the program or assertions were wrong.

- Difference between bad inputs and negative samples (Reviewer-B)

A "sample" (defined in Definition 3.5) is informally a model in SMT,
and this model can describe impossible to construct data that violates
the intended semantics of its constituent predicates.  In line 302,
the CEX is a negative sample, but it cannot be written as a "bad
input" since "These claims clearly violate the intended semantics of
member and hd; it should not be possible for s1 to have a head which
is not also a member."(line 311-313)." In other words, a negative
sample is an interpretation of predicates made by the underlying
solver that cannot be witnessed by any concrete input.

Simply observing positive ("good") inputs, ascribing bad inputs
as "true", does not solve the problem since the missing lemma cannot
be derived from simply observing positive runs.
