
We thank the reviewers for their detailed comments; we look forward to integrating their feedback into future versions of the paper.

It is clear from the reviews that there is skepticism with several aspects of our problem setup, particularly the assumption that we only have incomplete specifications of library methods and the need to manually verify inferred lemmas in order to have a complete verification story. There was also concern that our evaluation only involved correct programs and valid inferred lemmas. We plan to further refine our problem setup and to include buggy programs and invalid inferred lemmas in subsequent iterations of the paper.

We would also like to clarify a couple of specific points raised by the reviewers:
Q: What is the difference between negative samples and bad inputs (Reviewer B)?
A: Samples (Definition 3.5) are SMT models. These models can correspond to impossible data values which violate the intended semantics of predicates. The set of such samples is larger than data in other data-driven methods. Concretely, in the paragraph on line 302, the CEX is the negative sample, but it is not a "bad input" as "These claims clearly violate the intended semantics of member and hd; it should not be possible for s1 to have a head which is not also a member."(line 311-313). There doesn’t exist a list value consistent with this CEX, thus there is not a "input" on which to run the program.
