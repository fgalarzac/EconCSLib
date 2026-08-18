# Source Clarification: Stability in Sections 4--5

## Reading used for Theorem 2

The page-10 displayed definition identifies one way an assignment can be
unstable: a college can replace one currently assigned applicant with another
who is preferred by both that college and the applicant. That displayed
condition is formalized literally as its own paper claim.

For the Section 4 waiting-list procedure and Theorem 2, “stable assignment” is
read in the completed operational sense used by the procedure: the final
assignment respects college quotas, assigns only acceptable pairs, and has no
applicant-college block. A block can arise when an acceptable applicant is
unmatched or prefers a college and that college either has an open seat or
prefers the applicant to a current assignee.

This reading follows the Section 4 account of applications, waiting lists,
rejections, and the terminal assignment, together with Section 5's comparison
of that assignment to every other stable assignment. It is a clarification of
which stability notion those sections use; it does not alter the literal scope
of the earlier displayed definition.

## Preference representation

The source expresses acceptability and strict preferences as lists rather than
numbers.  The formal model uses an order-preserving numerical representation:
positive values are names on an acceptable list, negative values are omitted
names, and zero is the outside option for an unmatched applicant.  This fixes
only a convenient representation of the source's comparison “at least as well
off”; it does not add a cardinal-utility claim.  The full `Spec` states this
normalization explicitly through the eligibility, individual-rationality, and
comparison clauses, and the packet separately presents the library definition
of the outside-option evaluator.

## Source locations

- Page 10, displayed definitions of unstable and optimal assignments.
- Printed pages 13--14, Sections 4--5 and Theorem 2.
- Printed page 9, Section 2's preference lists and the willingness convention.
