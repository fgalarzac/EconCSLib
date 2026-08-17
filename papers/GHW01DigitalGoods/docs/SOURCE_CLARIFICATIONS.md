# Source Clarifications: Competitive Auctions and Digital Goods

This note states the current mathematical readings used for the formalized
results. It does not assert that every condition below appears verbatim in the
preliminary conference version.

## Logarithmic domains

The logarithmic lower bounds require nondegenerate domains:

- Theorem 4.1 uses `h >= 2`.
- Corollary 4.2 uses at least two bidders.
- Theorem 7.1 and the lower-bound clause of Theorem 7.2 use `h >= 2`.

At the excluded boundaries, the displayed logarithmic denominators vanish or
do not support the asserted real-valued bound. These are clarifications of the
intended nondegenerate regime and preserve the stated rates there.

## Lemma 8.1 and Theorem 8.2

The preliminary cross-bidder inference in Lemma 8.1 does not follow from
ordinary truthfulness alone: truthfulness controls a bidder's response to that
bidder's own report, not outcomes for two different bidders in one profile.

The formalized result uses the later journal monotone-offer condition. If
`b_i <= b_j` and `x <= b_i`, the probability that bidder `i` receives and can
accept an offer at price at most `x` is no larger than the corresponding
probability for bidder `j`. Under that condition, the Lemma 8.1 comparison and
the Theorem 8.2 revenue conclusion hold. The formalized Theorem 8.2 is stated
for finite randomized offers; it does not claim that finiteness is wording of
the journal theorem.

These are source corrections for Lemma 8.1 and Theorem 8.2, not caveats about
the corrected results.
