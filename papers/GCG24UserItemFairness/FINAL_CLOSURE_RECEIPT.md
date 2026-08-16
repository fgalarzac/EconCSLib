+++
schema = 2
paper = "GCG24UserItemFairness"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-16"

[source_artifact]
path = "papers/GCG24UserItemFairness/GCG24UserItemFairness.txt"
sha256 = "7a0981ed1c26b7e69886e093b37d24b7778a645fe205c301ee14928ddd9c81ea"

[statement_map]
path = "papers/GCG24UserItemFairness/audit/paper_statement_map.json"
sha256 = "bad5a12cd0e1e33efced2dd3e49e1f2c80a46092110f4552f7a1456e70d3fdee"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "8047841c9e70d59443e2af98480c296207c887b188508378c276002d9dca60fe"

[review_ledger]
path = "papers/GCG24UserItemFairness/audit/direct_source_row_review.json"
sha256 = "2c521149fe3c511b00c8974e3851d1ecdfa00ddab318228ee9ec7dc91d430094"

[focused_build]
command = "lake build GCG24UserItemFairness"
target = "GCG24UserItemFairness"
result = "passed"
commit = "5b0858f2d2a9e9db87326c66fddc2627be8c1ed4"

[protocol]
formalization_review_protocol_sha256 = "e94b775a4b0bfdebe915ac7d0c13c414fad98036906876fb9239a7086c3cd805"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
