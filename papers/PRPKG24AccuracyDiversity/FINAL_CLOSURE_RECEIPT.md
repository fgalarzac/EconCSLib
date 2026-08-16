+++
schema = 2
paper = "PRPKG24AccuracyDiversity"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-16"

[source_artifact]
path = "papers/PRPKG24AccuracyDiversity/PRPKG24AccuracyDiversity.txt"
sha256 = "4dd55b1445de448e81d5494fbf9bafe4aac3f8c59f0ee62dac00aa1345dc4830"

[statement_map]
path = "papers/PRPKG24AccuracyDiversity/audit/paper_statement_map.json"
sha256 = "39d589e2c195cc62743003368a4840f4ba19a63be97896bedd3b339833b0022e"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "6cfc7b5a79824d25e72b11270416f82eecfde84815dfe8e9021350550f3eb343"

[review_ledger]
path = "papers/PRPKG24AccuracyDiversity/audit/direct_source_row_review.json"
sha256 = "9409b70b0255b8b6a064e29e3782df273f7056cbee654c0980cdcded5f7deaef"

[focused_build]
command = "lake build PRPKG24AccuracyDiversity"
target = "PRPKG24AccuracyDiversity"
result = "passed"
commit = "5b0858f2d2a9e9db87326c66fddc2627be8c1ed4"

[protocol]
formalization_review_protocol_sha256 = "e94b775a4b0bfdebe915ac7d0c13c414fad98036906876fb9239a7086c3cd805"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
