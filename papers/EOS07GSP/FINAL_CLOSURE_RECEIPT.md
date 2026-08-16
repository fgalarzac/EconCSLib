+++
schema = 2
paper = "EOS07GSP"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-16"

[source_artifact]
path = "papers/EOS07GSP/EOS07GSP.txt"
sha256 = "9094a9c8cd917b728cf872b7741a4de9b5636c5cdadd08b7bfcc4b7c64df9cbc"

[statement_map]
path = "papers/EOS07GSP/audit/paper_statement_map.json"
sha256 = "6d031d10d7db5dc8564ffec6ea96364f709a35222f2b3a6602f403e600e62f4f"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "b43fceca640c939d7fea290ae454799518a038ca81ca02f04963a49c8bf32b78"

[review_ledger]
path = "papers/EOS07GSP/audit/direct_source_row_review.json"
sha256 = "14cfed640864ea2038380cdbd77c16c1da361efe5694c58d88974f86659bffa3"

[focused_build]
command = "lake build EOS07GSP"
target = "EOS07GSP"
result = "passed"
commit = "5b0858f2d2a9e9db87326c66fddc2627be8c1ed4"

[protocol]
formalization_review_protocol_sha256 = "e94b775a4b0bfdebe915ac7d0c13c414fad98036906876fb9239a7086c3cd805"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
