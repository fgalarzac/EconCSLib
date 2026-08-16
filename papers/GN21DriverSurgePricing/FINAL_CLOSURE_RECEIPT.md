+++
schema = 2
paper = "GN21DriverSurgePricing"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-16"

[source_artifact]
path = "papers/GN21DriverSurgePricing/source.txt"
sha256 = "6b6668553e576084e0c6c9995964252bed6b14aae113d6ce90f78538a7eb9889"

[statement_map]
path = "papers/GN21DriverSurgePricing/audit/paper_statement_map.json"
sha256 = "d7cf21f165b5c63635df570e39ddcb17ae83acfe83b139831327a8d15cd10b84"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "e4f9f62ed5f06b0eb2914ea4bd546533040e3dfaae97980fbab6b45d0feb6bad"

[review_ledger]
path = "papers/GN21DriverSurgePricing/audit/direct_source_row_review.json"
sha256 = "cf9558c9e2c93b19c7a5b1d5ffbb27af7180a23371850337ff0897f2a0fcd31e"

[focused_build]
command = "lake build GN21DriverSurgePricing"
target = "GN21DriverSurgePricing"
result = "passed"
commit = "5b0858f2d2a9e9db87326c66fddc2627be8c1ed4"

[protocol]
formalization_review_protocol_sha256 = "e94b775a4b0bfdebe915ac7d0c13c414fad98036906876fb9239a7086c3cd805"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
