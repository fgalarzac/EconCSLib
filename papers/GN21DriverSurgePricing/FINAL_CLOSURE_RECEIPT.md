+++
schema = 2
paper = "GN21DriverSurgePricing"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-18"

[source_artifact]
path = "papers/GN21DriverSurgePricing/cited publication"
sha256 = "6b6668553e576084e0c6c9995964252bed6b14aae113d6ce90f78538a7eb9889"

[statement_map]
path = "papers/GN21DriverSurgePricing/audit/paper_statement_map.json"
sha256 = "add3b00e8099d392433825b8ed7cee7e3b5f18cf05983ca14c7bb06c2a8c4e31"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "30908d90b93057a917d3ac76e7c2b52a8c58bee7c24e682d8164b40e64ab4781"

[review_ledger]
path = "papers/GN21DriverSurgePricing/audit/v11_raw_source_spec_screening.json"
sha256 = "e833b407e935fb8134982e39c0c73ff49d0907e368b1b828cc9e12b51a50cadb"

[focused_build]
command = "lake build GN21DriverSurgePricing"
target = "GN21DriverSurgePricing"
result = "passed"
commit = "bcf78eb32bf2c4cda5a1b56c360963fbdbaedd9f"

[protocol]
formalization_review_protocol_sha256 = "345e2b1c89c9ca81d8d51463fa57ad502450652e438ef4561cf76f9c5ca1fe09"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
