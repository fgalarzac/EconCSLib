+++
schema = 3
paper = "GS62CollegeAdmissions"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-18"

[source_artifact]
path = "papers/GS62CollegeAdmissions/cited publication"
sha256 = "159e8d7735c826a6725bcbe41370aa4f87c3d30bf9d55aa87a0a00b23cfd615d"

[statement_map]
path = "papers/GS62CollegeAdmissions/audit/paper_statement_map.json"
sha256 = "c48ddc877a39cb440bb78b3c4e6bc98c98bfde4ac508f9acf077057d1adaabbd"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "3ef0b8b207b71bcad24bb61393413c9681cfbaaf00804efff9f943ac37dbdb93"

[review_ledger]
path = "papers/GS62CollegeAdmissions/audit/v11_raw_source_spec_screening.json"
sha256 = "a92f73030da752d545776fb44753b225a8e8bd3578fc76543e336bcbc9063f5e"

[focused_build]
command = "lake build GS62CollegeAdmissions"
target = "GS62CollegeAdmissions"
result = "passed"
commit = "e8d9ba3d44bdae98bfa9739fe2b83569b792a131"

[focused_build_receipt]
path = "papers/GS62CollegeAdmissions/audit/FOCUSED_BUILD_RECEIPT.json"
sha256 = "96ab4c77ac3f781c7f7a95a97a8267e10abc93dcaadf5ac04b1a237e1d992a90"

[protocol]
formalization_review_protocol_sha256 = "345e2b1c89c9ca81d8d51463fa57ad502450652e438ef4561cf76f9c5ca1fe09"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
