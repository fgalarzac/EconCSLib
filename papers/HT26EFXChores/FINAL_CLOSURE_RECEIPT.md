+++
schema = 3
paper = "HT26EFXChores"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-18"

[source_artifact]
path = "papers/HT26EFXChores/cited publication"
sha256 = "d6bb00d52184df636e5b690f5baa9da36aac2795b114cae10a113b5f32da9ba1"

[statement_map]
path = "papers/HT26EFXChores/audit/paper_statement_map.json"
sha256 = "03f563c4efb5c02bce3cfb8bd7b2415c718ca178bec4a9698162951d1f7ad526"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "d66f73d789f24110642e26082b6494fb18bce0696f8c53f7cc6473004fe3fff0"

[review_ledger]
path = "papers/HT26EFXChores/audit/v11_raw_source_spec_screening.json"
sha256 = "54a96aaff27b55069a9801774c4c719868b7ced3cc48d8327b98702dd9a82e6c"

[focused_build]
command = "lake build HT26EFXChores"
target = "HT26EFXChores"
result = "passed"
commit = "e8d9ba3d44bdae98bfa9739fe2b83569b792a131"

[focused_build_receipt]
path = "papers/HT26EFXChores/audit/FOCUSED_BUILD_RECEIPT.json"
sha256 = "24c1eac1f445f3d23875f7bd005e44d112cd183fbb7f0d83176a3598e2813181"

[protocol]
formalization_review_protocol_sha256 = "345e2b1c89c9ca81d8d51463fa57ad502450652e438ef4561cf76f9c5ca1fe09"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
