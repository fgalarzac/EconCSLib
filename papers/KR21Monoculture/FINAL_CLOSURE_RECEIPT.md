+++
schema = 2
paper = "KR21Monoculture"
closure_status = "current"
evidence_lane = "direct-source-row-review"
closed_at = "2026-08-16"

[source_artifact]
path = "papers/KR21Monoculture/sources/2101.05853.txt"
sha256 = "aed647e81248dd53a36395cbaef93a343a9b6a8a525da05f3dcd06662384fb23"

[statement_map]
path = "papers/KR21Monoculture/audit/paper_statement_map.json"
sha256 = "cb1703dea8623ac773ad63c4476168327c484d82350fd4577d1a72d6513bee2c"

[paper_interface_closure]
root = "PaperInterface.lean"
sha256 = "d7ce0f7af3d97a87eed6081e4114213496de92a2dc48727169ab13f7e64e52f9"

[review_ledger]
path = "papers/KR21Monoculture/audit/direct_source_row_review.json"
sha256 = "6955826ec338a2440388a22abcb2c6c508f5c96b139efc2157b183b218bb5d74"

[focused_build]
command = "env LEAN_NUM_THREADS=1 lake build KR21Monoculture"
target = "KR21Monoculture"
result = "passed"
commit = "5b0858f2d2a9e9db87326c66fddc2627be8c1ed4"

[protocol]
formalization_review_protocol_sha256 = "e94b775a4b0bfdebe915ac7d0c13c414fad98036906876fb9239a7086c3cd805"

+++

# Final Closure Receipt

This receipt binds the current final-closeout inputs. See the pinned review ledger for the source-row reasoning.
