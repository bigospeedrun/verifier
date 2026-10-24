-- Independent extraction probe (auditor-written; not part of the audited source).
-- Imports the freshly compiled Snaky oleans and prints the two audited
-- theorems' types and axiom dependencies for comparison against the
-- author's recorded kernel-audit.json.
import Snaky.Result19

#check @Snaky.snaky_wins_plane_in_19
#check @Snaky.snaky_wins_17x17_in_19
#print axioms Snaky.snaky_wins_plane_in_19
#print axioms Snaky.snaky_wins_17x17_in_19
