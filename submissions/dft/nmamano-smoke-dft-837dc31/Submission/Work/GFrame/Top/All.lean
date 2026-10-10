import Submission.Work.GFrame.Top.Flag
import Submission.Work.GFrame.Top.Stage
import Submission.Work.GFrame.Engine.Twisted
import Submission.Work.GFrame.Labels.All
import Submission.Work.GFrame.Clifford.Step

/-!
# GFrame (key: eng-integrate): everything together

One import for the whole GFrame development (ENGINE 13 modules, CLIFFORD 14, LABELS 19, TOP 8):
checks that all of it loads together without a name clash and prints the axioms of the
assembled theorems.  No `sorry`.
-/

#print axioms OAI.PowerSaving.GF.gcert_of_sched
#print axioms OAI.PowerSaving.RAM.engine_program_gsched
#print axioms OAI.PowerSaving.RAM.engine_program_groute
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_gsched
#print axioms OAI.PowerSaving.RAM.engine_program_bsched
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_bsched
#print axioms OAI.PowerSaving.GF.gcert_through_submodule
#print axioms OAI.PowerSaving.GF.gsstage
#print axioms OAI.PowerSaving.RAM.engine_program_g_costR
#print axioms OAI.PowerSaving.RAM.engine_program_ggroup_list
#print axioms OAI.PowerSaving.RAM.GRig.open_tblock
#print axioms OAI.PowerSaving.GF.frame_lemma
#print axioms OAI.PowerSaving.GF.cross_lemma
#print axioms OAI.PowerSaving.GF.rep_change
#print axioms OAI.PowerSaving.GF.alt_block
#print axioms OAI.PowerSaving.GF.bsched_groute_full
#print axioms OAI.PowerSaving.GF.asched_groute
#print axioms OAI.PowerSaving.GF.sched_route_any
