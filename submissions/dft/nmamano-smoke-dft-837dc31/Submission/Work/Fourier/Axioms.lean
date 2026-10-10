import Submission.Work.Fourier.Main

/-! Axiom report for the every-length Fourier theorems at our exponent (nothing is proved here). -/

#print axioms OAI.PowerSaving.transform_mainZ
#print axioms OAI.PowerSaving.convolution_mainZ
#print axioms OAI.PowerSaving.transform_main_orderZ
#print axioms OAI.PowerSaving.convolution_main_orderZ
#print axioms OAI.PowerSaving.RAM.hillsZ_program
#print OAI.PowerSaving.decimalExponentZ
#print OAI.PowerSaving.alphaZ
#check (OAI.PowerSaving.transform_mainZ : OAI.PowerSaving.DFTGoalZ)
#check (OAI.PowerSaving.convolution_mainZ : OAI.PowerSaving.ConvGoalZ)
