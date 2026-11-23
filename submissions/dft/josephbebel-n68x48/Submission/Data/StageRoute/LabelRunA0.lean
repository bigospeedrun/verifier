import Submission.Cert.Label.Pack
import Submission.Data.StageRoute.Events

-- this submission: labelSeg0..9 of PR 209's LabelRun (HalitZiyaKARTAL v7-42), checked by the packed-state
-- label checker over the list of its scalar segments (WarpCheck.LabelPack.checkSegPL, sound for PR 209's checkSeg).
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
theorem labelSegP0 : WarpCheck.LabelPack.checkSegPL par qpar wt labL0 labS0 labS1 labR0 labN0 = true := by decide +kernel
theorem labL_eq0 : WarpCheck.LabelPack.joinR labL0 = labE0 := by delta labL0 labE0; rfl
theorem labelSeg0 : WarpCheck.checkSeg par wt labE0 labS0 labS1 labR0 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq0 labelSegP0
theorem labelSegP1 : WarpCheck.LabelPack.checkSegPL par qpar wt labL1 labS1 labS2 labR1 labN1 = true := by decide +kernel
theorem labL_eq1 : WarpCheck.LabelPack.joinR labL1 = labE1 := by delta labL1 labE1; rfl
theorem labelSeg1 : WarpCheck.checkSeg par wt labE1 labS1 labS2 labR1 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq1 labelSegP1
theorem labelSegP2 : WarpCheck.LabelPack.checkSegPL par qpar wt labL2 labS2 labS3 labR2 labN2 = true := by decide +kernel
theorem labL_eq2 : WarpCheck.LabelPack.joinR labL2 = labE2 := by delta labL2 labE2; rfl
theorem labelSeg2 : WarpCheck.checkSeg par wt labE2 labS2 labS3 labR2 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq2 labelSegP2
theorem labelSegP3 : WarpCheck.LabelPack.checkSegPL par qpar wt labL3 labS3 labS4 labR3 labN3 = true := by decide +kernel
theorem labL_eq3 : WarpCheck.LabelPack.joinR labL3 = labE3 := by delta labL3 labE3; rfl
theorem labelSeg3 : WarpCheck.checkSeg par wt labE3 labS3 labS4 labR3 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq3 labelSegP3
theorem labelSegP4 : WarpCheck.LabelPack.checkSegPL par qpar wt labL4 labS4 labS5 labR4 labN4 = true := by decide +kernel
theorem labL_eq4 : WarpCheck.LabelPack.joinR labL4 = labE4 := by delta labL4 labE4; rfl
theorem labelSeg4 : WarpCheck.checkSeg par wt labE4 labS4 labS5 labR4 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq4 labelSegP4
theorem labelSegP5 : WarpCheck.LabelPack.checkSegPL par qpar wt labL5 labS5 labS6 labR5 labN5 = true := by decide +kernel
theorem labL_eq5 : WarpCheck.LabelPack.joinR labL5 = labE5 := by delta labL5 labE5; rfl
theorem labelSeg5 : WarpCheck.checkSeg par wt labE5 labS5 labS6 labR5 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq5 labelSegP5
theorem labelSegP6 : WarpCheck.LabelPack.checkSegPL par qpar wt labL6 labS6 labS7 labR6 labN6 = true := by decide +kernel
theorem labL_eq6 : WarpCheck.LabelPack.joinR labL6 = labE6 := by delta labL6 labE6; rfl
theorem labelSeg6 : WarpCheck.checkSeg par wt labE6 labS6 labS7 labR6 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq6 labelSegP6
theorem labelSegP7 : WarpCheck.LabelPack.checkSegPL par qpar wt labL7 labS7 labS8 labR7 labN7 = true := by decide +kernel
theorem labL_eq7 : WarpCheck.LabelPack.joinR labL7 = labE7 := by delta labL7 labE7; rfl
theorem labelSeg7 : WarpCheck.checkSeg par wt labE7 labS7 labS8 labR7 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq7 labelSegP7
theorem labelSegP8 : WarpCheck.LabelPack.checkSegPL par qpar wt labL8 labS8 labS9 labR8 labN8 = true := by decide +kernel
theorem labL_eq8 : WarpCheck.LabelPack.joinR labL8 = labE8 := by delta labL8 labE8; rfl
theorem labelSeg8 : WarpCheck.checkSeg par wt labE8 labS8 labS9 labR8 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq8 labelSegP8
theorem labelSegP9 : WarpCheck.LabelPack.checkSegPL par qpar wt labL9 labS9 labS10 labR9 labN9 = true := by decide +kernel
theorem labL_eq9 : WarpCheck.LabelPack.joinR labL9 = labE9 := by delta labL9 labE9; rfl
theorem labelSeg9 : WarpCheck.checkSeg par wt labE9 labS9 labS10 labR9 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq9 labelSegP9
end StageRoute
