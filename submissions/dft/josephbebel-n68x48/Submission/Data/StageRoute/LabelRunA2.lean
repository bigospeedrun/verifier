import Submission.Cert.Label.Pack
import Submission.Data.StageRoute.Events

-- this submission: labelSeg20..29 of PR 209's LabelRun (HalitZiyaKARTAL v7-42), checked by the packed-state
-- label checker over the list of its scalar segments (WarpCheck.LabelPack.checkSegPL, sound for PR 209's checkSeg).
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
theorem labelSegP20 : WarpCheck.LabelPack.checkSegPL par qpar wt labL20 labS20 labS21 labR20 labN20 = true := by decide +kernel
theorem labL_eq20 : WarpCheck.LabelPack.joinR labL20 = labE20 := by delta labL20 labE20; rfl
theorem labelSeg20 : WarpCheck.checkSeg par wt labE20 labS20 labS21 labR20 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq20 labelSegP20
theorem labelSegP21 : WarpCheck.LabelPack.checkSegPL par qpar wt labL21 labS21 labS22 labR21 labN21 = true := by decide +kernel
theorem labL_eq21 : WarpCheck.LabelPack.joinR labL21 = labE21 := by delta labL21 labE21; rfl
theorem labelSeg21 : WarpCheck.checkSeg par wt labE21 labS21 labS22 labR21 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq21 labelSegP21
theorem labelSegP22 : WarpCheck.LabelPack.checkSegPL par qpar wt labL22 labS22 labS23 labR22 labN22 = true := by decide +kernel
theorem labL_eq22 : WarpCheck.LabelPack.joinR labL22 = labE22 := by delta labL22 labE22; rfl
theorem labelSeg22 : WarpCheck.checkSeg par wt labE22 labS22 labS23 labR22 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq22 labelSegP22
theorem labelSegP23 : WarpCheck.LabelPack.checkSegPL par qpar wt labL23 labS23 labS24 labR23 labN23 = true := by decide +kernel
theorem labL_eq23 : WarpCheck.LabelPack.joinR labL23 = labE23 := by delta labL23 labE23; rfl
theorem labelSeg23 : WarpCheck.checkSeg par wt labE23 labS23 labS24 labR23 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq23 labelSegP23
theorem labelSegP24 : WarpCheck.LabelPack.checkSegPL par qpar wt labL24 labS24 labS25 labR24 labN24 = true := by decide +kernel
theorem labL_eq24 : WarpCheck.LabelPack.joinR labL24 = labE24 := by delta labL24 labE24; rfl
theorem labelSeg24 : WarpCheck.checkSeg par wt labE24 labS24 labS25 labR24 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq24 labelSegP24
theorem labelSegP25 : WarpCheck.LabelPack.checkSegPL par qpar wt labL25 labS25 labS26 labR25 labN25 = true := by decide +kernel
theorem labL_eq25 : WarpCheck.LabelPack.joinR labL25 = labE25 := by delta labL25 labE25; rfl
theorem labelSeg25 : WarpCheck.checkSeg par wt labE25 labS25 labS26 labR25 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq25 labelSegP25
theorem labelSegP26 : WarpCheck.LabelPack.checkSegPL par qpar wt labL26 labS26 labS27 labR26 labN26 = true := by decide +kernel
theorem labL_eq26 : WarpCheck.LabelPack.joinR labL26 = labE26 := by delta labL26 labE26; rfl
theorem labelSeg26 : WarpCheck.checkSeg par wt labE26 labS26 labS27 labR26 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq26 labelSegP26
theorem labelSegP27 : WarpCheck.LabelPack.checkSegPL par qpar wt labL27 labS27 labS28 labR27 labN27 = true := by decide +kernel
theorem labL_eq27 : WarpCheck.LabelPack.joinR labL27 = labE27 := by delta labL27 labE27; rfl
theorem labelSeg27 : WarpCheck.checkSeg par wt labE27 labS27 labS28 labR27 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq27 labelSegP27
theorem labelSegP28 : WarpCheck.LabelPack.checkSegPL par qpar wt labL28 labS28 labS29 labR28 labN28 = true := by decide +kernel
theorem labL_eq28 : WarpCheck.LabelPack.joinR labL28 = labE28 := by delta labL28 labE28; rfl
theorem labelSeg28 : WarpCheck.checkSeg par wt labE28 labS28 labS29 labR28 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq28 labelSegP28
theorem labelSegP29 : WarpCheck.LabelPack.checkSegPL par qpar wt labL29 labS29 labS30 labR29 labN29 = true := by decide +kernel
theorem labL_eq29 : WarpCheck.LabelPack.joinR labL29 = labE29 := by delta labL29 labE29; rfl
theorem labelSeg29 : WarpCheck.checkSeg par wt labE29 labS29 labS30 labR29 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq29 labelSegP29
end StageRoute
