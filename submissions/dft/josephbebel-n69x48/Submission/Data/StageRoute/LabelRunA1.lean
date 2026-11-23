import Submission.Cert.Label.Pack
import Submission.Data.StageRoute.Events

-- this submission: labelSeg10..19 of PR 209's LabelRun (HalitZiyaKARTAL v7-42), checked by the packed-state
-- label checker over the list of its scalar segments (WarpCheck.LabelPack.checkSegPL, sound for PR 209's checkSeg).
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
theorem labelSegP10 : WarpCheck.LabelPack.checkSegPL par qpar wt labL10 labS10 labS11 labR10 labN10 = true := by decide +kernel
theorem labL_eq10 : WarpCheck.LabelPack.joinR labL10 = labE10 := by delta labL10 labE10; rfl
theorem labelSeg10 : WarpCheck.checkSeg par wt labE10 labS10 labS11 labR10 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq10 labelSegP10
theorem labelSegP11 : WarpCheck.LabelPack.checkSegPL par qpar wt labL11 labS11 labS12 labR11 labN11 = true := by decide +kernel
theorem labL_eq11 : WarpCheck.LabelPack.joinR labL11 = labE11 := by delta labL11 labE11; rfl
theorem labelSeg11 : WarpCheck.checkSeg par wt labE11 labS11 labS12 labR11 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq11 labelSegP11
theorem labelSegP12 : WarpCheck.LabelPack.checkSegPL par qpar wt labL12 labS12 labS13 labR12 labN12 = true := by decide +kernel
theorem labL_eq12 : WarpCheck.LabelPack.joinR labL12 = labE12 := by delta labL12 labE12; rfl
theorem labelSeg12 : WarpCheck.checkSeg par wt labE12 labS12 labS13 labR12 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq12 labelSegP12
theorem labelSegP13 : WarpCheck.LabelPack.checkSegPL par qpar wt labL13 labS13 labS14 labR13 labN13 = true := by decide +kernel
theorem labL_eq13 : WarpCheck.LabelPack.joinR labL13 = labE13 := by delta labL13 labE13; rfl
theorem labelSeg13 : WarpCheck.checkSeg par wt labE13 labS13 labS14 labR13 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq13 labelSegP13
theorem labelSegP14 : WarpCheck.LabelPack.checkSegPL par qpar wt labL14 labS14 labS15 labR14 labN14 = true := by decide +kernel
theorem labL_eq14 : WarpCheck.LabelPack.joinR labL14 = labE14 := by delta labL14 labE14; rfl
theorem labelSeg14 : WarpCheck.checkSeg par wt labE14 labS14 labS15 labR14 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq14 labelSegP14
theorem labelSegP15 : WarpCheck.LabelPack.checkSegPL par qpar wt labL15 labS15 labS16 labR15 labN15 = true := by decide +kernel
theorem labL_eq15 : WarpCheck.LabelPack.joinR labL15 = labE15 := by delta labL15 labE15; rfl
theorem labelSeg15 : WarpCheck.checkSeg par wt labE15 labS15 labS16 labR15 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq15 labelSegP15
theorem labelSegP16 : WarpCheck.LabelPack.checkSegPL par qpar wt labL16 labS16 labS17 labR16 labN16 = true := by decide +kernel
theorem labL_eq16 : WarpCheck.LabelPack.joinR labL16 = labE16 := by delta labL16 labE16; rfl
theorem labelSeg16 : WarpCheck.checkSeg par wt labE16 labS16 labS17 labR16 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq16 labelSegP16
theorem labelSegP17 : WarpCheck.LabelPack.checkSegPL par qpar wt labL17 labS17 labS18 labR17 labN17 = true := by decide +kernel
theorem labL_eq17 : WarpCheck.LabelPack.joinR labL17 = labE17 := by delta labL17 labE17; rfl
theorem labelSeg17 : WarpCheck.checkSeg par wt labE17 labS17 labS18 labR17 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq17 labelSegP17
theorem labelSegP18 : WarpCheck.LabelPack.checkSegPL par qpar wt labL18 labS18 labS19 labR18 labN18 = true := by decide +kernel
theorem labL_eq18 : WarpCheck.LabelPack.joinR labL18 = labE18 := by delta labL18 labE18; rfl
theorem labelSeg18 : WarpCheck.checkSeg par wt labE18 labS18 labS19 labR18 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq18 labelSegP18
theorem labelSegP19 : WarpCheck.LabelPack.checkSegPL par qpar wt labL19 labS19 labS20 labR19 labN19 = true := by decide +kernel
theorem labL_eq19 : WarpCheck.LabelPack.joinR labL19 = labE19 := by delta labL19 labE19; rfl
theorem labelSeg19 : WarpCheck.checkSeg par wt labE19 labS19 labS20 labR19 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq19 labelSegP19
end StageRoute
