import Submission.Cert.Label.Pack
import Submission.Data.StageRoute.Events

-- this submission: labelSeg30..39 of PR 209's LabelRun (HalitZiyaKARTAL v7-42), checked by the packed-state
-- label checker over the list of its scalar segments (WarpCheck.LabelPack.checkSegPL, sound for PR 209's checkSeg).
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
theorem labelSegP30 : WarpCheck.LabelPack.checkSegPL par qpar wt labL30 labS30 labS31 labR30 labN30 = true := by decide +kernel
theorem labL_eq30 : WarpCheck.LabelPack.joinR labL30 = labE30 := by delta labL30 labE30; rfl
theorem labelSeg30 : WarpCheck.checkSeg par wt labE30 labS30 labS31 labR30 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq30 labelSegP30
theorem labelSegP31 : WarpCheck.LabelPack.checkSegPL par qpar wt labL31 labS31 labS32 labR31 labN31 = true := by decide +kernel
theorem labL_eq31 : WarpCheck.LabelPack.joinR labL31 = labE31 := by delta labL31 labE31; rfl
theorem labelSeg31 : WarpCheck.checkSeg par wt labE31 labS31 labS32 labR31 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq31 labelSegP31
theorem labelSegP32 : WarpCheck.LabelPack.checkSegPL par qpar wt labL32 labS32 labS33 labR32 labN32 = true := by decide +kernel
theorem labL_eq32 : WarpCheck.LabelPack.joinR labL32 = labE32 := by delta labL32 labE32; rfl
theorem labelSeg32 : WarpCheck.checkSeg par wt labE32 labS32 labS33 labR32 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq32 labelSegP32
theorem labelSegP33 : WarpCheck.LabelPack.checkSegPL par qpar wt labL33 labS33 labS34 labR33 labN33 = true := by decide +kernel
theorem labL_eq33 : WarpCheck.LabelPack.joinR labL33 = labE33 := by delta labL33 labE33; rfl
theorem labelSeg33 : WarpCheck.checkSeg par wt labE33 labS33 labS34 labR33 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq33 labelSegP33
theorem labelSegP34 : WarpCheck.LabelPack.checkSegPL par qpar wt labL34 labS34 labS35 labR34 labN34 = true := by decide +kernel
theorem labL_eq34 : WarpCheck.LabelPack.joinR labL34 = labE34 := by delta labL34 labE34; rfl
theorem labelSeg34 : WarpCheck.checkSeg par wt labE34 labS34 labS35 labR34 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq34 labelSegP34
theorem labelSegP35 : WarpCheck.LabelPack.checkSegPL par qpar wt labL35 labS35 labS36 labR35 labN35 = true := by decide +kernel
theorem labL_eq35 : WarpCheck.LabelPack.joinR labL35 = labE35 := by delta labL35 labE35; rfl
theorem labelSeg35 : WarpCheck.checkSeg par wt labE35 labS35 labS36 labR35 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq35 labelSegP35
theorem labelSegP36 : WarpCheck.LabelPack.checkSegPL par qpar wt labL36 labS36 labS37 labR36 labN36 = true := by decide +kernel
theorem labL_eq36 : WarpCheck.LabelPack.joinR labL36 = labE36 := by delta labL36 labE36; rfl
theorem labelSeg36 : WarpCheck.checkSeg par wt labE36 labS36 labS37 labR36 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq36 labelSegP36
theorem labelSegP37 : WarpCheck.LabelPack.checkSegPL par qpar wt labL37 labS37 labS38 labR37 labN37 = true := by decide +kernel
theorem labL_eq37 : WarpCheck.LabelPack.joinR labL37 = labE37 := by delta labL37 labE37; rfl
theorem labelSeg37 : WarpCheck.checkSeg par wt labE37 labS37 labS38 labR37 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq37 labelSegP37
theorem labelSegP38 : WarpCheck.LabelPack.checkSegPL par qpar wt labL38 labS38 labS39 labR38 labN38 = true := by decide +kernel
theorem labL_eq38 : WarpCheck.LabelPack.joinR labL38 = labE38 := by delta labL38 labE38; rfl
theorem labelSeg38 : WarpCheck.checkSeg par wt labE38 labS38 labS39 labR38 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq38 labelSegP38
theorem labelSegP39 : WarpCheck.LabelPack.checkSegPL par qpar wt labL39 labS39 labS40 labR39 labN39 = true := by decide +kernel
theorem labL_eq39 : WarpCheck.LabelPack.joinR labL39 = labE39 := by delta labL39 labE39; rfl
theorem labelSeg39 : WarpCheck.checkSeg par wt labE39 labS39 labS40 labR39 = true :=
  WarpCheck.LabelPack.checkSegPL_sound tabN_ok rfl labL_eq39 labelSegP39
end StageRoute
