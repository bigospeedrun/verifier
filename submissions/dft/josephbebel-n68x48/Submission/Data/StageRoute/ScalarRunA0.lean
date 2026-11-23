import Submission.Data.StageRoute.Events
import Submission.Cert.Scalar.Skip
import Submission.Cert.Scalar.KernelRfl

-- Native-68 port of PR 209's ScalarRun (HalitZiyaKARTAL v7-42): one key chain; segments 1..50.
-- Segments use the zero-source skip (ScalarCheck.Skip) and state the run itself
-- (runPZ ... = some next checkpoint), proved by kernel_rfl.
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
kernel_rfl scalarSegA1 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg0 wrSA0 = some wrSA1
kernel_rfl scalarSegA2 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1 wrSA1 = some wrSA2
kernel_rfl scalarSegA3 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg2 wrSA2 = some wrSA3
kernel_rfl scalarSegA4 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg3 wrSA3 = some wrSA4
kernel_rfl scalarSegA5 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg4 wrSA4 = some wrSA5
kernel_rfl scalarSegA6 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg5 wrSA5 = some wrSA6
kernel_rfl scalarSegA7 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg6 wrSA6 = some wrSA7
kernel_rfl scalarSegA8 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg7 wrSA7 = some wrSA8
kernel_rfl scalarSegA9 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg8 wrSA8 = some wrSA9
kernel_rfl scalarSegA10 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg9 wrSA9 = some wrSA10
kernel_rfl scalarSegA11 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg10 wrSA10 = some wrSA11
kernel_rfl scalarSegA12 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg11 wrSA11 = some wrSA12
kernel_rfl scalarSegA13 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg12 wrSA12 = some wrSA13
kernel_rfl scalarSegA14 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg13 wrSA13 = some wrSA14
kernel_rfl scalarSegA15 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg14 wrSA14 = some wrSA15
kernel_rfl scalarSegA16 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg15 wrSA15 = some wrSA16
kernel_rfl scalarSegA17 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg16 wrSA16 = some wrSA17
kernel_rfl scalarSegA18 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg17 wrSA17 = some wrSA18
kernel_rfl scalarSegA19 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg18 wrSA18 = some wrSA19
kernel_rfl scalarSegA20 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg19 wrSA19 = some wrSA20
kernel_rfl scalarSegA21 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg20 wrSA20 = some wrSA21
kernel_rfl scalarSegA22 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg21 wrSA21 = some wrSA22
kernel_rfl scalarSegA23 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg22 wrSA22 = some wrSA23
kernel_rfl scalarSegA24 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg23 wrSA23 = some wrSA24
kernel_rfl scalarSegA25 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg24 wrSA24 = some wrSA25
kernel_rfl scalarSegA26 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg25 wrSA25 = some wrSA26
kernel_rfl scalarSegA27 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg26 wrSA26 = some wrSA27
kernel_rfl scalarSegA28 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg27 wrSA27 = some wrSA28
kernel_rfl scalarSegA29 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg28 wrSA28 = some wrSA29
kernel_rfl scalarSegA30 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg29 wrSA29 = some wrSA30
kernel_rfl scalarSegA31 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg30 wrSA30 = some wrSA31
kernel_rfl scalarSegA32 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg31 wrSA31 = some wrSA32
kernel_rfl scalarSegA33 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg32 wrSA32 = some wrSA33
kernel_rfl scalarSegA34 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg33 wrSA33 = some wrSA34
kernel_rfl scalarSegA35 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg34 wrSA34 = some wrSA35
kernel_rfl scalarSegA36 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg35 wrSA35 = some wrSA36
kernel_rfl scalarSegA37 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg36 wrSA36 = some wrSA37
kernel_rfl scalarSegA38 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg37 wrSA37 = some wrSA38
kernel_rfl scalarSegA39 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg38 wrSA38 = some wrSA39
kernel_rfl scalarSegA40 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg39 wrSA39 = some wrSA40
kernel_rfl scalarSegA41 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg40 wrSA40 = some wrSA41
kernel_rfl scalarSegA42 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg41 wrSA41 = some wrSA42
kernel_rfl scalarSegA43 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg42 wrSA42 = some wrSA43
kernel_rfl scalarSegA44 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg43 wrSA43 = some wrSA44
kernel_rfl scalarSegA45 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg44 wrSA44 = some wrSA45
kernel_rfl scalarSegA46 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg45 wrSA45 = some wrSA46
kernel_rfl scalarSegA47 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg46 wrSA46 = some wrSA47
kernel_rfl scalarSegA48 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg47 wrSA47 = some wrSA48
kernel_rfl scalarSegA49 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg48 wrSA48 = some wrSA49
kernel_rfl scalarSegA50 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg49 wrSA49 = some wrSA50
end StageRoute
