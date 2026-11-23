import Submission.Data.StageRoute.Events
import Submission.Cert.Scalar.Skip
import Submission.Cert.Scalar.KernelRfl

-- Native-68 port of PR 209's ScalarRun (HalitZiyaKARTAL v7-42): one key chain; segments 1001..1050.
-- Segments use the zero-source skip (ScalarCheck.Skip) and state the run itself
-- (runPZ ... = some next checkpoint), proved by kernel_rfl.
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
kernel_rfl scalarSegA1001 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1000 wrSA1000 = some wrSA1001
kernel_rfl scalarSegA1002 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1001 wrSA1001 = some wrSA1002
kernel_rfl scalarSegA1003 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1002 wrSA1002 = some wrSA1003
kernel_rfl scalarSegA1004 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1003 wrSA1003 = some wrSA1004
kernel_rfl scalarSegA1005 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1004 wrSA1004 = some wrSA1005
kernel_rfl scalarSegA1006 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1005 wrSA1005 = some wrSA1006
kernel_rfl scalarSegA1007 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1006 wrSA1006 = some wrSA1007
kernel_rfl scalarSegA1008 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1007 wrSA1007 = some wrSA1008
kernel_rfl scalarSegA1009 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1008 wrSA1008 = some wrSA1009
kernel_rfl scalarSegA1010 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1009 wrSA1009 = some wrSA1010
kernel_rfl scalarSegA1011 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1010 wrSA1010 = some wrSA1011
kernel_rfl scalarSegA1012 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1011 wrSA1011 = some wrSA1012
kernel_rfl scalarSegA1013 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1012 wrSA1012 = some wrSA1013
kernel_rfl scalarSegA1014 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1013 wrSA1013 = some wrSA1014
kernel_rfl scalarSegA1015 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1014 wrSA1014 = some wrSA1015
kernel_rfl scalarSegA1016 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1015 wrSA1015 = some wrSA1016
kernel_rfl scalarSegA1017 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1016 wrSA1016 = some wrSA1017
kernel_rfl scalarSegA1018 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1017 wrSA1017 = some wrSA1018
kernel_rfl scalarSegA1019 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1018 wrSA1018 = some wrSA1019
kernel_rfl scalarSegA1020 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1019 wrSA1019 = some wrSA1020
kernel_rfl scalarSegA1021 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1020 wrSA1020 = some wrSA1021
kernel_rfl scalarSegA1022 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1021 wrSA1021 = some wrSA1022
kernel_rfl scalarSegA1023 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1022 wrSA1022 = some wrSA1023
kernel_rfl scalarSegA1024 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1023 wrSA1023 = some wrSA1024
kernel_rfl scalarSegA1025 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1024 wrSA1024 = some wrSA1025
kernel_rfl scalarSegA1026 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1025 wrSA1025 = some wrSA1026
kernel_rfl scalarSegA1027 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1026 wrSA1026 = some wrSA1027
kernel_rfl scalarSegA1028 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1027 wrSA1027 = some wrSA1028
kernel_rfl scalarSegA1029 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1028 wrSA1028 = some wrSA1029
kernel_rfl scalarSegA1030 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1029 wrSA1029 = some wrSA1030
kernel_rfl scalarSegA1031 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1030 wrSA1030 = some wrSA1031
kernel_rfl scalarSegA1032 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1031 wrSA1031 = some wrSA1032
kernel_rfl scalarSegA1033 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1032 wrSA1032 = some wrSA1033
kernel_rfl scalarSegA1034 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1033 wrSA1033 = some wrSA1034
kernel_rfl scalarSegA1035 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1034 wrSA1034 = some wrSA1035
kernel_rfl scalarSegA1036 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1035 wrSA1035 = some wrSA1036
kernel_rfl scalarSegA1037 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1036 wrSA1036 = some wrSA1037
kernel_rfl scalarSegA1038 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1037 wrSA1037 = some wrSA1038
kernel_rfl scalarSegA1039 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1038 wrSA1038 = some wrSA1039
kernel_rfl scalarSegA1040 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1039 wrSA1039 = some wrSA1040
kernel_rfl scalarSegA1041 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1040 wrSA1040 = some wrSA1041
kernel_rfl scalarSegA1042 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1041 wrSA1041 = some wrSA1042
kernel_rfl scalarSegA1043 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1042 wrSA1042 = some wrSA1043
kernel_rfl scalarSegA1044 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1043 wrSA1043 = some wrSA1044
kernel_rfl scalarSegA1045 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1044 wrSA1044 = some wrSA1045
kernel_rfl scalarSegA1046 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1045 wrSA1045 = some wrSA1046
kernel_rfl scalarSegA1047 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1046 wrSA1046 = some wrSA1047
kernel_rfl scalarSegA1048 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1047 wrSA1047 = some wrSA1048
kernel_rfl scalarSegA1049 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1048 wrSA1048 = some wrSA1049
kernel_rfl scalarSegA1050 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1049 wrSA1049 = some wrSA1050
end StageRoute
