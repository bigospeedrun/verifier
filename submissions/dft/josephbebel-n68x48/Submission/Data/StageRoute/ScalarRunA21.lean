import Submission.Data.StageRoute.Events
import Submission.Cert.Scalar.Skip
import Submission.Cert.Scalar.KernelRfl

-- Native-68 port of PR 209's ScalarRun (HalitZiyaKARTAL v7-42): one key chain; segments 1051..1100.
-- Segments use the zero-source skip (ScalarCheck.Skip) and state the run itself
-- (runPZ ... = some next checkpoint), proved by kernel_rfl.
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
kernel_rfl scalarSegA1051 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1050 wrSA1050 = some wrSA1051
kernel_rfl scalarSegA1052 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1051 wrSA1051 = some wrSA1052
kernel_rfl scalarSegA1053 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1052 wrSA1052 = some wrSA1053
kernel_rfl scalarSegA1054 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1053 wrSA1053 = some wrSA1054
kernel_rfl scalarSegA1055 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1054 wrSA1054 = some wrSA1055
kernel_rfl scalarSegA1056 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1055 wrSA1055 = some wrSA1056
kernel_rfl scalarSegA1057 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1056 wrSA1056 = some wrSA1057
kernel_rfl scalarSegA1058 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1057 wrSA1057 = some wrSA1058
kernel_rfl scalarSegA1059 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1058 wrSA1058 = some wrSA1059
kernel_rfl scalarSegA1060 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1059 wrSA1059 = some wrSA1060
kernel_rfl scalarSegA1061 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1060 wrSA1060 = some wrSA1061
kernel_rfl scalarSegA1062 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1061 wrSA1061 = some wrSA1062
kernel_rfl scalarSegA1063 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1062 wrSA1062 = some wrSA1063
kernel_rfl scalarSegA1064 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1063 wrSA1063 = some wrSA1064
kernel_rfl scalarSegA1065 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1064 wrSA1064 = some wrSA1065
kernel_rfl scalarSegA1066 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1065 wrSA1065 = some wrSA1066
kernel_rfl scalarSegA1067 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1066 wrSA1066 = some wrSA1067
kernel_rfl scalarSegA1068 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1067 wrSA1067 = some wrSA1068
kernel_rfl scalarSegA1069 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1068 wrSA1068 = some wrSA1069
kernel_rfl scalarSegA1070 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1069 wrSA1069 = some wrSA1070
kernel_rfl scalarSegA1071 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1070 wrSA1070 = some wrSA1071
kernel_rfl scalarSegA1072 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1071 wrSA1071 = some wrSA1072
kernel_rfl scalarSegA1073 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1072 wrSA1072 = some wrSA1073
kernel_rfl scalarSegA1074 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1073 wrSA1073 = some wrSA1074
kernel_rfl scalarSegA1075 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1074 wrSA1074 = some wrSA1075
kernel_rfl scalarSegA1076 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1075 wrSA1075 = some wrSA1076
kernel_rfl scalarSegA1077 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1076 wrSA1076 = some wrSA1077
kernel_rfl scalarSegA1078 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1077 wrSA1077 = some wrSA1078
kernel_rfl scalarSegA1079 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1078 wrSA1078 = some wrSA1079
kernel_rfl scalarSegA1080 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1079 wrSA1079 = some wrSA1080
kernel_rfl scalarSegA1081 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1080 wrSA1080 = some wrSA1081
kernel_rfl scalarSegA1082 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1081 wrSA1081 = some wrSA1082
kernel_rfl scalarSegA1083 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1082 wrSA1082 = some wrSA1083
kernel_rfl scalarSegA1084 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1083 wrSA1083 = some wrSA1084
kernel_rfl scalarSegA1085 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1084 wrSA1084 = some wrSA1085
kernel_rfl scalarSegA1086 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1085 wrSA1085 = some wrSA1086
kernel_rfl scalarSegA1087 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1086 wrSA1086 = some wrSA1087
kernel_rfl scalarSegA1088 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1087 wrSA1087 = some wrSA1088
kernel_rfl scalarSegA1089 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1088 wrSA1088 = some wrSA1089
kernel_rfl scalarSegA1090 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1089 wrSA1089 = some wrSA1090
kernel_rfl scalarSegA1091 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1090 wrSA1090 = some wrSA1091
kernel_rfl scalarSegA1092 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1091 wrSA1091 = some wrSA1092
kernel_rfl scalarSegA1093 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1092 wrSA1092 = some wrSA1093
kernel_rfl scalarSegA1094 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1093 wrSA1093 = some wrSA1094
kernel_rfl scalarSegA1095 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1094 wrSA1094 = some wrSA1095
kernel_rfl scalarSegA1096 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1095 wrSA1095 = some wrSA1096
kernel_rfl scalarSegA1097 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1096 wrSA1096 = some wrSA1097
kernel_rfl scalarSegA1098 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1097 wrSA1097 = some wrSA1098
kernel_rfl scalarSegA1099 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1098 wrSA1098 = some wrSA1099
kernel_rfl scalarSegA1100 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1099 wrSA1099 = some wrSA1100
end StageRoute
