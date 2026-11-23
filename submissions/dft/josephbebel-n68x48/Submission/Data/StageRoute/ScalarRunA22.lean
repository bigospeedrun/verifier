import Submission.Data.StageRoute.Events
import Submission.Cert.Scalar.Skip
import Submission.Cert.Scalar.KernelRfl

-- Native-68 port of PR 209's ScalarRun (HalitZiyaKARTAL v7-42): one key chain; segments 1101..1150.
-- Segments use the zero-source skip (ScalarCheck.Skip) and state the run itself
-- (runPZ ... = some next checkpoint), proved by kernel_rfl.
set_option maxRecDepth 100000
set_option Elab.async false
namespace StageRoute
kernel_rfl scalarSegA1101 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1100 wrSA1100 = some wrSA1101
kernel_rfl scalarSegA1102 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1101 wrSA1101 = some wrSA1102
kernel_rfl scalarSegA1103 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1102 wrSA1102 = some wrSA1103
kernel_rfl scalarSegA1104 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1103 wrSA1103 = some wrSA1104
kernel_rfl scalarSegA1105 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1104 wrSA1104 = some wrSA1105
kernel_rfl scalarSegA1106 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1105 wrSA1105 = some wrSA1106
kernel_rfl scalarSegA1107 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1106 wrSA1106 = some wrSA1107
kernel_rfl scalarSegA1108 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1107 wrSA1107 = some wrSA1108
kernel_rfl scalarSegA1109 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1108 wrSA1108 = some wrSA1109
kernel_rfl scalarSegA1110 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1109 wrSA1109 = some wrSA1110
kernel_rfl scalarSegA1111 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1110 wrSA1110 = some wrSA1111
kernel_rfl scalarSegA1112 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1111 wrSA1111 = some wrSA1112
kernel_rfl scalarSegA1113 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1112 wrSA1112 = some wrSA1113
kernel_rfl scalarSegA1114 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1113 wrSA1113 = some wrSA1114
kernel_rfl scalarSegA1115 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1114 wrSA1114 = some wrSA1115
kernel_rfl scalarSegA1116 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1115 wrSA1115 = some wrSA1116
kernel_rfl scalarSegA1117 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1116 wrSA1116 = some wrSA1117
kernel_rfl scalarSegA1118 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1117 wrSA1117 = some wrSA1118
kernel_rfl scalarSegA1119 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1118 wrSA1118 = some wrSA1119
kernel_rfl scalarSegA1120 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1119 wrSA1119 = some wrSA1120
kernel_rfl scalarSegA1121 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1120 wrSA1120 = some wrSA1121
kernel_rfl scalarSegA1122 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1121 wrSA1121 = some wrSA1122
kernel_rfl scalarSegA1123 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1122 wrSA1122 = some wrSA1123
kernel_rfl scalarSegA1124 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1123 wrSA1123 = some wrSA1124
kernel_rfl scalarSegA1125 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1124 wrSA1124 = some wrSA1125
kernel_rfl scalarSegA1126 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1125 wrSA1125 = some wrSA1126
kernel_rfl scalarSegA1127 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1126 wrSA1126 = some wrSA1127
kernel_rfl scalarSegA1128 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1127 wrSA1127 = some wrSA1128
kernel_rfl scalarSegA1129 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1128 wrSA1128 = some wrSA1129
kernel_rfl scalarSegA1130 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1129 wrSA1129 = some wrSA1130
kernel_rfl scalarSegA1131 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1130 wrSA1130 = some wrSA1131
kernel_rfl scalarSegA1132 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1131 wrSA1131 = some wrSA1132
kernel_rfl scalarSegA1133 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1132 wrSA1132 = some wrSA1133
kernel_rfl scalarSegA1134 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1133 wrSA1133 = some wrSA1134
kernel_rfl scalarSegA1135 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1134 wrSA1134 = some wrSA1135
kernel_rfl scalarSegA1136 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1135 wrSA1135 = some wrSA1136
kernel_rfl scalarSegA1137 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1136 wrSA1136 = some wrSA1137
kernel_rfl scalarSegA1138 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1137 wrSA1137 = some wrSA1138
kernel_rfl scalarSegA1139 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1138 wrSA1138 = some wrSA1139
kernel_rfl scalarSegA1140 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1139 wrSA1139 = some wrSA1140
kernel_rfl scalarSegA1141 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1140 wrSA1140 = some wrSA1141
kernel_rfl scalarSegA1142 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1141 wrSA1141 = some wrSA1142
kernel_rfl scalarSegA1143 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1142 wrSA1142 = some wrSA1143
kernel_rfl scalarSegA1144 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1143 wrSA1143 = some wrSA1144
kernel_rfl scalarSegA1145 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1144 wrSA1144 = some wrSA1145
kernel_rfl scalarSegA1146 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1145 wrSA1145 = some wrSA1146
kernel_rfl scalarSegA1147 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1146 wrSA1146 = some wrSA1147
kernel_rfl scalarSegA1148 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1147 wrSA1147 = some wrSA1148
kernel_rfl scalarSegA1149 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1148 wrSA1148 = some wrSA1149
kernel_rfl scalarSegA1150 : ScalarCheck.Skip.runPZ ScalarCheck.params 2811 seg1149 wrSA1149 = some wrSA1150
end StageRoute
