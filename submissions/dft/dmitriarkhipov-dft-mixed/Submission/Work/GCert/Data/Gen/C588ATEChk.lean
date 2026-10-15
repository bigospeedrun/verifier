import Work.Gauge.ECheck
import Work.GCert.Data.Gen.C588ATGl
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace GXD.C588AT
open GXD
theorem echk0_ok : GS.eCheck raw ⟨10, 9, 2, 8, 8⟩ glb0 = true := by decide +kernel
theorem echk1_ok : GS.eCheck raw ⟨10, 9, 2, 8, 8⟩ glb1 = true := by decide +kernel
theorem echk2_ok : GS.eCheck raw ⟨10, 9, 2, 8, 8⟩ glb2 = true := by decide +kernel
end GXD.C588AT
#print axioms GXD.C588AT.echk0_ok
#print axioms GXD.C588AT.echk1_ok
#print axioms GXD.C588AT.echk2_ok
