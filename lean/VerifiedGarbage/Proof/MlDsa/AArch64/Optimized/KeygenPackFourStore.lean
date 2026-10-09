import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourInput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourStore_ok (s : State) (hw : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block [.umov .x .x9 .v0 0,.str .x .x9 .x2 0]) s fun t=>
      ((t.gpr .x9=(s.v .v0).extractLsb' 0 64 ∧
        t.mem=s.mem.writeW (s.gpr .x2) ((s.v .v0).extractLsb' 0 64)) ∧ Keep [.x9] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=by rfl)
  arun [Option.bind_some,exec,addr,Size.bytes,State.store,State.read,Mem.writeW,hw]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
