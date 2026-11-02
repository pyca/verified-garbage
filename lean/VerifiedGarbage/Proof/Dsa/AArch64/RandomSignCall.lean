module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Omega

/-! Call any registered supplied-nonce backend, retaining its contract and frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def randomSignerName (v : Backend) : String := "vg_dsa_sign" ++ v.suffix

theorem random_signer_call (v : Backend) {s : State} {rd wr : List Region}
    (hp : (Spec.Dsa.signContract abi v.stack).pre (s.callEntry.withRegions rd wr))
    (hr : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.call (randomSignerName v) (SignVerify.sign v.mul)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧
      Frame (wr ++ [below s.sp v.stack]) s.mem t.mem ∧
      (Spec.Dsa.signContract abi v.stack).post (s.callEntry.withRegions rd wr) (t.withRegions rd wr) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have hd := v.signDepth
  have hb := v.stackBound
  refine WP.callFV v.signVerified.1 hp hr hw (fun t hrd hwr hsp hf hcs hv hp => ?_) (by omega)
  exact ⟨hrd, hwr, hsp, hcs, Frame.below_mono hf hd (by omega), hp, hv⟩

end VG.Proof.Dsa.AArch64
