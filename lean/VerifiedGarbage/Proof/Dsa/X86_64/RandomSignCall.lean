module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract

/-! Call any registered supplied-nonce backend, retaining its contract and frame. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64

def randomSignerName (v : Backend) : String := "vg_dsa_sign" ++ v.suffix

theorem random_signer_call (v : Backend) {s : State} {rd wr : List Region}
    (hp : (Spec.Dsa.signContract abi v.stack).pre (s.callEntry.withRegions rd wr))
    (hr : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.call (randomSignerName v) (SignVerify.sign v.sq v.mul)) s fun t =>
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame (wr ++ [below (s.gpr .rsp) ((SignVerify.sign v.sq v.mul).x86_64Depth + 8)]) s.mem t.mem ∧
      (∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .rsp → u.gpr r = t.gpr r) ∧
        (Spec.Dsa.signContract abi v.stack).post (s.callEntry.withRegions rd wr) u) ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hd := v.signDepth
  have hb := v.stackBound
  exact WP.call_sp_mx v.signVerified.1 (SpSafe.of_all v.signSp) (by omega) hp hr hw
    (fun _ hrd hwr hcs hf _ hpost hmx => ⟨hrd, hwr, hcs, hf, hpost, hmx⟩)

end VG.Proof.Dsa.X86_64
