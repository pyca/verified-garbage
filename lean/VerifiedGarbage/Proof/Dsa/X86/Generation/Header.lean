module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Header
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar

/-! # Header initialization retains the existing runtime-workspace invariant -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem set_header {L : Lay} {s : State} {base : Addr} {bytes len count d value : Nat}
    (h : RtWs L s base bytes len count) (hd : d + 4 ≤ Impl.Rsa.X86.Keys.hdr) (small : value < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86.Generation.setHeader d value)) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [] [d] s.mem t.mem ∧
      slot t.mem base d = value ∧ Keeps [.eax] s t := by
  unfold Impl.Dsa.X86.Generation.setHeader
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok hu hd .eax) ?_
  rintro t ⟨ht, frame, val, K⟩
  rw [U.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at val
  rw [U.mem] at frame
  exact ⟨ht, frame, val, U.keeps.trans (K.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
