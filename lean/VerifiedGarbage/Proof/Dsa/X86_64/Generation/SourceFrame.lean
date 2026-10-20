module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Preserve the random tape across workspace, buffer, and stack writes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem source_of_work {s t : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    {rs : List (Nat × Nat)} {extra : List Region} {regs : List Reg}
    (h : Src s B Z p bs) (hf : WorkFrame B rs extra s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (he : ∀ r ∈ extra, Region.Disjoint ⟨p, bs.length⟩ r)
    (hlen : bs.length < 2 ^ 64) (hk : Keep regs s t) : Src t B Z p bs := by
  refine ⟨fun i hi => by rw [hk.2.1, hk.2.2]; exact h.rd i hi, ?_, h.out⟩
  intro i hi
  rw [hf]
  · exact h.val i hi
  · intro r hmem hc
    apply he r hmem _ ?_ hc
    apply (Region.contains_self p bs.length).byte
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hi
  · intro r hmem
    exact Or.inr (Nat.le_trans (hr r hmem) (h.out i hi))

/-- Hashing and candidate construction preserve disjoint input tapes. -/
theorem source_of_frame {s t : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    {rs : List Region} (h : Src s B Z p bs) (hf : Frame rs s.mem t.mem)
    (hsep : ∀ r ∈ rs, (⟨p, bs.length⟩ : Region).Disjoint r)
    (hlen : bs.length < 2 ^ 64) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t B Z p bs := by
  refine ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, ?_, h.out⟩
  intro i hi
  rw [hf _ (fun r hr hc => hsep r hr _ (Offset.contains_base p (by omega) (by omega)) hc)]
  exact h.val i hi

end VG.Proof.Dsa.X86_64.Generation
