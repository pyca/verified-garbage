module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The saved candidate's pointer from the length in the header -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

theorem slot5_value (edi : BitVec 32) (w : Nat) :
    BitVec.ofNat 32 (8 * w) + 16 + (BitVec.ofNat 32 (8 * w) + 16) + (BitVec.ofNat 32 (8 * w) + 16 +
      (BitVec.ofNat 32 (8 * w) + 16)) + (BitVec.ofNat 32 (8 * w) + 16) + 256 + edi =
      edi + BitVec.ofNat 32 (slot w 5) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : BitVec 32).toNat = 16 := rfl
  have h256 : (256 : BitVec 32).toNat = 256 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, slot, stride, VG.Impl.Bignum.hdrBytes, h16, h256]
  have := edi.isLt
  omega

theorem slot0_eq (w : Nat) : slot w 0 = 256 := by simp [slot, VG.Impl.Bignum.hdrBytes]

theorem slot5_ge (w : Nat) : 256 + 8 * w ≤ slot w 5 := by
  simp only [slot, stride, VG.Impl.Bignum.hdrBytes]; omega

theorem slot5_eq (w : Nat) : slot w 5 = 336 + 40 * w := by
  simp only [slot, stride, VG.Impl.Bignum.hdrBytes]; omega

theorem slot5_lo (w : Nat) : 336 ≤ slot w 5 := by
  simp only [slot, stride, VG.Impl.Bignum.hdrBytes]; omega

theorem ptrAt_edi {s : State} {base : Addr} {size : Nat} (S : Scr s base size) {r : Reg} {d : Nat}
    (h : s.gpr r = s.gpr .edi + BitVec.ofNat 32 d) : PtrAt s base r d := by
  rw [PtrAt, h, BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
  omega

/-- `savedPtr r t`: `r` the saved candidate's address, for the length `8 w`
at header byte 4. -/
theorem savedPtr_ok {s : State} {base : Addr} {size w : Nat} {r t : Reg} {is : List Instr} {Q : State → Prop}
    (S : Scr s base size) (header : 8 ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (hrt : r ≠ t) (hr : r ≠ .edi) (ht : t ≠ .edi)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → u.gpr r = s.gpr .edi + BitVec.ofNat 32 (slot w 5) →
      WP isa (.block is) u Q) :
    WP isa (.block (savedPtr r t ++ is)) s Q := by
  simp only [savedPtr, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc S (by omega)) fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => wp_addS rfl fun s₄ u₄ _ => wp_addS rfl fun s₅ u₅ _ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => ?_
  have kr {a b : State} {v : BitVec 32} (u : Upd a b r v) : Keeps [r, t] a b := u.keeps.mono (by simp)
  have kt {a b : State} {v : BitVec 32} (u : Upd a b t v) : Keeps [r, t] a b := u.keeps.mono (by simp)
  have K₇ : Keeps [r, t] s s₇ :=
    ((((((kr u₁).trans (kr u₂)).trans (kt u₃)).trans (kr u₄)).trans (kr u₅)).trans (kr u₆)).trans (kr u₇)
  have K : Keeps [r, t] s s₈ := K₇.trans (kr u₈)
  refine k s₈ K (by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  have e₇ : s₇.gpr .edi = s.gpr .edi := K₇.1 .edi (by simp [hr.symm, ht.symm])
  have t₄ : s₄.gpr t = s₂.gpr r := by rw [u₄.other t hrt.symm, u₃.gpr]
  rw [u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₅.other t hrt.symm, t₄, u₃.other r hrt, u₂.gpr, u₁.gpr, len,
    e₇]
  exact slot5_value _ w

theorem savedPtr_block_ok {s : State} {base : Addr} {size w : Nat} {r t : Reg}
    (S : Scr s base size) (header : 8 ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (hrt : r ≠ t) (hr : r ≠ .edi) (ht : t ≠ .edi) :
    WP isa (.block (savedPtr r t)) s fun u =>
      Keeps [r, t] s u ∧ u.mem = s.mem ∧ u.gpr r = s.gpr .edi + BitVec.ofNat 32 (slot w 5) := by
  simpa only [List.append_nil] using
    savedPtr_ok (is := []) S header len hrt hr ht fun u K M h => WP.block_nil ⟨K, M, h⟩

end VG.Proof.RsaKeyGen.X86.ExponentRt
