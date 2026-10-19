module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PublicStack
import VerifiedGarbage.Proof.Bignum.Arm.StackPair

/-! # Restore each public RSA phase's arguments from the outer frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem publicExponentArgs_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) :
    WP isa (.block PublicFn.exponentArgs) s fun t =>
      t.gpr .r1 = ep ∧ t.gpr .lr = BitVec.ofNat 32 eLen ∧ t.mem = s.mem ∧ Rest [.r1, .lr] s t := by
  refine WP.mono (stackPair_ok s .r1 .lr 56 60 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega) (by have := h.nowrap; omega)
    (h.read (by decide) (by decide)) (h.read (by decide) (by decide))) ?_
  rintro t ⟨ptr, count, mem, rest⟩
  exact ⟨ptr.trans h.exponent, count.trans h.exponentCount, mem, rest⟩

theorem publicInputArgs_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) :
    WP isa (.block PublicFn.inputArgs) s fun t =>
      t.gpr .r4 = xp ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ t.mem = s.mem ∧ Rest [.r4, .r6] s t := by
  refine WP.mono (stackPair_ok s .r4 .r6 64 12 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega) (by have := h.nowrap; omega)
    (h.read (by decide) (by decide)) (h.read (by decide) (by decide))) ?_
  rintro t ⟨ptr, count, mem, rest⟩
  exact ⟨ptr.trans h.input, count.trans h.savedCount, mem, rest⟩

theorem publicControlArgs_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) :
    WP isa (.block PublicFn.controlArgs) s fun t =>
      t.gpr .r1 = ep ∧ t.gpr .r2 = BitVec.ofNat 32 eLen ∧ t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  refine WP.mono (stackPair_ok s .r1 .r2 56 60 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega) (by have := h.nowrap; omega)
    (h.read (by decide) (by decide)) (h.read (by decide) (by decide))) ?_
  rintro t ⟨ptr, count, mem, rest⟩
  exact ⟨ptr.trans h.exponent, count.trans h.exponentCount, mem, rest⟩

theorem publicOutputArgs_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) :
    WP isa (.block PublicFn.outputArgs) s fun t => t.gpr .r2 = BitVec.ofNat 32 6 ∧
      t.gpr .r4 = dst ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ t.mem = s.mem ∧ Rest [.r2, .r4, .r6] s t := by
  unfold PublicFn.outputArgs
  refine wp_mov (op2_imm (by decide)) fun u a => ?_
  refine WP.mono (stackPair_ok u .r4 .r6 4 12 (by decide) (by decide) (by decide)
    (by rw [a.sp]; have := h.nowrap; omega) (by rw [a.sp]; have := h.nowrap; omega)
    (by rw [a.rd, a.wr, a.sp]; exact h.read (by decide) (by decide))
    (by rw [a.rd, a.wr, a.sp]; exact h.read (by decide) (by decide))) ?_
  rintro t ⟨ptr, count, mem, rest⟩
  rw [a.mem, a.sp] at ptr count
  exact ⟨(rest.gpr .r2 (by simp)).trans a.gpr, ptr.trans h.savedOutput, count.trans h.savedCount,
    mem.trans a.mem, (a.rest (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Bignum.Arm
