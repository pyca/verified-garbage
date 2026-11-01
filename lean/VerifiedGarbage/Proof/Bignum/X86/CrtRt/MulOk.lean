module

import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape

public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Mul
import VerifiedGarbage.Proof.Framework.Omega

/-! # The Montgomery product of two slots of a context, by a call -/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (argAt_alloc)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- The words of a number of the context. -/
abbrev cwc (len : Nat) (c : Ctx) : Nat := bc len c / 4

theorem cwc_eq (len : Nat) (c : Ctx) : 2 * (bc len c / 8) = cwc len c := by
  have := bc_dvd len c; simp only [cwc]; omega

theorem bc_eq_cwc (len : Nat) (c : Ctx) : bc len c = 4 * cwc len c := by
  have := bc_dvd len c; simp only [cwc]; omega

theorem mulBody_noSp (c : Ctx) (o a b : Nat) :
    NoSp (.seq (.block (mulArgs c o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody) : Prog isa) := by
  apply NoSp.of_all
  have e : (!Taint.clobbers (Instr.alu AluOp.add Reg.eax (Src.reg Reg.edx)) Reg.esp) = true := rfl
  rw [Code.allInstrs_eq]
  cases c <;>
  simp only [instrs, mulArgs, widthC, VG.Impl.Bignum.X86.PublicRt.widthB, offIn, List.all_append, List.all_cons,
    List.all_nil, List.all_replicate, e, ite_self] <;>
  rw [← Code.allInstrs_eq] <;>
  rw [show Sse2.atBody.allInstrs (fun i => !Taint.clobbers i .esp)=true from VG.Proof.Mont.X86.Sse2.atBody_allNoSp] <;> rfl

/-- The callee's offsets for slots `o`, `a` and `b` (3 to 8) of a context. -/
theorem In.offs {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8) :
    Offs bytes (bc len c / 8) numBase invOff (lo len (.slot c 1)) (lo len (.slot c o)) (lo len (.slot c a))
      (lo len (.slot c b)) := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have e8 := bc_dvd len c
  have mo : ∀ j, 3 ≤ j → j ≤ 8 → numBase + 3 * st len c ≤ lo len (.slot c j) ∧
      lo len (.slot c j) + st len c ≤ lo len (.slot c 8) + st len c := fun j h3 h8 => by
    have := Nat.mul_le_mul_right (st len c) h3
    have := Nat.mul_le_mul_right (st len c) h8
    simp only [lo]; omega
  obtain ⟨o1, o2⟩ := mo o ho3 ho
  obtain ⟨a1, a2⟩ := mo a ha3 ha
  obtain ⟨b1, b2⟩ := mo b hb3 hb
  have hb8 : 8 * (bc len c / 8) = bc len c := by omega
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  simp only [lo] at f8 o1 o2 a1 a2 b1 b2
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [lo, scratchBytes, VG.Proof.Rsa.MontMul.Apart, invOff, hb8] <;> omega

theorem mul_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hinv : (val32 s.mem base numBase (cwc len c) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (lo len (.slot c b)) (cwc len c) < val32 s.mem base numBase (cwc len c)) :
    WP isa (mul c o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (lo len (.slot c o)), bc len c⟩, ⟨off base (lo len (.slot c 1)), 3 * bc len c + 56⟩,
        below (s.gpr .esp) 96] s.mem t.mem ∧
      val32 t.mem base (lo len (.slot c o)) (cwc len c) < val32 s.mem base numBase (cwc len c) ∧
      val32 t.mem base (lo len (.slot c o)) (cwc len c) * 2 ^ (8 * bc len c) % val32 s.mem base numBase (cwc len c) =
        val32 s.mem base (lo len (.slot c a)) (cwc len c) * val32 s.mem base (lo len (.slot c b)) (cwc len c) %
          val32 s.mem base numBase (cwc len c) := by
  have low := h.room.low
  have top := h.top
  have e8 := bc_dvd len c
  have hb8 : 8 * (bc len c / 8) = bc len c := by omega
  have sb : scratchBytes (bc len c / 8) = 3 * bc len c + 56 := by simp only [scratchBytes]; omega
  have p64 : 64 * (bc len c / 8) = 8 * bc len c := by omega
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have fEspN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [fEsp, VG.X86.sub_toNat (by omega)]
  have C := call_ok (is := mulArgs c o a b) h.scratch h.hbytes h.room (h.offs c ho3 ho ha3 ha hb3 hb)
    (by rw [cwc_eq]; exact hinv) (by rw [cwc_eq]; exact hB) (mulBody_noSp c o a b)
    (by
      have := mulArgs_ok (f := allocFrame 36 s) (len := len) (c := c) (o := o) (a := a) (b := b)
        (argAt_alloc h.width) (argAt_alloc (h.arg (i := wsLenArg) (by decide))) h.upper' (by omega) (by omega)
        (by omega) (by omega) (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)
      rwa [show (allocFrame 36 s).gpr .edi = s.gpr .edi from allocFrame_gpr _ _ (by decide)] at this)
  refine WP.mono C fun t ⟨cs, rd, wr, F, L, V⟩ => ⟨cs, rd, wr, ?_, ?_, ?_⟩
  · rw [hb8, sb] at F; exact F
  · rw [cwc_eq] at L; exact L
  · rw [cwc_eq, p64] at V; exact V

end VG.Proof.Bignum.X86.CrtRt
