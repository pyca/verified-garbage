module

public import VerifiedGarbage.Proof.Rsa.Arm.CvBase
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.Arm.CvBase

/-! # `vg_rsa_crt_values` on ARMv7: what every stage keeps

`Base s₀ s`: the stack pointer and the regions are those of the initial
state `s₀`, memory outside the working space is `s₀`'s, and the header holds
the registers to restore and `dp` and `dq` (`savedVal`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The registers saved at bytes `20 + 4 i` of the header. -/
def savedReg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11 | 8 => .lr
  | 9 => .r0 | _ => .r2

structure Base (s0 s : State) : Prop where
  pre : CvPre s0
  sp : s.sp = s0.sp
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  frame : Frame [rS s0] s0.mem s.mem
  saved : ∀ i < 11, slot s.mem (cvB s0) (20 + 4 * i) = (s0.gpr (savedReg i)).toNat

/-- Memory outside the working space, by the offset from its base. -/
theorem out_of_ofs {s0 : State} {x : Addr} (hx : ¬ (rS s0).Contains x 1) :
    cvZ s0 ≤ ofs (State.addr (cvB s0)) x := by
  simp only [Region.Contains] at hx
  simp only [ofs, cvZ, cvB]
  omega

theorem Base.keep {s0 s t : State} (h : Base s0 s) {js ds : List Nat}
    (k : Keep (cvB s0) (cvW s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, d + 4 ≤ 20 ∨ 64 ≤ d) (hdh : ∀ d ∈ ds, d + 4 ≤ hdr)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Base s0 t := by
  have fits := h.pre.fits
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, ?_, fun i hi => ?_⟩
  · refine h.frame.trans fun x hx => k.out (Z := cvZ s0) (fun j hj => ?_) (fun d hd => ?_)
      (out_of_ofs (by simpa using hx))
    · exact Nat.le_trans (arr_end (hjs j hj)) fits
    · exact Nat.le_trans (hdh d hd) (Nat.le_trans (Nat.le_add_right _ _) fits)
  · rw [k.slot (by simp only [hdr]; omega) (fun d hd => by rcases hds d hd with e | e <;> omega)]
    exact h.saved i hi

theorem Base.of_rest {s0 s t : State} (h : Base s0 s) {ws : List Reg} (r : Rest ws s t)
    (m : t.mem = s.mem) : Base s0 t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.frame, fun i hi => m ▸ h.saved i hi⟩

/-- A stack argument. -/
theorem Base.arg {s0 s : State} (h : Base s0 s) {i : Nat} (hi : i < 12) : stackArg s i = stackArg s0 i := by
  have sp := h.pre.sp48
  unfold stackArg
  have ea : stackArgAddr s i = stackArgAddr s0 i := by simp only [stackArgAddr, h.sp]
  rw [ea]
  refine h.frame.readW (r := rA s0) ?_ (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega), addr_add (by omega), Nat.mul_zero, BitVec.add_zero, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr; subst hr; exact h.pre.sA.symm

theorem Base.rA_mem {s0 s : State} (h : Base s0 s) : rA s ∈ s.rd := by
  rw [h.rd, h.pre.rd]; simp [rA, stackArgAddr, h.sp]

/-- The working space. -/
theorem Base.ws {s0 s : State} (h : Base s0 s) (h7 : s.gpr .r7 = BitVec.ofNat 32 (S (cvW s0)))
    (h8 : s.gpr .r8 = cvB s0) (h9 : s.gpr .r9 = BitVec.ofNat 32 (cvW s0)) :
    Ws s (cvB s0) (cvZ s0) (cvW s0) nArr := by
  have := h.pre.w16
  refine ⟨h.pre.fS, ?_, h.pre.fits, by omega, by omega, h7, h8, h9⟩
  rw [h.wr, h.pre.wr]; simp

/-- `ctx`: `r7`, `r8` and `r9` from the stack arguments. -/
theorem ctx_ok {s0 s : State} (h : Base s0 s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Base s0 t → Ws t (cvB s0) (cvZ s0) (cvW s0) nArr → Rest [.r7, .r8, .r9] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (ctx ++ rest)) s Q := by
  have sp := h.pre.sp48
  rw [h.sp.symm] at sp
  have w16 := h.pre.w16
  have kb := h.pre.kb
  unfold ctx stride
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp h.rA_mem sp (i := 10) (by decide) fun s1 u1 => ?_
  have b1 := h.of_rest (u1.rest (ws := [.r8]) (by simp)) u1.mem
  refine wp_ldrSp b1.rA_mem (by rw [u1.sp]; exact sp) (i := 3) (by decide) fun s2 u2 => ?_
  have b2 := b1.of_rest (u2.rest (ws := [.r9]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_lsl (by decide)) fun t u6 => ?_
  have rest : Rest [.r7, .r8, .r9] s t := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))))
  have mt : t.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have bt := h.of_rest rest mt
  have a3 : stackArg s1 3 = stackArg s0 3 := b1.arg (by decide)
  have e9 : s4.gpr .r9 = BitVec.ofNat 32 (cvW s0) := by
    rw [u4.gpr, u3.gpr, dpVal, u2.gpr, a3]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (3 : BitVec 32).toNat = 3 from rfl]
    have : (stackArg s0 3).toNat < 2 ^ 32 := (stackArg s0 3).isLt
    simp only [cvW, cvK] at *
    omega
  have t9 : t.gpr .r9 = BitVec.ofNat 32 (cvW s0) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), e9]
  have e7 : t.gpr .r7 = BitVec.ofNat 32 (S (cvW s0)) := by
    rw [u6.gpr, u5.gpr, dpVal, e9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [S]
    omega
  have e8 : t.gpr .r8 = cvB s0 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.gpr, h.arg (by decide)]
  exact k t bt (bt.ws e7 e8 t9) rest mt

end VG.Proof.Rsa.Arm.CrtValues
