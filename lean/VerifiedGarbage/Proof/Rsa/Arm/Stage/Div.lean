module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Sk
public import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
public import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint4
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2

/-! # The ARMv7 key stages: `q = n / p` (`div_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- `clrW j`: the word above the `w` of `[j]` cleared. -/
theorem clrW_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem → num t.mem B w j = num s.mem B w j →
      w32 t.mem (State.addr B) (arr w j + 4 * w) = 0 → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (clrW j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold clrW
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega_arith) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have e2 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * w) := by
    rw [u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    rw [this, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide)
    (by decide)
  have a0 : State.addr (s3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * w) := by
    rw [u3.other _ (by decide), e2, BitVec.add_zero]; exact h.addr (by omega_arith)
  refine wp_str (by decide) a0 (h3.write (by omega_arith)) fun t u4 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * w)) (0 : BitVec 32) := by
    rw [u4.mem, u3.gpr, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * w) (0 : BitVec 32) (by omega_arith)
  rw [← mt] at o1
  refine k t (h3.of_mupd u4) (Keep.of_arr (d := 4 * w) o1 (by omega_arith) (by simp)) ?_ ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest _))))
  · exact o1.val32 (by omega_arith) (by omega_arith)
  · simp only [w32]; rw [mt, Mem.readW_writeW_self32]; rfl

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- A step that writes array `o` but not its number. -/
theorem KS.same1 {o : Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B P.w [o] [] s.mem t.mem)
    (ho : o < nArr) (e : num t.mem P.B P.w o = num s.mem P.B P.w o) (hlW : ∀ j ∈ liveW, o / 2 ≠ j)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    KS P σ A live AW liveW V ls t := by
  have sz := h.sizes
  refine h.core k (by simpa using fitZ_w sz ho) (by simp) r8 sp rd wr (fun j hj => ?_) h.live_lt
    (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) (by simp)) h.liveW_lt
    (h.sl_keep k (by simp)) h.ls_ok
  by_cases ej : j = o
  · subst ej; rw [e]; exact h.arrs _ hj
  · rw [k.num (fun i hi ei => ej (by simp only [List.mem_singleton] at hi; rw [← ei, hi])) (by simp)
      (fit_w sz (h.live_lt j hj))]
    exact h.arrs j hj

end

section
end

end VG.Proof.Rsa.Arm.Recover
