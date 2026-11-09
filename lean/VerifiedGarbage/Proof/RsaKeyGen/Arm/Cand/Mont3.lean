module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Base
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Loads
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! # A candidate on ARMv7: tools for Montgomery multiplication's stages

`KS.of_outZ`: memory changed only outside the working space keeps a stage;
`VP.stk`: a piece of loads and stores relative to the stack;
`St.pctx`: the working space's context restored; `clrTopO_ok`: `clrTop j`
writes only the two words above the number of `[j]`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Loads, stores and arithmetic relative to the stack pointer. -/
theorem VP.stk {F G : State → State → Prop} {code : List Instr}
    (keep : code.all (fun i => decide (clobbers i .r12 = false)) = true)
    (leak : code.all VG.Proof.Rsa.Arm.stackInstruction = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (wp : ∀ σ s, F σ s → WP isa (.block (.addSp .r12 0 :: code)) s (G σ)) :
    VP F (.block (.addSp .r12 0 :: code)) G :=
  VP.of_ct (fun _ _ => (VG.Proof.Rsa.Arm.setupChecked_ct code keep leak).mono
    (fun _ _ h => sp _ _ _ _ h.1 h.2) fun _ _ _ => trivial) wp

section
variable {P : CP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- Memory that changed only in regions apart from the working space. -/
theorem outZ_of_frame {rs : List Region} {m m' : Mem} (f : Frame rs m m')
    (hd : ∀ r ∈ rs, P.rS.Disjoint r) : Outs (State.addr P.B) [(P.Z, 2 ^ 64)] m m' := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  have hz : (x - State.addr P.B).toNat < P.Z := by
    have := (x - State.addr P.B).isLt; simp only [ofs] at h; omega_arith
  refine f x fun r hr hc => ?_
  exact hd r hr x (by simp only [Region.Contains]; omega_arith) hc

/-- Memory that changed only outside the working space keeps a stage. -/
theorem KS.of_outZ (h : KS P σ A live V ls s) (o : Outs (State.addr P.B) [(P.Z, 2 ^ 64)] s.mem t.mem)
    (fr : Frame P.chg σ.mem t.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    KS P σ A live V ls t := by
  have pre := h.pre
  have hz := pre.hdr_Z
  have zl := pre.Z_le
  have sl : ∀ d, d + 4 ≤ hdr → slot t.mem P.B d = slot s.mem P.B d := fun d hd => by
    have := Outs.val32 (k := 1) (d := d) o (fun r hr => by simp at hr; subst hr; left; omega_arith) (by omega_arith)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  refine ⟨pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, fr, (sl 16 (by decide)).trans h.cnt,
    fun j hj => ?_, fun d hd => (sl d (h.ls_ok d hd).1).trans (h.sl d hd), h.live_lt, h.ls_ok⟩
  have := pre.fitZ (h.live_lt j hj)
  have : S P.W = 4 * (P.W + 2) := rfl
  rw [← h.arrs j hj]
  exact Outs.val32 o (fun r hr => by simp at hr; subst hr; left; omega_arith) (by omega_arith)

/-- Frame word 0 written. -/
theorem KS.w0 (h : KS P σ A live V ls s) (v : BitVec 32) (ht : t.mem = s.mem.writeW (State.addr P.sp) v)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KS P σ A live V ls t := by
  have pre := h.pre
  have hc : P.rW0.Contains (State.addr P.sp) (32 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have f0 : Frame [P.rW0] s.mem t.mem := by rw [ht]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  refine h.of_outZ (outZ_of_frame (P := P) f0 fun r hr => ?_) (by rw [ht]; exact h.frame.writeW (by simp) _ hc) sp rd wr
  simp only [List.mem_singleton] at hr; subst hr
  exact pre.sF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 84) (by decide) |>
    fun h => by simpa using h)

end

/-- `clrTop j`: the two top words of `[j]` cleared, and nothing else written. -/
theorem clrTopO_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) (hw : 2 ≤ w) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Outside (State.addr B) (arr w j + 4 * (w - 2)) 8 s.mem t.mem →
      num t.mem B w j = val32 s.mem (State.addr B) (arr w j) (w - 2) → Rest opRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (clrTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold clrTop VG.Impl.Rsa.Arm.Recover.clrTop
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega_arith) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have e3 : s3.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * (w - 2)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    rw [this, BitVec.add_assoc, ← BitVec.ofNat_add,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_arith)]
    congr 2; omega_arith
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N :=
    ((h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  have a0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * (w - 2)) := by
    rw [u4.other _ (by decide), e3, BitVec.add_zero]; exact h.addr (by omega_arith)
  refine wp_str (by decide) a0 (h4.write (by omega_arith)) fun s5 u5 => ?_
  have h5 := h4.of_mupd u5
  have a4 : State.addr (s5.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr B) (arr w j + 4 * (w - 2) + 4) := by
    rw [u5.gpr, u4.other _ (by decide), e3, BitVec.add_assoc, ← BitVec.ofNat_add]; exact h.addr (by omega_arith)
  refine wp_str (by decide) a4 (h5.write (by omega_arith)) fun t u6 => ?_
  have ht := h5.of_mupd u6
  have z4 : s4.gpr .r1 = 0 := u4.gpr
  have mt : t.mem = (s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 2))) (0 : BitVec 32)).writeW
      (off (State.addr B) (arr w j + 4 * (w - 2) + 4)) (0 : BitVec 32) := by
    rw [u6.mem, u5.gpr, z4, u5.mem, z4, u4.mem, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * (w - 2)) (0 : BitVec 32) (by omega_arith)
  have o2 := writeW32_outside (s.mem.writeW (off (State.addr B) (arr w j + 4 * (w - 2))) (0 : BitVec 32))
    (State.addr B) (d := arr w j + 4 * (w - 2) + 4) (0 : BitVec 32) (by omega_arith)
  rw [← mt] at o2
  refine k t ht ((o1.mono (Nat.le_refl _) (by omega_arith)).trans (o2.mono (by omega_arith) (by omega_arith))) ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest _).trans (u6.rest _))))))
  change val32 _ _ _ _ = _
  have e := val32_append t.mem (State.addr B) (arr w j) (w - 2) 2
  rw [show w - 2 + 2 = w by omega_arith] at e
  have t0 : w32 t.mem (State.addr B) (arr w j + 4 * (w - 2)) = 0 := by
    simp only [w32]
    rw [mt, Mem.readW_writeW_sep (w := 32) (w' := 32) (Offset.sep _ (d := arr w j + 4 * (w - 2)) (n := 4)
      (e := arr w j + 4 * (w - 2) + 4) (k := 4) (Or.inl (Nat.le_refl _)) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]; rfl
  have t1 : w32 t.mem (State.addr B) (arr w j + 4 * (w - 2) + 4) = 0 := by
    simp only [w32]; rw [mt, Mem.readW_writeW_self32]; rfl
  have top : val32 t.mem (State.addr B) (arr w j + 4 * (w - 2)) 2 = 0 := by
    simp only [val32, t0, t1]
  rw [e, top, Nat.mul_zero, Nat.add_zero]
  exact (o2.val32 (by omega_arith) (by omega_arith)).trans (o1.val32 (by omega_arith) (by omega_arith))

end VG.Proof.RsaKeyGen.Arm.Cand
