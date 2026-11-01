module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont5
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont3
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint6
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # A candidate on ARMv7: Montgomery multiplication modulo `c` ready (`montA_vp`)

After `r2`: the context, `c`'s top words cleared (`ctxClr_vp`), and the
stride in the header (`stride_vp`): the stage of the exponent, with `MS`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP}

theorem MSp.of_ar {σ s : State} (ar : ArithmeticReady P.M0 P.lenM P.w s)
    (n0 : numAt s.mem (State.addr P.M0) P.w 0 = cv P σ) (n4 : numAt s.mem (State.addr P.M0) P.w 4 = r2v P σ) :
    MSp P σ s :=
  ⟨ar.workspace, ar.layout, ar.width, ar.inverse, n0, n4, ar.stackRead, ar.stackSep, ar.saved⟩

/-- Memory of the working space changed only at offsets `[o, o + n)` past
array `mBase` that are no byte `MSp` reads. -/
theorem MSp.of_outside {σ s t : State} (pre : In P σ) (h : MSp P σ s) {o n : Nat}
    (out : Outside (State.addr P.B) (P.oM + o) n s.mem t.mem)
    (ho : ∀ d k, MRd P d k → d + k ≤ o ∨ o + n ≤ d)
    (h4 : arrAt P.w 4 + 8 * P.w ≤ o ∨ o + n ≤ arrAt P.w 4) (h5 : P.oM + arrAt P.w 5 ≤ P.Z)
    (sv : t.mem.readW (State.addr t.sp) 32 = s.mem.readW (State.addr s.sp) 32)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MSp P σ t := by
  have zl := pre.Z_le
  have a15 : mHd P ≤ arrAt P.w 5 := by simp only [mHd, arrAt]; omega
  have a45 : arrAt P.w 4 + 8 * P.w ≤ arrAt P.w 5 := by simp only [arrAt]; omega
  refine h.of_read (fun d k hd => ?_) ?_ sv sp rd wr
  · rw [pre.M0_off]
    refine Mem.read_congr fun i hi => out _ ?_
    have := ho d k hd
    have hdk : d + k ≤ mHd P := by
      rcases hd with h1 | ⟨_, h1⟩
      · have : 128 ≤ mHd P := by simp only [mHd, arrAt, Proof.Rsa.Mont.hdrBytes]; omega
        omega
      · exact h1
    rw [ofs_off _ (by omega)]
    omega
  · unfold numAt
    rw [show State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 4) = off (State.addr P.M0) (arrAt P.w 4) from rfl,
      pre.M0_off]
    refine congrArg BitVec.toNat (Mem.read_congr fun i hi => out _ ?_)
    rw [ofs_off _ (by omega)]
    omega

/-- `ctx` and `c`'s top words cleared. -/
theorem ctxClr_vp {E : State → Prop} :
    VP (SE P E) (.block (ctx ++ clrTop mBase)) (fun σ s => SX P E σ s ∧ MSp P σ s) := by
  rw [show ctx ++ clrTop mBase = [.ldrSp .r8 aoS] ++ (ctxW ++ clrTop mBase) from rfl]
  refine VP.block_append (G := fun σ s => SE P E σ s ∧ s.gpr .r8 = P.B) ?_ ?_
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s h => ?_
    · rw [h₁.1.1.2.sp, h₁.1.1.2.pre.sp, h₂.1.1.2.sp, h₂.1.1.2.pre.sp]
    obtain ⟨⟨⟨e, k⟩, ar, n0⟩, n4⟩ := h
    refine k.ldrSp (o := aoS) (by decide) fun t u => WP.block_nil ⟨⟨⟨⟨e, k.of_rest (u.rest (ws := [.r8])
      (by simp)) u.mem⟩, ar.of_mem u.mem (u.rest (ws := [.r8]) (by simp)) (by rw [u.other _ (by decide), ar.ptr]),
      by rw [u.mem]; exact n0⟩, by rw [u.mem]; exact n4⟩, by rw [u.gpr, k.pre.aS]⟩
  refine VP.block_append (G := fun σ s => (SE P E σ s ∧ Ws s P.B P.Z P.W nArr) ∧ s.gpr .r8 = P.B) ?_ ?_
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨⟨e, k⟩, ar, n0⟩, n4⟩, r8⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    have pre := k.pre
    have hz := pre.hdr_Z
    have hf := pre.fS
    have ea : State.addr (s.gpr .r8 + BitVec.ofNat 32 16) = off (State.addr P.B) 16 := by
      rw [r8]; exact addr_add (by simp only [hdr] at hz; omega)
    have rd : InRegions (s.rd ++ s.wr) (off (State.addr P.B) 16) 4 :=
      ⟨P.rS, List.mem_append_right _ (by rw [k.wr]; exact pre.rS_mem),
        Offset.contains_base _ (by simp only [hdr] at hz; omega) (by omega)⟩
    simp only [ctxW, stride, List.cons_append, List.nil_append]
    refine wp_ldr (by decide) ea rd fun s2 u2 => ?_
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 => WP.block_nil ?_
    have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem]
    have r4 : Rest [.r7, .r9] s s4 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp)))
    have wl := pre.wle
    have e9 : s4.gpr .r9 = BitVec.ofNat 32 P.W := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have e7 : s4.gpr .r7 = BitVec.ofNat 32 (S P.W) := by
      rw [u4.gpr, u3.gpr, dpVal, u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, this, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      simp only [show (2 : BitVec 32).toNat = 2 from rfl, S]
      omega
    have e8 : s4.gpr .r8 = P.B := by rw [r4.gpr _ (by decide), r8]
    have k4 := k.of_rest r4 m4
    exact ⟨⟨⟨⟨⟨e, k4⟩, ar.of_mem m4 r4 (by rw [r4.gpr _ (by decide), ar.ptr]), by rw [m4]; exact n0⟩,
      by rw [m4]; exact n4⟩, k4.ws e7 e8 e9⟩, e8⟩
  · refine VP.kv clrTopC_taint (fun _ _ h => h.1.2) fun σ s ⟨⟨⟨⟨⟨e, k⟩, ar, n0⟩, n4⟩, hw⟩, _⟩ => ?_
    have pre := k.pre
    have hW := pre.W_eq
    rw [← List.append_nil (clrTop mBase)]
    refine clrTopO_ok hw (by decide) (by decide) (by omega) fun t ht out nt rest => WP.block_nil ?_
    have hS := pre.S_eq
    have fit := pre.fitZ (j := mBase) (by decide)
    have kp : Keep P.B P.W [mBase] [] s.mem t.mem :=
      Keep.of_arr (d := 4 * (P.W - 2)) out (by simp only [S]; omega) (by simp)
    have v : num t.mem P.B P.W aC = cv P σ := by
      have e0 := pre.numAt_val32 s.mem 0
      simp only [Nat.add_zero] at e0
      show num t.mem P.B P.W mBase = _
      rw [nt, ← e0, n0]
    have k2 := k.write1 kp (by decide) (by simp) rest.sp rest.rd rest.wr v (by simp)
    refine ⟨⟨e, k2.mono (fun j hj => ⟨by mem_sub, ?_⟩) fun d hd => ⟨hd, rfl⟩, ht⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) only [upd, ↓reduceIte, AX, A3, A0]
    · have out' : Outside (State.addr P.B) (P.oM + (arrAt P.w 0 + 8 * P.w)) 8 s.mem t.mem := by
        have e0 := pre.oM_arrAt 0
        rw [show P.oM + (arrAt P.w 0 + 8 * P.w) = arr P.W mBase + 4 * (P.W - 2) by
          rw [← Nat.add_assoc, e0]; congr 1; omega]
        exact out
      refine (MSp.of_ar ar n0 n4).of_outside pre out' (fun d k hd => ?_) ?_ ?_ ?_ rest.sp rest.rd rest.wr
      · rcases hd with h1 | ⟨_, h1⟩
        · left; have : 128 ≤ arrAt P.w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
          omega
        · left; simp only [mHd] at h1; omega
      · right; simp only [arrAt]; omega
      · have := pre.oM_arrAt 5
        have := Nat.le_trans (arr_mono (w := P.W) (show mBase + 5 ≤ nArr by decide)) pre.fits
        omega
      · have hc : P.rW0.Contains (State.addr P.sp) (32 / 8) := by
          simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
        rw [rest.sp, k.sp, pre.sp]
        exact ((Keep.frameS (P := P) kp (fun j hj => by simp at hj; subst hj; exact fit)
          (by simp)).readW hc (fun r hr => by simp at hr; subst hr; exact pre.rW0_rS.symm) (by decide))

end

end VG.Proof.Dsa.Arm.Prime
