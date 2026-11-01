module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp7
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont1

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont6
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint6
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # A candidate on ARMv7: Montgomery multiplication modulo `c` ready (`montA_vp`)

The base of the working space into `r0` (`mont0_vp`), and the stride into its
header word 28 (`strideW_vp`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP}

/-- Frame word 0 holds the base. -/
theorem MSp.fw0 {σ s : State} (h : MSp P σ s) (sp : s.sp = P.sp) : fw s.mem P 0 = P.M0 := by
  have := h.saved
  rw [sp] at this
  simpa only [fw, off, BitVec.add_zero] using this

/-- `mont0`: the base into `r0`. -/
theorem mont0_vp {E : State → Prop} {X : State → State → Prop} (hX : ∀ σ s, X σ s → MSp P σ s)
    (hXr : ∀ σ s t, X σ s → t.mem = s.mem → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr → X σ t) :
    VP (fun σ s => SX P E σ s ∧ X σ s) (.block mont0)
      (fun σ s => (SX P E σ s ∧ X σ s) ∧ s.gpr .r0 = P.M0) := by
  show VP _ (.block ([(Reg.r0, 0)].map fun p => Instr.ldrSp p.1 p.2)) _
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, x⟩ => ?_
  · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
  have sp : s.sp = P.sp := h.sp.trans h.pre.sp
  refine h.bk.ldrSpV (o := 0) (by decide) (by decide) ((hX σ s x).fw0 sp) fun t u => WP.block_nil ?_
  have r := u.rest (ws := [.r0]) (by simp)
  exact ⟨⟨⟨e, h.of_rest r u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩,
    hXr σ s t x u.mem u.sp u.rd u.wr⟩, u.gpr⟩

/-- `strideW`: the stride into Montgomery multiplication's header word 28. -/
theorem strideW_vp {E : State → Prop} :
    VP (fun σ s => (SX P E σ s ∧ MSp P σ s) ∧ s.gpr .r0 = P.M0) (.block strideW)
      (fun σ s => SX P E σ s ∧ MS P σ s) := by
  refine VP.taint [.r0, .r7] strideW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, r0⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.1.2.2.r7, h₂.1.1.2.2.r7]
  have pre := h.pre
  have hf := pre.fS
  have zl := pre.Z_le
  have e1 := pre.oM_arrAt 1
  have fit1 := Nat.le_trans (arr_mono (w := P.W) (show mBase + 1 ≤ nArr by decide)) pre.fits
  have a1 : 256 ≤ arrAt P.w 1 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  unfold strideW
  refine wp_mov (op2_imm (by decide)) fun u1 v1 => ?_
  have hw1 := hw.of_upd v1 (by decide) (by decide) (by decide)
  have ea : State.addr (u1.gpr .r0 + BitVec.ofNat 32 224) = off (State.addr P.B) (P.oM + 224) := by
    rw [v1.other _ (by decide), r0, ← pre.M0_off]; exact addr_add (by have := pre.M0_toNat; omega)
  have eb : State.addr (u1.gpr .r0 + BitVec.ofNat 32 (224 + 4)) =
      off (State.addr P.B) (P.oM + 224) + BitVec.ofNat 64 4 := by
    rw [v1.other _ (by decide), r0, addr_add (by have := pre.M0_toNat; omega), pre.M0_addr, Offset.add_add,
      Offset.add_add]
  refine WP.mono (store64_ok u1 .r7 .r1 .r0 224 (off (State.addr P.B) (P.oM + 224)) (by decide) ea eb
    (hw1.write (by omega)) (by rw [Offset.add_add]; exact hw1.write (by omega))) fun t ⟨mt, rt⟩ => ?_
  have v64 : (u1.gpr .r1 ++ u1.gpr .r7) = BitVec.ofNat 64 (8 * (P.w + 2)) := by
    rw [v1.gpr, v1.other _ (by decide), hw.r7, pre.S_eq]
    apply BitVec.eq_of_toNat_eq
    have := pre.w4
    rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    simp
  rw [v64] at mt
  have out := writeW_outside u1.mem (State.addr P.B) (d := P.oM + 224) (BitVec.ofNat 64 (8 * (P.w + 2)))
    (by omega)
  rw [← mt, v1.mem] at out
  -- Within the header.
  have fH : Frame [⟨State.addr P.M0, 256⟩] s.mem t.mem := by
    rw [mt, v1.mem, ← pre.M0_off]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by
      have := pre.M0_toNat; omega))
  have kp := keep_of_frameH pre fH
  have ht : KS P σ (AX P σ) LX (V3 P σ) [sUsed] t :=
    h.core kp (by simp only [List.mem_range'_1]; intro j hj; simp only [nArr]; omega) (by simp)
      (by rw [rt.sp, v1.sp]) (by rw [rt.rd, v1.rd]) (by rw [rt.wr, v1.wr]) (h.arrs_keep kp (fun j hj hj' => by
        simp only [List.mem_range'_1] at hj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [mBase, aCm1, aTwo, aOne, aC] at hj' <;> omega)
        (by simp)) (h.sl_keep kp (by simp) (by simp)) h.live_lt h.ls_ok
  have sp : t.sp = s.sp := by rw [rt.sp, v1.sp]
  have a0 : 256 ≤ arrAt P.w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  have sv : t.mem.readW (State.addr t.sp) 32 = s.mem.readW (State.addr s.sp) 32 := by
    rw [sp, h.sp, pre.sp]
    refine fH.readW (r := P.rW0) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    refine pre.rW0_rM.sub_right ?_
    have := Offset.sub_base (State.addr P.M0) (d := 0) (n := 256) (k := 8 * P.lenM) (by simp only [CP.lenM]; omega)
    simpa only [BitVec.add_zero] using this
  refine ⟨⟨e, ht, hw1.rest rt⟩, ⟨m.of_outside pre out (fun d k hd => ?_) (.inr (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega))
    (by have := pre.oM_arrAt 5; have := Nat.le_trans (arr_mono (w := P.W) (show mBase + 5 ≤ nArr by decide)) pre.fits
        omega) sv sp (by rw [rt.rd, v1.rd]) (by rw [rt.wr, v1.wr]), ?_⟩⟩
  · rcases hd with h1 | ⟨h1, _⟩
    · left; omega
    · right; omega
  · unfold wordAt
    rw [show State.addr P.M0 + BitVec.ofNat 64 (8 * 28) = off (State.addr P.M0) 224 from rfl, pre.M0_off, mt,
      Mem.readW_writeW_self64]

/-- `MSp` of the same memory. -/
theorem MSp.of_same {σ s t : State} (h : MSp P σ s) (mem : t.mem = s.mem) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : MSp P σ t :=
  h.of_read (fun _ _ _ => by rw [mem]) (by rw [mem]) (by rw [mem, sp]) sp rd wr

/-- Montgomery multiplication modulo `c`: ready, with `R² mod c` in its array 4. -/
theorem montA_vp {E : State → Prop} : VP (SX P E) montA (fun σ s => SX P E σ s ∧ MS P σ s) := by
  simp only [montA, seqs]
  exact montSet_vp.seq (setup_vp.seq (pinv_vp.seq (r2_vp.seq (ctxClr_vp.seq
    ((mont0_vp (X := MSp P) (fun _ _ h => h) fun _ _ _ h m sp rd wr => h.of_same m sp rd wr).seq strideW_vp)))))

end

end VG.Proof.Dsa.Arm.Prime
