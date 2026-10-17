module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin1
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the results, as pieces

Status 0 (`finNone_vp`), 2 or 3 (`finUsed_vp`) with zeros to `out`, or 1
with the candidate (`finPrime_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem slot_lt (m : Mem) (B : BitVec 32) (d : Nat) : slot m B d < 2 ^ 32 := by
  simp only [slot, w32]; exact BitVec.isLt _

/-- A stage through a step that writes only `out` and `r0`–`r2`, `lr`. -/
theorem St.of_out {σ s t : State} (h : KS P σ (A σ) L (V σ) LS s) (hw : Ws s P.B P.Z P.W nArr)
    (f : Frame [P.rO] s.mem t.mem) (r : Rest [.r0, .r1, .r2, .lr] s t) :
    KS P σ (A σ) L (V σ) LS t ∧ Ws t P.B P.Z P.W nArr :=
  ⟨h.of_outZ (outZ_of_frame (P := P) f fun r' hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.pre.sO)
    (h.frame.trans (f.mono fun r' hr => by simp only [List.mem_singleton] at hr; subst hr; simp)) r.sp r.rd r.wr,
    hw.rest r⟩

/-- `used := [sUsed]`, and `r` returned. -/
theorem usedFinish_vp {r : Nat} {O : State → List Byte}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail r)) hc).isSome = true)
    (henc : encodable (BitVec.ofNat 32 r) = true) (hr : r < 2 ^ 32) (hU : sUsed ∈ LS) :
    VP (fun σ s => St P E A L V LS σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = O σ)
      (.block (([.ldr .r3 .r8 sUsed] : List Instr) ++ finish r)) (RF P E (fun _ => r) O (fun σ => V σ sUsed)) := by
  refine VP.block_append (VP.kv ldrUsed_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, o⟩ =>
    h.ldr hw hU (by decide) fun t _ _ u => WP.block_nil ⟨⟨e, h.bk.of_upd u, by rw [u.mem]; exact o⟩, u.gpr, ?_⟩)
    (finish_vp cert henc hr)
  rw [← h.sl sUsed hU]; exact slot_lt _ _ _

theorem zeroOS_vp :
    VP (St P E A L V LS) (VG.Impl.RsaKeyGen.Arm.Key.zeroOut foOut foL)
      (fun σ s => St P E A L V LS σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = List.replicate P.L 0) :=
  (zeroO_vp (Y := fun σ s => KS P σ (A σ) L (V σ) LS s ∧ Ws s P.B P.Z P.W nArr)
    fun _ _ _ ⟨h, hw⟩ _ f r => St.of_out h hw f r).mono (fun _ _ ⟨e, h, hw⟩ => ⟨e, h.bk, h, hw⟩)
    fun _ _ ⟨⟨e, _, h, hw⟩, o⟩ => ⟨⟨e, h, hw⟩, o⟩

/-- Status `r`, zeros to `out`, and `used := [sUsed]`. -/
theorem finUsed_vp {r : Nat}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2]) (.block (finTail r)) hc).isSome = true)
    (henc : encodable (BitVec.ofNat 32 r) = true) (hr : r < 2 ^ 32) (hU : sUsed ∈ LS) :
    VP (St P E A L V LS) (finUsed r) (RF P E (fun _ => r) (fun _ => List.replicate P.L 0) (fun σ => V σ sUsed)) :=
  zeroOS_vp.seq (usedFinish_vp cert henc hr hU)

/-- Status 0, zeros to `out` and `used`. -/
theorem finNone_vp :
    VP (fun σ s => E σ ∧ Bk P σ s) finNone (RF P E (fun _ => 0) (fun _ => List.replicate P.L 0) (fun _ => 0)) := by
  refine ((zeroO_vp (Y := fun _ _ => True) fun _ _ _ _ _ _ _ => trivial).mono
    (fun σ s ⟨e, h⟩ => ⟨e, h, trivial⟩) fun _ _ h => h).seq ?_
  refine VP.block_append (G := fun σ s => (E σ ∧ Bk P σ s ∧
    Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = List.replicate P.L 0) ∧
    s.gpr .r3 = BitVec.ofNat 32 0 ∧ 0 < 2 ^ 32) ?_ (finish_vp finTail0_taint (by decide) (by decide))
  refine VP.taint [] mov30_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
    fun σ s ⟨⟨e, h, _⟩, o⟩ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
      ⟨⟨e, h.of_upd u, by rw [u.mem]; exact o⟩, u.gpr, by decide⟩

/-- Status 1, the candidate in `[aC]` to `out`, and `used := [sUsed]`. -/
theorem finPrime_vp (hC : aC ∈ L) (hU : sUsed ∈ LS) (hlt : ∀ σ, E σ → A σ aC < 2 ^ (8 * P.L)) :
    VP (St P E A L V LS) finPrime
      (RF P E (fun _ => 1) (fun σ => Spec.Rsa.i2osp (A σ aC) P.L) (fun σ => V σ sUsed)) := by
  simp only [finPrime, seqs]
  refine VP.seq (VP.block_append (St.psetS setMask_taint (by decide) (by decide) (by decide))
    (H := fun σ s => St P E A L (fun σ => upd (V σ) sMask 1) (sMask :: LS) σ s ∧ s.gpr .r10 = P.oP ∧
      s.gpr .r11 = BitVec.ofNat 32 P.L) ?_) ?_
  · show VP _ (.block ([(Reg.r10, foOut), (Reg.r11, foL)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    refine h.ldrSp (o := foOut) (by decide) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r10]) (by simp)) u1.mem
    refine h1.ldrSp (o := foL) (by decide) fun t u2 => WP.block_nil ?_
    have r := (u1.rest (ws := [.r10, .r11]) (by simp)).trans (u2.rest (by simp))
    exact ⟨⟨e, h1.of_rest (u2.rest (ws := [.r11]) (by simp)) u2.mem, hw.rest r⟩,
      by rw [u2.other _ (by decide), u1.gpr, h.pre.wO], by rw [u2.gpr, h.pre.wL]⟩
  refine VP.seq (G := fun σ s => St P E A L (fun σ => upd (V σ) sMask 1) (sMask :: LS) σ s ∧
    Spec.Rsa.bytesAt s.mem (State.addr P.oP) P.L = Spec.Rsa.i2osp (A σ aC) P.L) ?_
    ((usedFinish_vp finTail1_taint (by decide) (by decide) (List.mem_cons_of_mem _ hU)).mono (fun _ _ h => h)
      fun σ s h => by
        obtain ⟨e, b, r0, o, u⟩ := h
        refine ⟨e, b, r0, o, ?_⟩
        rw [u]; dsimp only; rw [upd_ne _ _ (by decide)])
  refine VP.taint [.r7, .r8, .r9, .r10, .r11] storeC_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hw⟩, p10, p11⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  have pre := h.pre
  have hm : slot s.mem P.B VG.Impl.Rsa.Arm.CrtValues.sMask = 1 := by
    have := h.sl sMask (by simp); dsimp only at this; rw [upd_self] at this; exact this
  have hW : P.L ≤ 4 * P.W := by simp only [CP.W]; omega
  refine WP.mono (store_ok' hw (Z := P.Z) (w := P.W) (dst := P.oP) (k := P.L) (j := aC) (R := P.rO) (by decide)
    (h.live_lt aC hC) pre.sO.symm (by rw [h.wr]; exact pre.oW) rfl (by have := pre.k1; omega) hW pre.fO p10 p11
    (by rw [hm]) (Nat.le_trans (by decide) pre.hdr_Z)) fun t ⟨hwt, bt, ft, rt⟩ => ?_
  refine ⟨⟨e, (St.of_out (A := A) (L := L) (V := fun σ => upd (V σ) sMask 1) (LS := sMask :: LS) h hw ft rt).1,
    hwt⟩, ?_⟩
  rw [bt, hm, ite_eq_left rfl, h.arrs aC hC, Nat.mod_eq_of_lt (hlt σ e)]

end

end VG.Proof.RsaKeyGen.Arm.Cand
