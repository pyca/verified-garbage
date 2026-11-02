module
public import VerifiedGarbage.Proof.Rsa.Arm.RvFin5

import VerifiedGarbage.Proof.Rsa.Arm.RvStore
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: the factors written out (`storesD_vp`)

`Recover.stores` from arrays 5 and 6 holding any `p` and `q`, below `2^(8 k)`
where the mask `ok` holds.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- The outputs. -/
abbrev outPD (P : RP) (pv : State → Nat) (ok : State → Bool) (σ : State) : List Byte :=
  if ok σ then Spec.Rsa.i2osp (pv σ) P.K else List.replicate P.K 0
abbrev outQD (P : RP) (qv : State → Nat) (ok : State → Bool) (σ : State) : List Byte :=
  if ok σ then Spec.Rsa.i2osp (qv σ) P.K else List.replicate P.K 0

/-- Before the stores: `p` and `q` in arrays 5 and 6, the mask in `sMask`. -/
abbrev FoD (P : RP) (E : State → Prop) (pv qv : State → Nat) (ok : State → Bool) : State → State → Prop :=
  Sk P E (fun σ => upd (upd (fun _ => 0) 5 (pv σ)) 6 (qv σ)) [6, 5] (fun _ _ => 0) []
    (fun σ => upd (fun _ => 0) sMask (b2n (ok σ))) [sMask] P.w nArr

/-- The end of the body. -/
abbrev FeD (P : RP) (E : State → Prop) (pv qv : State → Nat) (ok : State → Bool) (σ s : State) : Prop :=
  E σ ∧ Bo P σ s ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = outPD P pv ok σ ∧
    Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = outQD P qv ok σ ∧ s.gpr .r0 = BitVec.ofNat 32 (b2n (ok σ))

section
variable {P : RP}

/-- After `p`. -/
abbrev Fs1D (P : RP) (E : State → Prop) (pv qv : State → Nat) (ok : State → Bool) (σ s : State) : Prop :=
  E σ ∧ Bo P σ s ∧ Ws s P.B P.Z P.w nArr ∧ slot s.mem P.B sMask = b2n (ok σ) ∧
    num s.mem P.B P.w 6 = qv σ ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = outPD P pv ok σ

theorem storePD_vp {E : State → Prop} (pv qv : State → Nat) (ok : State → Bool)
    (hp : ∀ σ, E σ → ok σ = true → pv σ < 2 ^ (8 * P.K)) :
    VP (fun σ s => FoD P E pv qv ok σ s ∧ s.gpr .r10 = P.pP ∧ s.gpr .r11 = BitVec.ofNat 32 P.K)
      (VG.Impl.Rsa.Arm.CrtValues.store 5) (Fs1D P E pv qv ok) := by
  refine VP.taint [.r7, .r8, .r9, .r10, .r11] storeP_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hw⟩, p10, p11⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  have pre := h.bs.pre
  have sz := pre.sizes
  have kw := sz.kw
  have vM : slot s.mem P.B sMask = b2n (ok σ) := by rw [h.sl sMask (by simp)]; simp [upd]
  have vM' : slot s.mem P.B VG.Impl.Rsa.Arm.CrtValues.sMask = b2n (ok σ) := vM
  refine WP.mono (store_ok' hw (Z := P.Z) (w := P.w) (dst := P.pP) (k := P.K) (j := 5) (R := P.rP) (by decide) (by decide) pre.sP.symm
    (by rw [h.bs.wr, pre.wr]; simp) rfl (by have := pre.k1; omega) (by omega) pre.fP p10 p11
    (by rw [vM']; exact VG.Proof.Rsa.b2n_le _) (Nat.le_trans (by decide) (hdr_Z sz)))
    fun t ⟨hwt, bt, ft, rt⟩ => ⟨e, ⟨pre, rt.sp.trans h.bs.sp, rt.rd.trans h.bs.rd, rt.wr.trans h.bs.wr,
      (h.bs.frame.mono (by simp)).trans (ft.mono (by simp))⟩, hwt, ?_, ?_, ?_⟩
  · rw [← vM]; exact w32_frame ft pre.sP.symm (Z_64 sz) (Nat.le_trans (by decide) (hdr_Z sz))
  · rw [num_frame ft pre.sP.symm sz (by decide), h.arrs 6 (by simp)]; simp [upd]
  · rw [bt, vM', h.arrs 5 (by simp)]
    have e5 : upd (upd (fun _ => 0) 5 (pv σ)) 6 (qv σ) 5 = pv σ := by simp [upd]
    dsimp only
    rw [e5]
    simp only [outPD]
    cases hok : ok σ
    · simp [b2n]
    · rw [Nat.mod_eq_of_lt (hp σ e hok)]; simp [b2n]

theorem storeQD_vp {E : State → Prop} (pv qv : State → Nat) (ok : State → Bool)
    (hq : ∀ σ, E σ → ok σ = true → qv σ < 2 ^ (8 * P.K)) :
    VP (fun σ s => Fs1D P E pv qv ok σ s ∧ s.gpr .r10 = P.qP ∧ s.gpr .r11 = BitVec.ofNat 32 P.K)
      (VG.Impl.Rsa.Arm.CrtValues.store 6) (fun σ s => E σ ∧ Bo P σ s ∧ Ws s P.B P.Z P.w nArr ∧
        slot s.mem P.B sMask = b2n (ok σ) ∧ Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = outPD P pv ok σ ∧
        Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = outQD P qv ok σ) := by
  refine VP.taint [.r7, .r8, .r9, .r10, .r11] storeQ_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hw, vM, v6, bp⟩, p10, p11⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.1.2.2.1.r7, h₂.1.2.2.1.r7]
    · rw [h₁.1.2.2.1.r8, h₂.1.2.2.1.r8]
    · rw [h₁.1.2.2.1.r9, h₂.1.2.2.1.r9]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  have pre := h.pre
  have sz := pre.sizes
  have kw := sz.kw
  have vM' : slot s.mem P.B VG.Impl.Rsa.Arm.CrtValues.sMask = b2n (ok σ) := vM
  refine WP.mono (store_ok' hw (Z := P.Z) (w := P.w) (dst := P.qP) (k := P.K) (j := 6) (R := P.rQ) (by decide) (by decide)
    pre.sQ.symm (by rw [h.wr, pre.wr]; simp) rfl (by have := pre.k1; omega) (by omega) pre.fQ p10 p11
    (by rw [vM']; exact VG.Proof.Rsa.b2n_le _) (Nat.le_trans (by decide) (hdr_Z sz)))
    fun t ⟨hwt, bt, ft, rt⟩ => ⟨e, ⟨pre, rt.sp.trans h.sp, rt.rd.trans h.rd, rt.wr.trans h.wr,
      h.frame.trans (ft.mono (by simp))⟩, hwt, ?_, ?_, ?_⟩
  · rw [← vM]; exact w32_frame ft pre.sQ.symm (Z_64 sz) (Nat.le_trans (by decide) (hdr_Z sz))
  · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame ft (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pre.pQ) (by have := pre.k2; omega), bp]
  · rw [bt, vM', v6]
    simp only [outQD]
    cases hok : ok σ
    · simp [b2n]
    · rw [Nat.mod_eq_of_lt (hq σ e hok)]; simp [b2n]

/-- The factors written out, and the mask returned. -/
theorem storesD_vp {E : State → Prop} (pv qv : State → Nat) (ok : State → Bool)
    (hp : ∀ σ, E σ → ok σ = true → pv σ < 2 ^ (8 * P.K))
    (hq : ∀ σ, E σ → ok σ = true → qv σ < 2 ^ (8 * P.K)) :
    VP (FoD P E pv qv ok) stores (FeD P E pv qv ok) := by
  simp only [stores, seqs]
  refine VP.seq (G := fun σ s => FoD P E pv qv ok σ s ∧ s.gpr .r10 = P.pP ∧ s.gpr .r11 = BitVec.ofNat 32 P.K) ?_
    (VP.seq (storePD_vp pv qv ok hp) (VP.seq (G := fun σ s => Fs1D P E pv qv ok σ s ∧ s.gpr .r10 = P.qP ∧
      s.gpr .r11 = BitVec.ofNat 32 P.K) ?_ (VP.seq (storeQD_vp pv qv ok hq) ?_)))
  · show VP _ (.block ([(Reg.r10, oP), (Reg.r11, aoK)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · refine h.bs.ldrSp (o := oP) (by decide) (by decide) (by decide) fun s1 u1 => ?_
      obtain ⟨h1, hw1⟩ := h.reg hw (u1.rest (ws := [.r10]) (by simp)) u1.mem
      refine h1.bs.ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
      obtain ⟨ht, hwt⟩ := h1.reg hw1 (u2.rest (ws := [.r11]) (by simp)) u2.mem
      exact ⟨⟨e, ht, hwt⟩, by rw [u2.other _ (by decide), u1.gpr, h.bs.pre.wP], by rw [u2.gpr, h.bs.pre.aK]⟩
  · show VP _ (.block ([(Reg.r10, oQ), (Reg.r11, aoK)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw, vM, v6, bp⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · refine h.ldrSp (o := oQ) (by decide) (by decide) (by decide) fun s1 u1 => ?_
      refine (h.of_upd u1).ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
      exact ⟨⟨e, (h.of_upd u1).of_upd u2, (hw.of_upd u1 (by decide) (by decide) (by decide)).of_upd u2 (by decide)
        (by decide) (by decide), by rw [u2.mem, u1.mem]; exact vM, by rw [u2.mem, u1.mem]; exact v6,
        by rw [u2.mem, u1.mem]; exact bp⟩, by rw [u2.other _ (by decide), u1.gpr, h.pre.wQ],
        by rw [u2.gpr, h.pre.aK]⟩
  · refine VP.ctx ret_taint (fun _ _ h => h.2.2.1) fun σ s ⟨e, h, hw, vM, bp, bq⟩ => ?_
    refine wp_ldrSlot hw (d := sMask) (by decide) fun t u => WP.block_nil ⟨e, h.of_upd u, by rw [u.mem]; exact bp,
      by rw [u.mem]; exact bq, ?_⟩
    rw [u.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le (ok σ); omega), ← vM]

end

end VG.Proof.Rsa.Arm.Recover
