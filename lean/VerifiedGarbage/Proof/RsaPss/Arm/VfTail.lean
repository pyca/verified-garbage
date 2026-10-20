module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfPos
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the end of both paths

Whichever path put `M'` in `Y` (`msg`), with its length and blocks in their
slots: its hash compared with `H`, and the result, 1 exactly when `acc` is
zero and the hashes are equal (`tail_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- Away from what `K2` reads. -/
abbrev Away2 (L : Lay) (scr : BitVec 32) (r : Region) : Prop :=
  (slotR L sC).Disjoint r ∧ (slotR L sLo).Disjoint r ∧ (slotR L sDb).Disjoint r ∧ (slotR L sAny).Disjoint r ∧
    (slotR L sPos).Disjoint r ∧ (slotR L sAcc).Disjoint r ∧ (sR scr oEm 1024).Disjoint r

theorem K2.keep {P : EP} {τ : State} {m m' : Mem} {rs : List Region} (hk : K2 h P τ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away2 (P.lay h.D) P.scr r) : K2 h P τ m' := by
  obtain ⟨hi, hfi, ⟨b1, b2, b3, b4⟩, hd, hh, hp, hac⟩ := hk
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hfi
  have kb : ∀ x < 1024, m' (sa P.scr (oEm + x)) = m (sa P.scr (oEm + x)) := fun x hx =>
    sbytes_keep hf (o := oEm) (n := 1024) (fun r hr => (ha r hr).2.2.2.2.2.2) (by decide)
      (f := fun i => m (sa P.scr (oEm + i))) (fun _ _ => rfl) x hx
  refine ⟨hi, hfi, ⟨slot_keep hf (fun r hr => (ha r hr).1) b1, slot_keep hf (fun r hr => (ha r hr).2.1) b2,
    slot_keep hf (fun r hr => (ha r hr).2.2.1) b3, slot_keep hf (fun r hr => (ha r hr).2.2.2.1) b4⟩,
    fun i hi' => ?_, fun i hi' => ?_, slot_keep hf (fun r hr => (ha r hr).2.2.2.2.1) hp,
    slot_keep hf (fun r hr => (ha r hr).2.2.2.2.2.1) hac⟩
  · have e := kb (lo P + i) (by omega)
    rw [← Nat.add_assoc] at e
    rw [e]; exact hd i hi'
  · have e := kb (lo P + dbN h P + i) (by omega)
    rw [show oEm + (lo P + dbN h P + i) = oEm + lo P + dbN h P + i by omega] at e
    rw [e]; exact hh i hi'

theorem away2_ctW {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctW h L scr T, Away2 L scr r := fun r hr =>
  ⟨ctW_slot h hg hT (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) r hr,
    ctW_em h hg hT (Nat.le_refl _) (by decide) r hr⟩

/-- What `ctHash` keeps, with `M'`'s length and blocks in their slots. -/
abbrev Kt (P : EP) (msg : State → List Byte) (nbm : Nat) (τ : State) (m : Mem) : Prop :=
  K2 h P τ m ∧ m.readW ((P.lay h.D).fr sL) 32 = BitVec.ofNat 32 (msg τ).length ∧
    m.readW ((P.lay h.D).fr sNb) 32 = BitVec.ofNat 32 nbm

/-- The hash of `x` is `H`. -/
abbrev HOk (P : EP) (τ : State) (x : List Byte) : Prop :=
  ∀ i < h.D, (h.ok.SH.H.hash x).getD i 0 = (seedV h P τ).getD i 0

theorem res_eq (x : BitVec 32) : (x ||| 0 - x) >>> 31 ^^^ 1 = if x = 0 then 1 else 0 := by
  rw [BitVec.or_comm, nzW]
  by_cases e : x = 0
  · rw [ite_eq_left e, ite_eq_left e]; decide
  · rw [ite_eq_right e, ite_eq_right e]; decide

/-- The hash of `M'` compared with `H`, and the result. -/
theorem tail_vp (P : EP) (hP : ∃ σ, In h.D P σ) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ τ, (msg τ).length + 1 + h.L ≤ nbm * h.B) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa P.scr (oY + i)) = (msg τ).getD i 0)
      (.seq (ctHash h.H) (cmpH h.H))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (msg τ) then 1 else 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oDig = 832 := rfl
  refine (ctHash_vp h hg hnb hnb0 hfit (Inv := Kt h P msg nbm)
    (fun τ m m' hk hf' => ⟨K2.keep h hk.1 hf' (away2_ctW h hg hnb),
      slot_keep hf' (ctW_slot h hg hnb (by decide) (by decide)) hk.2.1,
      slot_keep hf' (ctW_slot h hg hnb (by decide) (by decide)) hk.2.2⟩)
    (fun τ m hk => hk.2.1) (fun τ m hk => hk.2.2)).seq ?_
  show VP _ (.seq (.block (cmpSet h.H)) (.seq Impl.Bignum.Arm.compareBytes (.block result))) _
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        ∀ i < h.D, s.mem (sa P.scr (oDig + i)) = (h.ok.SH.H.hash (msg τ)).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 oDig ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧
      s.gpr .lr = BitVec.ofNat 32 h.D ∧ s.gpr .r2 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hd⟩ => ?_)
    (VP.seq (G := fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        (s.gpr .r2 = 0 ↔ HOk h P τ (msg τ)))
      ((cmp_vp (hg.rbuf (o := oDig) (n := h.D) (by omega) hD0)
        (hg.rbuf (o := oEm + lo P + dbN h P) (n := h.D) (by omega) hD0) hD0 (Inv := Kt h P msg nbm)
        (f := fun τ i => (h.ok.SH.H.hash (msg τ)).getD i 0) (g := fun τ i => (seedV h P τ).getD i 0)).mono
        (fun τ s ⟨⟨hc, hk, hd⟩, r0, r1, lr, r2⟩ => ⟨hc, hk, r0, r1, lr, r2, fun i hi => ?_, fun i hi => ?_⟩)
        fun τ s h' => h')
      (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hr⟩ => ?_))
  · have hw : WP isa (.block (cmpSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oDig ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧
        t.gpr .lr = BitVec.ofNat 32 h.D ∧ t.gpr .r2 = 0 := by
      prun [cmpSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1.2.1,
        hk.1.2.2.1.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide),
        movw_val (show 0 < 2 ^ 16 by decide), movw_val (show dig h.H < 2 ^ 16 by show h.D < 2 ^ 16; omega),
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rfl
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd⟩, r0, r1, lr, r2⟩
  · rw [hg.byteAt_scr (by omega)]; exact hd i hi
  · rw [hg.byteAt_scr (by omega)]; exact hk.1.2.2.2.2.1 i hi
  · have hw : WP isa (.block result) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = ((acc2 h P τ ||| s.gpr .r2) ||| 0 - (acc2 h P τ ||| s.gpr .r2)) >>> 31 ^^^ 1 := by
      prun [result, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.2.2.2.2,
        movw_val (show 0 < 2 ^ 16 by decide), dpVal]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0⟩ => ⟨hc.regs rd wr sp m, m ▸ hk.1, ?_⟩
    have oz : ∀ x y : BitVec 32, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun x y => BitVec.or_eq_zero_iff
    rw [r0, res_eq]
    simp only [oz, hr]

end VG.Proof.RsaPss.Arm.Vf
