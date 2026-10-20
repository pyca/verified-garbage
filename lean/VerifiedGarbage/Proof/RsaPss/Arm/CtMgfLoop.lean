module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS on ARMv7: `DB ⊕= MGF1(H, dbLen)`, the loop

An iteration of `mgfXor` (`mgfIter_vp`): the digest of `H ‖ C` for the
counter `c`, XORed into the `min(hLen, dbLen - c hLen)` bytes of `DB` from
`c hLen` on; and the loop of `⌈dbLen / hLen⌉` iterations (`mgf_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)
variable {lo db : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dbv : State → Nat → Byte}

/-- The digest of the seed and the counter at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < h.D, m (sa scr (oDig + i)) = (h.ok.SH.H.hash x).getD i 0

/-- The digest of `H ‖ C`. -/
theorem mgfD_vp (P : MP h L scr lo db seed Inv) (c : Nat) :
    VP (fun σ s => Ctx L scr σ s ∧ HI h L scr lo db c dbv seed Inv σ s.mem ∧
        ∀ i < 1 * h.B, s.mem (sa scr (oY + i)) = (seed σ ++ Spec.Rsa.i2osp c 4).getD i 0)
      (ctHash h.H)
      (fun σ s => Ctx L scr σ s ∧ HI h L scr lo db c dbv seed Inv σ s.mem ∧
        Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) := by
  have hB := h.B_le
  have hone : h.D + 5 + h.L ≤ h.B := h.one
  refine ctHash_vp h P.hg (nbm := 1) (by omega) (by decide) (msg := fun σ => seed σ ++ Spec.Rsa.i2osp c 4)
    (fun σ => by rw [List.length_append, P.sd σ, i2osp4_length]; omega) (fun σ m m' hm hf => ?_)
    (fun σ m hm => by rw [hm.2.1, List.length_append, P.sd σ, i2osp4_length]) fun σ m hm => hm.2.2
  rw [Nat.one_mul] at hf
  exact ⟨P.keep h hm.1 hf (fun r hr => List.mem_append_left _ hr) (P.ctW_away h),
    slot_keep hf (ctW_slot h P.hg (by omega) (by decide) (by decide)) hm.2.1,
    slot_keep hf (ctW_slot h P.hg (by omega) (by decide) (by decide)) hm.2.2⟩

/-- The XOR's registers. -/
theorem mgfE_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ HI h L scr lo db c dbv seed Inv σ s.mem ∧
        Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem)
      (.block (xorSet h.H))
      (fun σ s => Ctx L scr σ s ∧ (HI h L scr lo db c dbv seed Inv σ s.mem ∧
        Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .r0 = scr + BitVec.ofNat 32 (oEm + lo + c * h.D) ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .lr = BitVec.ofNat 32 (min h.D (db - c * h.D))) := by
  have hD := h.D_le
  have hN := h.N_le
  have hfit := P.fit
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, hd⟩ => ?_
  have hw : WP isa (.block (xorSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oEm + lo + c * h.D) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
      t.gpr .lr = if db - c * h.D < h.D then BitVec.ofNat 32 (db - c * h.D) else BitVec.ofNat 32 h.D := by
    prun [xorSet, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.lo σ _ hm.1.1,
      P.dbs σ _ hm.1.1, hm.1.2.done, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide),
      movw_val (show dig h.H < 2 ^ 16 by show h.D < 2 ^ 16; omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Offset.ofNat_sub_ofNat (w := 32) (show c * h.D ≤ db by omega),
      ltBit (a := db - c * h.D) (b := h.D) (by omega) (by omega), neg_bit, neg_bit', selW, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨hc.regs rd wr sp m, m ▸ ⟨hm, hd⟩, r0, r1, ?_⟩
  rw [lr]
  split
  · rw [Nat.min_eq_right (by omega)]
  · rw [Nat.min_eq_left (by omega)]

/-- The memory after the XOR of iteration `c`. -/
structure DX (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : Nat → Byte) (seed : List Byte) (m : Mem) : Prop where
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * h.D)
  dbx : ∀ i < db, m (sa scr (oEm + lo + i)) =
    if i < c * h.D + h.D then dbv i ^^^ (Spec.Mgf1.mgf1 h.G seed db).getD i 0 else dbv i
  sd : ∀ i < h.D, m (sa scr (oEm + lo + db + i)) = seed.getD i 0

/-- A byte of the mask, in the digest of iteration `c`. -/
theorem mask_byte {seed : List Byte} {c i : Nat} (hi : i < db) (h₁ : c * h.D ≤ i) (h₂ : i < c * h.D + h.D) :
    (Spec.Mgf1.mgf1 h.G seed db).getD i 0 = (h.ok.SH.H.hash (seed ++ Spec.Rsa.i2osp c 4)).getD (i - c * h.D) 0 := by
  have hv := h.valid
  have hD0 := h.D_pos
  have glen : h.G.len = h.D := h.glen
  rw [RsaPss.mgf1_getD hv _ hi, glen, ← h.hash]
  have e1 : i / h.D = c := Nat.div_eq_of_lt_le h₁ (by rw [Nat.succ_mul]; omega)
  have e2 : i % h.D = i - c * h.D := by
    have := Nat.mod_add_div i h.D
    rw [e1, Nat.mul_comm] at this
    omega
  rw [e1, e2]

/-- The XOR of the digest into `DB`. -/
theorem mgfF_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ (HI h L scr lo db c dbv seed Inv σ s.mem ∧
        Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .r0 = scr + BitVec.ofNat 32 (oEm + lo + c * h.D) ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .lr = BitVec.ofNat 32 (min h.D (db - c * h.D)))
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX h L scr lo db c (dbv σ) (seed σ) s.mem) := by
  have hD := h.D_le
  have hD0 := h.D_pos
  have hN := h.N_le
  have hfit := P.fit
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hn : min h.D (db - c * h.D) = n
  have hn0 : 0 < n := by omega
  have hnD : n ≤ h.D := by omega
  have hnd : c * h.D + n ≤ db := by omega
  refine (xor_vp hg (od := oEm + lo + c * h.D) (os := oDig) (n := n) hn0 (by pomega) (by pomega) (by pomega)
    (X := fun σ m => HI h L scr lo db c dbv seed Inv σ m ∧ Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) m)).mono
    (fun _ _ h => h) fun σ s ⟨hc, m₀, ⟨hm, hd⟩, hf, hx⟩ => ⟨hc, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · have hsub : ∀ r ∈ [sR scr (oEm + lo + c * h.D) n], ∃ r' ∈ mgfW h L scr lo db, Region.Sub r r' := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sR scr (oEm + lo) db, by simp, by
        rw [show oEm + lo + c * h.D = (oEm + lo) + c * h.D from rfl]; exact Offset.sub _ (by omega) (by omega)⟩
    exact P.I σ _ _ hm.1.1 (Frame.sub hf hsub)
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide)) hm.1.2.ctr
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide)) hm.1.2.done
  · have old := hm.1.2.dbx i hi
    by_cases h1 : i < c * h.D
    · rw [ite_eq_left (by omega)]
      rw [ite_eq_left h1] at old
      rw [← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := oEm + lo + i) (n := 1) (by pomega) (by pomega) (by pomega) _
          (Region.contains_self _ _)
    rw [ite_eq_right h1] at old
    by_cases h2 : i < c * h.D + n
    · rw [ite_eq_left (by omega), mask_byte h (c := c) hi (by omega) (by omega), ← hd _ (by omega), ← old]
      have e := hx (i - c * h.D) (by omega)
      rw [show oEm + lo + c * h.D + (i - c * h.D) = oEm + lo + i by omega] at e
      exact e
    · rw [ite_eq_right (by omega), ← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := oEm + lo + i) (n := 1) (by pomega) (by pomega) (by pomega) _
          (Region.contains_self _ _)
  · exact sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega))
      (by pomega) hm.1.2.sd

theorem bit_z (p : Prop) [Decidable p] : ((if p then (1 : BitVec 32) else 0) - 0 == 0) = decide (¬ p) := by
  by_cases hp : p <;> simp [hp]

/-- The next counter and bytes masked. -/
theorem mgfG_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX h L scr lo db c (dbv σ) (seed σ) s.mem)
      (.block (mgfNext h.H))
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db (c + 1) dbv seed Inv σ s.mem ∧
        s.z = decide (db ≤ c * h.D + h.D)) := by
  have hD := h.D_le
  have hN := h.N_le
  have hfit := P.fit
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hm⟩ => ?_
  have r1 : ∀ v : BitVec 32, (s.mem.writeW (L.fr sCtr) v).readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * h.D) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide), hm.done]
  have r2 : ∀ v w : BitVec 32, ((s.mem.writeW (L.fr sCtr) v).writeW (L.fr sDone) w).readW (L.fr sDb) 32 =
      BitVec.ofNat 32 db :=
    fun v w => by rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      P.dbs σ _ hi]
  have hw : WP isa (.block (mgfNext h.H)) s fun t =>
      t.mem = (s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1))).writeW (L.fr sDone)
        (BitVec.ofNat 32 (c * h.D + h.D)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (db ≤ c * h.D + h.D) := by
    prun [mgfNext, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hm.ctr, r1, r2,
      movw_val (show dig h.H < 2 ^ 16 by show h.D < 2 ^ 16; omega), VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32,
      BitVec.ofNat_add_ofNat, ltBit (a := c * h.D + h.D) (b := db) (by omega) (by omega), bit_z, dpVal]
    simp only [decide_eq_decide]
    omega
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t.mem := by
    rw [m]
    exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_⟩⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotW hg (by decide)
    · exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotSep (by decide) (by decide) (by decide)
    · exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32, Nat.succ_mul]
  · intro i hi'
    rw [Nat.succ_mul]
    exact sbytes_keep fr (fun r hr => dis r hr _ _ (by pomega)) (by pomega) hm.dbx i hi'
  · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by pomega)) (by pomega) hm.sd

/-- An iteration of `mgfXor`. -/
theorem mgfIter_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem)
      (mgfBody h.H)
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db (c + 1) dbv seed Inv σ s.mem ∧
        s.z = decide (db ≤ c * h.D + h.D)) := by
  have hc32 : c < 2 ^ 32 := by
    have := P.fit
    have : c ≤ c * h.D := Nat.le_mul_of_pos_right c h.D_pos
    omega
  show VP _ (.seq (.block (mgfClr h.H)) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (mgfSeed h.H))
    (.seq Impl.Bignum.Arm.copyBytes (.seq (.block (ctrSet h.H)) (.seq (.block ctrPut) (.seq (ctHash h.H)
      (.seq (.block (xorSet h.H)) (.seq (countLoop xorBody) (.block (mgfNext h.H))))))))))) _
  exact VP.assoc (VP.seq (mgfA_vp h (dbv := dbv) P c) (VP.assoc (VP.seq (mgfB_vp h P c)
    (VP.assoc (VP.seq (mgfC_vp h P hc32) (VP.seq (mgfD_vp h P c) (VP.seq (mgfE_vp h P hcd)
      (VP.seq (mgfF_vp h P hcd) (mgfG_vp h P hcd)))))))))

/-- `DB ⊕= MGF1(H, dbLen)`. -/
theorem mgf_vp (P : MP h L scr lo db seed Inv) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < db, s.mem (sa scr (oEm + lo + i)) = dbv σ i) ∧
        ∀ i < h.D, s.mem (sa scr (oEm + lo + db + i)) = (seed σ).getD i 0)
      (mgfXor h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        (∀ i < db, s.mem (sa scr (oEm + lo + i)) = dbv σ i ^^^ (Spec.Mgf1.mgf1 h.G (seed σ) db).getD i 0) ∧
        ∀ i < h.D, s.mem (sa scr (oEm + lo + db + i)) = (seed σ).getD i 0) := by
  have hD := h.D_le
  have hD0 := h.D_pos
  have hN := h.N_le
  have hfit := P.fit
  have hdb := P.db0
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hK : (db + h.D - 1) / h.D = K
  have hK0 : 0 < K := by
    rw [← hK]; exact (Nat.le_div_iff_mul_le hD0).2 (by omega)
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ MI h L scr lo db 0 dbv seed Inv σ s.mem)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hd, hs⟩ => ?_) ?_
  · have hw : WP isa (.block mgfInit) s fun t =>
        t.mem = (s.mem.writeW (L.fr sCtr) (0 : BitVec 32)).writeW (L.fr sDone) (0 : BitVec 32) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [mgfInit, sp0, st, mw, hc.st.sp, hc.aFr hg, hc.wFr hg]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t.mem := by
      rw [m]
      exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
    have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
      intro r hr o n hon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
      P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, fun i hi' => ?_, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotW hg (by decide)
      · exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotSep (by decide) (by decide) (by decide)
      · exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [m, Mem.readW_writeW_self32, Nat.zero_mul]; rfl
    · rw [ite_eq_right (by omega)]
      exact sbytes_keep fr (fun r hr => dis r hr _ _ (by pomega)) (by pomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by pomega)) (by pomega) hs
  refine (VP.loop (I := fun k σ s => k ≤ K ∧ Ctx L scr σ s ∧ MI h L scr lo db (K - k) dbv seed Inv σ s.mem)
    (fun k => ?_) (K - 1)).mono (fun σ s hs => ⟨by omega, by rw [show K - (K - 1 + 1) = 0 by omega]; exact hs⟩)
    fun _ _ h => h
  by_cases hk : k + 1 ≤ K
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hk h
  generalize hc : K - (k + 1) = c
  have key : ∀ x, (db + h.D - 1) / h.D ≤ x + 1 ↔ db ≤ x * h.D + h.D := fun x => by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hD0, Nat.succ_mul, Nat.succ_mul]
    omega
  have hcd : c * h.D < db := by
    have := (Nat.le_div_iff_mul_le hD0).1 (show c + 1 ≤ (db + h.D - 1) / h.D by omega)
    rw [Nat.succ_mul] at this
    omega
  refine (mgfIter_vp h P hcd).mono (fun σ s ⟨_, hs⟩ => hs) fun σ s ⟨hc', hm, z⟩ => ⟨?_, fun h0 => ?_, fun hp => ?_⟩
  · rw [VG.Proof.X25519.Arm.eval_ne, z]
    have e := key c
    rw [hK] at e
    by_cases hz : k = 0
    · rw [decide_eq_true (e.1 (by omega)), hz]; rfl
    · rw [decide_eq_false (fun h' => hz (by have := e.2 h'; omega))]
      simp only [Bool.not_false, Option.some.injEq]
      exact (decide_eq_true (by omega)).symm
  · have e := (key c).1 (by omega)
    refine ⟨hc', hm.1, fun i hi => ?_, hm.2.sd⟩
    rw [hm.2.dbx i hi, ite_eq_left (by rw [Nat.succ_mul]; omega)]
  · exact ⟨by omega, hc', by rw [show K - k = c + 1 by omega]; exact hm⟩

end VG.Proof.RsaPss.Arm
