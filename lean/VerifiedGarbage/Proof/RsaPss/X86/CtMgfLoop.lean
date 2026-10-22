module

public import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtXor
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: `DB ⊕= MGF1(H, dbLen)`

`mgf_vp`: with `DB` at `oEm + lo` (`dbLen` bytes, both in their slots) and
the seed `H` after it, `mgfXor` XORs MGF1's mask of `H` into `DB`, one
digest of `H ‖ C` (hashed by `ctHash` in one block) at a time.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)
variable {lo db : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dbv : State → Nat → Byte}

/-- The digest of the seed and the counter at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < h.D, m (sa scr (oDig + i)) = (h.ok.hH.SH.H.hash x).getD i 0

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
    slot_keep hf (ctW_slot h P.hg (by omega) (by decide) (by decide) (by decide)) hm.2.1,
    slot_keep hf (ctW_slot h P.hg (by omega) (by decide) (by decide) (by decide)) hm.2.2⟩

/-- `min(hLen, x)`, by a mask. -/
theorem minSel {x D : Nat} (hx : x < 2 ^ 32) (hD : D < 2 ^ 32) :
    ((BitVec.ofNat 32 x - BitVec.ofNat 32 D) &&&
        (if decide ((BitVec.ofNat 32 x).toNat < (BitVec.ofNat 32 D).toNat) = true then BitVec.allOnes 32 else 0)) +
      BitVec.ofNat 32 D = BitVec.ofNat 32 (min D x) := by
  rw [toNat_ofNat_lt hx, toNat_ofNat_lt hD]
  by_cases e : x < D
  · rw [ite_eq_left (by simp [e]), BitVec.and_allOnes, BitVec.sub_add_cancel, Nat.min_eq_right (by omega)]
  · rw [ite_eq_right (by simp [e]), Nat.min_eq_left (by omega)]
    simp

/-- The XOR's registers. -/
theorem mgfE_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ HI h L scr lo db c dbv seed Inv σ s.mem ∧
        Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem)
      (.block (xorSet h.H))
      (fun σ s => Ctx L scr σ s ∧ (HI h L scr lo db c dbv seed Inv σ s.mem ∧
        Dg h scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .edi = scr + BitVec.ofNat 32 (oEm + lo + c * h.D) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .ecx = BitVec.ofNat 32 (min h.D (db - c * h.D))) := by
  have hD := h.D_le
  have hN := h.N_le
  have hfit := P.fit
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.xorSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, hd⟩ => ?_
  simp only [xorSet, atDb, atS, addSlot, addi, ld, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
    List.nil_append]
  have rS : ∀ {t : State} (d : Nat), Ctx L scr σ t → d + 4 ≤ frameBytes →
      InRegions (t.rd ++ t.wr) (VG.X86.addr L.B d) 4 := fun d ct hd => by
    rw [hg.aFr ok d hd]; exact ct.rFr hg d hd
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_addm (B := L.B) (by rw [c2.st.sp]) (rS sLo c2 (by decide)) fun t3 u3 => ?_
  have c3 : Ctx L scr σ t3 := c2.upd u3 (by decide) (by decide)
  refine wp_addm (B := L.B) (by rw [c3.st.sp]) (rS sDone c3 (by decide)) fun t4 u4 => ?_
  refine wp_mov fun t5 u5 => wp_addi fun t6 u6 => ?_
  have c6 : Ctx L scr σ t6 := ((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
    (by decide) (by decide)
  refine c6.wp_slot hg (by decide) (by decide) (by decide) fun t7 c7 u7 => ?_
  refine wp_subm (B := L.B) (by rw [c7.st.sp]) (rS sDone c7 (by decide)) fun t8 u8 => ?_
  refine wp_mov fun t9 u9 => wp_subi fun t10 u10 c10 _ => wp_sbb_self c10 fun t11 u11 => ?_
  refine wp_and fun t12 u12 => wp_addi fun t13 u13 => wp_mov fun t14 u14 => WP.block_nil ?_
  have m14 : t14.mem = s.mem := by
    rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem,
      u2.mem, u1.mem]
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hx : db - c * h.D < 2 ^ 32 := by omega
  have e8 : t8.gpr .ecx = BitVec.ofNat 32 (db - c * h.D) := by
    rw [u8.gpr, u7.gpr, m7, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sDone (by decide),
      P.dbs σ _ hm.1.1, hm.1.2.done, sub_ofNat (by omega)]
  refine ⟨((((((((c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).upd u9 (by decide)
    (by decide)).upd u10 (by decide) (by decide)).upd u11 (by decide) (by decide)).upd u12 (by decide)
    (by decide)).upd u13 (by decide) (by decide)).upd u14 (by decide) (by decide)), by rw [m14]; exact ⟨hm, hd⟩,
    ?_, ?_, ?_⟩
  · simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.other, u5.other, u4.gpr, u3.gpr, u2.gpr, u1.gpr, hc.ebp, u3.mem, u2.mem, u1.mem,
      hg.aFr ok sLo (by decide), hg.aFr ok sDone (by decide), P.lo σ _ hm.1.1, hm.1.2.done, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · simp (disch := decide) only [u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other,
      u7.other, u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
  · rw [u14.gpr, u13.gpr, u12.gpr, u11.gpr, u11.other .eax (by decide), u10.gpr, u9.gpr, e8,
      minSel hx (by have : h.H.D ≤ 64 := Nat.le_trans h.D_le h.N_le; omega)]

/-- The memory after the XOR of iteration `c`. -/
structure DX (L : Lay) (scr : BitVec 32) (lo db c : Nat) (dbv : Nat → Byte) (seed : List Byte) (m : Mem) : Prop where
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * h.D)
  dbx : ∀ i < db, m (sa scr (oEm + lo + i)) =
    if i < c * h.D + h.D then dbv i ^^^ (Spec.Mgf1.mgf1 h.G seed db).getD i 0 else dbv i
  sd : ∀ i < h.D, m (sa scr (oEm + lo + db + i)) = seed.getD i 0

/-- A byte of the mask, in the digest of iteration `c`. -/
theorem mask_byte {seed : List Byte} {c i : Nat} (hi : i < db) (h₁ : c * h.D ≤ i) (h₂ : i < c * h.D + h.D) :
    (Spec.Mgf1.mgf1 h.G seed db).getD i 0 =
      (h.ok.hH.SH.H.hash (seed ++ Spec.Rsa.i2osp c 4)).getD (i - c * h.D) 0 := by
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
        s.gpr .edi = scr + BitVec.ofNat 32 (oEm + lo + c * h.D) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .ecx = BitVec.ofNat 32 (min h.D (db - c * h.D)))
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

/-- The next counter and bytes masked. -/
theorem mgfG_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX h L scr lo db c (dbv σ) (seed σ) s.mem)
      (.block (mgfNext h.H))
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db (c + 1) dbv seed Inv σ s.mem ∧
        s.cf = some (decide (c * h.D + h.D < db))) := by
  have hD := h.D_le
  have hN := h.N_le
  have hfit := P.fit
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.mgfNext (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hm⟩ => ?_
  simp only [mgfNext, ld, st, addi, Impl.RsaPkcs1Sig.X86.stk]
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_addi fun t2 u2 => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 => ?_
  refine c3.wp_slot hg (by decide) (by decide) (by decide) fun t4 c4 u4 => wp_addi fun t5 u5 => ?_
  refine (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 u6 => ?_
  refine wp_cmpm (B := L.B) (by rw [c6.st.sp]) (by rw [hg.aFr ok sDb (by decide)]; exact c6.rFr hg sDb (by decide))
    fun t7 u7 cf _ => WP.block_nil ?_
  have e2 : t2.gpr .eax = BitVec.ofNat 32 (c + 1) := by rw [u2.gpr, u1.gpr, hm.ctr, BitVec.ofNat_add_ofNat]
  have m3 : t3.mem = s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1)) := by rw [u3.mem, e2, u2.mem, u1.mem]
  have e5 : t5.gpr .eax = BitVec.ofNat 32 (c * h.D + h.D) := by
    rw [u5.gpr, u4.gpr, m3, Lay.readW_fr_other (d := sDone) (e := sCtr) L _ _ (by decide) (by decide)
      (by decide), hm.done, BitVec.ofNat_add_ofNat]
  have m7 : t7.mem = (s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1))).writeW (L.fr sDone)
      (BitVec.ofNat 32 (c * h.D + h.D)) := by rw [u7.mem, u6.mem, e5, u5.mem, u4.mem, m3]
  have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
  have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  rw [u6.gpr, e5, u6.mem, e5, u5.mem, u4.mem, m3, hg.aFr ok sDb (by decide),
    Lay.readW_fr_other (d := sDb) (e := sDone) L _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other (d := sDb) (e := sCtr) L _ _ (by decide) (by decide) (by decide), P.dbs σ _ hi,
    toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at cf
  refine ⟨c6.fupd u7, ⟨P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_⟩⟩, cf⟩
  · rw [m7, Lay.readW_fr_other (d := sCtr) (e := sDone) L _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m7, Mem.readW_writeW_self32, Nat.succ_mul]
  · intro i hi'
    rw [Nat.succ_mul]
    exact sbytes_keep fr (fun r hr => dis r hr _ _ (by pomega)) (by pomega) hm.dbx i hi'
  · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by pomega)) (by pomega) hm.sd

/-- An iteration of `mgfXor`. -/
theorem mgfIter_vp (P : MP h L scr lo db seed Inv) {c : Nat} (hcd : c * h.D < db) :
    VP (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db c dbv seed Inv σ s.mem)
      (mgfBody h.H)
      (fun σ s => Ctx L scr σ s ∧ MI h L scr lo db (c + 1) dbv seed Inv σ s.mem ∧
        s.cf = some (decide (c * h.D + h.D < db))) := by
  have hc32 : c < 2 ^ 32 := by
    have := P.fit
    have : c ≤ c * h.D := Nat.le_mul_of_pos_right c h.D_pos
    omega
  show VP _ (.seq (.block (clrArgs oY h.H.B)) (.seq zeroLoop (.seq (.block (mgfSeed h.H))
    (.seq Impl.Bignum.X86.copyBytes (.seq (.block (ctrSet h.H)) (.seq (ctHash h.H)
      (.seq (.block (xorSet h.H)) (.seq (countLoop xorBody) (.block (mgfNext h.H)))))))))) _
  exact mgfA_vp h (dbv := dbv) P c (mgfB_vp h P c (VP.seq (mgfC_vp h P hc32) (VP.seq (mgfD_vp h P c)
    (VP.seq (mgfE_vp h P hcd) (VP.seq (mgfF_vp h P hcd) (mgfG_vp h P hcd))))))

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
    (VP.taint [.esp, .ebp] mgfInit_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hd, hs⟩ => ?_) ?_
  · simp only [mgfInit, mi, st]
    refine wp_movi fun t1 u1 => (hc.upd u1 (by decide) (by decide)).wp_st hg (by decide) fun t2 c2 u2 =>
      c2.wp_st hg (by decide) fun t3 c3 u3 => WP.block_nil ?_
    have m3 : t3.mem = (s.mem.writeW (L.fr sCtr) (0 : BitVec 32)).writeW (L.fr sDone) (0 : BitVec 32) := by
      rw [u3.mem, u2.gpr, u2.mem, u1.mem, u1.gpr]; rfl
    have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t3.mem := by
      rw [m3]
      exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
    have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
      intro r hr o n hon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    refine ⟨c3, P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, fun i hi' => ?_, ?_⟩⟩
    · rw [m3, Lay.readW_fr_other (d := sCtr) (e := sDone) L _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]; rfl
    · rw [m3, Mem.readW_writeW_self32, Nat.zero_mul]; rfl
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
  · show eval .b s = _
    simp only [eval, z]
    have e := key c
    rw [hK] at e
    by_cases hz : k = 0
    · rw [decide_eq_false (fun h' => by have := e.2 (by omega); omega), hz]; rfl
    · rw [decide_eq_true (by by_contra h'; have := e.2 (by omega); omega), decide_eq_true (by omega)]
  · have e := (key c).1 (by omega)
    refine ⟨hc', hm.1, fun i hi => ?_, hm.2.sd⟩
    rw [hm.2.dbx i hi, ite_eq_left (by rw [Nat.succ_mul]; omega)]
  · exact ⟨by omega, hc', by rw [show K - k = c + 1 by omega]; exact hm⟩

end VG.Proof.RsaPss.X86
