module

public import VerifiedGarbage.Proof.RsaPss.X86.VfPos
public import VerifiedGarbage.Proof.RsaPss.X86.CtTab
public import VerifiedGarbage.Proof.RsaPss.X86.CmpLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the end of both paths

As on ARMv7 (`Proof/RsaPss/Arm/VfTail.lean`): whichever path put `M'` in `Y`
(`msg`), with its length and blocks in their slots: its hash compared with
`H` (`cmpLoop_vp`, the differences ORed into `edx`), and the result, 1
exactly when `acc` is zero and the hashes are equal (`tail_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

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
  ⟨ctW_slot h hg hT (by decide) (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) (by decide) r hr,
    ctW_em h hg hT (Nat.le_refl _) (by decide) r hr⟩

theorem away2_scr {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa)
    (he : oEm + 1024 ≤ o ∨ o + n ≤ oEm) : Away2 L scr (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    Geo.sep (by omega) (by decide) ho⟩

theorem away2_slot {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sC ∨ sC + 4 ≤ d) (h₂ : d + 4 ≤ sLo ∨ sLo + 4 ≤ d) (h₃ : d + 4 ≤ sDb ∨ sDb + 4 ≤ d)
    (h₄ : d + 4 ≤ sAny ∨ sAny + 4 ≤ d) (h₅ : d + 4 ≤ sPos ∨ sPos + 4 ≤ d) (h₆ : d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) :
    Away2 L scr (slotR L d) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega),
    slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega),
    (hg.slot ok (o := oEm) (n := 1024) (by decide) (by rw [hg.F]; omega)).symm⟩

theorem away2_ctWT {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctWT h L scr T, Away2 L scr r := fun r hr => by
  rcases List.mem_cons.mp hr with rfl | hr
  · exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact away2_ctW h hg hT r hr

/-- What `ctHash` keeps, with `M'`'s length and blocks in their slots. -/
abbrev Kt (P : EP) (msg : State → List Byte) (nbm : Nat) (τ : State) (m : Mem) : Prop :=
  K2 h P τ m ∧ m.readW ((P.lay h.D).fr sL) 32 = BitVec.ofNat 32 (msg τ).length ∧
    m.readW ((P.lay h.D).fr sNb) 32 = BitVec.ofNat 32 nbm

/-- The hash of `x` is `H`. -/
abbrev HOk (P : EP) (τ : State) (x : List Byte) : Prop :=
  ∀ i < h.D, (h.ok.hH.SH.H.hash x).getD i 0 = (seedV h P τ).getD i 0

variable {L : Lay} {scr : BitVec 32}

theorem res_eq (x : BitVec 32) :
    (if decide (x.toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32 else 0) &&& 1 =
      if x = 0 then 1 else 0 := by
  by_cases e : x = 0
  · subst e; rfl
  · have : x.toNat ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq h')
    rw [ite_eq_right e, ite_eq_right (by simp only [decide_eq_true_eq]; show ¬ x.toNat < 1; omega)]
    rfl

/-- The hash of `M'`, with the hash function of the table at the argument
14, compared with `H`, and the result. -/
theorem tail_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ τ, (msg τ).length + 1 + h.L ≤ nbm * h.B) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa P.scr (oY + i)) = (msg τ).getD i 0) ∧ s.syms = τ.syms)
      (.seq (ctHashT f h.H 14) (cmpH h.H))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (msg τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oDig = 832 := rfl
  have dT : ∀ d, d = sL ∨ d = sNb → ∀ r ∈ ctWT h (P.lay h.D) P.scr (nbm * h.B), (slotR (P.lay h.D) d).Disjoint r := by
    intro d hd r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rcases hd with rfl | rfl <;> exact Lay.fr_sep (by decide) (by decide) (by decide)
    · rcases hd with rfl | rfl <;> exact ctW_slot h hg hnb (by decide) (by decide) (by decide) r hr
  refine (ctHashT_vp h hg hnb hnb0 hfit (Inv := Kt h P msg nbm)
    (fun τ m m' hk hf' => ⟨K2.keep h hk.1 hf' (away2_ctWT h hg hnb),
      slot_keep hf' (dT sL (.inl rfl)) hk.2.1, slot_keep hf' (dT sNb (.inr rfl)) hk.2.2⟩)
    (fun τ m hk => hk.2.1) (fun τ m hk => hk.2.2) ⟨h.certs.digSp, h.certs.digCt⟩ (vf_arg h (j := 14) (by decide))
    hTab14_taint (fun τ m hk => hTH τ hk.1.1.tabTH) hi₀.tblH fne).seq (Proof.RsaOaep.X86.VP.syms ?_)
  show VP _ (.seq (.block (cmpArgs h.H)) (.seq (countLoop cmpBody) (.block result))) _
  let X : State → Mem → Prop := fun τ m => Kt h P msg nbm τ m ∧
    ∀ i < h.D, m (sa P.scr (oDig + i)) = (h.ok.hH.SH.H.hash (msg τ)).getD i 0
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 oDig ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧
      s.gpr .ecx = BitVec.ofNat 32 h.D ∧ s.gpr .edx = 0)
    (VP.taint [.esp, .ebp] h.certs.cmpArgs (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hd⟩ => ?_)
    (VP.seq (G := fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧
        (s.gpr .edx = 0 ↔ HOk h P τ (msg τ)))
      ((cmpLoop_vp hg (oa := oDig) (ob := oEm + lo P + dbN h P) (n := h.D) hD0 (by omega) (by omega) (X := X)
        (f := fun τ i => (h.ok.hH.SH.H.hash (msg τ)).getD i 0) (g := fun τ i => (seedV h P τ).getD i 0)
        (fun τ m hx i hi => hx.2 i hi) (fun τ m hx i hi => hx.1.1.2.2.2.2.1 i hi)).mono
        (fun τ s ⟨⟨hc, hx⟩, si, di, cx, dx⟩ => ⟨hc, hx, si, di, cx, dx⟩)
        fun τ s ⟨hc, hx, hr⟩ => ⟨hc, hx, hr⟩)
      (VP.taint [.esp, .ebp] result_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hx, hr⟩ => ?_))
  · simp only [cmpArgs, atDb, atS, addSlot, addi, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
    have c4 : Ctx (P.lay h.D) P.scr τ t4 :=
      (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4
        (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c4.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c4.rFr hg sLo (by decide)) fun t5 u5 => ?_
    have c5 : Ctx (P.lay h.D) P.scr τ t5 := c4.upd u5 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c5.st.sp])
      (by rw [hg.aFr ok sDb (by decide)]; exact c5.rFr hg sDb (by decide)) fun t6 u6 => ?_
    refine wp_movi fun t7 u7 => wp_movi fun t8 u8 => WP.block_nil ?_
    have m8 : t8.mem = s.mem := by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide),
      m8 ▸ hk, m8 ▸ hd⟩, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr,
        hc.ebp]
    · simp (disch := decide) only [u8.other, u7.other, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.other, u1.other,
        hc.ebp]
      rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide), hk.1.2.2.1.2.1,
        hg.aFr ok sDb (by decide), hk.1.2.2.1.2.2.1, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · rw [u8.gpr]
    · rw [u8.other _ (by decide), u7.gpr]; rfl
  · simp only [result, ld]
    refine hc.wp_slot hg (d := sAcc) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
    refine wp_or fun t2 u2 => wp_cmpi fun t3 f3 cf3 _ => wp_sbb_self cf3 fun t4 u4 => wp_andi fun t5 u5 =>
      WP.block_nil ?_
    have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, f3.mem, u2.mem, u1.mem]
    refine ⟨(((c1.upd u2 (by decide) (by decide)).fupd f3).upd u4 (by decide) (by decide)).upd u5 (by decide)
      (by decide), m5 ▸ hx.1.1, ?_⟩
    have oz : ∀ x y : BitVec 32, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun x y => BitVec.or_eq_zero_iff
    rw [u5.gpr, u4.gpr, res_eq, u2.gpr, u1.gpr, u1.other .edx (by decide), hx.1.1.2.2.2.2.2.2]
    simp only [oz, hr]

end VG.Proof.RsaPss.X86.Vf
