module

public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.RsaPss.X86.SgPSat
public import VerifiedGarbage.Proof.RsaPss.X86.SgPVerified
public import VerifiedGarbage.Proof.RsaPss.X86.VfPass
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.X86.VfPos
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.RsaPss.X86.Hashes.Md5
public import VerifiedGarbage.Proof.MdHashTable.X86.Tables
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.RsaPss.X86.YDig
public import VerifiedGarbage.Proof.RsaPss.X86.CtTab
public import VerifiedGarbage.Proof.RsaPss.X86.CmpLoop

/-! ### `RsaPss.X86.VfFixed`, which only this module used -/

section

/-! ### `RsaPss.X86.VfTail`, which this module and modules that import it used -/

section

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
  · have e := kb (lo P + i) (by omega_using [hsum, hK, hi'])
    rw [← Nat.add_assoc] at e
    rw [e]; exact hd i hi'
  · have e := kb (lo P + dbN h P + i) (by omega_using [hsum, hK, hi'])
    rw [show oEm + (lo P + dbN h P + i) = oEm + lo P + dbN h P + i by omega_using []] at e
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
    Geo.sep (by omega_using [he]) (by decide) ho⟩

theorem away2_slot {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : d + 4 ≤ sC ∨ sC + 4 ≤ d) (h₂ : d + 4 ≤ sLo ∨ sLo + 4 ≤ d) (h₃ : d + 4 ≤ sDb ∨ sDb + 4 ≤ d)
    (h₄ : d + 4 ≤ sAny ∨ sAny + 4 ≤ d) (h₅ : d + 4 ≤ sPos ∨ sPos + 4 ≤ d) (h₆ : d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) :
    Away2 L scr (slotR L d) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨slotSep (by decide) hd (by omega_using [h₁]), slotSep (by decide) hd (by omega_using [h₂]), slotSep (by decide) hd (by omega_using [h₃]),
    slotSep (by decide) hd (by omega_using [h₄]), slotSep (by decide) hd (by omega_using [h₅]), slotSep (by decide) hd (by omega_using [h₆]),
    (hg.slot ok (o := oEm) (n := 1024) (by decide) (by rw [hg.F]; omega_using [hd])).symm⟩

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
    rw [ite_eq_right e, ite_eq_right (by simp only [decide_eq_true_eq]; show ¬ x.toNat < 1; omega_using [this])]
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
      ((cmpLoop_vp hg (oa := oDig) (ob := oEm + lo P + dbN h P) (n := h.D) hD0 (by omega_using [hD, e2, e3]) (by omega_using [hsum, hK, e1, e2]) (X := X)
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

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on x86: a salt of the expected length

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`, `VfFixed.lean`): `Y` cleared and
`mHash` after its 8 zero bytes (`yDig_vf`); the last `sLen` bytes of `DB`
after it (`fxSalt_vp`), `M'`'s length and blocks (`lenF_vp`), and the end of
the paths (`fixed_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (add_ofNat_sub)

variable (h : PssHash)

theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  have hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.dig.isLt; omega_using [])] at hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  exact ⟨hf, by omega_using [hD], ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `Y`: 8 zero bytes and `mHash`. -/
abbrev Y1 (P : EP) (τ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- `Y` cleared and `mHash` after its 8 zero bytes. -/
theorem yDig_vf (P : EP) (hP : ∃ σ, In h.D P σ) (Q : Prop) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ Q) (yDig h.H 4)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ Q) ∧ Y1 h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 4) h.certs.cpDig4 (by simp) (dgP := P.dig) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.bytesAt_len _ _ _) (fun σ s hc i hi => ?_) (X := fun τ m => K2 h P τ m ∧ Q)
    fun σ m m' ⟨hk, hq⟩ hf => ⟨K2.keep h hk hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by decide) (by decide), hq⟩).mono
    (fun σ s ⟨hc, hk, hq⟩ => ⟨hc, hk, hq⟩) fun σ s h' => h'
  have e : Spec.Rsa.bytesAt s.mem (P.dig.setWidth 64) h.D = Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (P.dig.setWidth 64 + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD hi]

/-- The last `sLen` bytes of `DB`. -/
abbrev sltB (P : EP) (τ : State) : List Byte := (List.range P.slt).map fun i => dbF h P τ (dbN h P - P.slt + i)

/-- `M'`. -/
abbrev Mf (P : EP) (τ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P τ ++ sltB h P τ

/-- Its blocks. -/
abbrev nbF (P : EP) : Nat := (P.slt + (8 + h.D) + h.L) / h.B + 1

/-- `Y`, with `M'`. -/
abbrev Yf (P : EP) (τ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mf h P τ).getD i 0

theorem Mf_length (P : EP) (τ : State) : (Mf h P τ).length = P.slt + (8 + h.D) := by
  simp only [Mf, List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len, sltB,
    List.length_map, List.length_range]; omega_using []

/-- What the fixed path starts from. -/
abbrev F0 (P : EP) (τ s : State) : Prop := Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Y1 h P τ s.mem

/-- The last `sLen` bytes of `DB` after `mHash`. -/
theorem fxSalt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (F0 h P) (.seq (.block (fxSalt h.H)) (.ite .e (.block []) Impl.Bignum.X86.copyBytes))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.2.1.1.2.1, h'.2.1.2⟩
  obtain ⟨hf, ha⟩ := hf
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have hsl := hi₀.slt32
  refine VP.seq (G := fun τ s => F0 h P τ s ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.slt) ∧ s.gpr .ecx = BitVec.ofNat 32 P.slt ∧
      s.zf = some (decide (P.slt = 0)))
    (VP.taint [.esp, .ebp] h.certs.fxSalt (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, ⟨hk, ha'⟩, hy⟩ => ?_)
    (VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
      (VP.block_nil fun τ s ⟨⟨⟨hc, hk, hy⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_)
  · simp only [fxSalt, atDb, atS, addSlot, addi, ld, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
      List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
    have c3 : Ctx (P.lay h.D) P.scr τ t3 := c2.upd u3 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp])
      (by rw [hg.aFr ok sDb (by decide)]; exact c3.rFr hg sDb (by decide)) fun t4 u4 => ?_
    have c4 : Ctx (P.lay h.D) P.scr τ t4 := c3.upd u4 (by decide) (by decide)
    refine wp_subm (B := (P.lay h.D).B) (by rw [c4.st.sp]) (by rw [hg.aArg ok 8 (by simp)]; exact
      (by rw [c4.st.rd, c4.st.wr]; exact c4.st.ok.arg_read (vf_arg h (by decide)))) fun t5 u5 => ?_
    refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => ?_
    have c7 : Ctx (P.lay h.D) P.scr τ t7 :=
      ((c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)
    refine c7.wp_arg hg (vf_arg h (j := 8) (by decide)) (by decide) (by decide) fun t8 c8 u8 =>
      wp_test fun t9 f9 z9 => WP.block_nil ?_
    have m9 : t9.mem = s.mem := by rw [f9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c8.fupd f9, m9 ▸ ⟨hk, ha'⟩, m9 ▸ hy⟩, ?_, ?_, ?_, ?_⟩
    · rw [f9.gpr]
      simp (disch := decide) only [u8.other, u7.gpr, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other,
        hc.ebp]
    · rw [f9.gpr]
      simp (disch := decide) only [u8.other, u7.other, u6.other, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr, hc.ebp]
      rw [u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide), hk.2.2.1.2.1, hg.aFr ok sDb (by decide),
        hk.2.2.1.2.2.1, hg.aArg ok 8 (by simp), hc.st.arg (vf_arg h (by decide)),
        show (P.lay h.D).argv.getD 8 0 = BitVec.ofNat 32 P.slt from rfl, BitVec.add_assoc, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, add_ofNat_sub (by omega_using [hdb, es]), Nat.add_assoc]
    · rw [f9.gpr, u8.gpr]; rfl
    · rw [z9, u8.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hsl)
  · have h0 : P.slt = 0 := by
      simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [hy i hi]
    simp [Mf, sltB, h0]
  · by_cases h0 : P.slt = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.slt) (by omega_using [hdb, hsum, hK, es, e2, e3]) (by omega_using [h0]))
      (hg.rbuf (o := oEm + lo P + dbN h P - P.slt) (n := P.slt) (by omega_using [hdb, hsum, hK, es, e1, e2]) (by omega_using [h0]))
      (by rw [hg.scrA (by omega_using [hsum, hK, e1, e2]), hg.scrA (by omega_using [hD, e2, e3])]; exact Geo.sep (by omega_using [hdb, hsum, hK, es, e1, e3]) (by omega_using [hdb, hsum, hK, es, e1, e2]) (by omega_using [hdb, hsum, hK, es, e2, e3])) (by omega_using [h0])
      (f := fun τ i => dbF h P τ (dbN h P - P.slt + i))
      (Inv := fun τ m => (K2 h P τ m ∧ P.any = 0) ∧
        (∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0) ∧
        YZ P.scr (8 + h.D + P.slt) m) fun τ m m' ⟨⟨hk, ha'⟩, h1, h2⟩ hf' => ?_).mono
      (fun τ s ⟨⟨⟨hc, hk, hy⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega_using [hD, hi]), fun i hi => ?_⟩, bx, si, cx,
        fun i hi => ?_⟩) fun τ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
    · rw [hg.scrA (by omega_using [hD, e2, e3])] at hf'
      refine ⟨⟨K2.keep h hk hf' fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_using [hdb, hsum, hK, es, e2, e3]) (by omega_using [e1, e3]), ha'⟩,
        sbytes_keep hf' (fun r hr => ?_) (by omega_using [hD, e3]) h1, sbytes_keep hf' (fun r hr => ?_) (by omega_using [hD, e3, hsl]) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_using []) (by omega_using [hD, e2, e3]) (by omega_using [hdb, hsum, hK, es, e2, e3])
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_using []) (by omega_using [hdb, hsum, hK, es, e2, e3]) (by omega_using [hdb, hsum, hK, es, e2, e3])
    · rw [show oY + (8 + h.D + P.slt) + i = oY + (8 + h.D + P.slt + i) by omega_using [], hy _ (by omega_using [hi]),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]; omega_using [])]
    · rw [hg.byteAt_scr (by omega_using [hlo, hdb, hsum, hK, hD, hD0, hK0, es, e1, e2, hsl, h0, hi]), show oEm + lo P + dbN h P - P.slt + i = oEm + lo P + (dbN h P - P.slt + i) by omega_using [hdb, es]]
      exact hk.1.2.2.2.1 _ (by omega_using [hdb, es, hi])
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]
      rw [RsaPss.getD_app, hl]
      by_cases e1 : i < 8 + h.D
      · rw [ite_eq_left e1]; exact h1 i e1
      rw [ite_eq_right e1]
      by_cases e2 : i < 8 + h.D + P.slt
      · have e := hs (i - (8 + h.D)) (by omega_using [h0, e2])
        rw [hg.byteAt_scr (by omega_arith), show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_using [e1]] at e
        rw [e]
        simp [sltB, List.getD_eq_getElem?_getD, show i - (8 + h.D) < P.slt by omega_using [h0, e2]]
      · rw [getD_ge (l := sltB h P τ) (by simp only [sltB, List.length_map, List.length_range]; omega_using [e2]),
          show oY + i = oY + (8 + h.D + P.slt) + (i - (8 + h.D + P.slt)) by omega_using [e2]]
        exact h2 _ (by omega_using [hi, e2])

/-- `M'`'s length and blocks. -/
theorem lenF_vp (P : EP) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem)
      (.block (lenArgs h.H 8))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Mf h P) (nbF h P) τ s.mem ∧ Yf h P τ s.mem) := by
  refine VP.taint [.esp, .ebp] h.certs.lenArgs8 (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, ⟨hk, ha⟩, hy⟩ => ?_
  have hg := hk.1.geo
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.slt32
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hk.1 hk.2.1
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have e1 : BitVec.ofNat 32 (P.slt + (8 + h.D) + h.L) >>> lgB h.H =
      BitVec.ofNat 32 ((P.slt + (8 + h.D) + h.L) / h.B) := by
    rw [ofNat_shr (by omega_using [hL, hdb, hsum, hK, es]), h.pow_lg]
  obtain ⟨σ', ok⟩ := hg.ok
  simp only [lenArgs, ld, st, addi]
  refine hc.wp_arg hg (vf_arg h (j := 8) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
    wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 =>
      wp_addi fun t4 u4 => wp_shr h.lg_range fun t5 u5 _ => wp_addi fun t6 u6 => ?_
  refine ((((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide)
    (by decide))).wp_st hg (by decide) fun t7 c7 u7 => WP.block_nil ?_
  have e2 : t2.gpr .eax = BitVec.ofNat 32 (P.slt + (8 + h.D)) := by
    rw [u2.gpr, u1.gpr]; exact BitVec.ofNat_add_ofNat ..
  have e6 : t6.gpr .eax = BitVec.ofNat 32 (nbF h P) := by
    rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, e2, BitVec.ofNat_add_ofNat]
    show BitVec.ofNat 32 (P.slt + (8 + h.D) + h.L) >>> lgB h.H + _ = _
    rw [e1, BitVec.ofNat_add_ofNat]
  have m7 : t7.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.slt + (8 + h.D)))).writeW
      ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbF h P)) := by
    rw [u7.mem, e6, u6.mem, u5.mem, u4.mem, u3.mem, e2, u2.mem, u1.mem]
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨c7, ⟨K2.keep h hk fr fun r hr => ?_, ?_, ?_⟩, sbytes_keep fr (fun r hr => ?_) (by pomega) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · rw [m7, Lay.readW_fr_other (d := sL) (e := sNb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mf_length]
  · rw [m7, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm

/-- A salt of the expected length. -/
theorem fixed_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ P.any = 0) ∧ s.syms = τ.syms) (fixedPathT f h.H)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (Mf h P τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.1.2.1.2.1, h'.1.2.2⟩
  obtain ⟨hf, ha⟩ := hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  have hB0 : 0 < h.B := by have := h.B_ge; omega_using [this]
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hi₀ hf
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have q1 := Nat.lt_mul_div_succ (P.slt + (8 + h.D) + h.L) hB0
  have q2 := Nat.mul_div_le (P.slt + (8 + h.D) + h.L) h.B
  have hT : nbF h P * h.B ≤ 2048 := by
    show ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_using [hD, hL, hB, hB0, hlo, hdb, hsum, hK, hD', hD0, hK0, es, q1, q2]
  show VP _ (.seq (yDig h.H 4) (.seq (.block (fxSalt h.H)) (.seq (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
    (.seq (.block (lenArgs h.H 8)) (.seq (ctHashT f h.H 14) (cmpH h.H)))))) _
  refine (Proof.RsaOaep.X86.VP.syms (yDig_vf h P ⟨σ₀, hi₀⟩ (P.any = 0))).seq ?_
  refine Sg.vpAssoc ((Proof.RsaOaep.X86.VP.syms (fxSalt_vp h P ⟨σ₀, hi₀⟩)).seq
    ((Proof.RsaOaep.X86.VP.syms (lenF_vp h P)).seq ?_))
  exact (tail_vp h P ⟨σ₀, hi₀⟩ hTH fne hT (Nat.succ_pos _) (msg := Mf h P) fun τ => by
      rw [Mf_length]; show _ ≤ ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_using [q1]).mono
    (fun τ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_using [hT, hi])⟩, sy⟩) fun τ s h => h

end VG.Proof.RsaPss.X86.Vf

end

end

/-! ### `RsaPss.X86.VfSat`, which only this module used -/

section

/-! ### `RsaPss.X86.VfVerified`, which only this module used -/

section

/-! ### `RsaPss.X86.VfMain`, which only this module used -/

section

/-! ### `RsaPss.X86.VfLogic`, which only this module used -/

section

/-! ### `RsaPss.X86.VfAny`, which only this module used -/

section

/-! ### `RsaPss.X86.VfShift`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the shift

As on ARMv7 (`Proof/RsaPss/Arm/VfShift.lean`): `DB`'s place in `Y` shifted
left by `pos + 1` bytes in ten passes, pass `p` by `2^p` bytes if bit `p` of
the distance is set (`shift_vp`), so that no address depends on `pos`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- Byte `i` of `DB`, zero after its end. -/
abbrev Dp (P : EP) (τ : State) (i : Nat) : Byte := if i < dbN h P then dbF h P τ i else 0

/-- The shift's distance. -/
abbrev aV (P : EP) (τ : State) : Nat := pzF h P τ + 1

/-- What the shift keeps. -/
abbrev Kq (P : EP) (τ : State) (m : Mem) : Prop :=
  K2 h P τ m ∧ ∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- After `p` passes. -/
abbrev SH (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ p)

theorem mask_bit {v : Nat} (hv : v < 2 ^ 32) : 0 - (BitVec.ofNat 32 v &&& 1) = maskOf (v % 2 = 1) := by
  obtain e : BitVec.ofNat 32 v &&& 1 = BitVec.ofNat 32 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    rw [show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]; omega_using []
  rw [e]; unfold maskOf
  rcases Nat.mod_two_eq_zero_or_one v with e' | e' <;> rw [e'] <;> decide

theorem pzF_lt {P : EP} {τ : State} (hdb : 1 ≤ dbN h P) : pzF h P τ < dbN h P := by
  unfold pzF pzJ; split <;> omega_arith

/-- The bounds a pass needs. -/
theorem shB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ 1 ≤ dbN h P ∧ dbN h P + h.D ≤ 1023 ∧ h.D ≤ 64 ∧ 0 < h.D := by
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  exact ⟨hlo, by omega_using [hdb], by omega_using [hsum, hK], hD, hD0⟩

/-- A pass's registers. -/
theorem passSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (.block (passSet h.H))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .esi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .edx = maskOf (aV h P τ / 2 ^ p % 2 = 1)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.passSet (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_using [hp])
  have haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega_using [hdD, hpz]
  have hav : aV h P τ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [haV])
  simp only [passSet, atS, addSlot, addi, ld, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => ?_
  have c3 : Ctx (P.lay h.D) P.scr τ t3 :=
    ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp])
    (by rw [hg.aFr ok sD (by decide)]; exact c3.rFr hg sD (by decide)) fun t4 u4 => ?_
  have c4 : Ctx (P.lay h.D) P.scr τ t4 := c3.upd u4 (by decide) (by decide)
  refine c4.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_andi fun t6 u6 => wp_movi fun t7 u7 => wp_sub fun t8 u8 _ => ?_
  have c8 : Ctx (P.lay h.D) P.scr τ t8 :=
    ((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)
  refine c8.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t9 c9 u9 => WP.block_nil ?_
  have m9 : t9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have esi2 : t2.gpr .esi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) := by rw [u2.gpr, u1.gpr, hc.ebp]
  refine ⟨⟨c9, m9 ▸ hk, m9 ▸ hs⟩, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, esi2]
  · simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.gpr, u3.gpr, esi2]
    rw [u3.mem, u2.mem, u1.mem, hg.aFr ok sD (by decide), hs.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [u9.gpr, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hk.1.2.2.1.2.2.1]
  · simp (disch := decide) only [u9.other, u8.gpr, u7.gpr, u7.other, u6.gpr, u5.gpr]
    rw [u4.mem, u3.mem, u2.mem, u1.mem, hs.1]
    exact mask_bit hav

/-- Between a pass's bytes and its next stage: the slots of pass `p`, the
bytes of pass `p + 1`. -/
abbrev SM (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ (p + 1))

theorem mod_succ (a p : Nat) : a % 2 ^ (p + 1) = a % 2 ^ p + 2 ^ p * (a / 2 ^ p % 2) := by
  rw [Nat.pow_succ, Nat.mod_mul]

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .esi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .edi = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .ecx = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .edx = maskOf (aV h P τ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  obtain hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_using [hp])
  obtain hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  have e1 : oEm = 1024 := rfl
  refine (pass_vp hg (o := oY + 8 + h.D) (d := 2 ^ p) (n := dbN h P) (by omega_using [hdb]) hp0 (by omega_using [hdD, e2, e3, hp9])
    (c := fun τ => aV h P τ / 2 ^ p % 2 = 1) (X := fun τ m => Kq h P τ m ∧ SH h P τ p m)).mono
    (fun τ s ⟨⟨hc, hk, hs⟩, si, di, cx, dx⟩ => ⟨hc, ⟨hk, hs⟩, si, di, cx, dx⟩)
    fun τ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  obtain away : ∀ r ∈ [sR P.scr (oY + 8 + h.D) (dbN h P)], Away2 (P.lay h.D) P.scr r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_using [hdD, e2, e3]) (by omega_using [e3, e1])
  obtain ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW ((P.lay h.D).fr d) 32 = m₀.readW ((P.lay h.D).fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by omega_using [hdD, e2, e3]) (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd])) rfl
  refine ⟨hc, ⟨K2.keep h hk.1 fr away, sbytes_keep fr (fun r hr => ?_) (by omega_using [hdD, e3]) hk.2⟩,
    by rw [ks _ (by decide)]; exact hs.1, by rw [ks _ (by decide)]; exact hs.2.1,
    by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_using []) (by omega_using [hdD, e2, e3]) (by omega_using [hdD, e2, e3])
  obtain ms := mod_succ (aV h P τ) p
  by_cases e : j < dbN h P
  · rw [hsel j e]
    by_cases hc' : aV h P τ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oY + 8 + h.D + 2 ^ p + j = oY + 8 + h.D + (2 ^ p + j) by omega_using [],
        hs.2.2.2 _ (by omega_using [hdD, hp9, e])]
      congr 1; rw [ms, hc']; omega_using []
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV h P τ / 2 ^ p % 2 = 0 by omega_using [hc']]; omega_using []
  · have hm : s.mem (sa P.scr (oY + 8 + h.D + j)) = m₀ (sa P.scr (oY + 8 + h.D + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_using [e]) (by omega_using [e2, e3, hj]) (by omega_using [hdD, e2, e3]) _
          (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj]; unfold Dp; rw [ite_eq_right (by omega_using [e]), ite_eq_right (by omega_using [e])]

/-- The bytes and the slots after a pass. -/
theorem keep3 (P : EP) (hg : Geo (P.lay h.D) P.scr) {τ : State} {m m' : Mem}
    (hf : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] m m') (hk : Kq h P τ m)
    {f : Nat → Byte} (hy : ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = f j) :
    Kq h P τ m' ∧ ∀ j < 2040 - h.D, m' (sa P.scr (oY + 8 + h.D + j)) = f j := by
  obtain ⟨σ', ok⟩ := hg.ok
  have e3 : oY = 2048 := rfl
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  obtain aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  refine ⟨⟨K2.keep h hk.1 hf fun r hr => ?_, sbytes_keep hf (aw _ _ (by omega_using [e3, hD, e2])) (by omega_using [e3, hD]) hk.2⟩,
    sbytes_keep hf (aw _ _ (by omega_using [e3, hD, e2])) (by omega_using [e3, hD]) hy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- Three words stored in the slots of the shift. -/
theorem fr3 (L : Lay) (m : Mem) (a b c : BitVec 32) :
    Frame [slotR L sA, slotR L sD, slotR L sPc] m (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c) :=
  ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
    ((slot_frame _ _ _ _).mono (by simp))

/-- The words of the three slots after the stores. -/
theorem rd3 (L : Lay) (m : Mem) (a b c : BitVec 32) :
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sA) 32 = a ∧
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sD) 32 = b ∧
    (((m.writeW (L.fr sA) a).writeW (L.fr sD) b).writeW (L.fr sPc) c).readW (L.fr sPc) 32 = c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) (.block passNext)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.zf = some (decide (10 - (p + 1) = 0))) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.taint [.esp, .ebp] passNext_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  obtain hpz := pzF_lt h (τ := τ) hdb
  obtain haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega_using [hdD, hpz]
  obtain hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_using [hp])
  obtain ea : BitVec.ofNat 32 (aV h P τ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)) := by
    rw [ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [haV])), Nat.div_div_eq_div_mul,
      Nat.pow_one, ← Nat.pow_succ]
  obtain ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega_using []
  obtain ec : BitVec.ofNat 32 (10 - p) - 1 = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [ofNat_pred (by omega_using [hp]), Nat.sub_sub]
  simp only [passNext, ld, st]
  refine hc.wp_slot hg (d := sA) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_shr (by decide) fun t2 u2 _ => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_slot hg (d := sD) (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_add fun t5 u5 _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t6 c6 m6 => ?_
  refine c6.wp_slot hg (d := sPc) (by decide) (by decide) (by decide) fun t7 c7 u7 => ?_
  refine wp_subi fun t8 u8 _ z8 => (c7.upd u8 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t9 c9 m9 => WP.block_nil ?_
  obtain va : t2.gpr .eax = BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)) := by rw [u2.gpr, u1.gpr, hs.1, ea]
  obtain m3' : t3.mem = s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1))) := by
    rw [m3.mem, va, u2.mem, u1.mem]
  obtain vd : t5.gpr .eax = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [u5.gpr, u4.gpr, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.1, ed]
  obtain vc : t8.gpr .eax = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [u8.gpr, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec]
  obtain mm : t9.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)))).writeW
      ((P.lay h.D).fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW ((P.lay h.D).fr sPc)
        (BitVec.ofNat 32 (10 - (p + 1))) := by
    rw [m9.mem, vc, u8.mem, u7.mem, m6.mem, vd, u5.mem, u4.mem, m3']
  obtain ⟨hk', hy'⟩ := keep3 h P hg (mm ▸ fr3 _ _ _ _ _) hk hs.2.2.2
  obtain ⟨r1, r2, r3⟩ := rd3 (P.lay h.D) s.mem (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)))
    (BitVec.ofNat 32 (2 ^ (p + 1))) (BitVec.ofNat 32 (10 - (p + 1)))
  rw [← mm] at r1 r2 r3
  refine ⟨⟨c9, hk', r1, r2, r3, hy'⟩, ?_⟩
  rw [m9.zf, z8, u7.gpr, m6.mem, u5.mem, u4.mem, m3', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), hs.2.2.1, ec, ofNat_beq_zero (by omega_using [])]

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (passOne h.H)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.zf = some (decide (10 - (p + 1) = 0))) :=
  (passSet_vp h P hP hp).seq ((passMid_vp h P hP hp).seq (passNext_vp h P hP hp))

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (.block shInit)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ 0 s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.taint [.esp, .ebp] shInit_taint (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hy⟩ => ?_
  simp only [shInit, ld, st, mi, addi]
  refine hc.wp_slot hg (d := sPos) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (d := sA) (by decide)
    fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (d := sD) (by decide)
    fun t5 c5 m5 => ?_
  refine wp_movi fun t6 u6 => (c5.upd u6 (by decide) (by decide)).wp_st hg (d := sPc) (by decide)
    fun t7 c7 m7 => WP.block_nil ?_
  obtain mm : t7.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ))).writeW
      ((P.lay h.D).fr sD) (BitVec.ofNat 32 1)).writeW ((P.lay h.D).fr sPc) (BitVec.ofNat 32 10) := by
    rw [m7.mem, u6.gpr, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, u2.gpr, u1.gpr, u2.mem, u1.mem, hk.1.2.2.2.2.2.1,
      BitVec.ofNat_add_ofNat]
  obtain ⟨hk', hy'⟩ := keep3 h P hg (mm ▸ fr3 _ _ _ _ _) hk hy
  obtain ⟨r1, r2, r3⟩ := rd3 (P.lay h.D) s.mem (BitVec.ofNat 32 (aV h P τ)) (BitVec.ofNat 32 1) (BitVec.ofNat 32 10)
  rw [← mm] at r1 r2 r3
  refine ⟨c7, hk', ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [r1, Nat.pow_zero, Nat.div_one]
  · rw [r2]
  · rw [r3]
  · rw [hy' j hj, Nat.pow_zero, Nat.mod_one, Nat.add_zero]

/-- `DB` shifted left by `pos + 1` bytes. -/
theorem shift_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (shift h.H)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) := by
  refine (shInit_vp h P hP).seq ?_
  let I : Nat → State → State → Prop := fun k τ s => k ≤ 10 ∧ Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
    SH h P τ (10 - k) s.mem
  refine (VP.loop (I := I) (fun k => ?_) 9).mono (fun τ s ⟨hc, hk, hs⟩ => ⟨by omega_using [], hc, hk, hs⟩) fun _ _ h => h
  by_cases hk : k ≤ 9
  swap
  · exact VP.empty fun τ s h' => hk (by have := h'.1; omega_using [this])
  refine (onePass_vp h P hP (p := 9 - k) (by omega_using [])).mono
    (fun τ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 9 - k = 10 - (k + 1) by omega_using []]; exact hs⟩)
    fun τ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega_using [hk], hc, hq, ?_⟩⟩
  · show eval .ne s = _
    simp only [eval, z, show 10 - (9 - k + 1) = k by omega_using [hk]]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega_using [h0]
  · subst h0
    obtain hb := shB h hq.1.1 hq.1.2.1
    obtain hpz := pzF_lt h (τ := τ) hb.2.1
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV h P τ < 2 ^ (9 - 0 + 1) by
      show pzF h P τ + 1 < 1024; omega_using [hb, hpz])]
  · rw [show 10 - k = 9 - k + 1 by omega_using [hk]]; exact hs

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: a salt of any length

As on ARMv7 (`Proof/RsaPss/Arm/VfFixed.lean`): `DB` after `mHash` in `Y`
(`cpDb_vp`), shifted left by `pos + 1` bytes, so that `M'` is in `Y`
(`Ma`); its length and the blocks of the longest salt (`anyLen_vp`); and the
end of the paths (`any_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- `M'`. -/
abbrev Ma (P : EP) (τ : State) : List Byte :=
  Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (pzF h P τ + 1)

/-- Its blocks, those of the longest salt. -/
abbrev nbA (P : EP) : Nat := (dbN h P + (7 + h.D + h.L)) / h.B + 1

theorem pre_length (P : EP) (τ : State) : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
  simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]

theorem dbL_length (P : EP) (τ : State) : (dbL h P τ).length = dbN h P := by simp [dbL]

theorem Ma_length (P : EP) (τ : State) : (Ma h P τ).length = 8 + h.D + (dbN h P - (pzF h P τ + 1)) := by
  rw [Ma, List.length_append, pre_length, List.length_drop, dbL_length]

theorem Ma_getD {P : EP} {τ : State} {j : Nat} :
    (Ma h P τ).getD (8 + h.D + j) 0 = Dp h P τ (j + aV h P τ) := by
  rw [Ma, RsaPss.getD_app, pre_length, ite_eq_right (by omega_using []), Nat.add_sub_cancel_left]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD]
  unfold Dp aV
  by_cases e : j + (pzF h P τ + 1) < dbN h P
  · rw [ite_eq_left e, Nat.add_comm, ← dbL_getD h e]
  · rw [ite_eq_right e, getD_ge (by rw [dbL_length]; omega_using [e])]

/-- `DB` after `mHash`. -/
theorem cpDb_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem)
      (.seq (.block (cpDb h.H)) Impl.Bignum.X86.copyBytes)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
      s.gpr .ecx = BitVec.ofNat 32 (dbN h P))
    (VP.taint [.esp, .ebp] h.certs.cpDb (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hy⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := dbN h P) (by omega_using [hdD, e2, e3]) (by omega_using [hdb]))
      (hg.rbuf (o := oEm + lo P) (n := dbN h P) (by omega_using [hlo, hdD, e1, e2]) (by omega_using [hdb]))
      (by rw [hg.scrA (by omega_using [hlo, e1, e2]), hg.scrA (by omega_using [hdD, e2, e3])]; exact Geo.sep (by omega_using [hlo, hdD, e1, e3]) (by omega_using [hlo, hdD, e1, e2]) (by omega_using [hdD, e2, e3])) (by omega_using [hdb])
      (f := fun τ i => dbF h P τ i)
      (Inv := fun τ m => Kq h P τ m ∧ ∀ j, dbN h P ≤ j → j < 2040 - h.D → m (sa P.scr (oY + 8 + h.D + j)) = 0)
      fun τ m m' ⟨hk, hz⟩ hf' => ?_).mono
      (fun τ s ⟨⟨hc, ⟨hk, _⟩, hy⟩, bx, si, cx⟩ => ⟨hc, ⟨⟨hk, fun i hi => hy i (by omega_using [hdD, hi])⟩, fun j hj hj' => ?_⟩, bx, si,
        cx, fun i hi => ?_⟩)
      fun τ s ⟨hc, ⟨hk, hz⟩, hs⟩ => ⟨hc, hk, fun j hj => ?_⟩)
  · simp only [cpDb, atS, atDb, addSlot, addi, ld, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    obtain c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
    refine wp_mov fun t4 u4 => wp_addi fun t5 u5 => ?_
    obtain c5 : Ctx (P.lay h.D) P.scr τ t5 :=
      ((c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)
    refine c5.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t6 c6 u6 => WP.block_nil ?_
    obtain m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c6, m6 ▸ hk, m6 ▸ hy⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u6.other, u5.gpr, u4.gpr, u3.other, u2.other, u1.other, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.gpr, u2.gpr, u1.gpr, hc.ebp]
      rw [u2.mem, u1.mem, hg.aFr ok sLo (by decide), hk.1.2.2.1.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hk.1.2.2.1.2.2.1]
  · rw [hg.scrA (by omega_using [hdD, e2, e3])] at hf'
    refine ⟨⟨K2.keep h hk.1 hf' fun r hr => ?_, sbytes_keep hf' (fun r hr => ?_) (by omega_using [hdD, e3]) hk.2⟩,
      fun j hj hj' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_using [hdD, e2, e3]) (by omega_using [e1, e3])
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_using []) (by omega_using [hdD, e2, e3]) (by omega_using [hdD, e2, e3])
    · rw [← hz j hj hj']
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_using [hj]) (by omega_using [e2, e3, hj']) (by omega_using [hdD, e2, e3]) _
          (Region.contains_self _ _)
  · rw [show oY + 8 + h.D + j = oY + (8 + h.D + j) by omega_using [], hy _ (by omega_using [hj'])]
    exact getD_ge (by rw [pre_length]; omega_using [])
  · rw [hg.byteAt_scr (by omega_using [hlo, hdD, e1, e2, hi])]; exact hk.2.2.2.1 i hi
  · unfold Dp
    by_cases e : j < dbN h P
    · rw [ite_eq_left e, ← hs j e, hg.byteAt_scr (by omega_using [e2, e3, hj])]
    · rw [ite_eq_right e]; exact hz j (by omega_using [e]) hj

/-- `M'`'s length and blocks. -/
theorem anyLen_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) (.block (anyLen h.H))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Ma h P) (nbA h P) τ s.mem ∧
        ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Ma h P τ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.anyLen (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi hk.1.2.1
  obtain hpz := pzF_lt h (τ := τ) hdb
  have hL := h.L_le
  have hB := h.B_ge
  have e3 : oY = 2048 := rfl
  obtain e1 : BitVec.ofNat 32 (dbN h P + (7 + h.D + h.L)) >>> lgB h.H =
      BitVec.ofNat 32 ((dbN h P + (7 + h.D + h.L)) / h.B) := by
    rw [ofNat_shr (by omega_using [hdD, hL]), h.pow_lg]
  obtain es : BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) = BitVec.ofNat 32 (dbN h P - pzF h P τ) :=
    Offset.ofNat_sub_ofNat (w := 32) (by omega_using [hpz])
  simp only [anyLen, ld, st, addi]
  refine hc.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_subm (B := (P.lay h.D).B) (by rw [c1.st.sp])
    (by rw [hg.aFr ok sPos (by decide)]; exact c1.rFr hg sPos (by decide)) fun t2 u2 => ?_
  refine wp_addi fun t3 u3 => ((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).wp_st hg
    (d := sL) (by decide) fun t4 c4 m4 => ?_
  refine c4.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_addi fun t6 u6 => wp_shr h.lg_range fun t7 u7 _ => wp_addi fun t8 u8 => ?_
  refine (((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide)
    (by decide)).wp_st hg (d := sNb) (by decide) fun t9 c9 m9 => WP.block_nil ?_
  obtain v3 : t3.gpr .eax = BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)) := by
    rw [u3.gpr, u2.gpr, u1.gpr, u1.mem, hg.aFr ok sPos (by decide), hk.1.2.2.1.2.2.1, hk.1.2.2.2.2.2.1, es,
      BitVec.ofNat_add_ofNat]
  obtain m4' : t4.mem = s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D))) := by
    rw [m4.mem, v3, u3.mem, u2.mem, u1.mem]
  obtain v8 : t8.gpr .eax = BitVec.ofNat 32 (nbA h P) := by
    rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr, m4', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      hk.1.2.2.1.2.2.1, BitVec.ofNat_add_ofNat, show dbN h P + (7 + h.D + h.L) = dbN h P + (7 + h.D + h.L) from rfl,
      e1, BitVec.ofNat_add_ofNat]
  obtain m : t9.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)))).writeW
      ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbA h P)) := by
    rw [m9.mem, v8, u8.mem, u7.mem, u6.mem, u5.mem, m4']
  obtain fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t9.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  obtain hy' := sbytes_keep fr (aw _ _ (by omega_using [hdD, e3, e2])) (by omega_using [hdD, e3]) hy
  obtain hp' := sbytes_keep fr (aw _ _ (by omega_using [hdD, e3, e2])) (by omega_using [hdD, e3]) hk.2
  refine ⟨c9, ⟨K2.keep h hk.1 fr fun r hr => ?_, ?_, ?_⟩, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · rw [m, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Ma_length]
    congr 1; omega_using [hpz]
  · rw [m, Mem.readW_writeW_self32]
  · by_cases e : i < 8 + h.D
    · rw [hp' i e, Ma, RsaPss.getD_app (l := Spec.RsaPss.zeros 8 ++ digB h P τ), pre_length, ite_eq_left e]
    · have := hy' (i - (8 + h.D)) (by omega_using [hdD, hi'])
      rw [show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_using [e]] at this
      rw [this, show i = 8 + h.D + (i - (8 + h.D)) by omega_using [e], Ma_getD]
      congr 1; omega_using []

/-- A salt of any length. -/
theorem any_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ True) ∧ s.syms = τ.syms) (anyPathT f h.H)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (Ma h P τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.2.1
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  obtain hB0 : 0 < h.B := by have := h.B_ge; omega_using [this]
  obtain ⟨hlo, hdb, hdD, hD', hD0⟩ := shB h hi₀ hf
  obtain q1 := Nat.lt_mul_div_succ (dbN h P + (7 + h.D + h.L)) hB0
  obtain q2 := Nat.mul_div_le (dbN h P + (7 + h.D + h.L)) h.B
  obtain hT : nbA h P * h.B ≤ 2048 := by
    show ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_using [hL, hB, hdD, q2]
  show VP _ (.seq (yDig h.H 4) (.seq (.block (cpDb h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq (shift h.H)
    (.seq (.block (anyLen h.H)) (.seq (ctHashT f h.H 14) (cmpH h.H))))))) _
  refine (Proof.RsaOaep.X86.VP.syms (yDig_vf h P ⟨σ₀, hi₀⟩ True)).seq (Sg.vpAssoc
    ((Proof.RsaOaep.X86.VP.syms (cpDb_vp h P ⟨σ₀, hi₀⟩)).seq ((Proof.RsaOaep.X86.VP.syms (shift_vp h P ⟨σ₀, hi₀⟩)).seq
    ((Proof.RsaOaep.X86.VP.syms (anyLen_vp h P ⟨σ₀, hi₀⟩)).seq ?_))))
  exact (tail_vp h P ⟨σ₀, hi₀⟩ hTH fne hT (Nat.succ_pos _) (msg := Ma h P) fun τ => by
      rw [Ma_length]; show _ ≤ ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_using [hdb, q1]).mono
    (fun τ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_using [hT, hi])⟩, sy⟩) fun τ s h => h

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the result

As on ARMv7 (`Proof/RsaPss/Arm/VfLogic.lean`): `acc` is zero and the hash of
`M'` is `H` exactly when the encoding is valid (`good_iff`): `acc`'s bits are
the checks of `EncOk` (`Proof/RsaPss/VerifyCases.lean`), one by one
(`acc2_iff`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

theorem bc_iff : ∀ a : Byte, a.setWidth 32 ^^^ 0xbc = 0 ↔ a = 0xbc := by decide
theorem one_iff : ∀ a : Byte, a.setWidth 32 ^^^ 1 = 0 ↔ a = 1 := by decide
theorem zero_iff : ∀ a : Byte, a.setWidth 32 = 0 ↔ a = 0 := by decide
theorem top_iff : ∀ j < 9, ∀ b : Byte, (b.setWidth 32 &&& (BitVec.ofNat 32 (2 ^ j - 1) ^^^ 0xFF) = 0 ↔
    b &&& ~~~((BitVec.ofNat 32 (2 ^ j - 1)).setWidth 8) = 0) := by decide +kernel

/-- The mask of a first byte not zero, `2^j - 1`. -/
theorem cW_cases {b : Byte} (hb : b.toNat ≠ 0) : ∃ j < 9, cW (b.setWidth 32) = BitVec.ofNat 32 (2 ^ j - 1) := by
  rw [setWidth_byte]
  obtain ⟨-, h1, h2⟩ := params_table b.toNat b.isLt
  by_cases e : b.toNat = 1
  · exact ⟨8, by decide, by rw [h1 e]; rfl⟩
  · obtain ⟨j, hj, -, -, he⟩ := h2 (by omega_using [hb, e])
    exact ⟨j, by omega_using [hj], he⟩

theorem or0 (x y : BitVec 32) : (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := BitVec.or_eq_zero_iff

/-- `acc`'s bits, the checks. -/
theorem acc2_iff (P : EP) (τ : State) (hlo : lo P ≤ 1) (hb : (n0 P).toNat ≠ 0) (hdb : dbN h P < 2 ^ 32)
    (hsl : P.slt < 2 ^ 32) :
    acc2 h P τ = 0 ↔ (emv P τ (P.K - 1) = 0xbc ∧ (lo P = 1 → emv P τ 0 = 0) ∧
      emv P τ (lo P) &&& ~~~((cW ((n0 P).setWidth 32)).setWidth 8) = 0) ∧
      (lzF h P τ < dbN h P ∧ dbF h P τ (lzF h P τ) = 1 ∧ (P.any = 0 → dbN h P - lzF h P τ - 1 = P.slt)) := by
  obtain e0 : ((emv P τ 0).setWidth 32 &&& (0 - BitVec.ofNat 32 (lo P)) = 0) ↔ (lo P = 1 → emv P τ 0 = 0) := by
    rcases (show lo P = 0 ∨ lo P = 1 by omega_using [hlo]) with e | e <;> rw [e]
    · simp
    · rw [show (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes, zero_iff]
      simp
  obtain ⟨j, hj, hc⟩ := cW_cases hb
  obtain ht := top_iff j hj (emv P τ (lo P))
  simp only [acc2, accW, or0, and_assoc]
  rw [hc, bc_iff, ht, e0]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  by_cases hf : lzF h P τ < dbN h P
  · have p1 : pzJ h P τ (dbN h P) = lzF h P τ := by simp only [pzJ, hf, ite_true]
    obtain p2 : vzJ h P τ (dbN h P) = dbF h P τ (lzF h P τ) := by simp only [vzJ, hf, ite_true]
    obtain p3 : nfJ h P τ (dbN h P) = 0 := by simp only [nfJ, hf, ite_true]
    simp only [pzF, p1, p2, p3, show (0 : BitVec 32) >>> 31 = 0 by decide, hf, true_and]
    refine and_congr (one_iff _) ?_
    by_cases ha : P.any = 0
    · simp only [anyW, ha, ite_true, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
        true_implies]
      obtain xz : ∀ x y : BitVec 32, x ^^^ y = 0 ↔ x = y := fun x y => BitVec.xor_eq_zero_iff
      rw [xz, Offset.ofNat_sub_ofNat (w := 32) (by omega_using [hf]),
        show BitVec.ofNat 32 (dbN h P - lzF h P τ) - 1 = BitVec.ofNat 32 (dbN h P - lzF h P τ - 1) from
          ofNat_pred (by omega_using [hf])]
      constructor
      · intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt (by omega_using [hdb]), Nat.mod_eq_of_lt hsl] at this
      · intro e; rw [e]
    · have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
      simp only [anyW, ha, ite_false, show (1 : BitVec 32) - 1 = 0 by decide, az, false_implies]
  · have p3 : nfJ h P τ (dbN h P) = BitVec.allOnes 32 := by simp only [nfJ, hf, ite_false]
    simp only [p3, show BitVec.allOnes 32 >>> 31 = (1 : BitVec 32) by decide, hf, false_and, iff_false]
    exact fun ⟨_, h1, _⟩ => absurd h1 (by decide)

theorem list_eq_iff {l₁ l₂ : List Byte} {n : Nat} (h₁ : l₁.length = n) (h₂ : l₂.length = n) :
    l₁ = l₂ ↔ ∀ i < n, l₁.getD i 0 = l₂.getD i 0 := by
  refine ⟨fun e _ _ => by rw [e], fun e => List.ext_getElem (by omega_using [h₁, h₂]) fun i a b => ?_⟩
  have := e i (by omega_using [h₁, a])
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem a, List.getElem?_eq_getElem b] using this

theorem HOk_iff (P : EP) (τ : State) (x : List Byte) : HOk h P τ x ↔ h.G.hash x = seedV h P τ := by
  rw [h.hash, list_eq_iff (n := h.D) (by rw [← h.hash, (PssHash.valid h).2, h.glen]) (by simp [seedV])]

/-- `M'`, when `DB`'s padding ends where it should. -/
theorem M_eq {P : EP} {τ : State} (hf : lzF h P τ < dbN h P) (hs : P.any = 0 → dbN h P - lzF h P τ - 1 = P.slt) :
    (if P.any = 0 then Mf h P τ else Ma h P τ) =
      Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (lzF h P τ + 1) := by
  by_cases ha : P.any = 0
  · rw [ite_eq_left ha, Mf]
    obtain hs := hs ha
    refine congrArg (Spec.RsaPss.zeros 8 ++ digB h P τ ++ ·) (RsaPss.eq_range_map (by rw [List.length_drop, dbL_length]; omega_using [hs])
      fun i hi => ?_).symm
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, dbL_getD h (by omega_using [hs, hi])]
    congr 1; omega_using [hf, hs]
  · rw [ite_eq_right ha, Ma]
    simp only [pzF, pzJ, hf, ite_true]

/-- The result: `acc` is zero and the hash of `M'` is `H` exactly when the
encoding is valid. -/
theorem good_iff (P : EP) (τ : State) (hi : In h.D P τ) (hf : fits h P) {sB : List Byte} (hsB : sB.length = P.K)
    (hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB sB).getD (Spec.RsaPss.zeros P.K)).getD i 0 = emv P τ i) :
    (acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)) ↔
      Spec.RsaPss.verify h.G P.g.G P.nB P.eB (digB h P τ) sB (sLenO P) = true := by
  obtain hl := nB_length hi
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega_arith
    | cons b rest => exact ⟨b, rest, rfl⟩
  obtain hn0 : n0 P = b := by simp [n0, hbr]
  obtain hbt : b.toNat ≠ 0 := fun e => hf.1 (hn0 ▸ BitVec.eq_of_toNat_eq e)
  obtain hb0 : b ≠ 0 := fun e => hbt (by rw [e]; rfl)
  rw [hbr, List.length_cons] at hl
  obtain hem := emLen_eq hbr hl hbt
  have hG := P.g.valid
  have gl : h.G.len = h.D := h.glen
  obtain hcz := cW_byte hb0 rest
  rw [hem] at hcz
  obtain hs0 : (sLenO P).getD 0 = eLen P := by unfold sLenO eLen; split <;> rfl
  rw [show Spec.RsaPss.verify h.G P.g.G P.nB = Spec.RsaPss.verify h.G P.g.G (b :: rest) by rw [hbr],
    RsaPss.verify_bytes₂ P.g.G h.G hG (emLen := P.K - lo P) (lo := lo P)
      (by unfold digB; rw [RsaPkcs1Sig.bytesAt_len, gl]) (by rw [hsB, List.length_cons]; omega_arith) rfl hem
      (by rw [List.length_cons]; omega_arith) hlo (by rw [gl, hs0]; omega_arith)]
  generalize hz : 8 * (P.K - lo P) - (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = z at hcz ⊢
  replace hcz : (cW ((n0 P).setWidth 32)).setWidth 8 = (0xFF : Byte) >>> z := by rw [hn0]; exact hcz
  obtain hx' : ∀ i < P.K, ((Spec.Rsa.publicOpChecked (b :: rest) P.eB sB).getD
      (Spec.RsaPss.zeros (b :: rest).length)).getD i 0 = emv P τ i := by
    rw [List.length_cons, hl, ← hbr]; exact hx
  obtain hxl : ((Spec.Rsa.publicOpChecked (b :: rest) P.eB sB).getD
      (Spec.RsaPss.zeros (b :: rest).length)).length = P.K := by
    cases e : Spec.Rsa.publicOpChecked (b :: rest) P.eB sB with
    | none => rw [Option.getD_none, RsaPss.zeros_length, List.length_cons]; omega_arith
    | some y => rw [Option.getD_some, RsaPss.publicOpChecked_length' e, List.length_cons]; omega_arith
  generalize ((Spec.Rsa.publicOpChecked (b :: rest) P.eB sB).getD (Spec.RsaPss.zeros (b :: rest).length)) = x
    at hx' hxl ⊢
  obtain hdrop : ∀ i, lo P + i < P.K → (x.drop (lo P)).getD i 0 = emv P τ (lo P + i) := fun i hi' => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, hx' _ hi']
  obtain hL : P.K - lo P - h.G.len - 1 = dbN h P := by rw [gl]
  obtain hvH : RsaPss.vH h.G (x.drop (lo P)) (dbN h P) = seedV h P τ := by
    unfold RsaPss.vH
    refine RsaPss.eq_range_map (by simp only [List.length_take, List.length_drop, hxl, gl]; omega_arith) fun i hi' => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by rw [gl]; exact hi'), List.getElem?_drop,
      ← List.getD_eq_getElem?_getD, hdrop _ (by omega_arith), Nat.add_assoc]
  obtain ht : ∀ j < dbN h P, ((x.drop (lo P)).take (dbN h P)).getD j 0 = emv P τ (lo P + j) := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, ← List.getD_eq_getElem?_getD, hdrop _ (by omega_arith)]
  obtain hmk : (Spec.Mgf1.mgf1 P.g.G (seedV h P τ) (dbN h P)).length = dbN h P := Mgf1.mgf1_length hG _ _
  obtain htl : ((x.drop (lo P)).take (dbN h P)).length = dbN h P := by
    simp only [List.length_take, List.length_drop, hxl]; omega_arith
  obtain hvDb : RsaPss.vDb₂ P.g.G h.G (x.drop (lo P)) (dbN h P) z = dbL h P τ := by
    unfold RsaPss.vDb₂
    rw [hvH]
    refine RsaPss.eq_range_map (by rw [RsaPss.clearTop_length, Mgf1.xorBytes_length, hmk, htl]; omega_arith)
      fun i hi' => ?_
    rw [RsaPss.clearTop_getD]
    by_cases e : i = 0
    · subst e
      rw [ite_eq_left rfl, RsaPss.xorBytes_getD (by omega_arith) (by omega_arith), ht 0 (by omega_arith), ← hcz]
      simp only [dbF, ite_true, Nat.add_zero]
    · rw [ite_eq_right e, RsaPss.xorBytes_getD (by omega_arith) (by omega_arith), ht i hi']
      simp only [dbF, e, ite_false]
  have hlz : RsaPss.lz (dbL h P τ) = lzF h P τ := rfl
  unfold RsaPss.EncOk₂
  rw [hL, hvDb, hvH, hlz, hdrop _ (by omega_arith), hdrop 0 (by omega_arith), show lo P + (P.K - lo P - 1) = P.K - 1 by omega_arith,
    Nat.add_zero, hx' 0 (by omega_arith), ← hcz, acc2_iff h P τ hlo (fun e => hf.1 (BitVec.eq_of_toNat_eq e)) (by omega_arith) hi.slt32, HOk_iff]
  constructor
  · rintro ⟨⟨⟨a1, a0, a2⟩, f, v, sl⟩, hm⟩
    rw [M_eq h f sl] at hm
    refine ⟨a0, a1, a2, f, by rw [dbL_getD h f]; exact v, ?_, hm⟩
    unfold sLenO
    by_cases ha : P.any = 0
    · rw [ite_eq_left ha]; right; have := sl ha; congr 1; omega_arith
    · rw [ite_eq_right ha]; left; rfl
  · rintro ⟨a0, a1, a2, f, v, sl, hm⟩
    obtain sl' : P.any = 0 → dbN h P - lzF h P τ - 1 = P.slt := fun ha => by
      unfold sLenO at sl
      rw [ite_eq_left ha] at sl
      rcases sl with sl | sl
      · exact absurd sl (by simp)
      · have := Option.some.inj sl; omega_arith
    exact ⟨⟨⟨a1, a0, a2⟩, f, by rw [← dbL_getD h f]; exact v, sl'⟩, by rw [M_eq h f sl']; exact hm⟩

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the body

As on ARMv7 (`Proof/RsaPss/Arm/VfMain.lean`): the checks, then either 0 or
the call and the pieces after it, proven over the state the call leaves
(`VQ.reidx`); the result is `verify`'s (`fin_of`, `body_vq`). The stages keep
the addresses of the statics (`VP.syms`) for the indirect calls, and what the
tables give holds of the state the call leaves too (`hfacts_st`,
`tabfacts_st`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

variable (h : PssHash)

/-- The end of the body, over the state `τ` the call leaves. -/
abbrev GE (P : EP) (τ t : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ t ∧ K2 h P τ t.mem ∧
    t.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ) then 1 else 0

/-- The path for the expected salt length, or for any. -/
theorem tailIte_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) :
    VP (fun τ s => ((Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.zf = some (decide (P.any = 0))) ∧
        s.syms = τ.syms)
      (.ite .e (fixedPathT f h.H) (anyPathT f h.H)) (fun τ s => GE h P τ s ∧ s.syms = τ.syms) := by
  refine VP.ite (fun σ s hs => ⟨decide (P.any = 0), by simp only [eval, hs.1.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2, h₂.1.2]) ?_ ?_
  · by_cases ha : P.any = 0
    · exact (fixed_vp h P hP hTH fne).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, ha⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_left ha]⟩, sy⟩
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        simp only [eval, z, decide_eq_false ha] at e; exact absurd e (by decide)
  · by_cases ha : P.any = 0
    · exact VP.empty fun τ s ⟨⟨⟨_, z⟩, _⟩, e⟩ => by
        simp only [eval, z, decide_eq_true ha] at e; exact absurd e (by decide)
    · exact (any_vp h P hP hTH fne).mono (fun τ s ⟨⟨⟨⟨hc, hk⟩, _⟩, sy⟩, _⟩ => ⟨⟨hc, hk, trivial⟩, sy⟩)
        fun τ s ⟨⟨hc, hk, r0⟩, sy⟩ => ⟨⟨hc, hk, by rw [r0, ite_eq_right ha]⟩, sy⟩

/-- After the call. -/
theorem rest_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {fG : Impl.RsaOaep.X86.Fns}
    (hT : ∀ σ, P.T σ → Proof.RsaOaep.X86.TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VP (fun τ s => W0 h P τ s ∧ s.syms = τ.syms)
      (seqs [.block accSet, .block acc0, .block (mgfArgsT h.H), Impl.RsaOaep.X86.mgfXor fG 15,
        .block topSet, .block topAnd, .block scanSet, countLoop scanBody, .block posChk,
        .ite .e (fixedPathT f h.H) (anyPathT f h.H)]) (fun τ s => GE h P τ s ∧ s.syms = τ.syms) :=
  vpAssoc ((Proof.RsaOaep.X86.VP.syms (acc_vp h P hP)).seq (unmask_vp h P hP hT fne
    ((Proof.RsaOaep.X86.VP.syms (scanSet_vp h P hP)).seq ((Proof.RsaOaep.X86.VP.syms (scan_vp h P hP)).seq
      ((Proof.RsaOaep.X86.VP.syms (pos_vp h P hP)).seq (tailIte_vp h P hP hTH fneH))))))

/-- The result is `verify`'s. -/
theorem fin_of (P : EP) {σ τ t : State} (hv : V2 h P σ τ) (hg : GE h P τ t) : Fin h P σ t := by
  obtain ⟨⟨hc, hi, hf, -⟩, hcr⟩ := hv
  obtain ⟨hc', hk, r0⟩ := hg
  obtain st : (P.lay h.D).St σ t :=
    ⟨hc.st.ok, hc'.st.sp, hc'.st.rd.trans hc.st.rd, hc'.st.wr.trans hc.st.wr, hc.st.frame.trans hc'.st.frame⟩
  refine ⟨⟨hi, st⟩, fun hpre => ?_⟩
  obtain hw := hcr hpre
  obtain hxb : Spec.Rsa.bytesAt τ.mem ((P.scr + BitVec.ofNat 32 oEm).setWidth 64) P.K =
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K) := by
    revert hw
    cases Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ) with
    | none => exact fun hw => hw.2
    | some y => exact fun hw => hw.2
  obtain hx : ∀ i < P.K, ((Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ)).getD (Spec.RsaPss.zeros P.K)).getD i 0 =
      emv P τ i := fun i hi' => by
    rw [← hxb, RsaPkcs1Sig.bytesAt_getD hi', (call_geo h hi).1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  obtain hdig : digB h P τ = digB h P σ := hc.st.ro (R := P.DIG h.D) (by simp)
  obtain g := good_iff h P τ hk.1 hf (RsaPkcs1Sig.bytesAt_len _ _ _) hx
  rw [hdig] at g
  rw [r0]
  by_cases e : acc2 h P τ = 0 ∧ HOk h P τ (if P.any = 0 then Mf h P τ else Ma h P τ)
  · rw [ite_eq_left e, ite_eq_left (g.1 e)]
  · rw [ite_eq_right e, ite_eq_right (fun h' => e (g.2 h'))]

/-- What the table of `MdHash` gives holds of a later state of the body. -/
theorem hfacts_st {P : EP} {σ τ : State} {dn : String} {f : MdFns} {ai ac ad : BitVec 32} (hi : In h.D P σ)
    (hs : (P.lay h.D).St σ τ) (sy : τ.syms = σ.syms) (hf : HFacts h dn f P.tabH ai ac ad σ) :
    HFacts h dn f P.tabH ai ac ad τ := by
  obtain ⟨R0, hR0, c0⟩ := hi.tblH 0 (by decide)
  obtain ⟨R3, hR3, c3⟩ := hi.tblH 3 (by decide)
  obtain ⟨R4, hR4, c4⟩ := hi.tblH 4 (by decide)
  exact ⟨by rw [sy]; exact hf.fi, by rw [sy]; exact hf.fc, by rw [sy]; exact hf.fd,
    by rw [Proof.RsaOaep.X86.St_roW hs hR0 c0]; exact hf.m0, by rw [Proof.RsaOaep.X86.St_roW hs hR3 c3]; exact hf.m3,
    by rw [Proof.RsaOaep.X86.St_roW hs hR4 c4]; exact hf.m4, by rw [sy]; exact hf.ai, by rw [sy]; exact hf.ac,
    by rw [sy]; exact hf.ad⟩

/-- What the table of `MdHash` gives holds of a later state of the body. -/
theorem tabfacts_st {P : EP} {σ τ : State} {G : Impl.Pbkdf2.Stream.X86.Hash} {fG : Impl.RsaOaep.X86.Fns}
    {ai au af : BitVec 32} (hi : In h.D P σ) (hs : (P.lay h.D).St σ τ) (sy : τ.syms = σ.syms)
    (hf : Proof.RsaOaep.X86.TabFacts G fG P.tab ai au af σ) : Proof.RsaOaep.X86.TabFacts G fG P.tab ai au af τ := by
  obtain ⟨R, hR, hc⟩ := hi.tbl
  obtain e : ∀ o, o + 4 ≤ 44 → τ.mem.readW (VG.X86.addr P.tab o) 32 = σ.mem.readW (VG.X86.addr P.tab o) 32 :=
    fun o ho => Proof.RsaOaep.X86.St_roW hs hR (hc o ho)
  obtain ⟨m0, m4, m8⟩ := hf.mem
  exact ⟨by rw [sy]; exact hf.ok, ⟨by rw [e 0 (by decide), sy]; exact m0, by rw [e 4 (by decide), sy]; exact m4,
    by rw [e 8 (by decide), sy]; exact m8⟩, by rw [e 24 (by decide)]; exact hf.d, by rw [sy]; exact hf.ai,
    by rw [sy]; exact hf.au, by rw [sy]; exact hf.af⟩

/-- The body, with the hash function of the table of `MdHash` and MGF1's of
the table of `MdHash`, whose facts hold of every later state of the body. -/
theorem body_vq (P : EP) (c : Ver.PublicImpl) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (hTHs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.TH τ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {fG : Impl.RsaOaep.X86.Fns}
    (hT : ∀ σ, P.T σ → Proof.RsaOaep.X86.TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (hTs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.T τ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VQ (fun σ s => S h P σ s ∧ s.syms = σ.syms) (verifyTail f h.H fG c.name c.code) (Fin h P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VQ.of_vp (VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩)
  show VQ _ (.seq (.block (verifyChk ++ params h.H)) (.ite .ne (.block [mi .eax 0])
    (.seq (.block pubArgs) (.seq (.call c.name c.code) _)))) _
  refine VQ.seq (Proof.RsaOaep.X86.VP.syms (chk_vp h P)) (VQ.ite (fun σ s hs => ⟨!decide (fits h P), by
      simp only [eval, hs.1.2.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2.2, h₂.1.2.2.2.2.2.2])
    (VQ.of_vp ((fail_vp h P).mono (fun σ s ⟨⟨hc, _⟩, e⟩ => ⟨hc, e⟩) fun _ _ h => h)) ?_)
  refine VQ.seq ((Proof.RsaOaep.X86.VP.syms (pa_vp h P)).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨m0_of h h1 e, sy⟩)
    fun _ _ h => h) (VQ.seq (Proof.RsaOaep.X86.VP.syms (call_vp h P c)) (VQ.reidx (rest_vp h P hP hTH fneH hT fne)
      (fun σ s ⟨hv, sy⟩ => ⟨w0_self h hv (hTHs σ s hv.1.2.1 hv.1.1.st sy) (hTs σ s hv.1.2.1 hv.1.1.st sy), rfl⟩)
      fun σ τ t ⟨hv, _⟩ hg => fin_of h P hv hg.1))

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/Inst.lean`), with the hash functions as
tables, as for signing (`SgVerified.lean`): the index of the hash function
of the table of `MdHash` at the argument 14 (`idx_vp`) chooses the tail for
it among those of `idxs` (`byLen_vq`, `body_vq'`), whose code for the index
is that for its sizes, with MGF1's of the table of `MdHash` at 15. The body
writes `esp` only through the frames of its calls (`body_noSp`); with the
frames around it (`wrap_ok`, `wrap_ct`) and the result as the shared
contract states it: `vg_rsa_pss_verify_precomputed`, calling a precomputed
public operation `c`, with the hash function any of the tables of `vs` and
MGF1's any of `gs`, is verified (`verify_verified`), given a state that meets
the contract (`VfSat.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaOaep.X86 (Fns byLen)
open VG.Proof.RsaOaep.X86 (OHash TabFacts VP.syms St_roW)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable (h : PssHash)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

theorem VQ.mono_pre {F F' G : State → State → Prop} {c : Prog isa} (hq : VQ F c G) (hF : ∀ σ s, F' σ s → F σ s) :
    VQ F' c G :=
  ⟨fun σ s hs => hq.1 σ s (hF σ s hs),
    hq.2.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, hF _ _ h₁, hF _ _ h₂⟩) fun _ _ h => h⟩

/-- `byLen` from stages with the index `D` in `edx`, which a `cmp` keeps:
the branch of `D`, at the end of the body. -/
theorem byLen_vq {F G : State → State → Prop} {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 32)
    (h16 : ∀ σ s, F σ s → s.gpr .edx = BitVec.ofNat 32 D)
    (hst : ∀ σ s t, F σ s → Fupd s t → t.syms = s.syms → F σ t)
    (hb : VQ F (b D) G) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 2 ^ 32 ∧
      TaintOk [] (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 x))])) → VQ F (byLen b ds) G
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, htx⟩ := hx x (List.mem_cons_self ..)
    refine VQ.seq (G := fun σ s => F σ s ∧ isa.eval .e s = some (decide (D = x)))
      (VP.taint [] htx (fun _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) fun σ s hs =>
        WP.mono_syms (Q := fun t => Fupd s t ∧ t.zf = some (s.gpr .edx - BitVec.ofNat 32 x == 0))
          (wp_cmpi fun t f _ z => WP.block_nil ⟨f, z⟩) fun t ⟨f, z⟩ sy => ⟨hst σ s t hs f sy, ?_⟩) ?_
    · show eval .e t = _
      simp only [eval, z, h16 σ s hs, Proof.RsaOaep.X86.ofNat_sub_beq32 hD hx0]
    refine VQ.ite (fun σ s hs => ⟨_, hs.2⟩) (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono_pre fun σ s hs => hs.1.1
      · exact VQ.of_vp (VP.empty fun σ s hs => by
          obtain e := hs.1.2.symm.trans hs.2
          simp [hDx] at e)
    · by_cases hDx : D = x
      · exact VQ.of_vp (VP.empty fun σ s hs => by
          obtain e := hs.1.2.symm.trans hs.2
          simp [hDx] at e)
      · exact (byLen_vq hD h16 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono_pre fun σ s hs => hs.1.1

/-- The index of the hash function of the table at the argument 14, to
`edx`. -/
theorem idx_vp (P : EP) {ix : Nat} (hix : ∀ σ, P.TH σ → σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix) :
    VP (Sy (S h P)) (.block (idxLoad 14)) (fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = BitVec.ofNat 32 ix) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.tblH5
  show VP _ (.block ([ld .edx (arg 14)] ++ [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 20))])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = P.tabH)
    (VP.taint [.esp] idxArg14_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] idxWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.sp, h₂.1.2.sp]
  · obtain ⟨⟨hi, hs⟩, sy⟩ := hs
    simp only [ld]
    refine hs.wp_arg (vf_arg h (j := 14) (by decide)) (by decide) fun t1 s1 u1 => WP.block_nil
      ⟨⟨⟨hi, s1⟩, u1.syms.trans sy⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.2.sp, h₂.1.1.2.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨⟨hi, hs⟩, sy⟩, hdx⟩ := hs
    obtain hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabH 20) 4 := ⟨tR, hs.inRo tRo, tC⟩
    refine wp_ldm (B := P.tabH) hdx hin fun t2 u2 => WP.block_nil ⟨⟨⟨hi, hs.upd u2 (by decide)⟩, u2.syms.trans sy⟩, ?_⟩
    rw [u2.gpr, St_roW hs tRo tC, hix σ hi.tabTH]

/-- The tail for an index is that for the sizes of its hash function. -/
theorem tail_eq {i : Nat} {f : MdFns} {fG : Fns} {pn : String} {pc : Prog isa}
    (hs : sizes h.H = sizesOf i) : verifyTail f (ofIdx i) fG pn pc = verifyTail f h.H fG pn pc := by
  rw [show ofIdx i = ofSizes (sizes h.H) by rw [hs]; rfl]
  rfl

/-- The body, for the hash function `h` of index `ix` and MGF1's `P.g`. -/
theorem body_vq' (P : EP) (c : Ver.PublicImpl) {dn : String} {f : MdFns} {ix : Nat} (hix₀ : ix ∈ idxs)
    (hs : sizes h.H = sizesOf ix)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ ∧
      σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix)
    (hTHs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.TH τ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (hTs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.T τ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VQ (Sy (S h P)) (verifyBodyT f fG c.name c.code) (Fin h P) := by
  obtain hlt : ix < 2 ^ 32 := (cmpIdxs_taint ix hix₀).1
  show VQ _ (.seq (.block (idxLoad 14)) (byLen (fun i => verifyTail f (ofIdx i) fG c.name c.code) idxs)) _
  refine VQ.seq (idx_vp h P fun σ hσ => (hTH σ hσ).2) (byLen_vq (D := ix) hlt (fun _ _ hs => hs.2)
    (fun σ s t ⟨⟨⟨hi, hs⟩, sy⟩, dx⟩ fu sy' => ⟨⟨⟨hi, hs.fupd fu⟩, sy'.trans sy⟩, by rw [fu.gpr]; exact dx⟩) ?_ hix₀
    cmpIdxs_taint)
  rw [tail_eq h hs]
  exact (body_vq h P c (fun σ hσ => (hTH σ hσ).1) hTHs fneH hT hTs fne).mono_pre fun _ _ hs => hs.1

/-! ## The stack -/

theorem tail_noSp {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {fG : Fns} (gi : ∀ q ∈ fG.init, NoSp q.2) (gu : ∀ q ∈ fG.upd, NoSp q.2)
    (gf : ∀ q ∈ fG.fin, NoSp q.2) (c : Ver.PublicImpl) : NoSp (verifyTail f h.H fG c.name c.code) := by
  obtain sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig4
  have p3 := sp.lenArgs8
  have p4 := sp.fxSalt
  have p5 := sp.cpDb
  have p6 := sp.passSet
  have p7 := sp.anyLen
  have p8 := sp.cmpArgs
  have p9 := sp.mgfArgs
  obtain hct := ctHashT_noSp h hi hc hd (j := 14) (NoSp.of_all (by decide +kernel))
  obtain hm := Proof.RsaOaep.X86.mgfX_noSp gi gu gf (j := 15) (NoSp.of_all (by decide +kernel))
  have hcc := c.noSp
  simp only [verifyTail, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [verifyMainT, fixedPathT, anyPathT, yDig, shift, passOne, cmpH, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSp {f : MdFns} {fG : Fns} (hf : Sg.FnsSp f fG) (hall : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i)
    (c : Ver.PublicImpl) : NoSp (verifyBodyT f fG c.name c.code) := by
  refine noSp_seq (NoSp.of_all (by decide +kernel)) (Proof.RsaOaep.X86.byLen_noSp fun i hi => ?_)
  obtain ⟨h', hs⟩ := hall i hi
  rw [tail_eq h' hs]
  exact tail_noSp h' hf.hi hf.hc hf.hd hf.gi hf.gu hf.gf c

/-! ## The entry -/

variable {vs : List MVar} {gs : List TVar}

/-- The code, calling `c`, with the hash function any of the tables of `vs`
and MGF1's any of `gs`. -/
abbrev verifyCode (vs : List MVar) (gs : List TVar) (c : Ver.PublicImpl) : Prog isa :=
  verifyPrecomputed (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) c.name c.code

/-- The contract, with those tables. -/
abbrev vspec (vs : List MVar) (gs : List TVar) : Contract isa :=
  spec (Proof.MdHashTable.X86.tables vs) (Proof.HashTable.X86.tables gs)

theorem code_noSp (hok : Sg.OK vs gs) (c : Ver.PublicImpl) : NoSp (verifyCode vs gs c) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp (Sg.fnsSp vs gs) (Sg.hall_of hok) c)) restore_noSp)

theorem code_sp (hok : Sg.OK vs gs) (c : Ver.PublicImpl) : (verifyCode vs gs c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp hok c)

theorem spec_sp {s : State} (hs : (vspec vs gs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  verify_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega_using [hsa]⟩

/-- The public parameters for the table of `MdHash` of `w` and that of
`Hash` of `wg`, with their functions where `s'` has them. -/
abbrev epw (vs : List MVar) (gs : List TVar) (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep s (s'.syms w.h.H.st.initN) (s'.syms w.h.H.compN) (s'.syms (Proof.MdHashTable.X86.digName w))
    (Sg.THw vs w (arg s 14) s') (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (TabFacts wg.g.H (Proof.HashTable.X86.fnsOf gs) (arg s 15) (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN)
      (s'.syms wg.g.H.finN)) wg.g

/-- The digest's length, from the hash function the table names. -/
theorem dlen_of {s : State} (hs : (vspec vs gs).pre s) {w : MVar}
    (hh : Abi.tableHeld 32 s.mem ((arg s 14).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w))) :
    (arg s 5).toNat = w.h.D := by
  obtain ⟨-, -, -, hfitH, -, hdl⟩ := spec_tab hs
  have := hdl _ (Proof.MdHashTable.X86.hashAt_tableOf hfitH (Proof.MdHashTable.X86.held_tableOf hfitH hh).2.2.2)
  rw [this, w.h.glen]

/-- The entry state, for the tables of `w` at the argument 14 and `wg` at
15, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hok : Sg.OK vs gs) {s s' : State} (hs : (vspec vs gs).pre s) {w : MVar} {wg : TVar}
    (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hhH : Abi.tableHeld 32 s.mem ((arg s 14).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w)))
    (hh : Abi.tableHeld 32 s.mem ((arg s 15).setWidth 64) (FnTable.words isa s (Proof.HashTable.X86.tableOf wg)))
    (hsy : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s.syms n = s'.syms n) :
    Sy (S w.h (epw vs gs s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitH, hfit, -⟩ := spec_tab hs
  obtain hpwH := hpw.sublist (List.sublist_append_left _ _)
  obtain hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  obtain hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  obtain hD := dlen_of hs hhH
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 (fun _ => True) wg.g
  obtain ok := (in_of_pre (hai := 0) (hac := 0) (had := 0) (TH := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) (g := wg.g) hs trivial trivial).ok
  rw [ep_lay] at ok
  obtain hn := Proof.MdHashTable.X86.mem_names hw
  obtain hng := Proof.HashTable.X86.mem_names hwg
  obtain hsyH : ∀ n ∈ Proof.MdHashTable.X86.names vs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_left _ h)
  obtain hsyG : ∀ n ∈ Proof.HashTable.X86.names gs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_right _ h)
  obtain tf := Proof.HashTable.X86.tabFacts_entered (argv := e0.argv (arg s 5).toNat) (ro := e0.ro (arg s 5).toNat)
    (rw := e0.rw) (C := 100) hsp ok (p := arg s 15) (by simp [e0, ep]) hfit hok.2.2.1 hpwG hwg hh
  rw [hsyG _ hng.1, hsyG _ hng.2.1, hsyG _ hng.2.2] at tf
  obtain sy : (entered frameBytes s).syms = s.syms := pushRegs_syms s _
  obtain ⟨m0, m3, m4, m5⟩ := Proof.MdHashTable.X86.held_entered (argv := e0.argv (arg s 5).toNat)
    (ro := e0.ro (arg s 5).toNat) (rw := e0.rw) (C := 100) hsp ok (p := arg s 14) (by simp [e0, ep]) hfitH hhH
  obtain hf := Proof.MdHashTable.X86.hfacts_of hok.1 (σ := entered frameBytes s) (by rw [sy]; exact hpwH) hw m0 m3 m4
  rw [sy, hsyH _ hn.1, hsyH _ hn.2.2.2.1, hsyH _ hn.2.2.2.2] at hf
  obtain hi := in_of_pre (hai := s'.syms w.h.H.st.initN) (hac := s'.syms w.h.H.compN)
    (had := s'.syms (Proof.MdHashTable.X86.digName w)) (TH := Sg.THw vs w (arg s 14) s')
    (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN) (af := s'.syms wg.g.H.finN) (g := wg.g) hs ⟨hf, m5⟩ tf
  rw [hD] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

/-- The body, for the tables of `w` and `wg`. -/
theorem bodyw_vq (hok : Sg.OK vs gs) (c : Ver.PublicImpl) (s s' : State) {w : MVar} {wg : TVar} (hw : w ∈ vs)
    (hwg : wg ∈ gs) :
    VQ (Sy (S w.h (epw vs gs s s' w wg))) (verifyBodyT (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs)
      c.name c.code) (Fin w.h (epw vs gs s s' w wg)) := by
  obtain ⟨fneH, fne⟩ := Sg.fne_of hw hwg
  refine body_vq' w.h (epw vs gs s s' w wg) c (hok.2.1 w hw).1 (hok.2.1 w hw).2 (fun _ x => x) ?_ fneH
    (fun _ x => x) (fun σ τ hi hs sy => tabfacts_st w.h hi hs sy hi.tabT) fne
  intro σ τ hi hs sy
  obtain ⟨tR, tRo, tC⟩ := hi.tblH5
  exact ⟨hfacts_st w.h hi hs sy hi.tabTH.1, (St_roW hs tRo tC).trans hi.tabTH.2⟩

theorem code_ok (hok : Sg.OK vs gs) (c : Ver.PublicImpl) {s : State} (hs : (vspec vs gs).pre s) :
    WP isa (verifyCode vs gs c) s fun t => abiPreserved s t ∧ (vspec vs gs).post s t := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨T, hT, hh⟩, -, hfitH, hfit, -⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  obtain hidxH := (Proof.MdHashTable.X86.held_tableOf hfitH hhH).2.2.2
  obtain hidx := (Proof.HashTable.X86.held_tableOf hfit hh).2.1
  obtain he := entered_state hok hs hw hwg hhH hh (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  obtain hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega_using [hsp0]
  obtain hb := (bodyw_vq hok c s s hw hwg).1 _ _ he
  obtain hD := dlen_of hs hhH
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp (Sg.fnsSp vs gs) (Sg.hall_of hok) c) hsp hfit4
    (W := ((epw vs gs s s w wg).lay w.h.D).W)
    (Q := fun r _ => Res w.h (epw vs gs s s w wg) (entered frameBytes s) r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩) (fun r m m' fl hres => ?_)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok hr
    rw [save_eq (argv := (epw vs gs s s w wg).argv (arg s 5).toNat) (ro := (epw vs gs s s w wg).ro (arg s 5).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 100) hsp,
      ret_eq (argv := (epw vs gs s s w wg).argv (arg s 5).toNat) (ro := (epw vs gs s s w wg).ro (arg s 5).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 100) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · exact hres
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok
    obtain ro := fun {R : Region} (hR : R ∈ (epw vs gs s s w wg).ro (arg s 5).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argSlots, argVal, argBytes]
    intro H G hH hG
    rw [Proof.MdHashTable.X86.hashAt_tableOf hfitH hidxH, Option.some.injEq] at hH
    rw [Proof.HashTable.X86.hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    obtain hG : sigB (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 1).toNat := by
      obtain e : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 6).setWidth 64) (epw vs gs s s w wg).gl =
          Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (epw vs gs s s w wg).gl :=
        ro (R := (epw vs gs s s w wg).SIG) (by simp)
      rw [hin.glK] at e
      exact e
    obtain hdg : digB w.h (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat := by
      unfold digB; rw [← hD]; exact ro (R := (epw vs gs s s w wg).DIG (arg s 5).toNat) (by simp)
    rw [hdg, hG, hD] at res
    rw [BitVec.setWidth_append_eq_right, w.h.glen]
    exact res

theorem code_ct (hok : Sg.OK vs gs) (c : Ver.PublicImpl) :
    ConstantTime isa (vspec vs gs).pre (vspec vs gs).pub (verifyCode vs gs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨T, hT, hh₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabH, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hp
  obtain hhH₂ := (htabH _ _ rfl rfl _ hTH).mp hhH₁
  obtain hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  obtain hsy' : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s₂.syms n = s₁.syms n :=
    fun n hn => (hsy n (by simpa [Proof.MdHashTable.X86.names, Proof.HashTable.X86.names] using hn)).symm
  obtain hep : epw vs gs s₁ s₁ w wg = epw vs gs s₂ s₁ w wg := by
    obtain ⟨hab, hw'⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a1, a3])
    obtain ⟨hn, he⟩ := List.append_inj (Sg.map_toNat_inj hab) (by simp [RsaPkcs1Sig.bytesAt_len, a1])
    obtain hw'' := Sg.map_toNat_inj hw'
    simp only [ep]
    rw [hsp, a0, a1, a2, a3, a4, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
    rw [a0, a1] at hn
    rw [a2, a3] at he
    rw [a12, a13] at hw''
    rw [hn, he, hw'']
  refine (wrap_ct (F := frameBytes) (body_noSp (Sg.fnsSp vs gs) (Sg.hall_of hok) c)
    (P := fun a b => a = s₁ ∧ b = s₂) (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
    e₁ e₂).1
  refine (bodyw_vq hok c s₁ s₁ hw hwg).2.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hok h₁ hw hwg hhH₁ hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hok h₂ hw hwg hhH₂ hh₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_verify_precomputed`, calling `c`, with the hash function any
of the tables of `vs` and MGF1's any of `gs`, meets the shared contract
(satisfiable, `VfSat.lean`). -/
theorem verify_verified (hok : Sg.OK vs gs) (hsat : ∃ s, (vspec vs gs).pre s) (c : Ver.PublicImpl) :
    Verified target (verifyCode vs gs c) (vspec vs gs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hok c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hok c, hsat⟩

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on x86: the contract is satisfiable

A state that meets `verifyPrecomputedMdTableContract` (`verify_sat`), with the
hash function's table that of any variant `w` of `vs` and MGF1's that of any
variant `wg` of `gs`: a modulus of 64 bytes, `e` of one byte, a signature of
64 bytes, the working space it needs, the precomputed values' 16 words, the
arguments above `esp = 0x20000`, and the tables where signing's are
(`Sg.withTabs`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct2)
open VG.Proof.RsaPss.X86.Sg (withTabs withTabs_arg withTabs_heldH withTabs_held D_mem)

/-- The state, but for the tables, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131096 then BitVec.ofNat 8 D else if a = 131077 then 0x20 else if a = 131080 then 0x40 else
    if a = 131085 then 0x21 else if a = 131088 then 0x1 else if a = 131093 then 0x30 else
    if a = 131101 then 0x31 else if a = 131104 then 0x40 else if a = 131118 then 0x1 else
    if a = 131120 then 0x20 else if a = 131121 then 0x8 else if a = 131125 then 0x70 else
    if a = 131128 then 0x10 else if a = 131134 then 0x30 else if a = 131137 then 0x1 else
    if a = 131138 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, D⟩, ⟨0x3100, 64⟩, ⟨0x7000, 128⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩]
  wr := [⟨0x10000, 2080 * 8⟩, ⟨0x20004, 64⟩]

theorem verify_sat16 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 16) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hA : ∀ j < 16, (argAddr (satState 16) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hhH := withTabs_heldH (satState 16) vs gs w wg
  obtain hhG := withTabs_held (satState 16) vs gs w wg
  obtain hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 16) vs gs w wg, ?_⟩
  obtain a0 : arg (withTabs (satState 16) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  obtain a1 : arg (withTabs (satState 16) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  obtain a2 : arg (withTabs (satState 16) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  obtain a3 : arg (withTabs (satState 16) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  obtain a4 : arg (withTabs (satState 16) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  obtain a5 : arg (withTabs (satState 16) vs gs w wg) 5 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  obtain a6 : arg (withTabs (satState 16) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  obtain a7 : arg (withTabs (satState 16) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  obtain a8 : arg (withTabs (satState 16) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  obtain a9 : arg (withTabs (satState 16) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  obtain a10 : arg (withTabs (satState 16) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  obtain a11 : arg (withTabs (satState 16) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  obtain a12 : arg (withTabs (satState 16) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  obtain a13 : arg (withTabs (satState 16) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  obtain a14 : arg (withTabs (satState 16) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  obtain a15 : arg (withTabs (satState 16) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  obtain e : argAddr (withTabs (satState 16) vs gs w wg) 0 = 0x20004 := show argAddr (satState 16) 0 = _ by decide
  have esp : (withTabs (satState 16) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 16) vs gs w wg).rd = (satState 16).rd := rfl
  have wr : (withTabs (satState 16) vs gs w wg).wr = (satState 16).wr := rfl
  have sy : (withTabs (satState 16) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 16) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat20 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 20) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hA : ∀ j < 16, (argAddr (satState 20) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hhH := withTabs_heldH (satState 20) vs gs w wg
  obtain hhG := withTabs_held (satState 20) vs gs w wg
  obtain hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 20) vs gs w wg, ?_⟩
  obtain a0 : arg (withTabs (satState 20) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  obtain a1 : arg (withTabs (satState 20) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  obtain a2 : arg (withTabs (satState 20) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  obtain a3 : arg (withTabs (satState 20) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  obtain a4 : arg (withTabs (satState 20) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  obtain a5 : arg (withTabs (satState 20) vs gs w wg) 5 = 0x14 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  obtain a6 : arg (withTabs (satState 20) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  obtain a7 : arg (withTabs (satState 20) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  obtain a8 : arg (withTabs (satState 20) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  obtain a9 : arg (withTabs (satState 20) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  obtain a10 : arg (withTabs (satState 20) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  obtain a11 : arg (withTabs (satState 20) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  obtain a12 : arg (withTabs (satState 20) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  obtain a13 : arg (withTabs (satState 20) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  obtain a14 : arg (withTabs (satState 20) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  obtain a15 : arg (withTabs (satState 20) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  obtain e : argAddr (withTabs (satState 20) vs gs w wg) 0 = 0x20004 := show argAddr (satState 20) 0 = _ by decide
  have esp : (withTabs (satState 20) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 20) vs gs w wg).rd = (satState 20).rd := rfl
  have wr : (withTabs (satState 20) vs gs w wg).wr = (satState 20).wr := rfl
  have sy : (withTabs (satState 20) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 20) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat28 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 28) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hA : ∀ j < 16, (argAddr (satState 28) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hhH := withTabs_heldH (satState 28) vs gs w wg
  obtain hhG := withTabs_held (satState 28) vs gs w wg
  obtain hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 28) vs gs w wg, ?_⟩
  obtain a0 : arg (withTabs (satState 28) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  obtain a1 : arg (withTabs (satState 28) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  obtain a2 : arg (withTabs (satState 28) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  obtain a3 : arg (withTabs (satState 28) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  obtain a4 : arg (withTabs (satState 28) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  obtain a5 : arg (withTabs (satState 28) vs gs w wg) 5 = 0x1c := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  obtain a6 : arg (withTabs (satState 28) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  obtain a7 : arg (withTabs (satState 28) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  obtain a8 : arg (withTabs (satState 28) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  obtain a9 : arg (withTabs (satState 28) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  obtain a10 : arg (withTabs (satState 28) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  obtain a11 : arg (withTabs (satState 28) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  obtain a12 : arg (withTabs (satState 28) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  obtain a13 : arg (withTabs (satState 28) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  obtain a14 : arg (withTabs (satState 28) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  obtain a15 : arg (withTabs (satState 28) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  obtain e : argAddr (withTabs (satState 28) vs gs w wg) 0 = 0x20004 := show argAddr (satState 28) 0 = _ by decide
  have esp : (withTabs (satState 28) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 28) vs gs w wg).rd = (satState 28).rd := rfl
  have wr : (withTabs (satState 28) vs gs w wg).wr = (satState 28).wr := rfl
  have sy : (withTabs (satState 28) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 28) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat32 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 32) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hA : ∀ j < 16, (argAddr (satState 32) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hhH := withTabs_heldH (satState 32) vs gs w wg
  obtain hhG := withTabs_held (satState 32) vs gs w wg
  obtain hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 32) vs gs w wg, ?_⟩
  obtain a0 : arg (withTabs (satState 32) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  obtain a1 : arg (withTabs (satState 32) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  obtain a2 : arg (withTabs (satState 32) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  obtain a3 : arg (withTabs (satState 32) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  obtain a4 : arg (withTabs (satState 32) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  obtain a5 : arg (withTabs (satState 32) vs gs w wg) 5 = 0x20 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  obtain a6 : arg (withTabs (satState 32) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  obtain a7 : arg (withTabs (satState 32) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  obtain a8 : arg (withTabs (satState 32) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  obtain a9 : arg (withTabs (satState 32) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  obtain a10 : arg (withTabs (satState 32) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  obtain a11 : arg (withTabs (satState 32) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  obtain a12 : arg (withTabs (satState 32) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  obtain a13 : arg (withTabs (satState 32) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  obtain a14 : arg (withTabs (satState 32) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  obtain a15 : arg (withTabs (satState 32) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  obtain e : argAddr (withTabs (satState 32) vs gs w wg) 0 = 0x20004 := show argAddr (satState 32) 0 = _ by decide
  have esp : (withTabs (satState 32) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 32) vs gs w wg).rd = (satState 32).rd := rfl
  have wr : (withTabs (satState 32) vs gs w wg).wr = (satState 32).wr := rfl
  have sy : (withTabs (satState 32) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 32) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat48 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 48) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hA : ∀ j < 16, (argAddr (satState 48) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hhH := withTabs_heldH (satState 48) vs gs w wg
  obtain hhG := withTabs_held (satState 48) vs gs w wg
  obtain hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 48) vs gs w wg, ?_⟩
  obtain a0 : arg (withTabs (satState 48) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  obtain a1 : arg (withTabs (satState 48) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  obtain a2 : arg (withTabs (satState 48) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  obtain a3 : arg (withTabs (satState 48) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  obtain a4 : arg (withTabs (satState 48) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  obtain a5 : arg (withTabs (satState 48) vs gs w wg) 5 = 0x30 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  obtain a6 : arg (withTabs (satState 48) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  obtain a7 : arg (withTabs (satState 48) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  obtain a8 : arg (withTabs (satState 48) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  obtain a9 : arg (withTabs (satState 48) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  obtain a10 : arg (withTabs (satState 48) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  obtain a11 : arg (withTabs (satState 48) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  obtain a12 : arg (withTabs (satState 48) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  obtain a13 : arg (withTabs (satState 48) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  obtain a14 : arg (withTabs (satState 48) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  obtain a15 : arg (withTabs (satState 48) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  obtain e : argAddr (withTabs (satState 48) vs gs w wg) 0 = 0x20004 := show argAddr (satState 48) 0 = _ by decide
  have esp : (withTabs (satState 48) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 48) vs gs w wg).rd = (satState 48).rd := rfl
  have wr : (withTabs (satState 48) vs gs w wg).wr = (satState 48).wr := rfl
  have sy : (withTabs (satState 48) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 48) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat64 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 64) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hA : ∀ j < 16, (argAddr (satState 64) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hhH := withTabs_heldH (satState 64) vs gs w wg
  obtain hhG := withTabs_held (satState 64) vs gs w wg
  obtain hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 64) vs gs w wg, ?_⟩
  obtain a0 : arg (withTabs (satState 64) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  obtain a1 : arg (withTabs (satState 64) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  obtain a2 : arg (withTabs (satState 64) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  obtain a3 : arg (withTabs (satState 64) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  obtain a4 : arg (withTabs (satState 64) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  obtain a5 : arg (withTabs (satState 64) vs gs w wg) 5 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  obtain a6 : arg (withTabs (satState 64) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  obtain a7 : arg (withTabs (satState 64) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  obtain a8 : arg (withTabs (satState 64) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  obtain a9 : arg (withTabs (satState 64) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  obtain a10 : arg (withTabs (satState 64) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  obtain a11 : arg (withTabs (satState 64) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  obtain a12 : arg (withTabs (satState 64) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  obtain a13 : arg (withTabs (satState 64) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  obtain a14 : arg (withTabs (satState 64) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  obtain a15 : arg (withTabs (satState 64) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  obtain e : argAddr (withTabs (satState 64) vs gs w wg) 0 = 0x20004 := show argAddr (satState 64) 0 = _ by decide
  have esp : (withTabs (satState 64) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 64) vs gs w wg).rd = (satState 64).rd := rfl
  have wr : (withTabs (satState 64) vs gs w wg).wr = (satState 64).wr := rfl
  have sy : (withTabs (satState 64) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 64) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hs : Proof.MdHashTable.X86.Shape w)
    (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  obtain hDm := D_mem hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hDm
  rcases hDm with e | e | e | e | e | e
  exacts [verify_sat16 hw hwg e hl, verify_sat20 hw hwg e hl, verify_sat28 hw hwg e hl, verify_sat32 hw hwg e hl,
    verify_sat48 hw hwg e hl, verify_sat64 hw hwg e hl]

end VG.Proof.RsaPss.X86.Vf

end

end


/-!
# RSASSA-PSS on x86: the instances emitted

The variants of the hash functions whose tables of `MdHash` the functions
take (`mvars`: MD5's, SHA-1's and SHA-224's and SHA-256's with each of their
backends, and the SHA-512 family's), and the instances' proofs against the
contracts the registrations state, with the hash function any of the tables
of `MdHash` and MGF1's any of `MdHash`: signing (`sign_ok`, and `signP_ok`
given `pre`) and verification (`verify_ok`), when the registration's check
(`Sg.OK`) holds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable {vs : List MVar} {gs : List TVar}

theorem ok_sat (hok : Sg.OK vs gs) : ∃ w ∈ vs, ∃ wg ∈ gs, Proof.MdHashTable.X86.Shape w := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  obtain ⟨wg, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2.1
  exact ⟨w, hw, wg, hwg, hok.2.1 w hw⟩

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs` and the private-key
operation of `c`. -/
theorem sign_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (Sg.signCode vs gs c) (Sg.sspec vs gs) :=
  Sg.sign_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Sg.sign_sat hw hwg hs hok.2.2.2.2.2) c

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs` and `gs` and the
private-key operation of `c` and `w`, given `pre`. -/
theorem signP_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : Proof.Rsa.X86.PrivChecked.CrtImpl)
    (w : Proof.Rsa.X86.PrivChecked.CrtPImpl) :
    Verified target (Sg.signCodeP vs gs c w) (Sg.sspecP vs gs) :=
  Sg.signP_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Sg.sign_satP hw hwg hs hok.2.2.2.2.2) c w

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs` and the
public-key operation of `c`. -/
theorem verify_ok (vs : List MVar) (gs : List TVar) (hok : Sg.OK vs gs) (c : RsaPkcs1Sig.X86.Ver.PublicImpl) :
    Verified target (Vf.verifyCode vs gs c) (Vf.vspec vs gs) :=
  Vf.verify_verified hok (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; Vf.verify_sat hw hwg hs hok.2.2.2.2.2) c

end VG.Proof.RsaPss.X86
