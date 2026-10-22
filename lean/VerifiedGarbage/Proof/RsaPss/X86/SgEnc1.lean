module

public import VerifiedGarbage.Proof.RsaPss.X86.SgChk
public import VerifiedGarbage.Proof.RsaPss.X86.CtMgfLoop
public import VerifiedGarbage.Proof.RsaPss.X86.YDig
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on x86: `H = Hash(M')`

When everything fits (`E0`): `M' = 0x00 ×8 ‖ mHash ‖ salt` in `Y`
(`yDig_sg`, `salt_vp`), its length and blocks to their slots (`lenSet_vp`),
and its hash `H` at `oDig` (`hash_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- The modulus' first byte, as a word; `dbLen`. -/
abbrev xB (P : EP) : BitVec 32 := (n0 P).setWidth 32
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots of the encoding's parameters. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW (xB P) ∧ m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P)

/-- What the encoding keeps. -/
abbrev Kp (P : EP) (σ : State) (m : Mem) : Prop := In h.D P σ ∧ fits h P ∧ Bm h P m

/-- When everything fits. -/
abbrev E0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem

/-- What misses the slots of the parameters. -/
abbrev Away3 (L : Lay) (r : Region) : Prop :=
  (slotR L sC).Disjoint r ∧ (slotR L sLo).Disjoint r ∧ (slotR L sDb).Disjoint r

theorem Kp.keep {P : EP} {σ : State} {m m' : Mem} {rs : List Region} (hk : Kp h P σ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Away3 (P.lay h.D) r) : Kp h P σ m' :=
  ⟨hk.1, hk.2.1, slot_keep hf (fun r hr => (hd r hr).1) hk.2.2.1, slot_keep hf (fun r hr => (hd r hr).2.1) hk.2.2.2.1,
    slot_keep hf (fun r hr => (hd r hr).2.2) hk.2.2.2.2⟩

theorem away3_scr {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) :
    Away3 L (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide)⟩

theorem away3_slot {L : Lay} {d : Nat} (hd : d + 4 ≤ frameBytes) (h₁ : d + 4 ≤ sLo ∨ sDb + 4 ≤ d) :
    Away3 L (slotR L d) := by
  have e1 : sLo = 80 := rfl
  have e2 : sC = 84 := rfl
  have e3 : sDb = 88 := rfl
  exact ⟨slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega), slotSep (by decide) hd (by omega)⟩

theorem away3_ctW {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctW h L scr T, Away3 L r := fun r hr =>
  ⟨ctW_slot h hg hT (by decide) (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) (by decide) r hr⟩

/-- Everything fits, and the parameters are in their slots. -/
theorem e0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : E0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, z⟩ := hc
  have hf : fits h P := by
    simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
    exact e
  refine ⟨hc, hi, hf, sc, sl, ?_⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega
  have hD : h.H.D = h.D := rfl
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by have := hf.2; omega), Offset.ofNat_sub_ofNat (by have := hf.2; omega)]
  congr 1

/-- The digest, a buffer the body only reads. -/
theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  have hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.dig.isLt; omega)] at hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  exact ⟨hf, by omega, ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `M'`. -/
abbrev Mp (P : EP) (σ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P σ ++ saltB P σ

/-- `Y` cleared, and the digest after 8 zeros. -/
theorem yDig_sg (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E0 h P) (yDig h.H 16)
      (fun σ s => E0 h P σ s ∧ ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 16) h.certs.cpDig16 (by simp) (dgP := P.dig) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.bytesAt_len _ _ _) (fun σ s hc i hi => ?_) (X := Kp h P)
    fun σ m m' hk hf => hk.keep h hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by decide)).mono
    (fun σ s h => h) fun σ s ⟨hc, hk, hy⟩ => ⟨⟨hc, hk⟩, hy⟩
  have e : Spec.Rsa.bytesAt s.mem (P.dig.setWidth 64) h.D = Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (P.dig.setWidth 64 + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD hi]

/-- `Y` before and after the salt. -/
abbrev Y1 (P : EP) (σ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0
abbrev Y2 (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mp h P σ).getD i 0

theorem salt_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.salt P.sl := by
  obtain ⟨σ, hi⟩ := hP
  have hf := hi.ok.fits P.SALT (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.salt.isLt; omega)] at hf
  exact ⟨hf, hi.sl32, ⟨P.SALT, by simp, Region.contains_self _ _⟩⟩

theorem salt_at {P : EP} {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) {i : Nat} (hi : i < P.sl) :
    s.mem (byteAt P.salt i) = (saltB P σ).getD i 0 := by
  have e : Spec.Rsa.bytesAt s.mem (P.salt.setWidth 64) P.sl = Spec.Rsa.bytesAt σ.mem (P.salt.setWidth 64) P.sl :=
    hc.st.ro (R := P.SALT) (by simp)
  show s.mem (P.salt.setWidth 64 + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (P.salt.setWidth 64) P.sl).getD i 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD hi]

/-- The arguments of `sign`. -/
theorem sg_arg {j : Nat} (hj : j < 21) {P : EP} : j < ((P.lay h.D).argv).length := by simp; omega

/-- The salt after the digest. -/
theorem salt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => E0 h P σ s ∧ Y1 h P σ s.mem)
      (.seq (.block (cpSalt h.H)) (.ite .e (.block []) Impl.Bignum.X86.copyBytes))
      (fun σ s => E0 h P σ s ∧ Y2 h P σ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have eD : h.H.D = h.D := rfl
  have hK := hi₀.k1024
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.2.1
  have hsl : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega
  refine VP.seq (G := fun σ s => (E0 h P σ s ∧ Y1 h P σ s.mem) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .esi = P.salt ∧ s.gpr .ecx = BitVec.ofNat 32 P.sl ∧ s.zf = some (decide (P.sl = 0)))
    (VP.taint [.esp, .ebp] h.certs.cpSalt (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hk⟩, hy⟩ => ?_)
    (VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
      (VP.block_nil fun σ s ⟨⟨⟨⟨hc, hk⟩, hy⟩, _, _, _, z⟩, e⟩ => ⟨⟨hc, hk⟩, fun i hi => ?_⟩) ?_)
  · simp only [cpSalt, atS, ld, addi, List.cons_append, List.nil_append]
    refine hc.wp_arg hg (sg_arg h (j := 17) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
      wp_mov fun t2 u2 => wp_addi fun t3 u3 => ?_
    refine (((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide))).wp_arg hg
      (sg_arg h (j := 18) (by decide)) (by decide) (by decide) fun t4 c4 u4 => wp_test fun t5 u5 z5 => WP.block_nil ?_
    have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨c4.fupd u5, m5 ▸ hk⟩, m5 ▸ hy⟩, ?_, ?_, ?_, ?_⟩
    · rw [u5.gpr]; simp (disch := decide) only [u4.other, u3.gpr, u2.gpr, u1.other, hc.ebp]
    · rw [u5.gpr]; simp (disch := decide) only [u4.other, u3.other, u2.other, u1.gpr]; rfl
    · rw [u5.gpr, u4.gpr]; rfl
    · rw [z5, u4.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hi₀.sl32)
  · have h0 : P.sl = 0 := by
      simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [hy i hi]
    simp [Mp, saltB, h0, Spec.Rsa.bytesAt]
  · by_cases h0 : P.sl = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.sl) (by pomega) (by omega))
      (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.scrA (by pomega)]; exact (hg.ro ok (by pomega) (R := P.SALT)
        (by simp)).symm) (by omega) (f := fun σ i => (saltB P σ).getD i 0)
      (Inv := fun σ m => Kp h P σ m ∧ (∀ i < 8 + h.D, m (sa P.scr (oY + i)) =
        (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0) ∧ YZ P.scr (8 + h.D + P.sl) m) fun σ m m' ⟨hk, h1, h2⟩ hf => ?_).mono
      (fun σ s ⟨⟨⟨⟨hc, hk⟩, hy⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega), fun i hi => ?_⟩, bx, si,
        cx, fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨⟨hc, hk⟩, fun i hi => ?_⟩
    · rw [hg.scrA (by pomega)] at hf
      refine ⟨hk.keep h hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by pomega),
        sbytes_keep hf (fun r hr => ?_) (by pomega) h1, sbytes_keep hf (fun r hr => ?_) (by pomega) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [show oY + (8 + h.D + P.sl) + i = oY + (8 + h.D + P.sl + i) by omega, hy _ (by omega),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]; omega)]
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P σ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]
      rw [RsaPss.getD_app, hl]
      by_cases e1 : i < 8 + h.D
      · rw [ite_eq_left e1]; exact h1 i e1
      rw [ite_eq_right e1]
      by_cases e2 : i < 8 + h.D + P.sl
      · rw [← hs (i - (8 + h.D)) (by omega), hg.byteAt_scr (by pomega),
          show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega]
      · rw [getD_ge (l := saltB P σ) (by rw [RsaPkcs1Sig.bytesAt_len]; omega),
          show oY + i = oY + (8 + h.D + P.sl) + (i - (8 + h.D + P.sl)) by omega]
        exact h2 _ (by omega)

/-- `M'`'s blocks. -/
abbrev nbS (P : EP) : Nat := (P.sl + (8 + h.D) + h.L) / h.B + 1

/-- What `ctHash` keeps, with `M'`'s length and blocks in their slots. -/
abbrev Kh (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ m.readW ((P.lay h.D).fr sL) 32 = BitVec.ofNat 32 (Mp h P σ).length ∧
    m.readW ((P.lay h.D).fr sNb) 32 = BitVec.ofNat 32 (nbS h P)

theorem Mp_length (P : EP) (σ : State) : (Mp h P σ).length = P.sl + (8 + h.D) := by
  simp only [Mp, List.length_append, RsaPss.zeros_length, digB, saltB, RsaPkcs1Sig.bytesAt_len]; omega

/-- `M'`'s length and blocks. -/
theorem lenSet_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Y2 h P σ s.mem) (.block (lenArgs h.H 18))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kh h P σ s.mem ∧ Y2 h P σ s.mem) := by
  refine VP.taint [.esp, .ebp] h.certs.lenArgs18 (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hk⟩, hy⟩ => ?_
  have hg := hk.1.geo
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.sl32
  have hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hk.2.1.2; omega
  have hK := hk.1.k1024
  have e1 : BitVec.ofNat 32 (P.sl + (8 + h.D) + h.L) >>> lgB h.H =
      BitVec.ofNat 32 ((P.sl + (8 + h.D) + h.L) / h.B) := by
    rw [ofNat_shr (by omega), h.pow_lg]
  obtain ⟨σ', ok⟩ := hg.ok
  simp only [lenArgs, ld, st, addi]
  refine hc.wp_arg hg (sg_arg h (j := 18) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
    wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 =>
      wp_addi fun t4 u4 => wp_shr h.lg_range fun t5 u5 _ => wp_addi fun t6 u6 => ?_
  refine ((((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide)
    (by decide))).wp_st hg (by decide) fun t7 c7 u7 => WP.block_nil ?_
  have e2 : t2.gpr .eax = BitVec.ofNat 32 (P.sl + (8 + h.D)) := by
    rw [u2.gpr, u1.gpr]; exact BitVec.ofNat_add_ofNat ..
  have e6 : t6.gpr .eax = BitVec.ofNat 32 (nbS h P) := by
    rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, e2, BitVec.ofNat_add_ofNat]
    show BitVec.ofNat 32 (P.sl + (8 + h.D) + h.L) >>> lgB h.H + _ = _
    rw [e1, BitVec.ofNat_add_ofNat]
  have m7 : t7.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.sl + (8 + h.D)))).writeW
      ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbS h P)) := by
    rw [u7.mem, e6, u6.mem, u5.mem, u4.mem, u3.mem, e2, u2.mem, u1.mem]
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨c7, ⟨hk.keep h fr fun r hr => ?_, ?_, ?_⟩, sbytes_keep fr (fun r hr => ?_) (by pomega) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away3_slot (by decide) (by decide)
  · rw [m7, Lay.readW_fr_other (d := sL) (e := sNb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mp_length]
  · rw [m7, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm

/-- `H = Hash(M')`, at `oDig`. -/
theorem hash_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kh h P σ s.mem ∧ Y2 h P σ s.mem) (ctHash h.H)
      (fun σ s => E0 h P σ s ∧ Dg h P.scr (Mp h P σ) s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hL := h.L_le
  have hB := h.B_le
  have hB0 : 0 < h.B := by have := h.B_ge; omega
  have hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega
  have hK := hi₀.k1024
  have q1 := Nat.lt_mul_div_succ (P.sl + (8 + h.D) + h.L) hB0
  have q2 := Nat.mul_div_le (P.sl + (8 + h.D) + h.L) h.B
  have hT : nbS h P * h.B ≤ 2048 := by
    show ((P.sl + (8 + h.D) + h.L) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega
  refine (ctHash_vp h hg (nbm := nbS h P) hT (Nat.succ_pos _) (msg := Mp h P) (fun σ => by
      rw [Mp_length]; show _ ≤ ((P.sl + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega)
    (Inv := Kh h P) (fun σ m m' hk hf' => ⟨hk.1.keep h hf' (away3_ctW h hg hT), slot_keep hf'
      (ctW_slot h hg hT (by decide) (by decide) (by decide)) hk.2.1,
      slot_keep hf' (ctW_slot h hg hT (by decide) (by decide) (by decide)) hk.2.2⟩)
    (fun σ m hk => hk.2.1) (fun σ m hk => hk.2.2)).mono
    (fun σ s ⟨hc, hk, hy⟩ => ⟨hc, hk, fun i hi => hy i (by omega)⟩) fun σ s ⟨hc, hk, hd⟩ => ⟨⟨hc, hk.1⟩, hd⟩

end VG.Proof.RsaPss.X86.Sg
