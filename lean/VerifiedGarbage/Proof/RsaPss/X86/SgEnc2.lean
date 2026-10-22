module

public import VerifiedGarbage.Proof.RsaPss.X86.SgEnc1
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS signing on x86: `EM`

`EM` cleared (`clr_vp`), then `0x01` and the salt at the end of
`DB = EM[lo..lo + dbLen)` (`one_vp`, `cpS_vp`), `H` after it (`putH_vp`)
and `0xbc` last (`bc_vp`), as on ARMv7.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

theorem add_ofNat_sub {x : BitVec 32} {a b : Nat} (hb : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel hb]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `H`. -/
abbrev Hs (P : EP) (σ : State) : List Byte := h.ok.hH.SH.H.hash (Mp h P σ)

/-- What the rest of the encoding keeps. -/
abbrev Ke (P : EP) (σ : State) (m : Mem) : Prop := Kp h P σ m ∧ Dg h P.scr (Mp h P σ) m

/-- After `H`. -/
abbrev E4 (P : EP) (σ s : State) : Prop := E0 h P σ s ∧ Dg h P.scr (Mp h P σ) s.mem

/-- `EM`'s `k` bytes. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ i < P.K, m (sa P.scr (oEm + i)) = f i

/-- `DB`'s byte `j`: zeros, `0x01`, then the salt. -/
abbrev dbv (P : EP) (σ : State) (j : Nat) : Byte :=
  if j < dbN h P - P.sl - 1 then 0 else if j = dbN h P - P.sl - 1 then 1 else (saltB P σ).getD (j - (dbN h P - P.sl)) 0

/-- `EM` after `0x01`, after the salt, after `H` and after `0xbc`. -/
abbrev emP (P : EP) (i : Nat) : Byte := if i = lo P + dbN h P - P.sl - 1 then 1 else 0
abbrev emA (P : EP) (σ : State) (i : Nat) : Byte :=
  if i < lo P then 0 else if i < lo P + dbN h P then dbv h P σ (i - lo P) else 0
abbrev emB (P : EP) (σ : State) (i : Nat) : Byte :=
  if i < lo P + dbN h P then emA h P σ i else if i < lo P + dbN h P + h.D then (Hs h P σ).getD (i - lo P - dbN h P) 0
    else 0
abbrev emC (P : EP) (σ : State) (i : Nat) : Byte := if i = P.K - 1 then 0xbc else emB h P σ i

theorem Ke.keep {P : EP} {σ : State} {m m' : Mem} {o n : Nat} (hg : Geo (P.lay h.D) P.scr) (hk : Ke h P σ m)
    (hf : Frame [sR P.scr o n] m m') (ho : oEm ≤ o) (hn : o + n ≤ oY) : Ke h P σ m' := by
  have := h.D_le
  have := h.N_le
  exact ⟨hk.1.keep h hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by pomega),
    sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega))
      (by pomega) hk.2⟩

/-- `EM` cleared. -/
theorem clr_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E4 h P) (.seq (.block clrEm) zeroLoop)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  refine VP.seq (G := fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 oEm ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] clrEm_taint (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hk⟩, hd⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by pomega) (by omega)) (by omega) (Inv := Ke h P)
      fun σ m m' hk hf => hk.keep h hg (by rwa [hg.scrA (by pomega)] at hf) (Nat.le_refl _) (by pomega)).mono
      (fun _ _ h => h) fun σ s ⟨hc, hk, hz⟩ => ⟨hc, hk, fun i hi => by rw [← hg.byteAt_scr (by pomega)]; exact hz i hi⟩)
  simp only [clrEm, atS, ld, mi, addi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_arg hg
    (sg_arg h (j := 3) (by decide)) (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
  refine ⟨c3.upd u4 (by decide) (by decide), by rw [u4.mem, u3.mem, u2.mem, u1.mem]; exact ⟨hk, hd⟩, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr]; rfl

/-- The bounds of the encoding when everything fits. -/
theorem fit_bounds {P : EP} {σ : State} {m : Mem} (hk : Kp h P σ m) :
    lo P ≤ 1 ∧ P.sl + 1 ≤ dbN h P ∧ lo P + dbN h P + h.D + 1 = P.K ∧ P.K ≤ 1024 ∧ h.D ≤ 64 ∧ 0 < h.D := by
  have := hk.2.1.2
  have := hk.1.k1024
  have := h.D_le
  have := h.N_le
  have := h.D_pos
  have : lo P ≤ 1 := by unfold lo; split <;> omega
  refine ⟨this, ?_, ?_, hk.1.k1024, by omega, h.D_pos⟩ <;> unfold dbN <;> omega

/-- `0x01` before the salt's place at the end of `DB`. -/
theorem one_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0)
      (.seq (.block oneSet) (.block put1))
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emP h P)) ∧
        s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl) ∧ s.gpr .esi = P.salt ∧
        s.gpr .ecx = BitVec.ofNat 32 P.sl ∧ s.zf = some (decide (P.sl = 0))) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; omega
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1))
    (VP.taint [.esp, .ebp] oneSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ put1_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, bx⟩ => ?_)
  · simp only [oneSet, atDb, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp]) (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
    have c3 : Ctx (P.lay h.D) P.scr σ t3 := c2.upd u3 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp]) (by rw [hg.aFr ok sDb (by decide)]; exact c3.rFr hg sDb (by decide)) fun t4 u4 => ?_
    have c4 : Ctx (P.lay h.D) P.scr σ t4 := c3.upd u4 (by decide) (by decide)
    refine wp_subm (B := (P.lay h.D).B) (by rw [c4.st.sp]) (by rw [hg.aArg ok 18 (by simp)]; exact
      (by rw [c4.st.rd, c4.st.wr]; exact c4.st.ok.arg_read (sg_arg h (by decide)))) fun t5 u5 => ?_
    refine wp_subi fun t6 u6 _ _ => WP.block_nil ?_
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨((c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)), m6 ▸ hk, m6 ▸ he⟩, ?_⟩
    have a18 : t4.mem.readW (addr (P.lay h.D).B (Impl.RsaPkcs1Sig.X86.argOff frameBytes 18)) 32 =
        BitVec.ofNat 32 P.sl := by
      rw [hg.aArg ok 18 (by simp), u4.mem, u3.mem, u2.mem, u1.mem, hc.st.arg (sg_arg h (by decide))]; rfl
    rw [u6.gpr, u5.gpr, a18, u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.mem, u2.mem, u1.mem, hc.ebp,
      hg.aFr ok sLo (by decide), hg.aFr ok sDb (by decide), hk.1.2.2.2.1, hk.1.2.2.2.2, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, ← Nat.add_assoc,
      add_ofNat_sub (by omega), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_sub (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1)) 0 =
        sa P.scr (oEm + lo P + dbN h P - P.sl - 1) := by rw [hg.addrD (by omega), Nat.add_zero]
    have wd : InRegions s.wr (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) 1 := hg.wr hc.st (by omega)
    simp only [put1, mi, ld, addi, Impl.RsaPkcs1Sig.X86.at_]
    refine wp_movi fun t1 u1 => wp_store8 (a := sa P.scr (oEm + lo P + dbN h P - P.sl - 1))
      (by rw [ea_at, u1.other _ (by decide), bx]; exact ad) (by rw [u1.wr]; exact wd) fun t2 u2 => ?_
    have m2 : t2.mem = s.mem.writeW (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) (1 : Byte) := by
      rw [u2.mem, Reg8.reg, u1.gpr, u1.mem]; rfl
    have fr : Frame [sR P.scr (oEm + lo P + dbN h P - P.sl - 1) 1] s.mem t2.mem := by
      rw [m2]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    have c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).write
      (by rw [u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega))
      u2.rd u2.wr (by rw [u2.gpr]) (by rw [u2.gpr])
    refine wp_addi fun t3 u3 => ?_
    have c3 : Ctx (P.lay h.D) P.scr σ t3 := c2.upd u3 (by decide) (by decide)
    refine c3.wp_arg hg (sg_arg h (j := 17) (by decide)) (by decide) (by decide) fun t4 c4 u4 =>
      c4.wp_arg hg (sg_arg h (j := 18) (by decide)) (by decide) (by decide) fun t5 c5 u5 =>
        wp_test fun t6 u6 z6 => WP.block_nil ?_
    have m6 : t6.mem = t2.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem]
    refine ⟨⟨c5.fupd u6, ?_, fun i hi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [m6]; exact hk.keep h hg fr (by omega) (by omega)
    · rw [m6, m2, sa_write P.scr _ _ (by omega) (by omega), he i hi]
      by_cases e : i = lo P + dbN h P - P.sl - 1
      · rw [ite_eq_left (by omega)]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega)]; exact (ite_eq_right e).symm
    · rw [u6.gpr]
      simp (disch := decide) only [u5.other, u4.other, u3.gpr, u2.gpr, u1.other, bx]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show oEm + lo P + dbN h P - P.sl - 1 + 1 =
        oEm + lo P + dbN h P - P.sl by omega]
    · rw [u6.gpr]; simp (disch := decide) only [u5.other, u4.gpr]; rfl
    · rw [u6.gpr, u5.gpr]; rfl
    · rw [z6, u5.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hi₀.sl32)

/-- `EM` after the salt, from `EM` after `0x01`. -/
theorem emA_eq {P : EP} {σ : State} (hlo : lo P ≤ 1) (hdb : P.sl + 1 ≤ dbN h P) (i : Nat) :
    emA h P σ i = if lo P + dbN h P - P.sl ≤ i ∧ i < lo P + dbN h P then
      (saltB P σ).getD (i - (lo P + dbN h P - P.sl)) 0 else emP h P i := by
  unfold emA dbv emP
  by_cases h1 : i < lo P
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [ite_eq_right h1]
  by_cases h2 : i < lo P + dbN h P
  · rw [ite_eq_left h2]
    by_cases h3 : i - lo P < dbN h P - P.sl - 1
    · rw [ite_eq_left h3, ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [ite_eq_right h3]
    by_cases h4 : i - lo P = dbN h P - P.sl - 1
    · rw [ite_eq_left h4, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right h4, ite_eq_left (by omega), show i - lo P - (dbN h P - P.sl) = i - (lo P + dbN h P - P.sl) by omega]
  · rw [ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The salt at the end of `DB`. -/
theorem cpS_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emP h P)) ∧
        s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl) ∧ s.gpr .esi = P.salt ∧
        s.gpr .ecx = BitVec.ofNat 32 P.sl ∧ s.zf = some (decide (P.sl = 0)))
      (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
    (VP.block_nil fun σ s ⟨⟨⟨hc, hk, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_
  · have h0 : P.sl = 0 := by simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [he i hi, emA_eq h hlo hdb, ite_eq_right (by omega)]
  by_cases h0 : P.sl = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
  refine (copy_vp (hg.wbuf (o := oEm + lo P + dbN h P - P.sl) (n := P.sl) (by omega) (by omega))
    (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.scrA (by omega)]; exact (hg.ro ok (by omega) (R := P.SALT) (by simp)).symm)
    (by omega) (f := fun σ i => (saltB P σ).getD i 0)
    (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P - P.sl ∨ lo P + dbN h P ≤ i) →
      m (sa P.scr (oEm + i)) = emP h P i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨hc, hk, he⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, bx, si, cx,
      fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
  · rw [hg.scrA (by omega)] at hf'
    refine ⟨hk.keep h hg hf' (by omega) (by omega), fun i hi hr => ?_⟩
    rw [← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _)
  · rw [emA_eq h hlo hdb]
    by_cases hr : lo P + dbN h P - P.sl ≤ i ∧ i < lo P + dbN h P
    · rw [ite_eq_left hr, ← hs (i - (lo P + dbN h P - P.sl)) (by omega), hg.byteAt_scr (by omega),
        show oEm + lo P + dbN h P - P.sl + (i - (lo P + dbN h P - P.sl)) = oEm + i by omega]
    · rw [ite_eq_right hr]; exact ho i hi (by omega)

/-- `H` after `DB`. -/
theorem putH_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ))
      (.seq (.block (putH h.H)) Impl.Bignum.X86.copyBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hD0 := h.D_pos
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have e4 : oDig = 832 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ)) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .ecx = BitVec.ofNat 32 h.D)
    (VP.taint [.esp, .ebp] h.certs.putH (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + lo P + dbN h P) (n := h.D) (by omega) hD0)
      (hg.rbuf (o := oDig) (n := h.D) (by omega) hD0)
      (by rw [hg.scrA (by omega), hg.scrA (by omega)]; exact Geo.sep (by omega) (by omega) (by omega)) hD0
      (f := fun σ i => (Hs h P σ).getD i 0)
      (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P ∨ lo P + dbN h P + h.D ≤ i) →
        m (sa P.scr (oEm + i)) = emA h P σ i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hk, he⟩, bx, si, cx⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, bx, si, cx, fun i hi => by
        rw [hg.byteAt_scr (by omega)]; exact hk.2 i hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩)
  · simp only [putH, atDb, atS, addSlot, addi, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
    have c4 : Ctx (P.lay h.D) P.scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide)
      (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c4.st.sp]) (by rw [hg.aFr ok sLo (by decide)]; exact c4.rFr hg sLo (by decide)) fun t5 u5 => ?_
    have c5 : Ctx (P.lay h.D) P.scr σ t5 := c4.upd u5 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c5.st.sp]) (by rw [hg.aFr ok sDb (by decide)]; exact c5.rFr hg sDb (by decide)) fun t6 u6 => wp_movi fun t7 u7 => WP.block_nil ?_
    have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide), m7 ▸ hk, m7 ▸ he⟩, ?_, ?_, ?_⟩
    · rw [u7.other _ (by decide), u6.gpr, u5.gpr, u4.gpr, u3.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem,
        u2.other _ (by decide), u1.other _ (by decide), hc.ebp, hg.aFr ok sLo (by decide), hg.aFr ok sDb (by decide),
        hk.1.2.2.2.1, hk.1.2.2.2.2, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
        ← Nat.add_assoc]
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u7.gpr]
  · rw [hg.scrA (by omega)] at hf'
    refine ⟨hk.keep h hg hf' (by omega) (by omega), fun i hi hr => ?_⟩
    rw [← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _)
  · unfold emB
    by_cases h1 : i < lo P + dbN h P
    · rw [ite_eq_left h1]; exact ho i hi (.inl h1)
    rw [ite_eq_right h1]
    by_cases h2 : i < lo P + dbN h P + h.D
    · rw [ite_eq_left h2, ← hs (i - lo P - dbN h P) (by omega), hg.byteAt_scr (by omega),
        show oEm + lo P + dbN h P + (i - lo P - dbN h P) = oEm + i by omega]
    · rw [ite_eq_right h2, ho i hi (.inr (by omega))]
      unfold emA
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- `0xbc` last. -/
theorem bc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ))
      (.seq (.block bcSet) (.block putBc))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + P.K - 1))
    (VP.taint [.esp, .ebp] bcSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ putBc_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, si⟩ => ?_)
  · simp only [bcSet, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp]) (by rw [hg.aArg ok 3 (by simp)]; exact
      (by rw [c2.st.rd, c2.st.wr]; exact c2.st.ok.arg_read (sg_arg h (by decide)))) fun t3 u3 => ?_
    refine wp_subi fun t4 u4 _ _ => WP.block_nil ?_
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨(c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide), m4 ▸ hk, m4 ▸ he⟩, ?_⟩
    rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aArg ok 3 (by simp),
      hc.st.arg (sg_arg h (by decide)), show (P.lay h.D).argv.getD 3 0 = BitVec.ofNat 32 P.K from rfl,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      add_ofNat_sub (by omega)]
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) 0 = sa P.scr (oEm + P.K - 1) := by
      rw [hg.addrD (by omega), Nat.add_zero]
    have wd : InRegions s.wr (sa P.scr (oEm + P.K - 1)) 1 := hg.wr hc.st (by omega)
    simp only [putBc, mi, Impl.RsaPkcs1Sig.X86.at_]
    refine wp_movi fun t1 u1 => wp_store8 (a := sa P.scr (oEm + P.K - 1))
      (by rw [ea_at, u1.other _ (by decide), si]; exact ad) (by rw [u1.wr]; exact wd) fun t2 u2 => WP.block_nil ?_
    have m2 : t2.mem = s.mem.writeW (sa P.scr (oEm + P.K - 1)) (0xbc : Byte) := by
      rw [u2.mem, Reg8.reg, u1.gpr, u1.mem]; rfl
    have fr : Frame [sR P.scr (oEm + P.K - 1) 1] s.mem t2.mem := by
      rw [m2]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    refine ⟨(hc.upd u1 (by decide) (by decide)).write (by rw [u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)) u2.rd u2.wr (by rw [u2.gpr])
        (by rw [u2.gpr]), hk.keep h hg fr (by omega) (by omega), fun i hi => ?_⟩
    rw [m2, sa_write P.scr _ _ (by omega) (by omega), he i hi]
    by_cases e : i = P.K - 1
    · rw [ite_eq_left (by omega)]; exact (ite_eq_left e).symm
    · rw [ite_eq_right (by omega)]; exact (ite_eq_right e).symm

end VG.Proof.RsaPss.X86.Sg
