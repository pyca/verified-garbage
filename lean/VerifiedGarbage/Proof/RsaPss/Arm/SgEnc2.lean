module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc1
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc1
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS signing on ARMv7: `DB ‖ H ‖ 0xbc` in `EM`

`EM` (`k` bytes at `oEm`) cleared (`clr_vp`), `0x01` and the salt at the end
of `DB = EM[lo..lo + dbLen)` (`one_vp`, `cpS_vp`), `H` after it (`putH_vp`)
and `0xbc` last (`bc_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

theorem add_ofNat_sub {x : BitVec 32} {a b : Nat} (hb : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  have : BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel hb]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem add_ofNat_sub_one {x : BitVec 32} {a : Nat} (ha : 1 ≤ a) :
    x + BitVec.ofNat 32 a - 1 = x + BitVec.ofNat 32 (a - 1) := add_ofNat_sub ha

/-- `H`. -/
abbrev Hs (P : EP) (σ : State) : List Byte := h.ok.SH.H.hash (Mp h P σ)

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
    VP (E4 h P) (.seq (.block clrEm) Impl.Bignum.Arm.maskBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  refine VP.seq (G := fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 P.K)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hk⟩, hd⟩ => ?_)
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by pomega) (by omega)) (by omega) (Inv := Ke h P)
      fun σ m m' hk hf => hk.keep h hg (by rwa [hg.addr (by pomega)] at hf) (Nat.le_refl _) (by pomega)).mono
      (fun _ _ h => h) fun σ s ⟨hc, hk, hz⟩ => ⟨hc, hk, fun i hi => by rw [← hg.byteAt_scr (by pomega)]; exact hz i hi⟩)
  obtain ⟨a3, r3, v3⟩ := argAt hk.1 hc.st (j := 3) (by decide)
  have hw : WP isa (.block clrEm) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 P.K := by
    prun [clrEm, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a3, r3, v3, arg_lt,
      movw_val (show oEm < 2 ^ 16 by decide)]
    rfl
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ => ⟨hc.regs rd wr sp m, m ▸ ⟨hk, hd⟩, r0, r2, lr⟩

theorem put1_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .lr])
    (.block put1) hc).isSome = true := ⟨_, by taint_decide⟩

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
      (.seq (.block saltPos) (.block put1))
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emP h P)) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl) ∧ s.gpr .r1 = P.salt ∧
        s.gpr .lr = BitVec.ofNat 32 P.sl ∧ s.z = decide (P.sl = 0)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
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
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1) ∧ s.gpr .r1 = P.salt ∧
      s.gpr .lr = BitVec.ofNat 32 P.sl)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ put1_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, r0, r1, lr⟩ => ?_)
  · obtain ⟨a17, r17, v17⟩ := argAt hk.1.1 hc.st (j := 17) (by decide)
    obtain ⟨a18, r18, v18⟩ := argAt hk.1.1 hc.st (j := 18) (by decide)
    replace v18 : s.mem.readW ((P.lay h.D).fr (arg 18)) 32 = BitVec.ofNat 32 P.sl := v18
    have hw : WP isa (.block saltPos) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1) ∧ t.gpr .r1 = P.salt ∧
        t.gpr .lr = BitVec.ofNat 32 P.sl := by
      prun [saltPos, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a17, r17, v17, a18,
        r18, v18, arg_lt, hk.1.2.2.2.1, hk.1.2.2.2.2, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, add_ofNat_sub (x := P.scr) (a := oEm + lo P + dbN h P) (b := P.sl) (by omega),
        add_ofNat_sub_one (x := P.scr) (a := oEm + lo P + dbN h P - P.sl) (by omega)]
      rfl
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ he⟩, r0, r1, lr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1)) =
        sa P.scr (oEm + lo P + dbN h P - P.sl - 1) := hg.addr (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) 1 := hg.wr hc.st (by omega)
    have hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
    have hw : WP isa (.block put1) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) (1 : Byte) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1 + 1) ∧
        t.gpr .r1 = P.salt ∧ t.gpr .lr = BitVec.ofNat 32 P.sl ∧ t.z = decide (P.sl = 0) := by
      prun [put1, mw, r0, r1, lr, ad, wd, movw_val (show 1 < 2 ^ 16 by decide), dpVal, hz0,
        VG.Proof.X25519.Arm.ofNat_beq_zero hk.1.1.sl32, BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, tl, z⟩ => ?_
    have fr : Frame [sR P.scr (oEm + lo P + dbN h P - P.sl - 1) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h hg fr (by omega) (by omega),
      fun i hi => ?_⟩, by rw [t0, show oEm + lo P + dbN h P - P.sl - 1 + 1 = oEm + lo P + dbN h P - P.sl by omega],
      t1, tl, z⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)
    · obtain ⟨σ', ok⟩ := hg.ok
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega) (by rw [hg.F]; decide)
    · rw [m, sa_write P.scr _ _ (by omega) (by omega), he i hi]
      by_cases e : i = lo P + dbN h P - P.sl - 1
      · rw [ite_eq_left (by omega)]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega)]; exact (ite_eq_right e).symm

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
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl) ∧ s.gpr .r1 = P.salt ∧
        s.gpr .lr = BitVec.ofNat 32 P.sl ∧ s.z = decide (P.sl = 0))
      (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
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
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun σ s ⟨⟨⟨hc, hk, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_
  · have h0 : P.sl = 0 := by rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [he i hi, emA_eq h hlo hdb, ite_eq_right (by omega)]
  by_cases h0 : P.sl = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
  refine (copy_vp (hg.wbuf (o := oEm + lo P + dbN h P - P.sl) (n := P.sl) (by omega) (by omega))
    (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.addr (by omega)]; exact (hg.ro ok (by omega) (R := P.SALT) (by simp)).symm)
    (by omega) (f := fun σ i => (saltB P σ).getD i 0)
    (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P - P.sl ∨ lo P + dbN h P ≤ i) →
      m (sa P.scr (oEm + i)) = emP h P i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨hc, hk, he⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, r0, r1, lr,
      fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
  · rw [hg.addr (by omega)] at hf'
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
      (.seq (.block (putH h.H)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
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
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .lr = BitVec.ofNat 32 h.D)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + lo P + dbN h P) (n := h.D) (by omega) hD0)
      (hg.rbuf (o := oDig) (n := h.D) (by omega) hD0)
      (by rw [hg.addr (by omega), hg.addr (by omega)]; exact Geo.sep (by omega) (by omega) (by omega)) hD0
      (f := fun σ i => (Hs h P σ).getD i 0)
      (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P ∨ lo P + dbN h P + h.D ≤ i) →
        m (sa P.scr (oEm + i)) = emA h P σ i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hk, he⟩, r0, r1, lr⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, r0, r1, lr, fun i hi => by
        rw [hg.byteAt_scr (by omega)]; exact hk.2 i hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩)
  · have hw : WP isa (.block (putH h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
        t.gpr .lr = BitVec.ofNat 32 h.D := by
      prun [putH, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.2.1,
        hk.1.2.2.2.2, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide),
        movw_val (show dig h.H < 2 ^ 16 by show h.D < 2 ^ 16; omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ he⟩, r0, r1, lr⟩
  · rw [hg.addr (by omega)] at hf'
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

theorem bcPut_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0])
    (.block bcPut) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `0xbc` last. -/
theorem bc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ))
      (.seq (.block bcSet) (.block bcPut))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hK0 := hi₀.k64
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + P.K - 1))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ bcPut_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, r0⟩ => ?_)
  · obtain ⟨a3, r3, v3⟩ := argAt hk.1.1 hc.st (j := 3) (by decide)
    replace v3 : s.mem.readW ((P.lay h.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
    have hw : WP isa (.block bcSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) := by
      prun [bcSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a3, r3, v3, arg_lt,
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        add_ofNat_sub_one (x := P.scr) (a := oEm + P.K) (by omega)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ he⟩, r0⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) = sa P.scr (oEm + P.K - 1) := hg.addr (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + P.K - 1)) 1 := hg.wr hc.st (by omega)
    have hw : WP isa (.block bcPut) s fun t => t.mem = s.mem.writeW (sa P.scr (oEm + P.K - 1)) (0xbc : Byte) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [bcPut, mw, r0, ad, wd, movw_val (show 0xbc < 2 ^ 16 by decide)]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [sR P.scr (oEm + P.K - 1) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    obtain ⟨σ', ok⟩ := hg.ok
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h hg fr (by omega) (by omega),
      fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega) (by rw [hg.F]; decide)
    · rw [m, sa_write P.scr _ _ (by omega) (by omega), he i hi]
      by_cases e : i = P.K - 1
      · rw [ite_eq_left (by omega)]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega)]; exact (ite_eq_right e).symm

end VG.Proof.RsaPss.Arm.Sg
