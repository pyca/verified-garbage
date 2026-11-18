module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.PrivCall
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Rsa.Arm.PrivVerified
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.MgfBytes
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.EncBytes
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc1
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc1
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common

/-! ### `RsaPss.Arm.SgEnc3`, which only this module used -/

section

/-! ### `RsaPss.Arm.SgEnc2`, which only this module used -/

section

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
    (hf : Frame [sR P.scr o n] m m') (hn : o + n ≤ oY) : Ke h P σ m' := by
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
    ((zero_vp (hg.wbuf (o := oEm) (n := P.K) (by pomega) (by omega_arith)) (by omega_arith) (Inv := Ke h P)
      fun σ m m' hk hf => hk.keep h hg (by rwa [hg.addr (by pomega)] at hf) (by pomega)).mono
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
  have hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega_arith
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; omega_arith
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem fun _ => 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1) ∧ s.gpr .r1 = P.salt ∧
      s.gpr .lr = BitVec.ofNat 32 P.sl)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_)
    (VP.taint _ put1_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, he⟩, r0, r1, lr⟩ => ?_)
  · obtain ⟨a17, r17, v17⟩ := argAt hk.1.1 hc.st (j := 18) (by decide)
    obtain ⟨a18, r18, v18⟩ := argAt hk.1.1 hc.st (j := 19) (by decide)
    replace v18 : s.mem.readW ((P.lay h.D).fr (arg 19)) 32 = BitVec.ofNat 32 P.sl := v18
    have hw : WP isa (.block saltPos) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1) ∧ t.gpr .r1 = P.salt ∧
        t.gpr .lr = BitVec.ofNat 32 P.sl := by
      prun [saltPos, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a17, r17, v17, a18,
        r18, v18, arg_lt, hk.1.2.2.2.1, hk.1.2.2.2.2, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, add_ofNat_sub (x := P.scr) (a := oEm + lo P + dbN h P) (b := P.sl) (by omega_arith),
        add_ofNat_sub_one (x := P.scr) (a := oEm + lo P + dbN h P - P.sl) (by omega_arith)]
      rfl
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ he⟩, r0, r1, lr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.sl - 1)) =
        sa P.scr (oEm + lo P + dbN h P - P.sl - 1) := hg.addr (by omega_arith)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P + dbN h P - P.sl - 1)) 1 := hg.wr hc.st (by omega_arith)
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
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_arith) (by omega_arith)
    refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h hg fr (by omega_arith),
      fun i hi => ?_⟩, by rw [t0, show oEm + lo P + dbN h P - P.sl - 1 + 1 = oEm + lo P + dbN h P - P.sl by omega_arith],
      t1, tl, z⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith)
    · obtain ⟨σ', ok⟩ := hg.ok
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith) (by rw [hg.F]; decide)
    · rw [m, sa_write P.scr _ _ (by omega_arith) (by omega_arith), he i hi]
      by_cases e : i = lo P + dbN h P - P.sl - 1
      · rw [ite_eq_left (by omega_arith)]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega_arith)]; exact (ite_eq_right e).symm

/-- `EM` after the salt, from `EM` after `0x01`. -/
theorem emA_eq {P : EP} {σ : State} (hlo : lo P ≤ 1) (hdb : P.sl + 1 ≤ dbN h P) (i : Nat) :
    emA h P σ i = if lo P + dbN h P - P.sl ≤ i ∧ i < lo P + dbN h P then
      (saltB P σ).getD (i - (lo P + dbN h P - P.sl)) 0 else emP h P i := by
  unfold emA dbv emP
  by_cases h1 : i < lo P
  · rw [ite_eq_left h1, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  rw [ite_eq_right h1]
  by_cases h2 : i < lo P + dbN h P
  · rw [ite_eq_left h2]
    by_cases h3 : i - lo P < dbN h P - P.sl - 1
    · rw [ite_eq_left h3, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
    rw [ite_eq_right h3]
    by_cases h4 : i - lo P = dbN h P - P.sl - 1
    · rw [ite_eq_left h4, ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h4, ite_eq_left (by omega_arith), show i - lo P - (dbN h P - P.sl) = i - (lo P + dbN h P - P.sl) by omega_arith]
  · rw [ite_eq_right h2, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

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
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_arith
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_arith
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have fit := hg.fit
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun σ s ⟨⟨⟨hc, hk, he⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_
  · have h0 : P.sl = 0 := by rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [he i hi, emA_eq h hlo hdb, ite_eq_right (by omega_arith)]
  by_cases h0 : P.sl = 0
  · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
      rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
  refine (copy_vp (hg.wbuf (o := oEm + lo P + dbN h P - P.sl) (n := P.sl) (by omega_arith) (by omega_arith))
    (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.addr (by omega_arith)]; exact (hg.ro ok (by omega_arith) (R := P.SALT) (by simp)).symm)
    (by omega_arith) (f := fun σ i => (saltB P σ).getD i 0)
    (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P - P.sl ∨ lo P + dbN h P ≤ i) →
      m (sa P.scr (oEm + i)) = emP h P i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
    (fun σ s ⟨⟨⟨hc, hk, he⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, r0, r1, lr,
      fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
  · rw [hg.addr (by omega_arith)] at hf'
    refine ⟨hk.keep h hg hf' (by omega_arith), fun i hi hr => ?_⟩
    rw [← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _)
  · rw [emA_eq h hlo hdb]
    by_cases hr : lo P + dbN h P - P.sl ≤ i ∧ i < lo P + dbN h P
    · rw [ite_eq_left hr, ← hs (i - (lo P + dbN h P - P.sl)) (by omega_arith), hg.byteAt_scr (by omega_arith),
        show oEm + lo P + dbN h P - P.sl + (i - (lo P + dbN h P - P.sl)) = oEm + i by omega_arith]
    · rw [ite_eq_right hr]; exact ho i hi (by omega_arith)

/-- `H` after `DB`. -/
theorem putH_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ))
      (.seq (.block (putH h.sh)) Impl.Bignum.Arm.copyBytes)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emB h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_arith
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_arith
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hD0 := h.D_pos
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have e4 : oDig = 4928 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emA h P σ)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
      s.gpr .lr = BitVec.ofNat 32 h.D)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oEm + lo P + dbN h P) (n := h.D) (by omega_arith) hD0)
      (hg.rbuf (o := oDig) (n := h.D) (by omega_arith) hD0)
      (by rw [hg.addr (by omega_arith), hg.addr (by omega_arith)]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) hD0
      (f := fun σ i => (Hs h P σ).getD i 0)
      (Inv := fun σ m => Ke h P σ m ∧ ∀ i < P.K, (i < lo P + dbN h P ∨ lo P + dbN h P + h.D ≤ i) →
        m (sa P.scr (oEm + i)) = emA h P σ i) fun σ m m' ⟨hk, ho⟩ hf' => ?_).mono
      (fun σ s ⟨⟨hc, hk, he⟩, r0, r1, lr⟩ => ⟨hc, ⟨hk, fun i hi _ => he i hi⟩, r0, r1, lr, fun i hi => by
        rw [hg.byteAt_scr (by omega_arith)]; exact hk.2 i hi⟩) fun σ s ⟨hc, ⟨hk, ho⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩)
  · have hw : WP isa (.block (putH h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 oDig ∧
        t.gpr .lr = BitVec.ofNat 32 h.D := by
      prun [putH, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.2.1,
        hk.1.2.2.2.2, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide),
        movw_val (show dig h.sh < 2 ^ 16 by show h.D < 2 ^ 16; omega_arith), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ he⟩, r0, r1, lr⟩
  · rw [hg.addr (by omega_arith)] at hf'
    refine ⟨hk.keep h hg hf' (by omega_arith), fun i hi hr => ?_⟩
    rw [← ho i hi hr]
    exact hf' _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _)
  · unfold emB
    by_cases h1 : i < lo P + dbN h P
    · rw [ite_eq_left h1]; exact ho i hi (.inl h1)
    rw [ite_eq_right h1]
    by_cases h2 : i < lo P + dbN h P + h.D
    · rw [ite_eq_left h2, ← hs (i - lo P - dbN h P) (by omega_arith), hg.byteAt_scr (by omega_arith),
        show oEm + lo P + dbN h P + (i - lo P - dbN h P) = oEm + i by omega_arith]
    · rw [ite_eq_right h2, ho i hi (.inr (by omega_arith))]
      unfold emA
      rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

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
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
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
        add_ofNat_sub_one (x := P.scr) (a := oEm + P.K) (by omega_arith)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ he⟩, r0⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) = sa P.scr (oEm + P.K - 1) := hg.addr (by omega_arith)
    have wd : InRegions s.wr (sa P.scr (oEm + P.K - 1)) 1 := hg.wr hc.st (by omega_arith)
    have hw : WP isa (.block bcPut) s fun t => t.mem = s.mem.writeW (sa P.scr (oEm + P.K - 1)) (0xbc : Byte) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [bcPut, mw, r0, ad, wd, movw_val (show 0xbc < 2 ^ 16 by decide)]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [sR P.scr (oEm + P.K - 1) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_arith) (by omega_arith)
    obtain ⟨σ', ok⟩ := hg.ok
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h hg fr (by omega_arith),
      fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith) (by rw [hg.F]; decide)
    · rw [m, sa_write P.scr _ _ (by omega_arith) (by omega_arith), he i hi]
      by_cases e : i = P.K - 1
      · rw [ite_eq_left (by omega_arith)]; exact (ite_eq_left e).symm
      · rw [ite_eq_right (by omega_arith)]; exact (ite_eq_right e).symm

end VG.Proof.RsaPss.Arm.Sg

end

end

/-!
# RSASSA-PSS signing on ARMv7: `maskedDB`, and `EM`

`DB ⊕= MGF1(H, dbLen)` (`mask_vp`), `maskedDB`'s first byte ANDed with the
mask `c` (`top_vp`): `EM` is `emT` of the specification's encoding
(`EncBytes.lean`), and so is the whole encoding (`enc_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- `EM`'s bytes outside `DB` and `H`: the leading zero and `0xbc`. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ (∀ i < lo P, m (sa P.scr (oEm + i)) = 0) ∧ m (sa P.scr (oEm + (P.K - 1))) = 0xbc

/-- The mask, by MGF1 with `G`. -/
abbrev mkS (G : Spec.Mgf1.Hash) (P : EP) (σ : State) : List Byte := Spec.Mgf1.mgf1 G (Hs h P σ) (dbN h P)

theorem Hs_length (P : EP) (σ : State) : (Hs h P σ).length = h.D := by
  rw [Hs, ← h.hash]; have := (PssHash.valid h).2 (Mp h P σ); rw [this, h.glen]

/-- MGF1's slots: its source `H` and its destination `DB`. -/
theorem slots_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) (.block (mgfSlots h.sh))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ (Ke h P σ s.mem ∧
        RsaOaep.Arm.Sl (P.lay h.D) P.scr (oEm + lo P + dbN h P) h.D (oEm + lo P) (dbN h P) s.mem) ∧
        EMv P s.mem (emC h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_
  let L := P.lay h.D
  have hw : WP isa (.block (mgfSlots h.sh)) s fun t =>
      t.mem = (((s.mem.writeW (L.fr Impl.RsaOaep.Arm.sDst) (P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 (lo P))).writeW
        (L.fr Impl.RsaOaep.Arm.sDstLen) (BitVec.ofNat 32 (dbN h P))).writeW (L.fr Impl.RsaOaep.Arm.sSrc)
          (P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 (lo P) + BitVec.ofNat 32 (dbN h P))).writeW
        (L.fr Impl.RsaOaep.Arm.sSrcLen) (BitVec.ofNat 32 h.D) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [mgfSlots, atDb, atS, addSlot, sp0, ld, mw, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS,
      hk.1.2.2.2.1, hk.1.2.2.2.2, movw_val (show oEm < 2 ^ 16 by decide),
      movw_val (show dig h.sh < 2 ^ 16 by show h.D < 2 ^ 16; omega_arith), Impl.RsaOaep.Arm.sSrc,
      Impl.RsaOaep.Arm.sSrcLen, Impl.RsaOaep.Arm.sDst, Impl.RsaOaep.Arm.sDstLen]
    rfl
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR L Impl.RsaOaep.Arm.sDst, slotR L Impl.RsaOaep.Arm.sDstLen, slotR L Impl.RsaOaep.Arm.sSrc,
      slotR L Impl.RsaOaep.Arm.sSrcLen] s.mem t.mem := by
    rw [m]
    exact ((((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))).trans ((slot_frame _ _ _ _).mono (by simp))
  have dS : ∀ r ∈ [slotR L Impl.RsaOaep.Arm.sDst, slotR L Impl.RsaOaep.Arm.sDstLen, slotR L Impl.RsaOaep.Arm.sSrc,
      slotR L Impl.RsaOaep.Arm.sSrcLen], ∀ o n, o + n ≤ oRsa → (sR P.scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have hem : EMv P t.mem (emC h P σ) := fun i hi => by
    rw [← he i hi]
    exact fr _ fun r hr => dS r hr (oEm + i) 1 (by have := hi₀.k1024; pomega) _ (Region.contains_self _ _)
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hk.1.keep h fr fun r hr => ?_,
    sbytes_keep fr (fun r hr => dS r hr _ _ (by pomega)) (by pomega) hk.2⟩, ?_, ?_, ?_, ?_⟩, hem⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact away3_slot (by decide) (by decide)
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]

/-- `maskedDB`, before its first byte's top bits are cleared, by MGF1 with
the hash function `g` of the table `mgf1`. -/
theorem mask_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) ∧ s.syms = σ.syms)
      (mgfPart fg h.sh 23)
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h g.G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧ s.syms = σ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_arith
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_arith
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have e1 : oEm = 0 := rfl
  have e2 : Impl.RsaOaep.Arm.oBuf = 1024 := rfl
  have fit := hg.fit
  have fd : oEm + lo P + dbN h P ≤ Impl.RsaOaep.Arm.oBuf := by omega_arith
  -- What MGF1 writes misses the parameters and the bytes of `EM` outside `DB`.
  have away : ∀ r ∈ RsaOaep.Arm.mgfW g (P.lay h.D) P.scr (oEm + lo P) (dbN h P), Away3 (P.lay h.D) r :=
    fun r hr => ⟨RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
      RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
      RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr⟩
  have mp := RsaOaep.Arm.mpOf g hg (so := oEm + lo P + dbN h P) (sl := h.D) (dOff := oEm + lo P) (dl := dbN h P)
    h.D_pos (by omega_arith) (by omega_arith) fd (.inr (Nat.le_refl _)) (seed := Hs h P) (Hs_length h P)
    (X := Ko h P) (fun σ m m' ⟨hk, h0, hbc⟩ hf' => ⟨hk.keep h hf' away, fun i hi => by
      rw [← h0 i hi]
      exact hf' _ fun r hr => RsaOaep.Arm.mgfW_byte g hg fd (o := oEm + i) (by omega_arith) (by omega_arith) r hr _
        (Region.contains_self _ _), by
      rw [← hbc]
      exact hf' _ fun r hr => RsaOaep.Arm.mgfW_byte g hg fd (o := oEm + (P.K - 1)) (by omega_arith) (by omega_arith) r
        hr _ (Region.contains_self _ _)⟩)
    (j := 23) (by simp) hi₀.tbl (fun σ m hk => Q.t σ hk.1.1.tabT) Q.gne
  refine (VP.syms (slots_vp h P ⟨σ₀, hi₀⟩)).seq ((RsaOaep.Arm.mgf_vp g mp (arg_lt (by decide))
    (dstv := dbv h P)).mono (fun σ s ⟨⟨hc, ⟨hk, hs⟩, he⟩, sy⟩ => ⟨⟨hc, ⟨⟨hk.1, fun i hi => ?_, ?_⟩, hs⟩, fun i hi => ?_,
      fun i hi => ?_⟩, sy⟩) fun σ s ⟨⟨hc, ⟨hk, _⟩, hd, hh⟩, sy⟩ => ⟨⟨hc, hk, hd, hh⟩, sy⟩)
  · rw [he i (by omega_arith)]
    unfold emC emB emA
    rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), ite_eq_left hi]
  · rw [he _ (by omega_arith)]
    exact ite_eq_left rfl
  · rw [Nat.add_assoc, he _ (by omega_arith)]
    unfold emC emB emA
    rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith),
      Nat.add_sub_cancel_left]
  · rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega_arith)]
    unfold emC emB
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]
    congr 1; omega_arith

/-- `EM`, as the specification encodes it (`RsaPss.emT`). -/
abbrev emF (G : Spec.Mgf1.Hash) (P : EP) (σ : State) (i : Nat) : Byte :=
  RsaPss.emT (lo P) (dbN h P) P.sl (saltB P σ) (Hs h P σ) (mkS h G P σ) ((cW (xB P)).setWidth 8) i

theorem andByte (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 := by
  have e1 : (b.setWidth 32).setWidth 8 = b := by simp
  rw [BitVec.setWidth_and, e1]

theorem topAnd_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0])
    (.block topAnd) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `maskedDB`'s first byte ANDed with the mask: `EM`. -/
theorem top_vp (G : Spec.Mgf1.Hash) (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0)
      (.seq (.block topSet) (.block topAnd))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_arith
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_arith
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r1 = cW (xB P))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ topAnd_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, hd, hh⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block topSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = cW (xB P) := by
      prun [topSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1,
        hk.1.2.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd, m ▸ hh⟩, r0, r1⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega_arith)
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_arith)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega_arith)
    have hw : WP isa (.block topAnd) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P)) (s.mem (sa P.scr (oEm + lo P)) &&& (cW (xB P)).setWidth 8) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [topAnd, r0, r1, ad, rd, wd, dpVal, andByte]
    refine WP.mono hw fun t ⟨m, rd', wr', sp'⟩ => ?_
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_arith) (by omega_arith)
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', hk.1.keep h fr fun r hr => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith) (by rw [hg.F]; decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by omega_arith)
    rw [m, sa_write P.scr _ _ (by omega_arith) (by omega_arith)]
    have hl := Hs_length h P σ
    unfold emF RsaPss.emT
    by_cases h1 : i < lo P
    · rw [ite_eq_right (by omega_arith), ite_eq_left h1]; exact hk.2.1 i h1
    rw [ite_eq_right h1]
    by_cases h2 : i - lo P < dbN h P
    · rw [ite_eq_left h2]
      by_cases h3 : i - lo P = 0
      · rw [ite_eq_left (by omega_arith), ite_eq_left h3, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega_arith), h3]
      · rw [ite_eq_right (by omega_arith), ite_eq_right h3, show oEm + i = oEm + lo P + (i - lo P) by omega_arith, hd _ h2]
    rw [ite_eq_right h2, ite_eq_right (by omega_arith)]
    by_cases h4 : i - lo P < dbN h P + (Hs h P σ).length
    · rw [ite_eq_left h4, show oEm + i = oEm + lo P + dbN h P + (i - lo P - dbN h P) by omega_arith, hh _ (by omega_arith)]
    · rw [ite_eq_right h4, show oEm + i = oEm + (P.K - 1) by omega_arith]; exact hk.2.2

/-- The encoding, when everything fits. -/
theorem enc_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => E0 h P σ s ∧ s.syms = σ.syms) (signEnc f fg h.sh)
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h g.G P σ)) ∧ s.syms = σ.syms) := by
  show VP _ (.seq (yDig h.sh 16) (.seq (.block (cpSalt h.sh)) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (lenSet h.sh 19)) (.seq (ctHash f h.sh 22) (.seq (.block clrEm) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block saltPos) (.seq (.block put1) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (putH h.sh)) (.seq Impl.Bignum.Arm.copyBytes (.seq (.block bcSet) (.seq (.block bcPut)
    (.seq (mgfPart fg h.sh 23) (.seq (.block topSet) (.block topAnd))))))))))))))))) _
  exact (VP.syms (yDig_sg h P hP)).seq (VP.assoc ((VP.syms (salt_vp h P hP)).seq ((VP.syms (lenSet_vp h P)).seq
    ((hash_vp h P Q hP).seq (VP.assoc ((VP.syms (clr_vp h P hP)).seq (VP.assoc ((VP.syms (one_vp h P hP)).seq
    ((VP.syms (cpS_vp h P hP)).seq (VP.assoc ((VP.syms (putH_vp h P hP)).seq (VP.assoc ((VP.syms (bc_vp h P hP)).seq
    ((mask_vp h P Q hP).seq (VP.syms (top_vp h g.G P hP))))))))))))))))

end VG.Proof.RsaPss.Arm.Sg

end

end

/-!
# RSASSA-PSS signing on ARMv7: the call of `vg_rsa_private_checked`

The call's arguments (`pa_vp`): `out`, `n`, `e`, `EM` (at `oEm`) as its
input, the private key, and the rest of `scratch` from `oRsa` on; the call
(`call_vp`), correct and constant time: its arguments and the public key it
reads are the same in two runs, and it writes RSASP1 of `EM`, checked
against `e`, the specification's signature (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

section

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)
open VG.Proof.RsaPss (emT eq_range_map zeros_getD db_getD getD_app ifn zeros_length)

/-- `encodeK`, byte by byte (as in `Proof/RsaPss/EncBytes.lean`), with MGF1's
hash function `G` another than `H`. -/
theorem encodeK_eq₂ (H G : Hash) (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    encodeK H G (n₀ :: rest) mHash salt =
      some ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits)))) := by
  obtain hEL := emLength_eq rest h0
  rw [hb, he] at hEL
  obtain hle : emLen ≤ (n₀ :: rest).length := by rw [hEL, List.length_cons]; split <;> omega_arith
  simp only [encodeK, encode, hb, he, hdb, hlo]
  rw [ifn (by omega_arith)]
  simp only [Option.map_some]
  generalize hgen : H.hash (zeros 8 ++ mHash ++ salt) = h
  obtain hh : h.length = H.len := by rw [← hgen]; exact hH.2 _
  obtain hmk : (mgf1 G h db).length = db := mgf1_length hG _ _
  obtain hdbl : (zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt).length = db := by
    simp only [List.length_append, zeros_length, List.length_cons]; omega_arith
  obtain hX : (clearTop (8 * emLen - emBits) (xorBytes (zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt)
      (mgf1 G h db))).length = db := by
    rw [clearTop_length, xorBytes_length, hdbl, hmk, Nat.min_self]
  refine congrArg some (eq_range_map ?_ fun i hi => ?_)
  · simp only [List.length_append, zeros_length, hX, hh, List.length_cons, List.length_nil]
    simp only [List.length_cons] at hlo hle; omega_arith
  simp only [List.length_cons] at hi hlo hle
  simp only [emT, getD_app, List.length_append, zeros_length, hX, hh]
  obtain hlodb : lo + db + H.len + 1 = rest.length + 1 := by omega_arith
  by_cases h1 : i < lo
  · simp only [h1, ↓reduceIte]; exact zeros_getD _ _
  simp only [h1, ↓reduceIte]
  by_cases h2 : i - lo < db
  · have h2' : i - lo < db + H.len := by omega_arith
    simp only [h2, h2', ↓reduceIte, clearTop_getD]
    obtain hx : ∀ j < db, (xorBytes (zeros (emLen - salt.length - H.len - 2) ++ 1 :: salt) (mgf1 G h db)).getD j 0 =
        (if j < db - salt.length - 1 then 0 else if j = db - salt.length - 1 then 1
          else salt.getD (j - (db - salt.length)) 0) ^^^ (mgf1 G h db).getD j 0 := fun j hj => by
      rw [xorBytes_getD (by rw [hdbl]; exact hj) (by rw [hmk]; exact hj), db_getD,
        show emLen - salt.length - H.len - 2 = db - salt.length - 1 by omega_arith,
        show j - (db - salt.length - 1) - 1 = j - (db - salt.length) by omega_arith]
    by_cases h3 : i - lo = 0
    · simp only [h3, ↓reduceIte]; rw [hx 0 (by omega_arith)]
    · simp only [h3, ↓reduceIte]; rw [hx _ h2]
  · simp only [h2, ↓reduceIte]
    by_cases h4 : i - lo < db + H.len
    · simp only [h4, ↓reduceIte]
    · simp only [h4, ↓reduceIte]
      rw [show i - lo - (db + H.len) = 0 by omega_arith]; rfl

/-- `sign`, byte by byte (as in `Proof/RsaPss/SignCases.lean`), with MGF1's
hash function `G` another than `H`. -/
theorem sign_eq₂ (H G : Hash) (hH : Valid H) (hG : Valid G) {n₀ : Byte}
    {rest eB pB qB dPB dQB qInvB mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    sign H G (n₀ :: rest) eB pB qB dPB dQB qInvB mHash salt =
      Rsa.privateChecked (n₀ :: rest) eB ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits))))
        pB qB dPB dQB qInvB := by
  simp only [sign, encodeK_eq₂ H G hH hG h0 hm hb he hlo hdb hfit]

end

end VG.Proof.RsaPss.Arm

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ 64) (hj : j < 24) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by omega_arith)

/-- The call's stack arguments but the first. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [BitVec.ofNat 32 P.el, P.scr + BitVec.ofNat 32 oEm, BitVec.ofNat 32 P.K, P.p, BitVec.ofNat 32 P.pl, P.q,
    BitVec.ofNat 32 P.ql, P.dp, BitVec.ofNat 32 P.pl, P.dq, BitVec.ofNat 32 P.ql, P.qinv, BitVec.ofNat 32 P.pl,
    P.scr + BitVec.ofNat 32 oRsa, BitVec.ofNat 32 (P.scl - 1024)]

theorem pa_wp (P : EP) {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) (hi : In h.D P σ) :
    WP isa (.block privArgs) s fun t =>
      t.mem = wl (P.lay h.D) (s.mem.writeW (State.addr P.B) P.e) 1 (outv P) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.out ∧ t.gpr .r1 = BitVec.ofNat 32 P.K ∧
      t.gpr .r2 = P.n ∧ t.gpr .r3 = BitVec.ofNat 32 P.K := by
  have hg := hi.geo
  obtain hs1 : 1024 ≤ P.scl := by
    have := hi.slK; unfold Spec.RsaPss.scratchWords at this; omega_arith
  obtain ⟨a0, r0, v0⟩ := argAt hi hc.st (j := 0) (by decide)
  obtain ⟨a2, r2, v2⟩ := argAt hi hc.st (j := 2) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hc.st (j := 5) (by decide)
  obtain ⟨a6, r6, v6⟩ := argAt hi hc.st (j := 6) (by decide)
  obtain ⟨a7, r7, v7⟩ := argAt hi hc.st (j := 7) (by decide)
  obtain ⟨a8, r8, v8⟩ := argAt hi hc.st (j := 8) (by decide)
  obtain ⟨a9, r9, v9⟩ := argAt hi hc.st (j := 9) (by decide)
  obtain ⟨a10, r10, v10⟩ := argAt hi hc.st (j := 10) (by decide)
  obtain ⟨a12, r12, v12⟩ := argAt hi hc.st (j := 12) (by decide)
  obtain ⟨a14, r14, v14⟩ := argAt hi hc.st (j := 14) (by decide)
  obtain ⟨a20, r20, v20⟩ := argAt hi hc.st (j := 21) (by decide)
  replace v0 : s.mem.readW ((P.lay h.D).fr (arg 0)) 32 = P.out := v0
  replace v2 : s.mem.readW ((P.lay h.D).fr (arg 2)) 32 = P.n := v2
  replace v3 : s.mem.readW ((P.lay h.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.K := v3
  replace v4 : s.mem.readW ((P.lay h.D).fr (arg 4)) 32 = P.e := v4
  replace v5 : s.mem.readW ((P.lay h.D).fr (arg 5)) 32 = BitVec.ofNat 32 P.el := v5
  replace v6 : s.mem.readW ((P.lay h.D).fr (arg 6)) 32 = P.p := v6
  replace v7 : s.mem.readW ((P.lay h.D).fr (arg 7)) 32 = BitVec.ofNat 32 P.pl := v7
  replace v8 : s.mem.readW ((P.lay h.D).fr (arg 8)) 32 = P.q := v8
  replace v9 : s.mem.readW ((P.lay h.D).fr (arg 9)) 32 = BitVec.ofNat 32 P.ql := v9
  replace v10 : s.mem.readW ((P.lay h.D).fr (arg 10)) 32 = P.dp := v10
  replace v12 : s.mem.readW ((P.lay h.D).fr (arg 12)) 32 = P.dq := v12
  replace v14 : s.mem.readW ((P.lay h.D).fr (arg 14)) 32 = P.qinv := v14
  replace v20 : s.mem.readW ((P.lay h.D).fr (arg 21)) 32 = BitVec.ofNat 32 P.scl := v20
  obtain wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.D).fr d) 4 := fun d hd => hc.st.inFr hd
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  obtain w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  obtain rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 24 →
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr (arg j)) 32 = m.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  obtain rdS0 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr sS) 32 = m.readW ((P.lay h.D).fr sS) 32 :=
    fun m v => by rw [q0]; exact rdS m v (by decide)
  prun [privArgs, copyArg, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, hc.slotS, arg_lt,
    a0, r0, v0, a2, r2, v2, a3, r3, v3, a4, r4, v4, a5, r5, v5, a6, r6, v6, a7, r7, v7, a8, r8, v8, a9, r9, v9,
    a10, r10, v10, a12, r12, v12, a14, r14, v14, a20, r20, v20, rdArg, rdS, w0, rdA0, rdS0,
    movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oRsa < 2 ^ 16 by decide),
    movw_val (show 1024 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (w := 32) hs1, Nat.reduceMul, wl_cons, wl_nil,
    Nat.reduceAdd]

/-- Before the call. -/
abbrev R1 (G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ) ∧
    PrivArgs s P.out P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv (P.scr + BitVec.ofNat 32 oRsa)
      P.K P.el P.pl P.ql (P.scl - 1024)

theorem pa_vp (G : Spec.Mgf1.Hash) (P : EP) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ)) (.block privArgs)
      (R1 h G P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  refine WP.mono (pa_wp h P hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  rw [q0] at m
  obtain ⟨σ', ok⟩ := hg.ok
  obtain fr : Frame [⟨(P.lay h.D).fr 0, 64⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 0) (by decide)
      (by decide))).trans (wl_frame _ _ _ 1 (by simp))
  obtain rd0 : ∀ i, i < 16 → stackArg t i = t.mem.readW ((P.lay h.D).fr (4 * i)) 32 := by
    intro i hi
    simp only [stackArg, stackArgAddr, sp, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega_arith)]
  obtain v0 : stackArg t 0 = P.e := by
    rw [rd0 0 (by decide), m, wl_other _ _ _ 1 0 (by decide) (by simp), Mem.readW_writeW_self32]
  obtain v : ∀ i, 1 ≤ i → i < 16 → stackArg t i = (outv P).getD (i - 1) 0 := fun i h1 h2 => by
    rw [rd0 i h2, m, wl_read _ _ _ 1 i h1 (by simp; omega_arith) (by simp)]
  have hK := hi.k1024
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk.keep h fr fun r hr => ?_, fun i hi' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 64 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Lay.fr_sep (by decide) (by decide) (by decide), Lay.fr_sep (by decide) (by decide) (by decide),
      Lay.fr_sep (by decide) (by decide) (by decide)⟩
  · rw [← he i hi']
    exact fr _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (o := oEm + i) (n := 1) (d := 0) (k := 64) (by have := hi'; unfold oEm oRsa; omega_arith)
        (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords at hs
  exact ⟨t0, t1, t2, t3, v0, v 1 (by decide) (by decide), v 2 (by decide) (by decide), v 3 (by decide) (by decide),
    v 4 (by decide) (by decide), v 5 (by decide) (by decide), v 6 (by decide) (by decide), v 7 (by decide) (by decide),
    v 8 (by decide) (by decide), v 9 (by decide) (by decide), v 10 (by decide) (by decide),
    v 11 (by decide) (by decide), v 12 (by decide) (by decide), v 13 (by decide) (by decide),
    v 14 (by decide) (by decide), v 15 (by decide) (by decide), hi.kv, hi.el1, hi.elK, hi.pl1, hi.plK, hi.ql1, hi.qlK,
    by omega_arith, by have := hi.scl32; omega_arith⟩

/-- What the specification signs: RSASP1 of `EM`, checked against `e`. -/
theorem sign_ok (g : RsaOaep.Arm.OHash) {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    Spec.RsaPss.sign h.G g.G P.nB P.eB (pB P σ) (qB P σ) (dpB P σ) (dqB P σ) (qiB P σ) (digB h P σ) (saltB P σ) =
      Spec.Rsa.privateChecked P.nB P.eB ((List.range P.K).map (emF h g.G P σ)) (pB P σ) (qB P σ) (dpB P σ)
        (dqB P σ) (qiB P σ) := by
  obtain hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega_arith
    | cons b rest => exact ⟨b, rest, rfl⟩
  obtain hn0 : n0 P = b := by simp [n0, hbr]
  obtain hb0 : b ≠ 0 := fun e => hf.1 (by rw [hn0, e]; rfl)
  obtain e1 := lo_eq hb0 rest
  obtain e2 := RsaPss.emLength_eq rest hb0
  have gl : h.G.len = h.D := h.glen
  have hsl := hf.2
  obtain hlo : lo P = if b.toNat ≤ 1 then 1 else 0 := by unfold lo; rw [hn0]
  rw [hbr, List.length_cons] at hl
  rw [List.length_cons] at e1
  obtain hbt : b.toNat ≠ 0 := fun e => hb0 (BitVec.eq_of_toNat_eq e)
  obtain hem : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = P.K - lo P := by
    rw [hlo]
    by_cases hb1 : b.toNat = 1
    · rw [ite_eq_left hb1] at e2; rw [ite_eq_left (by omega_arith)]; all_goals omega_arith
    · rw [ite_eq_right hb1] at e2; rw [ite_eq_right (by have := b.isLt; omega_arith)]; all_goals omega_arith
  obtain hlo1 : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  obtain hdb : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) - h.G.len - 1 =
      dbN h P := by
    rw [hem, gl]
  obtain hm : (digB h P σ).length = h.G.len := by rw [gl]; exact RsaPkcs1Sig.Arm.bytesAt_length _ _ _
  obtain hfit : h.G.len + (saltB P σ).length + 2 ≤
      Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) := by
    rw [gl, RsaPkcs1Sig.Arm.bytesAt_length, hem]; have := hf.2; omega_arith
  rw [hbr, sign_eq₂ h.G g.G (PssHash.valid h) g.valid hb0 hm rfl rfl e1 hdb hfit]
  refine congrArg (fun em => Spec.Rsa.privateChecked (b :: rest) P.eB em (pB P σ) (qB P σ) (dpB P σ) (dqB P σ)
    (qiB P σ)) ?_
  rw [List.length_cons, show rest.length + 1 = P.K by omega_arith]
  refine congrArg (fun f => List.map f (List.range P.K)) (funext fun i => ?_)
  obtain hc := cW_byte hb0 rest
  unfold emF mkS Hs xB
  rw [hn0, ← hlo, ← hc, RsaPkcs1Sig.Arm.bytesAt_length, h.hash]

/-- The call's input and working space, in `scratch`. -/
abbrev inpR (P : EP) : Region := ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩
abbrev scrR (P : EP) : Region := ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩

theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
    State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm ∧
    State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa ∧
    Region.Sub (inpR P) P.SCR ∧ Region.Sub (scrR P) P.SCR ∧ (inpR P).Disjoint (scrR P) ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1024 ≤ P.scl ∧ P.K ≤ 1024 := by
  obtain hf := hi.ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hs := hi.slK
  unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs
  have hK := hi.k1024
  obtain e1 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm :=
    addr_add (by unfold oEm; omega_arith)
  obtain e2 : State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa :=
    addr_add (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, by omega_arith, hK⟩
  · rw [inpR, e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [scrR, e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [inpR, scrR, e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem call_pre {G : Spec.Mgf1.Hash} {P : EP} {σ s : State} (hr : R1 h G P σ s) :
    (Proof.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRd P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.K P.el
        P.pl P.ql) (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨hc, hk, -, pa⟩ := hr
  have hi := hk.1
  have ok := hi.ok
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  obtain oS : P.OUT.Disjoint P.SCR := List.pairwise_pair.mp ok.wrw
  refine priv_pre pa hc.st.sp hB (by simp only [frameBytes] at fit; omega_arith) ?_ (oS.sub_right sS') ?_ ?_
  · intro w hw r hr
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact oS.sub_right sI
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · exact ok.rw_ro (w := P.OUT) (by simp) (by simp)
    · rw [q0]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (d := 0) (n := 64) (by show 0 + 64 ≤ frameBytes + 56; decide)).symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.N) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sS'
    · exact dIS.symm
    · exact (ok.rw_ro (w := P.SCR) (r := P.PP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DP) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.DQ) (by simp) (by simp)).sub_left sS'
    · exact (ok.rw_ro (w := P.SCR) (r := P.QI) (by simp) (by simp)).sub_left sS'
    · rw [q0]; exact ((ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 64)
        (by show 0 + 64 ≤ frameBytes + 56; decide)).symm).sub_left sS'
  · intro r hr
    have low : (⟨State.addr P.B - BitVec.ofNat 64 3440, 3440⟩ : Region) = (P.lay h.D).LOW := rfl
    rw [low]
    simp only [privRd, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ok.low_buf (R := P.OUT) (.inr (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'
    · exact ok.low_buf (R := P.N) (.inl (by simp))
    · exact ok.low_buf (R := P.E) (.inl (by simp))
    · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
    · exact ok.low_buf (R := P.PP) (.inl (by simp))
    · exact ok.low_buf (R := P.QQ) (.inl (by simp))
    · exact ok.low_buf (R := P.DP) (.inl (by simp))
    · exact ok.low_buf (R := P.DQ) (.inl (by simp))
    · exact ok.low_buf (R := P.QI) (.inl (by simp))
    · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · intro r hr
    simp only [privBufs, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain fs := fun {R : Region} (hR : R ∈ (P.lay h.D).ro ++ (P.lay h.D).rw) => ok.fits R hR
    have hg := hi.geo
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (by decide)]; unfold oEm; omega_arith
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · exact fs (by simp)
    · dsimp only; rw [Proof.X25519.Arm.addr_toNat, hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega_arith

theorem nB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB

theorem eB_at {P : EP} {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) :
    Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB := (hs.ro (R := P.E) (by simp)).trans hi.eB

/-- `out` and the result: the call. -/
theorem call_vp (g : RsaOaep.Arm.OHash) (P : EP) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (R1 h g.G P) (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin h g.G P) := by
  refine VP.callF (Proof.Rsa.Arm.code_verified v) (privCode_stack v)
    (privRd P.B P.n P.e (P.scr + BitVec.ofNat 32 oEm) P.p P.q P.dp P.dq P.qinv P.K P.el P.pl P.ql)
    (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_pre h hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨hc, hk, -, -⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
    obtain hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain hscr : Covers [P.SCR] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    obtain hout : Covers [P.OUT] s.wr := Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hs.wr, ok.wr]; simp
    obtain inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega_arith)⟩
    obtain wr' : Covers (privWr P.out (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      hout.cons (by rw [e2]; exact inS (by unfold oRsa; omega_arith))
    refine ⟨Covers.append_left ((hro P.N (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ ((hro P.PP (by simp)).cons ((hro P.QQ (by simp)).cons ((hro P.DP (by simp)).cons
      ((hro P.DQ (by simp)).cons ((hro P.QI (by simp)).cons (Covers.cons ?_ Covers.nil))))))
    · rw [e1]; exact (inS (by unfold oEm; omega_arith)).right
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 64 ≤ frameBytes; decide))).right
  · rw [hr.1.st.sp]; exact hr.2.1.1.ok.B56
  · exact priv_pub h₁.2.2.2 h₂.2.2.2 (by rw [h₁.1.st.sp, h₂.1.st.sp]) (by rw [nB_at h h₁.2.1.1 h₁.1.st,
      nB_at h h₂.2.1.1 h₂.1.st]) (by rw [eB_at h h₁.2.1.1 h₁.1.st, eB_at h h₂.2.1.1 h₂.1.st]) _ _
  · obtain ⟨hc, hk, he, pa⟩ := hr
    have hi := hk.1
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain low : FrameStack.belowA s.sp Proof.Rsa.Arm.stackBytes = (P.lay h.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    obtain st : (P.lay h.D).St σ s' := hs.write fr (fun r hr => by
      simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.D).LOW, by simp, fun _ h => h⟩) rd wr sp
    refine ⟨⟨hi, st⟩, ?_⟩
    obtain em : Spec.Rsa.bytesAt s.mem (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K = (List.range P.K).map (emF h g.G P σ) := by
      unfold Spec.Rsa.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      rw [List.mem_range] at hi'
      rw [← he i hi', e1, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have := priv_post pa po
    rw [nB_at h hi hs, eB_at h hi hs, em, hs.ro (R := P.PP) (by simp), hs.ro (R := P.QQ) (by simp),
      hs.ro (R := P.DP) (by simp), hs.ro (R := P.DQ) (by simp), hs.ro (R := P.QI) (by simp)] at this
    rw [Res, sign_ok h g hi hk.2.1]
    exact this

end VG.Proof.RsaPss.Arm.Sg
