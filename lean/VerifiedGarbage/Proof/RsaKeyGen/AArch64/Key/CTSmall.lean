module

public import VerifiedGarbage.Proof.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DBase
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTLcm
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DPart
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTLcm
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.DPart
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw

/-! ### `RsaKeyGen.AArch64.Key.CTD`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: constant time, `d`

`dPart` branches on `e`, which is public (`kg_ite`), and in each branch runs
pieces of the key routines: `loadEv`, `lGe2`, `gcdIsOne`, `inverse` from
`invFrom`, `divisorOf`, and `dOdd`'s and `dEven`'s blocks. Each branch is
checked with no postcondition (`…_ct0`), the facts between its pieces from
their correctness; the facts after `dPart` come from `dPart_k`
(`dPart_ct`, to `KG DF`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- A store of some value into a word of array `j`. -/
theorem KS.arrW {I : KIn} {s₀ s t : State} (h : KS I s₀ s) {j d : Nat} (hj : j < 16) (hd : slot I.W j ≤ d)
    (hd' : d + 8 ≤ slot I.W j + 8 * (I.W + 2)) (hm : ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B d) v)
    {regs : List Reg} (k : Keep regs s t) (hr : ∀ r ∈ regs, r ∈ mmRegs := by decide) :
    KS I s₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem := by
  obtain ⟨v, hm⟩ := hm
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have o := writeW_outside s.mem I.B v (d := d) (by omega_arith)
  rw [← hm] at o
  have f := KF.arr1 (B := I.B) (W := I.W) (j := j) o hd hd'
  exact ⟨h.step f (all_mut_arr hj) k hr, f⟩

/-! ## `e` into `aE` -/

theorem loadEv_eq : seqs loadEv = .seq (zeroA aE) (.block (ws ++ (base aE .x16 ++
    ([ldh .x3 kEv, st .x3 .x16] : List Instr)))) := by
  simp only [loadEv, seqs, List.append_assoc]

theorem loadEvBlk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aE .x16 ++ ([ldh .x3 kEv, st .x3 .x16] : List Instr)))) s fun t =>
      KS I s₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧ Keep [.x11, .x12, .x16, .x3] s t := by
  have hn := h.ws.scr.nowrap
  have sE := h.ws.sl (j := aE) (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aE) fun s₂ ⟨⟨h16, _, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr k₂.wr
  have hx0 : s₂.gpr .x0 = I.B := (k₂.gpr .x0 (by decide)).trans h.ws.x0
  refine WP.mono (WP.keep [.x3] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W aE)) v) (by
    brun [hx0, hdr_enc (show kEv < 32 by decide), h16,
      hs₂.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith), hs₂.st (d := slot I.W aE) (by omega_arith), m₂]
    exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f⟩ := h.arrW (j := aE) (by decide) (Nat.le_refl _) (by omega_arith) hm (k₂.trans k₃)
  exact ⟨ht, f, (k₂.trans k₃).mono (by decide)⟩

/-- `loadEv`, for facts `F` that survive it. -/
theorem loadEv_ct {F : KIn → State → Prop} (hF : Stab F [.arr aE] allR) :
    RelCT isa (Two (KG F)) (seqs loadEv) (Two (KG F)) := by
  rw [loadEv_eq]
  exact RelCT.seq (zeroA_ct (by decide) hF.sub (by taint_decide))
    (kg_wsb (by taint_decide) fun I _ s h _ hf => WP.mono (loadEvBlk_k h) fun t ⟨ht, f, k⟩ =>
      ⟨ht, hF I s t h.hZ hf f (k.mono (by decide))⟩)

/-! ## `e = 0` and `e = 1` -/

theorem dZero_ct0 : RelCT isa (Two (KG NF)) (.block dZero) fun _ _ => True :=
  two_taint [.x0] (pins_kg NF) (by taint_decide)

theorem dOne_eq : dOne = constA 1 ++ (neMask aL aC ++ ([.block [sth .x15 kOk], zeroA aDd, .block (setOneA aDd)] :
    List (Prog isa))) := by
  simp only [dOne, List.append_assoc]

theorem dOne_ct0 : RelCT isa (Two (KG NF)) (seqs dOne) fun _ _ => True := by
  rw [dOne_eq]
  refine rs_app (by simp [constA]) (by simp [neMask, eqA]) (constA_ct 1 (by decide) (stab_nf _ _) (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => NF I t ∧ X15M I t)) (by simp [neMask, eqA]) (by simp)
    (neMask_ct (by decide) (by decide) (fun _ _ _ _ _ _ _ h15 => ⟨trivial, _, h15⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [.block [sth .x15 kOk]]) _ from
    stOk_ct (F := NF) (stab_nf _ _)) ?_
  exact RelCT.drop (show RelCT isa _ (seqs [zeroA aDd, .block (setOneA aDd)]) _ from
    RelCT.seq ((zeroAZ_ct (F := NF) (by decide) (stab_nf _ _) (by taint_decide)).mono
      (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h)
      (setOne_ct (G := NF) (by decide) (fun _ _ _ _ _ _ _ _ _ => trivial) (by taint_decide)))

/-! ## The pieces of `dOdd` and `dEven` -/

/-- What `invFrom j` and `inverse … j aT` change. -/
abbrev csI : List Rc := [.arr aU, .arr aV, .arr aX₁, .arr aX₂, .arr aT]

/-- `inverse` modulo `[j]`, from `invFrom j`, with word `W` of `u` zero. -/
theorem invFrom_ct [VG.Proof.Rsa.AArch64.InvLaw] {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjU : j ≠ aU) (hjV : j ≠ aV) (hj1 : j ≠ aX₁)
    (hj2 : j ≠ aX₂) (hjT : j ≠ aT) (hF : Stab F csI allR) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base aV .x17)) copyWords)
      hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([.lsr .x .x3 .x12 21] : List Instr))
      (.ite (.zero .x .x3) (VG.Impl.Rsa.AArch64.Keys.inverseB aU aV aX₁ aX₂ j aT) (VG.Impl.Rsa.AArch64.Keys.inverseBits aU aV aX₁ aX₂ j aT))) hc₂).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ TopZ aU I t)) (seqs (invFrom j ++ [inverse aU aV aX₁ aX₂ j aT]))
      (Two (KG F)) := by
  have sFT : ∀ (cs : List Rc), (∀ c ∈ cs, c ∈ csI) → cs.all Rc.ok = true → .arr aU ∉ cs →
      Stab (fun I t => F I t ∧ TopZ aU I t) cs allR :=
    fun _ h1 h2 h3 => stab_and (hF.mono h1 (by decide)) (stab_top _ (by decide) h2 h3)
  show RelCT isa _ (seqs ([zeroA aV] ++ ([copyA aV j, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂] ++
    [inverse aU aV aX₁ aX₂ j aT]))) _
  refine rs_app (by simp) (by simp) (zeroA_ct (by decide) (sFT [.arr aV] (by decide) (by decide) (by decide)).sub
    (by taint_decide)) ?_
  refine rs_app (by simp) (by simp) (invStart_ct (o := aV) (a := j) (by decide) hj hjV.symm (by decide) (by decide)
    hj1 hj2 (sFT [.arr aV, .arr aX₁, .arr aX₂] (by decide) (by decide) (by decide)) ht₁) ?_
  exact (inverse_ct (F := F) (by decide) (by decide) (by decide) (by decide) hj (by decide) (by decide)
    (by decide) (by decide) hjU.symm (by decide) (by decide) (by decide) hjV.symm (by decide) (by decide)
    hj1.symm (by decide) hj2.symm (by decide) hjT hF.sub ht₂).mono
    (fun _ _ h => two_kg (fun _ _ ⟨⟨hf, tU⟩, he, h1, h2⟩ => ⟨hf, tU, he, h1, h2⟩) h) fun _ _ h => h

theorem lGe2_eq : lGe2 = constA 2 ++ (geA aL aC ++ ([.block [sth .x15 kOk]] : List (Prog isa))) := by
  simp only [lGe2, List.append_assoc]

/-- `lGe2`: a mask in `kOk`. -/
theorem lGe2_ct {F : KIn → State → Prop} (hF : Stab F [.arr aC, .hdr kOk] allR) :
    RelCT isa (Two (KG F)) (seqs lGe2) (Two (KG fun I t => F I t ∧ KokM I t)) := by
  rw [lGe2_eq]
  refine rs_app (by simp [constA]) (by simp [geA, cmpA]) (constA_ct 2 (by decide) (hF.mono (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => F I t ∧ X15M I t)) (by simp [geA, cmpA]) (by simp)
    (geA_ct (by decide) (by decide) (fun I s t hZ hf hm k h15 =>
      ⟨hF I s t hZ hf (kf_eq hm) (k.mono (by decide)), _, h15⟩) (by taint_decide)) ?_
  exact show RelCT isa _ (seqs [.block [sth .x15 kOk]]) _ from stOk_ct (hF.mono (by decide) (by decide))

theorem gcdIsOne_eq : gcdIsOne = constA 1 ++ (eqMask aV aC ++
    ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]] : List (Prog isa))) := by
  simp only [gcdIsOne, List.append_assoc]

/-- `gcdIsOne`: `kOk` stays a mask. -/
theorem gcdIsOne_ct {F : KIn → State → Prop} (hF : Stab F [.arr aC, .hdr kOk] allR) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (seqs gcdIsOne) (Two (KG fun I t => F I t ∧ KokM I t)) := by
  have sK : Stab (fun I t => F I t ∧ KokM I t) [.arr aC] allR :=
    stab_and (hF.mono (by decide) (by decide)) (stab_kok _ (by decide) (by decide))
  rw [gcdIsOne_eq]
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 1 (by decide) sK.sub (by taint_decide)
    (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => (F I t ∧ KokM I t) ∧ X15M I t)) (by simp [eqMask, eqA]) (by simp)
    (eqMask_ct (by decide) (by decide) (fun I s t hZ hf hm k h15 =>
      ⟨sK I s t hZ hf (kf_eq hm) (k.mono (by decide)), _, h15⟩) (by taint_decide)) ?_
  exact show RelCT isa _ (seqs [.block _]) _ from kg_x0 (by taint_decide) fun I _ s h _ ⟨⟨hf, c, hok⟩, c', h15⟩ => by
    have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
    have hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
    refine WP.mono (WP.keep [.x3, .x15] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask (c' && c))) (by
      brun [h.ws.x0, hdr_enc (show kOk < 32 by decide), hst, hld, h15, hok, mask_and'])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
    obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) hm k
    exact ⟨ht, hF I s t h.hZ hf (f.mono (by decide)) (k.mono (by decide)), _, hw⟩

/-! ## `e` odd -/

/-- `e` odd. -/
abbrev OddE : KIn → State → Prop := fun I _ => I.E % 2 = 1

theorem stab_oddE (cs : List Rc) (rs : List Reg) : Stab OddE cs rs := fun _ _ _ _ h _ _ => h

/-- `e` into `x3`, and its inverse modulo `2⁶⁴` into `x4` (`minvX4_ok`). -/
theorem minvBlk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hev : EvOK I s) (heo : I.E % 2 = 1) :
    WP isa (.block (([ldh .x3 kEv] : List Instr) ++ minv)) s fun t => KS I s₀ t ∧ t.mem = s.mem := by
  have hlE := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 I.E ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hlE, hev]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h3₁, m₁⟩, k₁⟩ => ?_
  refine WP.mono (minvX4_ok s₁ (by rw [h3₁, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]; exact heo))
    fun t ⟨⟨_, _, m₂⟩, k₂⟩ => ?_
  have hm : t.mem = s.mem := m₂.trans m₁
  exact ⟨h.regs hm (k₁.trans k₂), hm⟩

theorem dOddBlk_eq : ([ldh .x3 kEv] : List Instr) ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
    ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
      .mul .x .x10 .x3 .x4] : List Instr) = (([ldh .x3 kEv] : List Instr) ++ minv) ++ (ws ++ (base aX₂ .x16 ++
    (base aR .x17 ++ ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1,
      .addImm .x .x3 .x3 1, .mul .x .x10 .x3 .x4] : List Instr)))) := by
  simp only [List.append_assoc]

/-- `dOdd`'s block computing `t` and `c` (`dOddC_ok`), for any contents of
`[aX₂]` and `[aR]`. -/
theorem dOddCblk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hev : EvOK I s) (heo : I.E % 2 = 1) :
    WP isa (.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
      ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
        .mul .x .x10 .x3 .x4] : List Instr))) s (KS I s₀) := by
  have hn := h.ws.scr.nowrap
  have sX := h.ws.sl (j := aX₂) (by decide)
  have sR := h.ws.sl (j := aR) (by decide)
  rw [dOddBlk_eq, WP.block_append_iff]
  refine WP.mono (minvBlk_k h hev heo) fun s₂ ⟨h₂, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono h₂.ws.ws_ok fun s₃ ⟨⟨_, h11, m₃, _⟩, k₃⟩ => ?_
  have hx0₃ : s₃.gpr .x0 = I.B := (k₃.gpr .x0 (by decide)).trans h₂.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aX₂ .x16 hx0₃ h11) fun s₄ ⟨⟨h16, m₄, _⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aR .x17 ((k₄.gpr .x0 (by decide)).trans hx0₃) ((k₄.gpr .x11 (by decide)).trans h11))
    fun s₅ ⟨⟨h17, m₅, _⟩, k₅⟩ => ?_
  have k35 := (k₃.trans k₄).trans k₅
  have hs₅ := h₂.ws.scr.congr k35.wr
  have hm₅ : s₅.mem = s₂.mem := by rw [m₅, m₄, m₃]
  have h16₅ : s₅.gpr .x16 = off I.B (slot I.W aX₂) := (k₅.gpr .x16 (by decide)).trans h16
  have hx0₅ : s₅.gpr .x0 = I.B := ((k₄.trans k₅).gpr .x0 (by decide)).trans hx0₃
  refine WP.mono (WP.keep [.x1, .x3, .x10] (Q := fun t => t.mem = s₅.mem) (by
    brun [hx0₅, hdr_enc (show kEv < 32 by decide), h16₅, h17,
      hs₅.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith),
      hs₅.ld (d := slot I.W aX₂) (by omega_arith), hs₅.ld (d := slot I.W aR) (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, kt⟩ => ?_
  exact h₂.regs (mt.trans hm₅) (k35.trans kt)

theorem dOdd_eq2 : dOdd = loadEv ++ (([zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] :
    List (Prog isa)) ++ ((invFrom aE ++ ([inverse aU aV aX₁ aX₂ aE aT] : List (Prog isa))) ++ (lGe2 ++ (gcdIsOne ++
    ([.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
        ([ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
          .mul .x .x10 .x3 .x4] : List Instr)),
      zeroA aDd,
      .block (ws ++ (base aDd .x8 ++ (([st .x10 .x8] : List Instr) ++ (base aQt .x9 ++
        ([movi .x7 0] : List Instr))))),
      mulAddRow] : List (Prog isa)))))) := by
  simp only [dOdd, List.append_assoc]

theorem dOdd_ct0 [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG fun I t => EvOK I t ∧ I.E % 2 = 1)) (seqs dOdd) fun _ _ => True := by
  have sF : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .hdr kEv ∉ cs →
      Stab (fun I t => EvOK I t ∧ OddE I t) cs rs :=
    fun _ rs hok hn => stab_and (stab_ev rs hok hn) (stab_oddE _ _)
  rw [dOdd_eq2]
  refine rs_app (by simp [loadEv]) (by simp) (loadEv_ct (sF _ _ (by decide) (by decide))) ?_
  -- `L = e Q + R`, `[aU] := R`.
  refine rs_app (R := Two (KG fun I t => (EvOK I t ∧ OddE I t) ∧ TopZ aU I t)) (by simp) (by simp [invFrom])
    (RelCT.seq (zeroA_ct (by decide) (sF _ _ (by decide) (by decide)) (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (sF _ _ (by decide) (by decide)) (by taint_decide))
        (RelCT.seq (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (sF _ _ (by decide) (by decide)) (by taint_decide) (by taint_decide))
          (zc_ct (by decide) (by decide) (by decide) (sF _ _ (by decide) (by decide)) (by taint_decide)
            (by taint_decide))))) ?_
  -- `x = R⁻¹ mod e`, `kOk`.
  refine rs_app (by simp [invFrom]) (by simp [lGe2, constA]) (invFrom_ct (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (sF _ _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [lGe2, constA]) (by simp [gcdIsOne, constA]) (lGe2_ct (sF _ _ (by decide) (by decide))) ?_
  refine rs_app (by simp [gcdIsOne, constA]) (by simp) (gcdIsOne_ct (sF _ _ (by decide) (by decide))) ?_
  -- `t`, `c`, and `d = Q t + c`.
  show RelCT isa _ (.seq _ (.seq _ (.seq _ _))) _
  refine RelCT.seq (kg_ct (G := NF) ?_ fun I _ s h _ ⟨⟨hev, ho⟩, _⟩ => WP.mono (dOddCblk_k h hev ho) fun t ht =>
    ⟨ht, trivial⟩) ?_
  · rw [dOddBlk_eq]
    exact kg_blk_ws0 (G := NF) (by taint_decide) (fun I _ s h _ ⟨⟨hev, ho⟩, _⟩ =>
      WP.mono (minvBlk_k h hev ho) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) (by taint_decide)
  exact kg_then (G := NF) (zeroA_ct0 (by taint_decide)) (fun I _ s h _ _ => WP.mono (zeroA_k h (j := aDd)
    (by decide)) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) (kg_ws0 (by taint_decide))

/-! ## `e` even -/

theorem divisorOf_eq2 (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    ([.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x15 .x4,
      .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))] : List (Prog isa)))) := by
  simp only [divisorOf, List.append_assoc]

/-- `divisorOf`'s last block: word 0 of `[aM]` changed. -/
theorem divisorBlk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x15 .x4,
      .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))) s fun t =>
      KS I s₀ t ∧ KF I.B I.W [.arr aM] s.mem t.mem ∧ Keep [.x11, .x12, .x16, .x3, .x4] s t := by
  have hn := h.ws.scr.nowrap
  have sM := h.ws.sl (j := aM) (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aM) fun s₂ ⟨⟨h16, _, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr k₂.wr
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => ∃ v : BitVec 64, t.mem = s.mem.writeW (off I.B (slot I.W aM)) v)
    (by
      brun [h16, hs₂.ld (d := slot I.W aM) (by omega_arith), hs₂.st (d := slot I.W aM) (by omega_arith), m₂]
      exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f⟩ := h.arrW (j := aM) (by decide) (Nat.le_refl _) (by omega_arith) hm (k₂.trans k₃)
  exact ⟨ht, f, (k₂.trans k₃).mono (by decide)⟩

/-- `divisorOf j`, for facts `F` that survive it. -/
theorem divisorOf_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjM : j ≠ aM) (_hjC : j ≠ aC)
    (hF : Stab F [.arr aM, .arr aC] allR) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base aM .x17)) copyWords)
      hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base j .x16 ++ base aC .x17)) (.seq (countLoop .x14 xorBody) (.block zeroMask)))) hc₂).isSome =
      true) :
    RelCT isa (Two (KG F)) (seqs (divisorOf j)) (Two (KG F)) := by
  rw [divisorOf_eq2]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA aM, copyA aM j]) _ from
    RelCT.seq (zeroA_ct (by decide) (hF.mono (by decide) (by decide)) (by taint_decide))
      (copyA_ct (by decide) hj hjM.symm (hF.mono (by decide) (by decide)) ht₁)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (by decide) (hF.mono (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := F) hj (by decide) (fun I s t hZ hf hm k _ =>
    hF I s t hZ hf (kf_eq hm) (k.mono (by decide))) ht₂) ?_
  exact show RelCT isa _ (seqs [.block _]) _ from kg_wsb (by taint_decide) fun I _ s h _ hf =>
    WP.mono (divisorBlk_k h) fun t ⟨ht, f, k⟩ => ⟨ht, hF I s t h.hZ hf (f.mono (by decide)) (k.mono (by decide))⟩

theorem dEvenBlk_eq : ([mov .x10 .x15] : List Instr) ++ evenMaskOf aL ++
    ([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ notMask ++
    ([sth .x15 kOk, mov .x15 .x10] : List Instr) = ([mov .x10 .x15] : List Instr) ++ (ws ++ (base aL .x16 ++
    (([ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr) ++
    (([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++
    (notMask ++ ([sth .x15 kOk, mov .x15 .x10] : List Instr)))))) := by
  simp only [evenMaskOf, List.append_assoc]

theorem dEven_eq2 : dEven = loadEv ++ (divisorOf aL ++
    (([zeroA aQt, copyA aQt aE, divmod aQt aR aM aT, zeroA aU, copyA aU aR] : List (Prog isa)) ++ (constA 3 ++
    (ltA aL aC ++ (([.block (([mov .x10 .x15] : List Instr) ++ evenMaskOf aL ++
        ([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ notMask ++
        ([sth .x15 kOk, mov .x15 .x10] : List Instr)),
      zeroA aM, copyA aM aL] : List (Prog isa)) ++ (selC aM ++ ((invFrom aM ++
    ([inverse aU aV aX₁ aX₂ aM aT] : List (Prog isa))) ++ (gcdIsOne ++
    ([zeroA aDd, copyA aDd aX₂] : List (Prog isa)))))))))) := by
  simp only [dEven, List.append_assoc]

/-- After `dEven`'s mask block. -/
abbrev EvM : KIn → State → Prop := fun I t => (TopZ aU I t ∧ KokM I t) ∧ X15M I t

theorem dEven_ct0 [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG EvOK)) (seqs dEven) fun _ _ => True := by
  suffices h : RelCT isa (Two (KG NF)) (seqs dEven) fun _ _ => True from
    h.mono (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h
  have sT : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .arr aU ∉ cs →
      Stab (fun I t => NF I t ∧ TopZ aU I t) cs rs :=
    fun _ rs hok hn => stab_and (stab_nf _ _) (stab_top rs (by decide) hok hn)
  have sM : ∀ (rs : List Reg), .x15 ∉ rs → Stab EvM [.arr aM] rs := fun rs h15 =>
    stab_and (stab_and (stab_top rs (by decide) (by decide) (by decide)) (stab_kok rs (by decide) (by decide)))
      (stab_x15 h15)
  rw [dEven_eq2]
  -- `[aE] := e`, `[aM] := L` (1 for 0), `[aU] := e mod [aM]`.
  refine rs_app (by simp [loadEv]) (by simp [divisorOf]) (loadEv_ct (stab_nf _ _)) ?_
  refine rs_app (by simp [divisorOf]) (by simp) (divisorOf_ct (by decide) (by decide) (by decide) (stab_nf _ _)
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => NF I t ∧ TopZ aU I t)) (by simp) (by simp [constA])
    (RelCT.seq (zeroA_ct (by decide) (stab_nf _ _) (by taint_decide))
      (RelCT.seq (copyA_ct (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide))
        (RelCT.seq (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide))
          (zc_ct (by decide) (by decide) (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide))))) ?_
  -- The mask of `L` even or below 3, `[aM] := L` or 3.
  refine rs_app (by simp [constA]) (by simp [ltA, cmpA]) (constA_ct 3 (by decide) (sT _ _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => (NF I t ∧ TopZ aU I t) ∧ X15M I t)) (by simp [ltA, cmpA]) (by simp)
    (ltA_ct (by decide) (by decide) (fun I s t hZ hf hm k h15 =>
      ⟨sT [] _ (by decide) (by decide) I s t hZ hf (kf_eq hm) k, _, h15⟩) (by taint_decide)) ?_
  refine rs_app (R := Two (KG EvM)) (by simp) (by simp [selC])
    (RelCT.seq (kg_ct (G := EvM) ?_ fun I _ s h _ ⟨⟨_, tU⟩, _, h15⟩ => WP.mono (dEvenMask_k h h15)
      fun _ ⟨ht, f, hw, h15'⟩ => ⟨ht, ⟨(f.at (by decide) (by decide) (by decide) h.hZ).trans tU, _, hw⟩, _, h15'⟩)
      (RelCT.seq (zeroA_ct (by decide) (sM _ (by decide)) (by taint_decide))
        (copyA_ct (by decide) (by decide) (by decide) (sM _ (by decide)) (by taint_decide)))) ?_
  · rw [dEvenBlk_eq]
    exact kg_blk_ws0 (G := NF) (by taint_decide) (fun I _ s h _ _ => WP.mono (WP.keep [.x10]
      (Q := fun t => t.mem = s.mem) (by brun) (by decide) (by decide) (by decide +kernel)) fun _ ⟨hm, k⟩ =>
        ⟨h.regs hm k, trivial⟩) (by taint_decide)
  refine rs_app (by simp [selC]) (by simp) (selC_ct (F := fun I t => TopZ aU I t ∧ KokM I t) (by decide) (by decide)
    (stab_and (stab_top _ (by decide) (by decide) (by decide)) (stab_kok _ (by decide) (by decide)))
    (by taint_decide)) ?_
  -- The inverse modulo `[aM]`, `kOk`, `[aDd] := x`.
  refine rs_app (by simp) (by simp [gcdIsOne, constA]) ((invFrom_ct (F := KokM) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (stab_kok _ (by decide) (by decide)) (by taint_decide)
    (by taint_decide)).mono (fun _ _ h => two_kg (fun _ _ ⟨tU, hk⟩ => ⟨hk, tU⟩) h) fun _ _ h => h) ?_
  refine rs_app (by simp [gcdIsOne, constA]) (by simp) ((gcdIsOne_ct (F := NF) (stab_nf _ _)).mono
    (fun _ _ h => two_kg (fun _ _ hk => ⟨trivial, hk⟩) h) fun _ _ h => h) ?_
  exact kg_then (G := NF) (zeroA_ct0 (by taint_decide)) (fun I _ s h _ _ => WP.mono (zeroA_k h (j := aDd)
    (by decide)) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) (copyA_ct0 (by taint_decide))

/-! ## `dPart` -/

theorem dPart_ct0 [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG EvOK)) dPart fun _ _ => True := by
  unfold dPart
  refine RelCT.seq (kg_x0 (G := fun I t => EvOK I t ∧ t.gpr .x3 = BitVec.ofNat 64 I.E) (by taint_decide)
    fun I _ s h _ hev => ?_) ?_
  · have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith)
    exact WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 I.E ∧ t.mem = s.mem) (by
      brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hld, hev]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h3, hm⟩, k⟩ => ⟨h.regs hm k, by dsimp only [EvOK]; rw [hm]; exact hev, h3⟩
  refine kg_ite (kg_zero_eq (g := fun p => BitVec.ofNat 64 (Spec.Rsa.os2ip p.q.eb)) fun _ _ h => h.2)
    (dZero_ct0.mono (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h) ?_
  -- `e ≠ 0`: `x3 := e − 1`.
  refine RelCT.seq (kg_x0 (G := fun I t => EvOK I t ∧ t.gpr .x3 = BitVec.ofNat 64 (I.E - 1)) (by taint_decide)
    fun I _ s h L ⟨⟨hev, h3⟩, hb⟩ => ?_) ?_
  · have hE0 : I.E ≠ 0 := by
      rw [eval_zero, h3, ofNat_beq_zero L.E_lt] at hb
      simpa using hb
    exact WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (I.E - 1) ∧ t.mem = s.mem) (by
      brun [h3]
      exact VG.Offset.ofNat_sub_ofNat (by omega_arith)) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h3', hm⟩, k⟩ => ⟨h.regs hm k, by dsimp only [EvOK]; rw [hm]; exact hev, h3'⟩
  refine kg_ite (kg_zero_eq (g := fun p => BitVec.ofNat 64 (Spec.Rsa.os2ip p.q.eb - 1)) fun _ _ h => h.2)
    (dOne_ct0.mono (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h) ?_
  -- `e ≠ 1`: `x3 := e mod 2`.
  refine RelCT.seq (kg_x0 (G := fun I t => EvOK I t ∧ t.gpr .x3 = BitVec.ofNat 64 (I.E % 2)) (by taint_decide)
    fun I _ s h L ⟨⟨hev, _⟩, _⟩ => ?_) ?_
  · have hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith)
    exact WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (I.E % 2) ∧ t.mem = s.mem) (by
      brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hld, hev]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have := L.E_lt
      omega_arith) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h3, hm⟩, k⟩ => ⟨h.regs hm k, by dsimp only [EvOK]; rw [hm]; exact hev, h3⟩
  refine kg_ite (kg_nonzero_eq (g := fun p => BitVec.ofNat 64 (Spec.Rsa.os2ip p.q.eb % 2)) fun _ _ h => h.2)
    (dOdd_ct0.mono (fun _ _ h => two_kg (fun I t ⟨⟨hev, h3⟩, hb⟩ => ⟨hev, ?_⟩) h) fun _ _ h => h)
    (dEven_ct0.mono (fun _ _ h => two_kg (fun _ _ h => h.1.1) h) fun _ _ h => h)
  rcases Nat.mod_two_eq_zero_or_one I.E with h2 | h2
  · rw [eval_nonzero, h3, h2] at hb
    exact absurd hb (by decide)
  · exact h2

/-- After `dPart`: the front's facts, and `d` with `kOk`. -/
abbrev DF : KIn → State → Prop := fun I t => PF I t ∧ DRes I I.E I.L t.mem

theorem dPart_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG LF)) dPart (Two (KG DF)) :=
  kg_ct (dPart_ct0.mono (fun _ _ h => two_kg (fun _ _ h => h.1.2.2.2.2.1) h) fun _ _ h => h)
    fun I _ s h L ⟨hf, hL⟩ => WP.mono (dPart_k h L.E_lt hf.2.2.2.2.1 hL L.L_lt) fun _ ⟨ht, f, d⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, d⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-! ### `RsaKeyGen.AArch64.Key.Small`, which this module and modules that import it used -/

section

/-!
# An RSA key from its primes on AArch64: `d` too small

`smallMask`: `x15 := kOk & ` the mask of `d ≤ 2^(64 w)`, by `ltA` against
`[aC] = 2^(64 w) + 1` (`smallMask_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- Word `k` of a number written, from zero. -/
theorem wv_set_k {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : word m B (d + 8 * k) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = wv m B d n + (if k < n then 2 ^ (64 * k) * v.toNat else 0)
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv, wv_set_k v hz hd hk n (by omega_using [hn])]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self, hz]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega_using [hd, hk])).word (by omega_using [hkn]) (by omega_using [hd, hn])]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega_using [hk']]; omega_using []
      · simp [hk', show ¬ k < n + 1 by omega_using [hkn, hk']]

/-- `smallMask`: `x15 := kOk & ` the mask of `d ≤ 2^(64 w)` (`ltA_k` against
`2^(64 w) + 1`). -/
theorem smallMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs smallMask) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.ws.w1; omega_using [hW, this]
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  unfold smallMask
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h (x := 1) (by decide))
    fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  -- Word `w` of `[aC]` set: `[aC] = 2^(64 w) + 1`.
  refine wp_seqs_append (by simp) (by simp [ltA, cmpA]) ?_
  simp only [seqs]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h₁ aC) fun s₂ ⟨⟨h16, h12, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h₁.ws.scr.congr k₂.wr
  have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 w := by
    rw [ofNat_shr1 (by omega_using [hw2])]; congr 1; omega_using [hW]
  have e8 : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega_using [hW, hw2])]
    omega_using []
  have ea : off I.B (slot I.W aC) + BitVec.ofNat 64 (8 * w) = off I.B (slot I.W aC + 8 * w) :=
    VG.Offset.add_add _ _ _
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w))
      (1 : BitVec 64)) (by
    brun [h16, h12, ew, e8, ea, hs₂.st (d := slot I.W aC + 8 * w) (by omega_using [hW, sC]), m₂]
    rfl) (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨m₃, k₃⟩ => ?_
  have o₃ := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * w) (by omega_using [hW, hn, sC])
  rw [← m₃] at o₃
  have f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aC) o₃ (by omega_using []) (by omega_using [hW])
  have h₃ := h₁.step f₃ (all_mut_arr (by decide)) (k₂.trans k₃)
  have c₃ : av I s₃.mem aC = 2 ^ (64 * w) + 1 := by
    have hz : word s₁.mem I.B (slot I.W aC + 8 * w) = 0 := by
      have e := VG.Proof.Rsa.AArch64.wv_low (m := s₁.mem) (B := I.B) (e := slot I.W aC) (w := I.W + 2) (by omega_using [])
      rw [c₁] at e
      have h0 : wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1)) with h0 | h0
        · exact h0
        · have := Nat.le_mul_of_pos_right (2 ^ 64) h0; omega_using [e]
      have := (wv_eq_zero_iff _ _ _ _).mp h0 (w - 1) (by omega_using [hW])
      rwa [show slot I.W aC + 8 + 8 * (w - 1) = slot I.W aC + 8 * w by omega_using [hw1]] at this
    have hv1 : av I s₁.mem aC = 1 := av_of_full c₁ (lt_pow_W h (by decide))
    dsimp only [av] at hv1 ⊢
    rw [m₃, wv_set_k (1 : BitVec 64) hz (by omega_using [hn, sC]) (by omega_using [hW, hw1]) I.W (Nat.le_refl _), hv1, ite_eq_left (by omega_using [hW, hw1])]
    simp; omega_using []
  have vD : av I s₃.mem aDd = av I s.mem aDd := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ]
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₃ (a := aDd) (b := aC) (by decide)
    (by decide)) fun s₄ ⟨h₄, m₄, h15, _, _⟩ => ?_)
  rw [vD, c₃] at h15
  simp only [seqs]
  have hok₄ : word s₄.mem I.B (8 * kOk) = mask ok := by
    rw [m₄, f₃.word (by decide) (by decide) (by decide), f₁.word (by decide) (by decide) (by decide), hok]
  have hld := h₄.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  have hd : decide (av I s.mem aDd < 2 ^ (64 * w) + 1) = decide (av I s.mem aDd ≤ 2 ^ (64 * w)) :=
    decide_eq_decide.mpr Nat.lt_succ_iff
  rw [hd] at h15
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun t => t.gpr .x15 = mask (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) ∧
    t.mem = s₄.mem) (by
      brun [h₄.ws.x0, hdr_enc (show kOk < 32 by decide), hld, hok₄, h15, mask_and'])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h15t, m⟩, k⟩ => ?_
  have f' : KF I.B I.W [.arr aC] s₁.mem t.mem := by rw [m, m₄]; exact f₃
  exact ⟨h₄.regs m k, (f₁.trans f').mono (by simp), h15t⟩

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-!
# An RSA key from its primes on AArch64: constant time, `d` too small

`smallMask` (`smallMask_ct`): the constant 1, word `w` of `[aC]` set
(`smallBlk_k`, whose base the taint analysis sees from `w` and the stride),
`ltA`, and `kOk` and'ed in; the facts after it from `smallMask_k`
(`KG FF`, which is `KFront` but for `KS`). The mask in `x15`,
on which the code branches, is the status' (`FF.x15`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-- After `smallMask`: `d` with `kOk`, and the mask of `d` too small in `x15`. -/
abbrev FF : KIn → State → Prop := fun I t => PF I t ∧ DRes I I.E I.L t.mem ∧
  ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.gpr .x15 = mask (decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok)

theorem smallMask_eq : smallMask = constA 1 ++ (([.block (ws ++ (base aC .x16 ++ ([.lsr .x .x3 .x12 1,
    .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1, st .x3 .x16] : List Instr)))] : List (Prog isa)) ++
    (ltA aDd aC ++ ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3]] : List (Prog isa)))) := by
  simp only [smallMask, List.append_assoc]

/-- `smallMask`'s middle block: word `W / 2` of `[aC]` set, for any contents
of `[aC]`. -/
theorem smallBlk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aC .x16 ++ ([.lsr .x .x3 .x12 1, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1,
      st .x3 .x16] : List Instr)))) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem := by
  have hn := h.ws.scr.nowrap
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aC) fun s₂ ⟨⟨h16, h12, _, m₂⟩, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr k₂.wr
  have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 (I.W / 2) := ofNat_shr1 (by omega_using [hw2])
  have e8 : BitVec.ofNat 64 (I.W / 2) <<< 3 = BitVec.ofNat 64 (8 * (I.W / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show I.W / 2 < 2 ^ 64 by omega_using [hw2])]
    omega_using []
  have ea : off I.B (slot I.W aC) + BitVec.ofNat 64 (8 * (I.W / 2)) = off I.B (slot I.W aC + 8 * (I.W / 2)) :=
    VG.Offset.add_add _ _ _
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC + 8 * (I.W / 2)))
      (1 : BitVec 64)) (by
    brun [h16, h12, ew, e8, ea, hs₂.st (d := slot I.W aC + 8 * (I.W / 2)) (by omega_using [sC]), m₂]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨m₃, k₃⟩ => ?_
  exact h.arrW (j := aC) (by decide) (by omega_using []) (by omega_using []) ⟨_, m₃⟩ (k₂.trans k₃)

/-- `smallMask` leaks the same in runs with the same public data, and leaves
`FF` (`smallMask_k`). -/
theorem smallMask_ct : RelCT isa (Two (KG DF)) (seqs smallMask) (Two (KG FF)) := by
  refine kg_ct ?_ fun I _ s h L ⟨hf, ok, hok, hiff, hdd⟩ => ?_
  · refine RelCT.mono (P := Two (KG NF)) ?_ (fun _ _ h => two_kg (fun _ _ _ => trivial) h) fun _ _ h => h
    rw [smallMask_eq]
    refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (by decide) (stab_nf _ _) (by taint_decide)
      (by taint_decide)) ?_
    refine kg_app0 (G := NF) (by simp) (by simp [ltA, cmpA]) (show RelCT isa _ (seqs [.block _]) _ from
      kg_wsb0 (by taint_decide)) (fun I _ s h _ _ => WP.mono (smallBlk_k h) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
    exact rs_app (by simp [ltA, cmpA]) (by simp) (ltA_ct (G := NF) (by decide) (by decide)
      (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide))
      (show RelCT isa _ (seqs [.block _]) _ from two_taint [.x0] (pins_kg NF) (by taint_decide))
  · have e8 : 64 * (I.pl / 8) = 8 * I.pl := by have := L.pl8; omega_using [this]
    refine WP.mono (smallMask_k h L.W hok) fun t ⟨ht, f, h15⟩ => ?_
    have hw : word t.mem I.B (8 * kOk) = mask ok := (f.word (by decide) (by decide) (by decide)).trans hok
    have hD : av I t.mem aDd = av I s.mem aDd := f.av (by decide) (by decide) (by decide) h.hZ
    refine ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f,
      ⟨ok, hw, hiff, fun d hd => hD.trans (hdd d hd)⟩, ok, hw, hiff, ?_⟩
    rw [h15, hD, e8]

/-- The status 2: `d` exists and is at most `2^(8 pl)`. -/
theorem KIn.st_two {I : KIn} : I.st = 2 ↔ ∃ d, Spec.Rsa.inverse I.E I.L = some d ∧ d ≤ 2 ^ (8 * I.pl) := by
  have hW : 8 * I.pl = 16 * I.pl / 2 := by omega_using []
  have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
    by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
  simp only [KIn.st]
  constructor
  · intro h2
    unfold Proof.RsaKeyGen.keyOp at h2
    generalize hk : Spec.RsaKeyGen.keyFromPrimes (16 * I.pl) (Spec.Rsa.os2ip I.eb) (Spec.Rsa.os2ip I.pb)
      (Spec.Rsa.os2ip I.qb) = r at h2
    unfold Spec.RsaKeyGen.keyFromPrimes at hk
    rw [hswap] at hk
    dsimp only at hk
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, ← hW] at hk
    rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
    · rw [hi] at hk; subst hk; simp [Proof.RsaKeyGen.keyStatus] at h2
    · rw [hi] at hk
      dsimp only at hk
      by_cases hd : d ≤ 2 ^ (8 * I.pl)
      · exact ⟨d, rfl, hd⟩
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hd)] at hk
        obtain ⟨x, rfl⟩ : ∃ x, r = .inl x := by
          rw [← hk]
          split
          · exact ⟨_, rfl⟩
          · split <;> exact ⟨_, rfl⟩
        cases x <;> simp [Proof.RsaKeyGen.keyStatus] at h2
  · rintro ⟨d, hd, hsm⟩
    have hr : Spec.RsaKeyGen.keyFromPrimes (16 * I.pl) (Spec.Rsa.os2ip I.eb) (Spec.Rsa.os2ip I.pb)
        (Spec.Rsa.os2ip I.qb) = .inr () := by
      unfold Spec.RsaKeyGen.keyFromPrimes
      rw [hswap]
      dsimp only
      rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, ← hW]
      dsimp only
      rw [ite_eq_left hsm]
    unfold Proof.RsaKeyGen.keyOp
    rw [hr]
    rfl

/-- The branch's mask is the status' (x86-64's `front_zf`). -/
theorem FF.x15 {I : KIn} {t : State} (h : FF I t) : t.gpr .x15 = mask (decide (I.st = 2)) := by
  obtain ⟨-, ⟨_, _, _, hdd⟩, ok, _, hiff, h15⟩ := h
  rw [h15]
  refine congrArg mask ?_
  cases hc : ok
  · rw [hc] at hiff
    rw [Bool.and_false]
    refine (decide_eq_false fun h => ?_).symm
    obtain ⟨d, hd, _⟩ := KIn.st_two.mp h
    exact absurd (hiff.mp ⟨d, hd⟩) (by simp)
  · rw [hc] at hiff
    obtain ⟨d, hd⟩ := hiff.mpr rfl
    rw [Bool.and_true, hdd d hd]
    exact decide_eq_decide.mpr ⟨fun h => KIn.st_two.mpr ⟨d, hd, h⟩, fun h => by
      obtain ⟨d', hd', h'⟩ := KIn.st_two.mp h
      rw [hd] at hd'; cases hd'; exact h'⟩

end VG.Proof.RsaKeyGen.AArch64.Key
