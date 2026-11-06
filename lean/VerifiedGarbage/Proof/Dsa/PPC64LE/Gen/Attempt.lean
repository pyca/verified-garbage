module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.QPart
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PLoop
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GPart
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.CheckPart
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.SeedSuffix
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.CheckCall
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Hash
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets

/-! # DSA parameter generation on PPC64LE: a seed

`attempt_vp`: q from the seed and its test, the search for p, the search for
g over the window after p's witnesses and the check, as
`VG.Proof.Dsa.Generation.refillAttempt` describes them: `fStatus` := 2 when
`rand` runs out, 1 with p‖q‖g at `sPacked` when the domain passes, and
`fUsed` the octets read.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Dsa.Generation (windowCandidates generatorCount refillAttempt)

/-! ## The result of a seed -/

/-- The search for g over the window after p's witnesses `r`, and the check:
`refillAttempt`'s last stage. -/
def winResult (pLen p q : Nat) (r : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.generator p q (windowCandidates pLen Spec.Dsa.generatorAttempts r) with
  | none =>
    if Spec.Dsa.generatorAttempts * pLen ≤ r.length then some (none, r.drop (Spec.Dsa.generatorAttempts * pLen))
    else none
  | some g =>
    some (if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none,
      r.drop (pLen * generatorCount p q (windowCandidates pLen Spec.Dsa.generatorAttempts r)))

/-- The search for p from the seed, then `winResult`. -/
def primeRes (pLen qLen q : Nat) (seed r : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) q seed r with
  | none => none
  | some (none, r') => some (none, r')
  | some (some p, r') => winResult pLen p q r'

theorem refillAttempt_eq (pLen qLen : Nat) (seed rest : List Byte) :
    refillAttempt pLen qLen seed rest =
      match Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * qLen) seed) rest with
      | none => none
      | some (false, r) => some (none, r)
      | some (true, r) => primeRes pLen qLen (Spec.Dsa.qCandidate (8 * qLen) seed) seed r := by
  unfold refillAttempt primeRes winResult
  rfl

theorem generatorCount_none {p q : Nat} :
    ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none → generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, e => by
    rw [VG.Proof.Dsa.Generation.generator_cons'] at e
    simp only [generatorCount, List.length_cons]
    split at e
    · cases e
    · next hh => rw [ite_eq_right_of_eq_false _ _ (eq_false hh), generatorCount_none e]

theorem take_window {l : List Byte} {n : Nat} : l.take (min l.length n) = l.take n := by
  rcases Nat.le_total l.length n with h | h
  · rw [Nat.min_eq_left h, List.take_length, List.take_of_length_le h]
  · rw [Nat.min_eq_right h]

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The search's stage at the seed at `k`, with `n` seeds left: the cursor
`fC`, `fSeed`, `fSeedLeft`, `fStatus` and the padding. -/
abbrev aBase (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 64) : Cfg :=
  (((({ cl := [(sMsg + G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 64 k)).setV fSeed
    (G.seeds + BitVec.ofNat 64 k)).setV fSeedLeft n).setV fStatus 0

/-- The stage after a seed. -/
def aOut (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 64) : Option (Option Spec.Dsa.Params × List Byte) → Cfg
  | none => (aBase G HO k n).setV fStatus 2
  | some (none, rest) => (aBase G HO k n).setV fUsed (BitVec.ofNat 64 (G.witLen - rest.length))
  | some (some a, rest) =>
    (({ aBase G HO k n with cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] }).setV fUsed
      (BitVec.ofNat 64 (G.witLen - rest.length))).setV fStatus 1

theorem aBase_LS (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 64) :
    (aBase G HO k n).LS = [fStatus, fSeedLeft, fSeed, fC] := rfl

theorem aBase_pnot (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 64) : PNot (aBase G HO k n) := by
  simp only [PNot]; decide

/-- The stage after p from the seed at `k`, with the witnesses up to `rest` read. -/
abbrev aPCfg (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 64) (p : Nat) (rest : List Byte) : Cfg :=
  ((pFound (aBase G HO k n) HO G k p).setV fUsed (BitVec.ofNat 64 (G.witLen - rest.length))).setV fP 1

/-- The window: `fHs` := `rand + w`, `fHsLen` := its length. -/
theorem gWindow_vp {g : Geo} (hg : g.pLen = G.pLen) {c : Cfg} {w : Nat} (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 64 w) (hw : w ≤ G.witLen) (h64 : G.witLen < 2 ^ 64) :
    VP (St G c X) g.gWindow
      (St G ((c.setV fHs (G.wit + BitVec.ofNat 64 w)).setV fHsLen
        (BitVec.ofNat 64 (min (G.witLen - w) (G.pLen * 2 ^ 7)))) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  unfold Geo.gWindow
  rw [hg]
  refine VP.seq (G := fun σ s => St G (c.setV fHs (G.wit + BitVec.ofNat 64 w)) X σ s ∧
      s.gpr .r3 = BitVec.ofNat 64 (G.witLen - w) ∧ s.gpr .r4 = BitVec.ofNat 64 (G.pLen * 2 ^ 7) ∧
      isa.eval (.zero .d .r0) s = some (decide (G.witLen - w < G.pLen * 2 ^ 7))) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28]) (.block ([ld .r3 fWit, ld .r4 fUsed, .add .r3 .r3 .r4, st .r3 fHs, ld .r3 fWitLen,
        .sub .r3 .r3 .r4] ++ shl .r4 G.pLen 7 ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
      fun σ s ⟨h, x⟩ => ?_
    rw [List.append_assoc]
    simp only [List.cons_append, List.nil_append]
    refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
      fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.gi.slotV hU).trans hUv) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine h₂.wrK exec_add (by decide) fun s₃ h₃ u₃ => ?_
    have e3 : s₃.gpr .r3 = G.wit + BitVec.ofNat 64 w := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
    refine h₃.stF (o := fHs) (varOk_of (by decide)) fun s₄ h₄ m₄ _ => ?_
    rw [e3] at h₄
    refine h₄.ldK (o := fWitLen) (by decide) (by decide) (h₄.gi.fixedV (v := BitVec.ofNat 64 G.witLen) (by simp [fixedWords])) (by decide)
      fun s₅ h₅ u₅ => ?_
    refine h₅.wrK exec_sub (by decide) fun s₆ h₆ u₆ => ?_
    have e6 : s₆.gpr .r3 = BitVec.ofNat 64 (G.witLen - w) := by
      rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.gpr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    refine shl_ok h₆ (r := .r4) (by decide) hp15 (by decide) fun s₇ h₇ K₇ e₇ _ => ?_
    refine ltR_ok (by rw [K₇.gpr (by decide), e6]) e₇ fun t K m sp _ e =>
      WP.block_nil ⟨⟨h₇.of_keep K m sp, x⟩, ?_, ?_, ?_⟩
    · rw [K.gpr (by decide), K₇.gpr (by decide), e6]
    · rw [K.gpr (by decide), e₇]
    · refine e.trans ?_
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by rcases l with e | e | e <;> rw [e] <;> decide)]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2]) ?_ ?_
  · refine st_vp (c := fun _ => c.setV fHs (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1.1.1)
      (varOk_of (by decide)) fun σ s t ⟨⟨⟨_, x⟩, r3, _, e⟩, z⟩ h' _ => ⟨?_, x⟩
    have hl : G.witLen - w < G.pLen * 2 ^ 7 := by rw [e] at z; simpa using z
    rw [r3] at h'
    rw [Nat.min_eq_left (Nat.le_of_lt hl)]; exact h'
  · refine st_vp (c := fun _ => c.setV fHs (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1.1.1)
      (varOk_of (by decide)) fun σ s t ⟨⟨⟨_, x⟩, _, r4, e⟩, z⟩ h' _ => ⟨?_, x⟩
    have hl : ¬G.witLen - w < G.pLen * 2 ^ 7 := by rw [e] at z; simpa using z
    rw [r4] at h'
    rw [Nat.min_eq_right (by omega)]; exact h'

/-- `fUsed` := past the candidates the search for g read. -/
theorem gUsed_vp {c : Cfg} {x : Nat} (hH : fH ∈ c.LS) (hHv : c.V fH = G.wit + BitVec.ofNat 64 x) :
    VP (St G c X) (.block Geo.gUsed) (St G (c.setV fUsed (BitVec.ofNat 64 x)) X) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block Geo.gUsed), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x'⟩ => ?_
  refine h.ldK (o := fH) (by decide) (by decide) ((h.gi.slotV hH).trans hHv) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fWit) (by decide) (by decide) (h₁.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
    fun s₂ h₂ u₂ => ?_
  refine h₂.wrK exec_sub (by decide) fun s₃ h₃ u₃ => ?_
  have e3 : s₃.gpr .r3 = BitVec.ofNat 64 x := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, BitVec.add_comm, BitVec.add_sub_cancel]
  refine h₃.stF (o := fUsed) (varOk_of (by decide)) fun t ht _ _ => WP.block_nil ⟨?_, x'⟩
  rw [e3] at ht; exact ht

/-- Without a g: `fStatus` := 2 if the window was short. -/
theorem gShort_vp {g : Geo} (hg : g.pLen = G.pLen) {c : Cfg} {HL : Nat} (hL : fHsLen ∈ c.LS)
    (hLv : c.V fHsLen = BitVec.ofNat 64 HL) (h64 : HL < 2 ^ 64) :
    VP (St G c X) g.gShort (St G (if HL < G.pLen * 2 ^ 7 then c.setV fStatus 2 else c) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  unfold Geo.gShort
  rw [hg]
  refine VP.seq (G := fun σ s => St G c X σ s ∧ isa.eval (.zero .d .r0) s = some (decide (HL < G.pLen * 2 ^ 7)))
    (ltShl_vp (c := fun _ => c) (x := BitVec.ofNat 64 HL) (fun σ s h => h.1) (by decide) (by decide) hp15
      (by decide) (by rcases l with e | e | e <;> rw [e] <;> decide) (fun σ s h => (h.1.gi.slotV hL).trans hLv)
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]⟩) ?_
  by_cases hs : HL < G.pLen * 2 ^ 7
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => c) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hs] at z)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
    exact VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hs] at z)
      (VP.block_nil fun σ s h => h.1.1)

/-- The search for g over the window after `rest` and the check, after p. -/
theorem attemptG_vp {g : Geo} (HO : HashOk Gh) (gcert : CertC G.pLen G.qLen) (hck : CheckOk g.checkCode)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hL : HO.P.L = 8) (hwl : G.witB.length = G.witLen) (h64 : G.witLen < 2 ^ 64)
    {k p : Nat} {n : BitVec 64} {rest : List Byte} (hrest : G.witB.drop (G.witLen - rest.length) = rest)
    (hpd : VG.Proof.Dsa.Generation.PDomain G.pLen p)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aPCfg G HO k n p rest) X)
      (seqs [g.gWindow, g.gPart, .block Geo.gUsed, .block (cmpF fG 1), .ite (.zero .d .r0) g.checkPart g.gShort])
      (St G (aOut G HO k n (winResult G.pLen p (Spec.Dsa.decodeBE (qBytes G k)) rest)) X) := by
  have hlq' : Spec.Dsa.generationLengthsValid G.pLen G.qLen := hlq
  have hq0 : 0 < G.qLen := by omega
  have hq32 : G.qLen ≤ 32 := by omega
  have hl384 : G.pLen ≤ 384 := by omega
  have hrl : rest.length ≤ G.witLen := by
    have := congrArg List.length hrest; simp only [List.length_drop, hwl] at this; omega
  generalize hqv : Spec.Dsa.decodeBE (qBytes G k) = qv at hqlo ⊢
  have qpos : 0 < qv := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  have pl := padTail_length HO.md (n := G.qLen) (by omega) hL
  -- (p − 1) / q fits its octets.
  have hev : (p - 1) / qv < 256 ^ eBytes G.pLen G.qLen := by
    have hp := hpd.upper
    rw [show (256 : Nat) ^ eBytes G.pLen G.qLen = 2 ^ (8 * eBytes G.pLen G.qLen) from (Nat.pow_mul 2 8 _).symm]
    refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul qpos).mpr ?_) (Nat.pow_le_pow_right (by decide)
      (show 8 * G.pLen - 8 * G.qLen + 1 ≤ 8 * eBytes G.pLen G.qLen by simp only [eBytes]; omega))
    calc p - 1 < 2 ^ (8 * G.pLen) := by omega
      _ = 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * 2 ^ (8 * G.qLen - 1) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * qv := Nat.mul_le_mul_left _ hqlo
  have hpv : p < 256 ^ G.pLen := by
    rw [show (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) from (Nat.pow_mul 2 8 _).symm]; exact hpd.upper
  generalize hw : G.witLen - rest.length = w at hrest
  generalize hHL : min (G.witLen - w) (G.pLen * 2 ^ 7) = HL
  let c₁ : Cfg := ((aPCfg G HO k n p rest).setV fHs (G.wit + BitVec.ofNat 64 w)).setV fHsLen (BitVec.ofNat 64 HL)
  have R : GReq G c₁ p ((p - 1) / qv) := by
    refine ⟨by simp [c₁], by simp [c₁, pAp, KU, VG.Proof.Rsa.KeyWorkspace.upd, aP, aE, aPm1], by simp [c₁],
      by simp [c₁, pAp, KU, VG.Proof.Rsa.KeyWorkspace.upd, aP, aE, aPm1, aOne], by simp [c₁],
      by simp [c₁, pAp, KU, VG.Proof.Rsa.KeyWorkspace.upd, aP, aE, aPm1, aOne, aZero],
      by simp [c₁, aH, aP, aE, aPm1, aOne, aZero], by simp [c₁, aTmp, aP, aE, aPm1, aOne, aZero], rfl, by simp [c₁],
      hpv, by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega); omega,
      hpd.odd, by simp [c₁, hqv], hev, fun x hx => ?_, by simp [c₁]; decide, by simp [c₁]; decide⟩
    simp only [c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, Apart, sE, sG, pB, eBytes]; omega
    · simp only [VG.Proof.Rsa.i2osp_length, Apart, sPBE, sG, pB]; omega
    · simp only [pl, Apart, sMsg, sG, pB]; omega
    · simp only [hql, Apart, sQ, sG, pB]; omega
  have hHL64 : HL < 2 ^ 64 := by omega
  have hwHL : w + HL ≤ G.witLen := by omega
  refine VP.seq (G := St G c₁ X) ((gWindow_vp (w := w) hp (by simp) (by simp [upd, fP, fUsed, ← hw]) (by omega) h64).mono
    (fun _ _ h => h) fun σ s h => by rw [hHL] at h; exact h) ?_
  refine VP.seq (gPart_vp (c := c₁) (pv := p) (ev := (p - 1) / qv) (qv := qv) (w := w) (HL := HL) hp hq gcert R
    (by simp [c₁]) (by simp [c₁, upd, fHs, fHsLen]) (by simp [c₁]) (by simp [c₁]) hwHL hwl hHL64 rfl) ?_
  -- The window's candidates are the spec's.
  have hcand : gCands G w HL 0 = windowCandidates G.pLen Spec.Dsa.generatorAttempts rest := by
    simp only [gCands, hsW, Nat.zero_mul, List.drop_zero, hrest, windowCandidates]
    rw [← hHL, show G.witLen - w = rest.length by omega, take_window,
      show G.pLen * 2 ^ 7 = Spec.Dsa.generatorAttempts * G.pLen by simp only [Spec.Dsa.generatorAttempts]; omega]
  have hcnt : gNum G w HL p qv 0 * G.pLen ≤ rest.length := by
    have h1 := VG.Proof.Dsa.Generation.generatorCount_le p qv (gCands G w HL 0)
    have h2 : (gCands G w HL 0).length * G.pLen ≤ rest.length := by
      rw [hcand]
      simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range]
      exact Nat.le_trans (Nat.div_mul_le_self _ _) (by simp only [List.length_take]; exact Nat.min_le_right _ _)
    exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
  unfold winResult
  rw [← hcand]
  rcases hgv : Spec.Dsa.generator p qv (gCands G w HL 0) with _ | gv
  · -- No g: a short window ran out.
    have hfin : gFin c₁ G w HL p qv = (c₁.setV fG 2).setV fH
        (G.wit + BitVec.ofNat 64 (w + gNum G w HL p qv 0 * G.pLen)) := by simp only [gFin, gRes, hgv]
    rw [hfin]
    refine VP.seq (gUsed_vp (x := w + gNum G w HL p qv 0 * G.pLen) (by simp) (by simp [upd])) ?_
    refine VP.seq (G := fun σ s => St G (((c₁.setV fG 2).setV fH
        (G.wit + BitVec.ofNat 64 (w + gNum G w HL p qv 0 * G.pLen))).setV fUsed
          (BitVec.ofNat 64 (w + gNum G w HL p qv 0 * G.pLen))) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fG, fH, fUsed]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine (gShort_vp hp (HL := HL) (by simp [c₁]) (by simp [c₁, upd, fHsLen, fG, fH, fUsed]) hHL64).mono
      (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    have hnum : gNum G w HL p qv 0 = (gCands G w HL 0).length :=
      generatorCount_none hgv
    by_cases hs : HL < G.pLen * 2 ^ 7
    · have hshort : ¬Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega
      simp only [hs, hshort, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed, fC]⟩
      · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [c₁, pRest]
    · have hfull : Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega
      have hHLv : HL = G.pLen * 2 ^ 7 := by omega
      have hlen : (gCands G w HL 0).length = 128 := by
        rw [hcand]
        simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range,
          List.length_take, Spec.Dsa.generatorAttempts]
        rw [Nat.min_eq_left (by omega), Nat.mul_div_cancel _ (by omega)]
      simp only [hs, hfull, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl
        · refine ⟨by simp, ?_⟩
          simp only [upd, ↓reduceIte, List.length_drop, hnum, hlen, Spec.Dsa.generatorAttempts]
          congr 1; omega
        all_goals exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft,
          fSeed, fC]⟩
      · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [c₁, pRest]
  · -- g: the check.
    have hgb := VG.Proof.Dsa.Generation.generator_bounds (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hpd.lower) _ hgv
    have hpl8 : (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) := by rw [Nat.pow_mul]
    have hql8 : (256 : Nat) ^ G.qLen = 2 ^ (8 * G.qLen) := by rw [Nat.pow_mul]
    have qlt : qv < 2 ^ (8 * G.qLen) := by
      rw [← hqv, ← hql8, ← hql]; exact VG.Proof.Dsa.decodeBE_lt _
    have hpk : pkOf (Spec.Rsa.i2osp p G.pLen) (qBytes G k) (Spec.Rsa.i2osp gv G.pLen) =
        Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩ := by
      have hqb : qBytes G k = Spec.Rsa.i2osp qv G.qLen := by
        rw [← hqv, ← VG.Proof.Dsa.encodeBE_i2osp, ← hql, VG.Proof.Dsa.encodeBE_decodeBE]
      simp only [pkOf, Spec.Dsa.encodeParams, VG.Proof.Dsa.encodeBE_i2osp, hqb]
    have hok : Spec.Dsa.checkParametersBytes G.pLen G.qLen
        (pkOf (Spec.Rsa.i2osp p G.pLen) (qBytes G k) (Spec.Rsa.i2osp gv G.pLen)) =
        decide (Spec.Dsa.parametersValid ⟨p, qv, gv⟩) := by
      rw [hpk]
      exact VG.Proof.Dsa.Generation.check_encodedParams (by
          unfold Spec.Dsa.lengthsValid; omega)
        (by rw [hpl8]; exact hpd.upper) (by rw [hql8]; exact qlt) (by rw [hpl8]; exact Nat.lt_trans hgb.2 hpd.upper)
    let xu := w + gNum G w HL p qv 0 * G.pLen
    let Dg : Cfg := ((({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 64 xu)).setV fUsed (BitVec.ofNat 64 xu)
    have hfin : gFin c₁ G w HL p qv = (({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV
        fH (G.wit + BitVec.ofNat 64 xu) := by simp only [gFin, gRes, hgv, xu]
    rw [hfin]
    refine VP.seq (G := St G Dg X) (gUsed_vp (x := xu) (by simp) (by simp [upd])) ?_
    refine VP.seq (G := fun σ s => St G Dg X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [Dg])).trans (by simp [Dg, upd, fG, fH, fUsed]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    refine (checkPart_vp (c := Dg) (X := X) hp hq hck (pB := Spec.Rsa.i2osp p G.pLen) (qB := qBytes G k)
      (gB := Spec.Rsa.i2osp gv G.pLen) (by simp [Dg, c₁, pRest]) (by simp [Dg, c₁, pRest]) (by simp [Dg])
      (VG.Proof.Rsa.i2osp_length _ _) hql (VG.Proof.Rsa.i2osp_length _ _) (fun x hx => ?_)).mono
      (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    · simp only [Dg, c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length, sG, sPacked]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length, sE, sPacked, eBytes]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sPacked]; omega_arith
      · simp only [pl, sPacked, sMsg]; omega
      · simp only [hql, sQ, sPacked]; omega_arith
    have hU : G.witLen - (rest.drop (G.pLen * gNum G w HL p qv 0)).length = xu := by
      simp only [List.length_drop, xu]; rw [Nat.mul_comm G.pLen]; omega
    rw [hok] at h
    by_cases hv : Spec.Dsa.parametersValid ⟨p, qv, gv⟩
    · simp only [hv, decide_true, ckCfg, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut, hU]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg, c₁], by simp [Dg, c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed, fC]⟩
      · change y ∈ [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩)] at hy
        rw [List.mem_singleton] at hy; subst hy; rw [← hpk]; simp
    · simp only [hv, decide_false, ckCfg, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut, hU]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg, c₁], by simp [Dg, c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed, fC]⟩
      · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [Dg, c₁, pRest]

/-- The stage after q passes, with the witnesses up to `r` read. -/
abbrev aQCfg (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 64) (u : Nat) (r : List Byte) : Cfg :=
  testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) (qClaims HO.md G k) G.witLen (some (true, r))

/-- The candidates of the counters are the spec's. -/
theorem pCand_spec (HO : HashOk Gh) {k : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hk4 : 4 * Gh.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen) (hk : k + G.qLen ≤ G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen) (j : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j := by
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega
  have hc : G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  refine pCandidate_xBytes HO (fun i => ?_) hH hsl hlen (by omega) hc _
  rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, HO.hN, hk4]

/-- The search for p, then g and the check, after q. -/
theorem attemptP_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (lay : PLay G g Lp) (gcert : CertC G.pLen G.qLen) (hck : CheckOk g.checkCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (h64 : G.witLen < 2 ^ 64)
    {k u : Nat} {n : BitVec 64} {r : List Byte} (hk : k + G.qLen ≤ G.seedsLen)
    (hr : G.witB.drop (G.witLen - r.length) = r)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aQCfg G HO k n u r) X)
      (seqs [g.pPart, .block (cmpF fP 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 2))
          (seqs [.block (cmpF fP 1),
            .ite (.zero .d .r0)
              (seqs [g.gWindow, g.gPart, .block Geo.gUsed, .block (cmpF fG 1),
                .ite (.zero .d .r0) g.checkPart g.gShort])
              (.block [])])])
      (St G (aOut G HO k n (primeRes G.pLen G.qLen (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r)) X) := by
  have hlq' : Spec.Dsa.generationLengthsValid G.pLen G.qLen := hlq
  have hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega
  have pl := padTail_length HO.md (n := G.qLen) (by omega) HO.hL
  refine VP.seq (pPart_vp (c := aBase G HO k n) (u0 := G.witLen - r.length) (d := aQCfg G HO k n u r) HO okp lay hlq
    hp hq hk4 hsb hH hwl (aBase_pnot G HO k n) hk (by simp) (by simp [upd, fSeed, fStatus, fSeedLeft])
    (by omega) (pCand_spec HO hlq hk4 hsb hk hH hlen) (by simp [testCfg])
    (by simp [testCfg, upd]) (fun o ho => ⟨by simp [testCfg, ho], by
      change o ∈ [fStatus, fSeedLeft, fSeed, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp [testCfg, upd, fUsed, fRes, fStatus, fSeedLeft, fSeed, fC]⟩)
    (by simp [testCfg, qClaims]) (by simp [testCfg, qClaims])) ?_
  have hS0 : pSpec HO G k (G.witLen - r.length) 0 = Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r := by
    rw [pSpec, VG.Proof.Dsa.Generation.primeSearch_start, pU, hr]
  rw [hS0]
  unfold primeRes
  rcases hR : Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r
    with _ | ⟨_ | p, r'⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G ((pNone (aBase G HO k n) HO G).setV fP 0) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨by simpa [pFin] using h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => (pNone (aBase G HO k n) HO G).setV fP 0) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fP, fStatus, fSeedLeft, fSeed, fC]⟩
  · -- No p: the next seed.
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k n) HO G).setV fUsed
        (BitVec.ofNat 64 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨by simpa [pFin] using h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k n) HO G).setV fUsed
        (BitVec.ofNat 64 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.gi.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨_, x⟩, _⟩, _⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fUsed, fP, fStatus, fSeedLeft, fSeed, fC]⟩
  · -- p: g and the check.
    have hpd := VG.Proof.Dsa.Generation.primeSearch_domain hw hlen _ _ _ _ hR
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k n p r') X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k n p r') X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.gi.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨_, x⟩, _⟩, _⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptG_vp HO gcert hck hp hq hlq HO.hL hwl h64 (rest := r') (by
        rw [← hwl]; exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.primeSearch_suffix _ _ _ hR).trans (hr ▸ List.drop_suffix _ _)))
        hpd hql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

/-- Where the test of q puts its candidate and working ranges. -/
structure QLay (G : GP) (g : Geo) (Lq : Impl.Dsa.ProbablePrime.Layout) : Prop where
  bits : Lq.bits = 8 * G.qLen
  cand : Lq.candidate = g.qCand
  size : Lq.size ≤ 8 * wWords G.pLen
  scratch : ∀ r ∈ Lq.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen
  candFit : Lq.candidate + Lq.bits / 8 ≤ 8 * wWords G.pLen
  cand15 : wB G.pLen + Lq.candidate < 2 ^ 15

/-- A seed: q, its test, then p, g and the check. -/
theorem attempt_vp {g : Geo} (HO : HashOk g.G) {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (okq : PrimeOk Lq g.qCode)
    (qlay : QLay G g Lq) (okp : PrimeOk Lp g.pCode) (lay : PLay G g Lp) (gcert : CertC G.pLen G.qLen)
    (hck : CheckOk g.checkCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (h64 : G.witLen < 2 ^ 64)
    {k u : Nat} {n : BitVec 64} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) X) g.attempt
      (St G (aOut G HO k n (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) := by
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by have := hlen (seedAt G k); omega
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega
  have ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega) _ (by rw [hHq])
  have hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega) (seedAt G k)).2.1
  unfold Geo.attempt
  refine VP.seq (qPart_vp (c := (aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) HO okq hlq hp hq hk4 hH hwl hsb
    qlay.bits qlay.cand qlay.size qlay.scratch qlay.candFit qlay.cand15 hk hu (by simp) (by simp [upd, fUsed, fSeed, fStatus, fSeedLeft]) (by simp)
    (by simp [upd]) (by simp; decide) (by simp; decide) (by simp)) ?_
  rw [refillAttempt_eq]
  rcases hpp : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u)
    with _ | ⟨_ | _, r⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) (qClaims HO.md G k)
        G.witLen none) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [testCfg])).trans (by simp [testCfg, upd]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) (qClaims HO.md G k)
        G.witLen none) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
    · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q is not prime: the next seed.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.gi.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨_, x⟩, _⟩, _⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
    · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q: p, g and the check.
    have hr : G.witB.drop (G.witLen - r.length) = r := by
      rw [← hwl]; exact VG.Proof.Dsa.Generation.probablePrime_cursor hpp
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k n u r) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k n u r) X σ s ∧ isa.eval (.zero .d .r0) s = some true)
      (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.gi.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨_, x⟩, _⟩, _⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩) ?_
    rw [← hqv]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptP_vp HO okp lay gcert hck hlq hp hq hk4 hsb hH hwl hlen h64 hk hr ql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

end

end VG.Proof.Dsa.PPC64LE.Gen
