module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PLoop
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GPart
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.CheckPart
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
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: a seed

`attempt_vp`: q from the seed and its test, the search for p, the search for
g over the window after p's witnesses and the check, as
`VG.Proof.Dsa.Generation.refillAttempt` describes them: `fStatus` := 2 when
`rand` runs out, 1 with p‖q‖g at `sPacked` when the domain passes, and
`fUsed` the octets read.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (Rest Upd wp_dp op2_reg dpVal)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
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
abbrev aBase (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) : Cfg :=
  (((({ cl := [(G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 32 k)).setV fSeed
    (G.seeds + BitVec.ofNat 32 k)).setV fSeedLeft n).setV fStatus 0

/-- The stage after a seed. -/
def aOut (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) : Option (Option Spec.Dsa.Params × List Byte) → Cfg
  | none => (aBase G HO k n).setV fStatus 2
  | some (none, rest) => (aBase G HO k n).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))
  | some (some a, rest) =>
    (({ aBase G HO k n with cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] }).setV fUsed
      (BitVec.ofNat 32 (G.witLen - rest.length))).setV fStatus 1

theorem aBase_LS (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) :
    (aBase G HO k n).LS = [fStatus, fSeedLeft, fSeed, fC] := rfl

theorem aBase_pnot (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) : PNot (aBase G HO k n) := by
  simp only [PNot]; decide

/-- The stage after p from the seed at `k`, with the witnesses up to `rest` read. -/
abbrev aPCfg (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) (p : Nat) (rest : List Byte) : Cfg :=
  ((pFound (aBase G HO k n) HO G k p).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))).setV fP 1

/-- The window: `fHs` := `rand + w`, `fHsLen` := its length. -/
theorem gWindow_vp {g : Geo} (hg : g.pLen = G.pLen) {c : Cfg} {w : Nat} (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 32 w) (hw : w ≤ G.witLen) :
    VP (St G c X) g.gWindow
      (St G ((c.setV fHs (G.wit + BitVec.ofNat 32 w)).setV fHsLen
        (BitVec.ofNat 32 (min (G.witLen - w) (128 * G.pLen)))) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hb : 128 * G.pLen < 2 ^ 32 := by omega_arith
  let c₁ : Cfg := c.setV fHs (G.wit + BitVec.ofNat 32 w)
  unfold Geo.gWindow
  rw [hg]
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hU).trans hUv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w) ∧ s.gpr .r0 = G.wit)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => h.1.1.fixedV (by simp [fixedWords])) fun σ s t ⟨⟨h, x⟩, r1⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w) ∧
      s.gpr .r0 = G.wit + BitVec.ofNat 32 w)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .add .r0 .r0 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2, h₂.2]
        · rw [h₁.1.2, h₂.1.2])
      fun σ s ⟨⟨⟨h, x⟩, r1⟩, r0⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩,
          by rw [u.gpr, dpVal, r0, r1]⟩) ?_
  refine VP.seq (G := fun σ s => St G c₁ X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w)
    (st_vp (c := fun _ => c) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨_, x⟩, r1⟩, r0⟩ h' R => ⟨⟨by rw [r0] at h'; exact h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  refine VP.seq (G := fun σ s => (St G c₁ X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 w) ∧
      s.gpr .r0 = BitVec.ofNat 32 G.witLen)
    (ld_vp (c := fun _ => c₁) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => h.1.1.fixedV (by simp [fixedWords])) fun σ s t ⟨⟨h, x⟩, r1⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c₁ X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (G.witLen - w) ∧
      s.gpr .r1 = BitVec.ofNat 32 (128 * G.pLen)) ∧ isa.eval .eq s = some (decide (G.witLen - w < 128 * G.pLen)))
    (VP.block_append (G := fun σ s => St G c₁ X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (G.witLen - w) ∧
        s.gpr .r1 = BitVec.ofNat 32 (128 * G.pLen))
      (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
        (.block ([.dp .sub .r0 .r0 (.reg .r1)] ++ cst .r1 0)), rfl⟩
        (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.2, h₂.2]
          · rw [h₁.1.2, h₂.1.2])
        fun σ s ⟨⟨⟨h, x⟩, r1⟩, r0⟩ => ?_)
      (less_vp (x := BitVec.ofNat 32 (G.witLen - w)) (y := BitVec.ofNat 32 (128 * G.pLen)) (fun σ s h => h.2.1)
        (fun σ s h => h.2.2) fun σ s t ⟨⟨h, x⟩, r0, r1⟩ R m e => ⟨⟨⟨h.of_rest R m, x⟩, by rw [R.gpr _ (by decide), r0],
          by rw [R.gpr _ (by decide), r1]⟩, by
            have := h.gi.witLt
            rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
              Nat.mod_eq_of_lt hb]⟩)) ?_
  · have := h.gi.witLt
    simp only [List.cons_append, List.nil_append]
    refine wp_dp (op2_reg _ _) fun s₁ u₁ => ?_
    rw [← List.append_nil (cst .r1 _)]
    refine wp_cst hb fun t u => WP.block_nil ⟨⟨(h.of_rest (u₁.rest (ws := [.r0]) (by simp)) u₁.mem).of_rest
      (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, ?_, u.gpr⟩
    rw [u.other _ (by decide), u₁.gpr, dpVal, r0, r1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · refine st_vp (c := fun _ => c₁) (fun σ s h => h.1.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨⟨_, x⟩, r0, _⟩, e⟩, z⟩ h' _ => ⟨?_, x⟩
    have hl : G.witLen - w < 128 * G.pLen := by rw [e] at z; simpa using z
    rw [r0] at h'
    rw [Nat.min_eq_left (Nat.le_of_lt hl)]; exact h'
  · refine st_vp (c := fun _ => c₁) (fun σ s h => h.1.1.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨⟨⟨_, x⟩, _, r1⟩, e⟩, z⟩ h' _ => ⟨?_, x⟩
    have hl : ¬G.witLen - w < 128 * G.pLen := by rw [e] at z; simpa using z
    rw [r1] at h'
    rw [Nat.min_eq_right (by omega_arith)]; exact h'

/-- `fUsed` := past the candidates the search for g read. -/
theorem gUsed_vp {c : Cfg} {x : Nat} (hH : fH ∈ c.LS) (hHv : c.V fH = G.wit + BitVec.ofNat 32 x) :
    VP (St G c X) Geo.gUsed (St G (c.setV fUsed (BitVec.ofNat 32 x)) X) := by
  unfold Geo.gUsed
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = G.wit + BitVec.ofNat 32 x)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hH).trans hHv)
      fun σ s t ⟨h, x'⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x'⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r0 = G.wit + BitVec.ofNat 32 x) ∧ s.gpr .r1 = G.wit)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => h.1.1.fixedV (by simp [fixedWords])) fun σ s t ⟨⟨h, x'⟩, r0⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x'⟩, by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 x)
    (VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block [.dp .sub .r0 .r0 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x'⟩, r0⟩, r1⟩ => wp_dp (op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x'⟩,
          by rw [u.gpr, dpVal, r0, r1, BitVec.add_comm, BitVec.add_sub_cancel]⟩) ?_
  exact st_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
    fun σ s t ⟨⟨_, x'⟩, r0⟩ h' _ => ⟨r0 ▸ h', x'⟩

/-- Without a g: `fStatus` := 2 if the window was short. -/
theorem gShort_vp {g : Geo} (hg : g.pLen = G.pLen) {c : Cfg} {HL : Nat} (hL : fHsLen ∈ c.LS)
    (hLv : c.V fHsLen = BitVec.ofNat 32 HL) (h32 : HL < 2 ^ 32) :
    VP (St G c X) g.gShort (St G (if HL < 128 * G.pLen then c.setV fStatus 2 else c) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hb : 128 * G.pLen < 2 ^ 32 := by omega_arith
  unfold Geo.gShort
  rw [hg]
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 HL)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hL).trans hLv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G c X σ s ∧ isa.eval .eq s = some (decide (HL < 128 * G.pLen)))
    (VP.block_append (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 HL ∧
        s.gpr .r1 = BitVec.ofNat 32 (128 * G.pLen))
      (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block (cst .r1 0)), rfl⟩
        (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨⟨h, x⟩, r0⟩ => by
          rw [← List.append_nil (cst .r1 _)]
          exact wp_cst hb fun t u => WP.block_nil ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
            by rw [u.other _ (by decide), r0], u.gpr⟩)
      (less_vp (x := BitVec.ofNat 32 HL) (y := BitVec.ofNat 32 (128 * G.pLen)) (fun σ s h => h.2.1)
        (fun σ s h => h.2.2) fun σ s t ⟨⟨h, x⟩, _, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by
          rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt hb]⟩)) ?_
  by_cases hs : HL < 128 * G.pLen
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
theorem attemptG_vp {g : Geo} {n : Nat} (HO : HashOk Gh) (certs : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e) (hL : HO.P.L = 8) (hwl : G.witB.length = G.witLen)
    (h32 : G.witLen < 2 ^ 32)
    {k p : Nat} {n' : BitVec 32} {rest : List Byte} (hrest : G.witB.drop (G.witLen - rest.length) = rest)
    (hpd : VG.Proof.Dsa.Generation.PDomain G.pLen p)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aPCfg G HO k n' p rest) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [g.gWindow, g.gPart, Geo.gUsed, .block (cmpF fG 1), .ite .eq g.checkPart g.gShort])
      (St G (aOut G HO k n' (winResult G.pLen p (Spec.Dsa.decodeBE (qBytes G k)) rest)) X) := by
  have hq0 : 0 < G.qLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hlq1 : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := hpd.width
  have hl384 : G.pLen ≤ 384 := by omega_arith
  have hrl : rest.length ≤ G.witLen := by
    have := congrArg List.length hrest; simp only [List.length_drop, hwl] at this; omega_arith
  generalize hqv : Spec.Dsa.decodeBE (qBytes G k) = qv at hqlo ⊢
  have qpos : 0 < qv := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  -- (p − 1) / q fits the exponent's words.
  have hev : (p - 1) / qv < 2 ^ (32 * g.e) := by
    have hp := hpd.upper
    refine (Nat.div_lt_iff_lt_mul qpos).mpr ?_
    calc p - 1 < 2 ^ (8 * G.pLen) := by omega_arith
      _ = 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * 2 ^ (8 * G.qLen - 1) := by rw [← Nat.pow_add]; congr 1; omega_arith
      _ ≤ 2 ^ (32 * g.e) * qv := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) he) hqlo
  have pl := padTail_length HO.md (n := G.qLen) (by omega_arith) hL
  generalize hw : G.witLen - rest.length = w at hrest
  generalize hHL : min (G.witLen - w) (128 * G.pLen) = HL
  let c₁ : Cfg := ((aPCfg G HO k n' p rest).setV fHs (G.wit + BitVec.ofNat 32 w)).setV fHsLen (BitVec.ofNat 32 HL)
  have hHL32 : HL < 2 ^ 32 := by omega_arith
  have hwHL : w + HL ≤ G.witLen := by omega_arith
  refine VP.seq (G := St G c₁ X) ((gWindow_vp (w := w) hp (by simp) (by simp [upd, fP, fUsed, ← hw])
    (by omega_arith)).mono (fun _ _ h => h) fun σ s h => by rw [hHL] at h; exact h) ?_
  refine VP.seq (gPart_vp (c := c₁) (pv := p) (ev := (p - 1) / qv) (qv := qv) (w := w) (HL := HL) certs ok hp hlq1
    hn hpm hpb hpe hpr hctx he4 he0 (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP])
    (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, hqv])
    (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1])
    (by simp [c₁]) (by simp [c₁, pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1, aOne])
    (by simp [c₁, aH, aP, aE, aPm1, aOne]) (by simp [c₁, aTmp, aP, aE, aPm1, aOne])
    (by simp [c₁, aG, aP, aE, aPm1, aOne]) rfl hpd.odd
    (by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega_arith); omega_arith)
    hpd.upper hev (fun x hx => ?_) (by simp [c₁]) (by simp [c₁, upd, fHs, fHsLen]) (by simp [c₁]) (by simp [c₁])
    hwHL hwl hHL32 (by simp [c₁]; decide) (by simp [c₁]; decide) rfl) ?_
  · simp only [c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sG]; omega_arith
    · simp only [pl, sG]; omega_arith
    · simp only [hql, sQ, sG]; omega_arith
  -- The window's candidates are the spec's.
  have hcand : gCands G w HL 0 = windowCandidates G.pLen Spec.Dsa.generatorAttempts rest := by
    simp only [gCands, hsW, Nat.zero_mul, List.drop_zero, hrest, windowCandidates]
    rw [← hHL, show G.witLen - w = rest.length by omega_arith, take_window,
      show 128 * G.pLen = Spec.Dsa.generatorAttempts * G.pLen from rfl]
  unfold winResult
  rw [← hcand]
  rcases hgv : Spec.Dsa.generator p qv (gCands G w HL 0) with _ | gv
  · -- No g: a short window ran out.
    have hfin : gFin c₁ G w HL p qv = (c₁.setV fG 2).setV fH
        (G.wit + BitVec.ofNat 32 (w + gNum G w HL p qv 0 * G.pLen)) := by simp only [gFin, gRes, hgv]
    rw [hfin]
    refine VP.seq (gUsed_vp (x := w + gNum G w HL p qv 0 * G.pLen) (by simp) (by simp [upd])) ?_
    refine VP.seq (G := fun σ s => St G (((c₁.setV fG 2).setV fH
        (G.wit + BitVec.ofNat 32 (w + gNum G w HL p qv 0 * G.pLen))).setV fUsed
          (BitVec.ofNat 32 (w + gNum G w HL p qv 0 * G.pLen))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp)).trans (by simp [upd, fG, fH, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine (gShort_vp hp (HL := HL) (by simp [c₁]) (by simp [c₁, upd, fHsLen, fG, fH, fUsed]) hHL32).mono
      (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    have hnum : gNum G w HL p qv 0 = (gCands G w HL 0).length := generatorCount_none hgv
    by_cases hs : HL < 128 * G.pLen
    · have hshort : ¬Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega_arith
      simp only [hs, hshort, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed, fC]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [c₁, pRest]
    · have hfull : Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega_arith
      have hlen : (gCands G w HL 0).length = 128 := by
        rw [hcand]
        simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range,
          List.length_take, Spec.Dsa.generatorAttempts]
        rw [Nat.min_eq_left (by omega_arith), Nat.mul_div_cancel _ (by omega_arith)]
      simp only [hs, hfull, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl
        · refine ⟨by simp, ?_⟩
          simp only [upd, ↓reduceIte, List.length_drop, hnum, hlen, Spec.Dsa.generatorAttempts]
          congr 1; omega_arith
        all_goals exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft,
          fSeed, fC]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
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
          unfold Spec.Dsa.generationLengthsValid at hlq; unfold Spec.Dsa.lengthsValid; omega_arith)
        (by rw [hpl8]; exact hpd.upper) (by rw [hql8]; exact qlt) (by rw [hpl8]; exact Nat.lt_trans hgb.2 hpd.upper)
    let xu := w + gNum G w HL p qv 0 * G.pLen
    let Dg : Cfg := ((({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 32 xu)).setV fUsed (BitVec.ofNat 32 xu)
    have hfin : gFin c₁ G w HL p qv = (({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV
        fH (G.wit + BitVec.ofNat 32 xu) := by simp only [gFin, gRes, hgv, xu]
    rw [hfin]
    refine VP.seq (G := St G Dg X) (gUsed_vp (x := xu) (by simp) (by simp [upd])) ?_
    refine VP.seq (G := fun σ s => St G Dg X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [Dg])).trans (by simp [Dg, upd, fG, fH, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    refine (checkPart_vp (c := Dg) (X := X) hp hq hck hlq (pB := Spec.Rsa.i2osp p G.pLen) (qB := qBytes G k)
      (gB := Spec.Rsa.i2osp gv G.pLen) (by simp [Dg, c₁, pRest]) (by simp [Dg, c₁, pRest]) (by simp [Dg])
      (VG.Proof.Rsa.i2osp_length _ _) hql (VG.Proof.Rsa.i2osp_length _ _) (fun x hx => ?_) (by simp [Dg, c₁]; decide)
      (by simp [Dg, c₁]; decide)).mono (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    · simp only [Dg, c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length, sG, sPacked]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sPacked]; omega_arith
      · simp only [pl, sPacked]; omega_arith
      · simp only [hql, sQ, sPacked]; omega_arith
    have hU : G.witLen - (rest.drop (G.pLen * gNum G w HL p qv 0)).length = xu := by
      simp only [List.length_drop, xu]; rw [Nat.mul_comm G.pLen]
      have h1 := VG.Proof.Dsa.Generation.generatorCount_le p qv (gCands G w HL 0)
      have h2 : (gCands G w HL 0).length * G.pLen ≤ rest.length := by
        rw [hcand]
        simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range]
        exact Nat.le_trans (Nat.div_mul_le_self _ _) (by simp only [List.length_take]; exact Nat.min_le_right _ _)
      have h3 := Nat.le_trans (Nat.mul_le_mul_right G.pLen h1) h2
      simp only [gNum] at h3 ⊢
      omega_arith
    rw [hok] at h
    by_cases hv : Spec.Dsa.parametersValid ⟨p, qv, gv⟩
    · simp only [hv, decide_true, ckCfg, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut, hU]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg, c₁], by simp [Dg, c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed,
            fC]⟩
      · change y ∈ [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩)] at hy
        rw [List.mem_singleton] at hy; subst hy; rw [← hpk]; simp
    · simp only [hv, decide_false, ckCfg, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut, hU]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg, c₁], by simp [Dg, c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft, fSeed,
            fC]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [Dg, c₁, pRest]

/-- The stage after q passes, with the witnesses up to `r` read. -/
abbrev aQCfg (G : GP) (HO : HashOk Gh) (k : Nat) (n : BitVec 32) (u : Nat) (r : List Byte) : Cfg :=
  testCfg ((aBase G HO k n).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k) G.witLen (some (true, r))

/-- The candidates of the counters are the spec's. -/
theorem pCand_spec (HO : HashOk Gh) {k : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hk4 : 4 * Gh.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen) (hk : k + G.qLen ≤ G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen) (j : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j := by
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  have hc : G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  refine VG.Proof.Dsa.Arm.Gen.pCandidate_xBytes HO (fun i => ?_) hH hsl hlen (by omega_arith) hc _
  rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]

/-- The search for p, then g and the check, after q. -/
theorem attemptP_vp {g : Geo} {n : Nat} (HO : HashOk g.G) (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen) (gcerts : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e)
    (h32 : G.witLen < 2 ^ 32)
    {k u : Nat} {n' : BitVec 32} {r : List Byte} (hk : k + G.qLen ≤ G.seedsLen)
    (hr : G.witB.drop (G.witLen - r.length) = r)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aQCfg G HO k n' u r) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [g.pPart, .block (cmpF fP 0),
        .ite .eq (.block (stImm fStatus 2))
          (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fP 1),
            .ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [g.gWindow, g.gPart, Geo.gUsed, .block (cmpF fG 1),
              .ite .eq g.checkPart g.gShort])
              (.block [])])])
      (St G (aOut G HO k n' (primeRes G.pLen G.qLen (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r)) X) := by
  have hlq' : Spec.Dsa.generationLengthsValid G.pLen G.qLen := hlq
  have hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega_arith
  have pl := padTail_length HO.md (n := G.qLen) (by omega_arith) HO.hL
  refine VP.seq (pPart_vp (c := aBase G HO k n') (u0 := G.witLen - r.length) (d := aQCfg G HO k n' u r) HO okp certs hlq
    hp hq hk4 hsb hH hwl hsize (aBase_pnot G HO k n') hk (by simp) (by simp [upd, fSeed, fStatus, fSeedLeft])
    (by omega_arith) (pCand_spec HO hlq hk4 hsb hk hH hlen) (by simp [testCfg])
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
    refine VP.seq (G := fun σ s => St G ((pNone (aBase G HO k n') HO G).setV fP 0) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [pFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => (pNone (aBase G HO k n') HO G).setV fP 0) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fP, fStatus, fSeedLeft, fSeed, fC]⟩
  · -- No p: the next seed.
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k n') HO G).setV fUsed
        (BitVec.ofNat 32 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [pFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k n') HO G).setV fUsed
        (BitVec.ofNat 32 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by simp [upd, fUsed, fP, fStatus, fSeedLeft, fSeed, fC]⟩
  · -- p: g and the check.
    have hpd := VG.Proof.Dsa.Generation.primeSearch_domain hw hlen _ _ _ _ hR
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k n' p r') X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k n' p r') X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptG_vp HO gcerts ok hp hq hck hlq' hn hpm hpb hpe hpr hctx he4 he0 he HO.hL hwl h32 (rest := r') (by
        rw [← hwl]; exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.primeSearch_suffix _ _ _ hR).trans (hr ▸ List.drop_suffix _ _)))
        hpd hql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

/-- A seed: q, its test, then p, g and the check. -/
theorem attempt_vp {g : Geo} {n : Nat} (HO : HashOk g.G) (okq : PrimeOk (8 * G.qLen) g.qCode)
    (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen) (gcerts : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    (hsizeq : keyOff + 8 * keyWords (8 * G.qLen) ≤ wa G.pLen) (hb8 : 8 * G.qLen / 8 ≤ wa G.pLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e)
    (h32 : G.witLen < 2 ^ 32)
    {k u : Nat} {n' : BitVec 32} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) X) g.attempt
      (St G (aOut G HO k n' (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) := by
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by have := hlen (seedAt G k); omega_arith
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_arith
  have ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [hHq])
  have hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
  unfold Geo.attempt
  refine VP.seq (qPart_vp (c := (aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) HO okq hlq hp hq hk4 hH hwl hsb
    hsizeq hb8 hk hu (by simp) (by simp [upd, fUsed, fSeed, fStatus, fSeedLeft]) (by simp)
    (by simp [upd]) (by simp; decide) (by simp; decide) (by simp)) ?_
  rw [refillAttempt_eq]
  rcases hpp : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u)
    with _ | ⟨_ | _, r⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen none) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen none) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q is not prime: the next seed.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k n').setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q: p, g and the check.
    have hr : G.witB.drop (G.witLen - r.length) = r := by
      rw [← hwl]; exact VG.Proof.Dsa.Generation.probablePrime_cursor hpp
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k n' u r) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k n' u r) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    rw [← hqv]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptP_vp HO okp certs gcerts ok hlq hp hq hk4 hsb hH hwl hsize hlen hck hn hpm hpb hpe hpr hctx he4 he0
        he h32 hk hr ql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

end

end VG.Proof.Dsa.Arm.Gen
