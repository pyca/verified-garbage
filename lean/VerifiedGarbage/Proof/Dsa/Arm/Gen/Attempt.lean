module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PLoop
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GPart
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.CheckPart
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: a seed

`attempt_vp`: q from the seed and its test, the search for p, the search for
g and the check, as `VG.Proof.Dsa.Generation.seedResult` describes them:
`fStatus` := 2 when a tape runs out, 1 with p‖q‖g at `sPacked` when the
domain passes, else the witnesses read so far for the next seed.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The h tape's candidates. -/
abbrev hsL (G : GP) : List Nat := (Spec.Dsa.generationChunks G.pLen G.hsB).map Spec.Dsa.decodeBE

/-- The search's stage at the seed at `k`: `fSeed`, `fSeedLeft`, `fStatus` and the padding. -/
abbrev aBase (G : GP) (HO : HashOk Gh) (k : Nat) : Cfg :=
  ((({ cl := [(G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fSeed (G.seeds + BitVec.ofNat 32 k)).setV fSeedLeft
    (BitVec.ofNat 32 (G.seedsLen - k))).setV fStatus 0

/-- The stage after a seed. -/
def aOut (G : GP) (HO : HashOk Gh) (k : Nat) : Option (Option Spec.Dsa.Params × List Byte) → Cfg
  | none => (aBase G HO k).setV fStatus 2
  | some (none, rest) => (aBase G HO k).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))
  | some (some a, _) =>
    ({ aBase G HO k with cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] }).setV fStatus 1

theorem aBase_LS (G : GP) (HO : HashOk Gh) (k : Nat) : (aBase G HO k).LS = [fStatus, fSeedLeft, fSeed] := rfl

theorem aBase_pnot (G : GP) (HO : HashOk Gh) (k : Nat) : PNot (aBase G HO k) := by
  simp only [PNot]; decide

/-- The stage after p from the seed at `k`, with the witnesses up to `rest` read. -/
abbrev aPCfg (G : GP) (HO : HashOk Gh) (k p : Nat) (rest : List Byte) : Cfg :=
  ((pFound (aBase G HO k) HO G k p).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))).setV fP 1

/-- The search for g and the check, after p. -/
theorem attemptG_vp {g : Geo} {n : Nat} (HO : HashOk Gh) (certs : GStepCerts g) (ok : PowOk n g.e g.powCode)
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * G.pLen - 8 * G.qLen + 1 ≤ 32 * g.e) (hL : HO.P.L = 8)
    (hhsb : G.hsB.length = G.hsLen) (hmod : G.hsLen % G.pLen = 0) (h32 : G.hsLen < 2 ^ 32)
    {k p : Nat} {rest : List Byte} (hpd : VG.Proof.Dsa.Generation.PDomain G.pLen p)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aPCfg G HO k p rest) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [g.gPart, .block (cmpF fG 1), .ite .eq g.checkPart (.block [])])
      (St G (aOut G HO k (VG.Proof.Dsa.Generation.generatorResult p (Spec.Dsa.decodeBE (qBytes G k)) (hsL G)
        rest)) X) := by
  have hq0 : 0 < G.qLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have hlq1 : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := hpd.width
  have hl384 : G.pLen ≤ 384 := by omega
  generalize hqv : Spec.Dsa.decodeBE (qBytes G k) = qv at hqlo ⊢
  have qpos : 0 < qv := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  -- (p − 1) / q fits the exponent's words.
  have hev : (p - 1) / qv < 2 ^ (32 * g.e) := by
    have hp := hpd.upper
    refine (Nat.div_lt_iff_lt_mul qpos).mpr ?_
    calc p - 1 < 2 ^ (8 * G.pLen) := by omega
      _ = 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * 2 ^ (8 * G.qLen - 1) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ (32 * g.e) * qv := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) he) hqlo
  have pl := padTail_length HO.md (n := G.qLen) (by omega) hL
  refine VP.seq (gPart_vp (c := aPCfg G HO k p rest) (pv := p) (ev := (p - 1) / qv) (qv := qv) certs ok hp hlq1 hn
    hpm hpb hpe hpr hctx he4 he0 (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP])
    (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, hqv])
    (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1])
    (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1, aOne])
    (by simp [aH, aP, aE, aPm1, aOne]) (by simp [aTmp, aP, aE, aPm1, aOne]) (by simp [aG, aP, aE, aPm1, aOne]) rfl
    hpd.odd (by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega); omega)
    hpd.upper hev (fun x hx => ?_) hhsb hmod h32 (by simp; decide) (by simp; decide) rfl) ?_
  · simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sG]; omega
    · simp only [pl, sG]; omega
    · simp only [hql, sQ, sG]; omega
  have hres : gRes G p qv 0 = Spec.Dsa.generator p qv (hsL G) := by simp [gRes]
  rw [hres]
  unfold VG.Proof.Dsa.Generation.generatorResult
  rcases hgv : Spec.Dsa.generator p qv (hsL G) with _ | gv
  · -- No g.
    refine VP.seq (G := fun σ s => St G ((aPCfg G HO k p rest).setV fG 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [gFin])).trans (by simp [gFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [gFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fUsed, fG, fP, fStatus, fSeedLeft, fSeed]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [pRest]
  · -- g: the check.
    have hgb := VG.Proof.Dsa.Generation.generator_bounds (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hpd.lower) (hsL G) hgv
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
          unfold Spec.Dsa.generationLengthsValid at hlq; unfold Spec.Dsa.lengthsValid; omega)
        (by rw [hpl8]; exact hpd.upper) (by rw [hql8]; exact qlt) (by rw [hpl8]; exact Nat.lt_trans hgb.2 hpd.upper)
    let Dg : Cfg := ({ aPCfg G HO k p rest with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: (aPCfg G HO k p rest).cl }).setV fG 1
    refine VP.seq (G := fun σ s => St G Dg X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [gFin])).trans (by simp [gFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [gFin, Dg] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    refine (checkPart_vp (c := Dg) (X := X) hp hq hck hlq (pB := Spec.Rsa.i2osp p G.pLen) (qB := qBytes G k)
      (gB := Spec.Rsa.i2osp gv G.pLen) (by simp [Dg, pRest]) (by simp [Dg, pRest]) (by simp [Dg])
      (VG.Proof.Rsa.i2osp_length _ _) hql (VG.Proof.Rsa.i2osp_length _ _) (fun x hx => ?_) (by simp [Dg]; decide)
      (by simp [Dg]; decide)).mono (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    · simp only [Dg, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length, sG, sPacked]; omega
      · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sPacked]; omega
      · simp only [pl, sPacked]; omega
      · simp only [hql, sQ, sPacked]; omega
    rw [hok] at h
    by_cases hv : Spec.Dsa.parametersValid ⟨p, qv, gv⟩
    · simp only [hv, decide_true, ckCfg, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg], by simp [Dg, upd, fUsed, fG, fP, fStatus, fSeedLeft, fSeed]⟩
      · change y ∈ [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩)] at hy
        rw [List.mem_singleton] at hy; subst hy; rw [← hpk]; simp
    · simp only [hv, decide_false, ckCfg, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hv, ↓reduceIte, aOut]
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl <;>
          exact ⟨by simp [Dg], by simp [Dg, upd, fUsed, fG, fP, fStatus, fSeedLeft, fSeed]⟩
      · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [Dg, pRest]

end

end VG.Proof.Dsa.Arm.Gen
