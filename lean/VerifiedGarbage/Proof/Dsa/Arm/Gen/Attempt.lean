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
  have hq0 : 0 < G.qLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega_arith
  have hlq1 : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := hpd.width
  have hl384 : G.pLen ≤ 384 := by omega_arith
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
  refine VP.seq (gPart_vp (c := aPCfg G HO k p rest) (pv := p) (ev := (p - 1) / qv) (qv := qv) certs ok hp hlq1 hn
    hpm hpb hpe hpr hctx he4 he0 (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP])
    (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, hqv])
    (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1])
    (by simp) (by simp [pAp, KU, VG.Proof.Rsa.Arm.Keys.upd, aP, aE, aPm1, aOne])
    (by simp [aH, aP, aE, aPm1, aOne]) (by simp [aTmp, aP, aE, aPm1, aOne]) (by simp [aG, aP, aE, aPm1, aOne]) rfl
    hpd.odd (by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega_arith); omega_arith)
    hpd.upper hev (fun x hx => ?_) hhsb hmod h32 (by simp; decide) (by simp; decide) rfl) ?_
  · simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sG]; omega_arith
    · simp only [pl, sG]; omega_arith
    · simp only [hql, sQ, sG]; omega_arith
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
          unfold Spec.Dsa.generationLengthsValid at hlq; unfold Spec.Dsa.lengthsValid; omega_arith)
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
      · simp only [VG.Proof.Rsa.i2osp_length, sG, sPacked]; omega_arith
      · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sPacked]; omega_arith
      · simp only [pl, sPacked]; omega_arith
      · simp only [hql, sQ, sPacked]; omega_arith
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

/-- The stage after q passes, with the witnesses up to `r` read. -/
abbrev aQCfg (G : GP) (HO : HashOk Gh) (k u : Nat) (r : List Byte) : Cfg :=
  testCfg ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k) G.witLen (some (true, r))

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
  refine VG.Proof.Dsa.Arm.Gen.pCandidate_xBytes HO (fun i => ?_) hH hsl hlen (by omega) hc _
  rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, HO.hN, hk4]

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
    (hhsb : G.hsB.length = G.hsLen) (hmod : G.hsLen % G.pLen = 0) (h32 : G.hsLen < 2 ^ 32)
    {k u : Nat} {r : List Byte} (hk : k + G.qLen ≤ G.seedsLen) (hr : G.witB.drop (G.witLen - r.length) = r)
    (hql : (qBytes G k).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k)) :
    VP (St G (aQCfg G HO k u r) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [g.pPart, .block (cmpF fP 0),
        .ite .eq (.block (stImm fStatus 2))
          (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fP 1),
            .ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [g.gPart, .block (cmpF fG 1), .ite .eq g.checkPart (.block [])])
              (.block [])])])
      (St G (aOut G HO k (VG.Proof.Dsa.Generation.primeResult (8 * G.pLen) (8 * G.qLen)
        (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (hsL G) r)) X) := by
  have hlq' : Spec.Dsa.generationLengthsValid G.pLen G.qLen := hlq
  have hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega
  have pl := padTail_length HO.md (n := G.qLen) (by omega) HO.hL
  refine VP.seq (pPart_vp (c := aBase G HO k) (u0 := G.witLen - r.length) (d := aQCfg G HO k u r) HO okp certs hlq
    hp hq hk4 hsb hH hwl hsize (aBase_pnot G HO k) hk (by simp) (by simp [upd, fSeed, fStatus, fSeedLeft])
    (by omega) (pCand_spec HO hlq hk4 hsb hk hH hlen) (by simp [testCfg])
    (by simp [testCfg, upd]) (fun o ho => ⟨by simp [testCfg, ho], by
      change o ∈ [fStatus, fSeedLeft, fSeed] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> simp [testCfg, upd, fUsed, fRes, fStatus, fSeedLeft, fSeed]⟩)
    (by simp [testCfg, qClaims]) (by simp [testCfg, qClaims])) ?_
  have hS0 : pSpec HO G k (G.witLen - r.length) 0 = Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r := by
    rw [pSpec, VG.Proof.Dsa.Generation.primeSearch_start, pU, hr]
  rw [hS0]
  unfold VG.Proof.Dsa.Generation.primeResult
  rcases hR : Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) r
    with _ | ⟨_ | p, r'⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G ((pNone (aBase G HO k) HO G).setV fP 0) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [pFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => (pNone (aBase G HO k) HO G).setV fP 0) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fP, fStatus, fSeedLeft, fSeed]⟩
  · -- No p: the next seed.
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k) HO G).setV fUsed
        (BitVec.ofNat 32 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨by simpa [pFin] using h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (((pNone (aBase G HO k) HO G).setV fUsed
        (BitVec.ofNat 32 (G.witLen - r'.length))).setV fP 2) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fUsed, fP, fStatus, fSeedLeft, fSeed]⟩
  · -- p: g and the check.
    have hpd := VG.Proof.Dsa.Generation.primeSearch_domain hw hlen _ _ _ _ hR
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k p r') X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [pFin])).trans (by simp [pFin, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aPCfg G HO k p r') X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptG_vp HO gcerts ok hp hq hck hlq' hn hpm hpb hpe hpr hctx he4 he0 he HO.hL hhsb hmod h32 hpd hql
        hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
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
    (hhsb : G.hsB.length = G.hsLen) (hmod : G.hsLen % G.pLen = 0) (h32 : G.hsLen < 2 ^ 32)
    {k u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) X) g.attempt
      (St G (aOut G HO k (VG.Proof.Dsa.Generation.seedResult (8 * G.pLen) (8 * G.qLen) (seedAt G k) (hsL G)
        (G.witB.drop u))) X) := by
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
  refine VP.seq (qPart_vp (c := (aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) HO okq hlq hp hq hk4 hH hwl hsb
    hsizeq hb8 hk hu (by simp) (by simp [upd, fUsed, fSeed, fStatus, fSeedLeft]) (by simp)
    (by simp [upd]) (by simp; decide) (by simp; decide) (by simp)) ?_
  unfold VG.Proof.Dsa.Generation.seedResult
  dsimp only
  rcases hpp : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k)) (G.witB.drop u)
    with _ | ⟨_ | _, r⟩
  · -- The witnesses ran out: `fStatus` := 2.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen none) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => testCfg ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen none) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    simp only [aOut]
    refine h'.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fStatus :: fStatus :: fSeedLeft :: fSeed :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q is not prime: the next seed.
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (testCfg ((aBase G HO k).setV fUsed (BitVec.ofNat 32 u)) (qClaims HO.md G k)
        G.witLen (some (false, r))) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨?_, x⟩)
    simp only [aOut]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: [] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;>
        exact ⟨by simp [testCfg], by simp [testCfg, upd, fRes, fUsed, fStatus, fSeedLeft, fSeed]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; simp [testCfg, qClaims]
  · -- q: p, g and the check.
    have hr : G.witB.drop (G.witLen - r.length) = r := by
      rw [← hwl]; exact VG.Proof.Dsa.Generation.probablePrime_cursor hpp
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k u r) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    refine VP.seq (G := fun σ s => St G (aQCfg G HO k u r) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.1.1.slotV (by simp [testCfg])).trans (by simp [testCfg, upd, fRes, fUsed]))
        fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    rw [← hqv]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      ((attemptP_vp HO okp certs gcerts ok hlq hp hq hk4 hsb hH hwl hsize hlen hck hn hpm hpb hpe hpr hctx he4 he0
        he hhsb hmod h32 hk hr ql hqlo).mono (fun σ s h => h.1.1) fun _ _ h => h)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)

end

end VG.Proof.Dsa.Arm.Gen
