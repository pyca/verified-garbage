module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.QPart
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.PPart
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.GCheck
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Top
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.SeedSuffix
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: a seed's attempt, which joins the searches for q (QPart), p (PPart) and g (GCheck)

/-! # DSA parameter search on RISC-V: a seed

`attempt_vp`: q from the seed and its test (`qPart_vp`), the search for p
(`pPart_vp`), and the generator and the check (`gCheck_vp`), ending as
`refillAttempt` on the seed at the cursor: `attCfg`. `attempt_ok`: the
controller's `AttemptOk`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Dsa.Generation (stAt)

/-- What a width supplies for a seed's attempt. -/
structure AOk (G : GP) (g : Geo) (HO : HashOk g.G) (Lq Lp : Impl.Dsa.ProbablePrime.Layout) : Prop where
  okq : PrimeOk Lq g.qCode
  qBits : Lq.bits = 8 * G.qLen
  qCand : Lq.candidate = 0
  qSize : Lq.size ≤ 256 * G.pLen
  qScr : ∀ r ∈ Lq.scratch, r.1 + r.2 ≤ 256 * G.pLen
  okp : PrimeOk Lp g.pCode
  lay : PLay G Lp
  hck : CheckOk g.checkCode
  hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  hp : g.pLen = G.pLen
  hq : g.qLen = G.qLen
  hk4 : 4 * g.G.k = G.qLen
  hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m
  hwl : G.randB.length = G.randLen
  hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen

attribute [local simp] fUsed fP fStatus fLeft fStart fSeed fRes

section
variable {G : GP} {X : State → Prop}

/-! ## Branches on a word -/

/-- `cmpF o v`, then a branch on whether word `o` is `v`. -/
theorem br_vp {d : Cfg} {o v : Nat} {x : BitVec 64} (hP : o ∈ d.LS) (hPv : d.V o = x)
    (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v ≤ 2048) {t e : Prog isa} {Q : State → State → Prop}
    (ht : (x == BitVec.ofNat 64 v) = true → VP (St G d X) t Q)
    (he : (x == BitVec.ofNat 64 v) = false → VP (St G d X) e Q) :
    VP (St G d X) (.seq (.block (cmpF o v)) (.ite (.zero .t2) t e)) Q := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval (.zero .t2) s = some (x == BitVec.ofNat 64 v))
    (cmpF_vp (c := fun _ => d) (fun σ s h => h.1) ho h8 hv (fun σ s h => (h.1.gi.slotV hP).trans hPv)
      fun σ s t h h' _ e => ⟨⟨h', h.2⟩, e⟩) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · cases hb : (x == BitVec.ofNat 64 v)
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
    · exact (ht hb).mono (fun σ s h => h.1.1) fun _ _ h => h
  · cases hb : (x == BitVec.ofNat 64 v)
    · exact (he hb).mono (fun σ s h => h.1.1) fun _ _ h => h
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z

/-- `fStatus := v`. -/
theorem status_vp {d : Cfg} {v : Nat} (hv : v < 2048) :
    VP (St G d X) (.block (stImm fStatus v)) (St G (d.setV fStatus (BitVec.ofNat 64 v)) X) :=
  stImm_vp (c := fun _ => d) (fun σ s h => h.1) hv (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.2⟩

/-- A stage seen as one with fewer words and claims. -/
theorem St.to {d d' : Cfg} (hV : ∀ o ∈ d'.LS, o ∈ d.LS ∧ d.V o = d'.V o) (hcl : ∀ x ∈ d'.cl, x ∈ d.cl)
    (hl : d'.live = [] := by rfl) (hk : d'.kls = [] := by rfl) {σ s : State} (h : St G d X σ s) :
    St G d' X σ s :=
  ⟨h.1.mono' hV hcl hl hk, h.2⟩

/-! ## The stages -/

/-- A seed's words but the cursor: status 2, the seeds left, its start and
its address, with the claims `cl0`. -/
abbrev aBase (G : GP) (cl0 : Claims) (K C : Nat) : Cfg :=
  (((({ cl := cl0 } : Cfg).setV fLeft (BitVec.ofNat 64 K)).setV fStart (BitVec.ofNat 64 C)).setV fSeed
    (G.rand + BitVec.ofNat 64 C)).setV fStatus (BitVec.ofNat 64 2)

theorem aBase_LS (G : GP) (cl0 : Claims) (K C : Nat) : (aBase G cl0 K C).LS = [fStatus, fSeed, fStart, fLeft] :=
  rfl

theorem aBase_pnot (G : GP) (cl0 : Claims) (K C : Nat) : PNot (aBase G cl0 K C) := by
  unfold PNot; rw [aBase_LS]; decide

theorem aBase_gKeys (G : GP) (cl0 : Claims) (K C : Nat) (a b : Nat) :
    ∀ o ∈ gKeys, o ∉ (((aBase G cl0 K C).setV fUsed (BitVec.ofNat 64 a)).setV fP (BitVec.ofNat 64 b)).LS := by
  show ∀ o ∈ gKeys, o ∉ fP :: fUsed :: (aBase G cl0 K C).LS
  rw [aBase_LS]; decide

/-- The words of `endCfg` from a stage. -/
theorem end_to {d : Cfg} {cl0 extra : Claims} {st K C u : Nat}
    (hS : fStatus ∈ d.LS ∧ d.V fStatus = BitVec.ofNat 64 st) (hL : fLeft ∈ d.LS ∧ d.V fLeft = BitVec.ofNat 64 K)
    (hT : fStart ∈ d.LS ∧ d.V fStart = BitVec.ofNat 64 C)
    (hU : st = 1 ∨ st = 2 → fUsed ∈ d.LS ∧ d.V fUsed = BitVec.ofNat 64 u)
    (hcl : ∀ x ∈ cl0 ++ extra, x ∈ d.cl) {σ s : State} (h : St G d X σ s) :
    St G (endCfg cl0 st K C u extra) X σ s := by
  refine St.to (fun o ho => ?_) hcl rfl rfl h
  simp only [fStatus, fLeft, fStart, fUsed] at hS hL hT hU
  simp only [endCfg] at ho
  split at ho
  · next hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact ⟨hS.1, by simp [endCfg, hS.2]⟩
    · exact ⟨hL.1, by simp [endCfg, hL.2]⟩
    · exact ⟨hT.1, by simp [endCfg, hT.2]⟩
    · exact ⟨(hU hs).1, by simp [endCfg, (hU hs).2]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact ⟨hS.1, by simp [endCfg, hS.2]⟩
    · exact ⟨hL.1, by simp [endCfg, hL.2]⟩
    · exact ⟨hT.1, by simp [endCfg, hT.2]⟩

end

/-! ## The spec's attempt, in pieces -/

/-- `refillAttempt` after p: the generator over the window, and the check. -/
def gTail (pLen p q : Nat) (r' : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.generator p q (Generation.windowCandidates pLen Spec.Dsa.generatorAttempts r') with
  | none =>
    if Spec.Dsa.generatorAttempts * pLen ≤ r'.length then
      some (none, r'.drop (Spec.Dsa.generatorAttempts * pLen))
    else none
  | some g =>
    some (if Spec.Dsa.parametersValid ⟨p, q, g⟩ then some ⟨p, q, g⟩ else none,
      r'.drop (pLen * Generation.generatorCount p q
        (Generation.windowCandidates pLen Spec.Dsa.generatorAttempts r')))

/-- `refillAttempt` after q passes. -/
def pTailS (pLen qLen q : Nat) (seed r : List Byte) : Option (Option Spec.Dsa.Params × List Byte) :=
  match Spec.Dsa.primeFromSeed (8 * pLen) (8 * qLen) q seed r with
  | none => none
  | some (none, r') => some (none, r')
  | some (some p, r') => gTail pLen p q r'

theorem refill_eq (pLen qLen : Nat) (seed rest : List Byte) :
    Generation.refillAttempt pLen qLen seed rest =
      match Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * qLen) seed) rest with
      | none => none
      | some (false, r) => some (none, r)
      | some (true, r) => pTailS pLen qLen (Spec.Dsa.qCandidate (8 * qLen) seed) seed r := by
  unfold Generation.refillAttempt pTailS gTail
  rfl

/-- The candidates `gTail` drops fit the tape. -/
theorem count_le (pLen p q : Nat) (r : List Byte) :
    pLen * Generation.generatorCount p q (Generation.windowCandidates pLen Spec.Dsa.generatorAttempts r) ≤
      r.length := by
  have h1 := Generation.generatorCount_le p q (Generation.windowCandidates pLen Spec.Dsa.generatorAttempts r)
  have h2 : (Generation.windowCandidates pLen Spec.Dsa.generatorAttempts r).length =
      (r.take (Spec.Dsa.generatorAttempts * pLen)).length / pLen := by
    simp [Generation.windowCandidates, Spec.Dsa.generationChunks]
  have h3 := Nat.div_mul_le_self (r.take (Spec.Dsa.generatorAttempts * pLen)).length pLen
  have h4 : (r.take (Spec.Dsa.generatorAttempts * pLen)).length ≤ r.length := by
    rw [List.length_take]; exact Nat.min_le_right _ _
  rw [h2] at h1
  calc pLen * _ ≤ pLen * ((r.take (Spec.Dsa.generatorAttempts * pLen)).length / pLen) := Nat.mul_le_mul_left _ h1
    _ ≤ (r.take (Spec.Dsa.generatorAttempts * pLen)).length := by rw [Nat.mul_comm]; exact h3
    _ ≤ r.length := h4

/-- `(p − 1) / q` fits its octets. -/
theorem ev_lt {pLen qLen pv qv : Nat} (hq0 : 0 < qLen) (hqp : qLen ≤ pLen) (hpu : pv < 2 ^ (8 * pLen))
    (hqlo : 2 ^ (8 * qLen - 1) ≤ qv) : (pv - 1) / qv < 256 ^ eBytes pLen qLen := by
  have qpos : 0 < qv := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  rw [show (256 : Nat) ^ eBytes pLen qLen = 2 ^ (8 * eBytes pLen qLen) from (Nat.pow_mul 2 8 _).symm]
  refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul qpos).mpr ?_) (Nat.pow_le_pow_right (by decide)
    (show 8 * pLen - 8 * qLen + 1 ≤ 8 * eBytes pLen qLen by simp only [eBytes]; omega))
  calc pv - 1 < 2 ^ (8 * pLen) := by omega
    _ = 2 ^ (8 * pLen - 8 * qLen + 1) * 2 ^ (8 * qLen - 1) := by rw [← Nat.pow_add]; congr 1; omega
    _ ≤ 2 ^ (8 * pLen - 8 * qLen + 1) * qv := Nat.mul_le_mul_left _ hqlo

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The candidates of the counters are the spec's. -/
theorem pCand_spec (HO : HashOk Gh) {k : Nat} (hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384)
    (hk4 : 4 * Gh.k = G.qLen) (hwl : G.randB.length = G.randLen) (hk : k + G.qLen ≤ G.randLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen) (j : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j := by
  have hqc := G.qLen_cases
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hwl]; omega
  have hc : G.pLen ≤ (cnt G + 1) * G.qLen := (cnt_facts G hw).2.1
  refine pCandidate_xBytes HO (fun i => ?_) hH hsl hlen (by omega) hc _
  rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega), HO.md.digest_length, hk4]

/-- After p: the generator and the check. -/
theorem attemptG_vp {g : Geo} (HO : HashOk g.G) {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (A : AOk G g HO Lq Lp)
    {K C pv : Nat} {r' : List Byte} (hr' : r' <:+ G.randB) (hpd : Generation.PDomain G.pLen pv)
    (hql : (qBytes G C).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G C)) :
    VP (St G (pFin (aBase G (padCl G HO.md) K C) HO G C (some (some pv, r'))) X) g.gCheck
      (St G (attCfg G (padCl G HO.md) (K, C) (gTail G.pLen pv (Spec.Dsa.decodeBE (qBytes G C)) r')) X) := by
  have hw := A.hw
  have hqc := G.qLen_cases
  have hq0 : 0 < G.qLen := by omega
  have hq32 : G.qLen ≤ 32 := by omega
  have hl384 : G.pLen ≤ 384 := by omega
  have pl : (padTail HO.md G.qLen).length = 64 - G.qLen := padTail_length HO.md (by omega) rfl
  have hqb : qBytes G C = Spec.Rsa.i2osp (Spec.Dsa.decodeBE (qBytes G C)) G.qLen := by
    rw [← VG.Proof.Dsa.encodeBE_i2osp, ← hql, VG.Proof.Dsa.encodeBE_decodeBE]
  have qlt : Spec.Dsa.decodeBE (qBytes G C) < 256 ^ G.qLen := by
    rw [← hql]; exact VG.Proof.Dsa.decodeBE_lt _
  have hev : (pv - 1) / Spec.Dsa.decodeBE (qBytes G C) < 256 ^ eBytes G.pLen G.qLen :=
    ev_lt hq0 (by omega) hpd.upper hqlo
  have hpv : pv < 256 ^ G.pLen := by
    rw [show (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) from (Nat.pow_mul 2 8 _).symm]; exact hpd.upper
  have hrl : r'.length ≤ G.randLen := by rw [← A.hwl]; exact hr'.length_le
  have hd : G.randB.drop (G.randLen - r'.length) = r' := by
    rw [← A.hwl]; exact Generation.suffix_drop_length hr'
  have e8 : (8 * G.qLen - 1) ≥ 1 := by omega
  have R : GReq G (pFin (aBase G (padCl G HO.md) K C) HO G C (some (some pv, r'))) pv
      ((pv - 1) / Spec.Dsa.decodeBE (qBytes G C)) := by
    refine ⟨by simp [pFin], by simp [pFin, pAp, KU, aP, aE, aPm1], by simp [pFin],
      by simp [pFin, pAp, KU, aP, aE, aPm1, aOne], by simp [pFin],
      by simp [pFin, pAp, KU, aP, aE, aPm1, aOne, aZero],
      by simp [pFin, aH, aP, aE, aPm1, aOne, aZero], by simp [pFin, aTmp, aP, aE, aPm1, aOne, aZero], rfl,
      by simp [pFin], hpv,
      by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega); omega,
      hpd.odd, by simp [pFin], hev, fun x hx => ?_, by simp [pFin]; decide, by simp [pFin]; decide⟩
    simp only [pFin, Cfg.setV, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, Apart, sE, sG, pB, eBytes]; omega
    · simp only [VG.Proof.Rsa.i2osp_length, Apart, sPBE, sG, pB]; omega
    · simp only [pl, Apart, sMsg, sG, pB]; omega
    · simp only [hql, Apart, sQ, sG, pB]; omega
  refine (gCheck_vp (c := pFin (aBase G (padCl G HO.md) K C) HO G C (some (some pv, r'))) (X := X)
    (u := G.randLen - r'.length) A.hp A.hq (certC _ _) A.hck R (by rw [← hqb]; simp [pFin]) qlt (by omega)
    (by simp [pFin]) (by simp [pFin, upd]) (aBase_gKeys G _ K C (G.randLen - r'.length) 1) (fun x hx => ?_)).mono
    (fun _ _ h => h) fun σ s h => ?_
  · simp only [pFin, Cfg.setV, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, sE, sPacked, eBytes]; omega
    · simp only [VG.Proof.Rsa.i2osp_length, sPBE, sPacked]; omega
    · simp only [pl, sPacked, sMsg]; omega
    · simp only [hql, sQ, sPacked]; omega
  have hs : hsOf G (G.randLen - r'.length) = Generation.windowCandidates G.pLen Spec.Dsa.generatorAttempts r' := by
    simp only [hsOf, hd]
  have hcnt := count_le G.pLen pv (Spec.Dsa.decodeBE (qBytes G C)) r'
  unfold gcCfg at h
  rw [hs, hd] at h
  unfold gTail
  rcases hgen : Spec.Dsa.generator pv (Spec.Dsa.decodeBE (qBytes G C)) (Generation.windowCandidates G.pLen Spec.Dsa.generatorAttempts r')
    with _ | gv
  · rw [hgen] at h
    dsimp only at h ⊢
    by_cases hf : Spec.Dsa.generatorAttempts * G.pLen ≤ r'.length
    · simp only [hf, ↓reduceIte] at h ⊢
      have e : G.randLen - (r'.drop (Spec.Dsa.generatorAttempts * G.pLen)).length =
          G.randLen - r'.length + Spec.Dsa.generatorAttempts * G.pLen := by rw [List.length_drop]; omega
      simp only [attCfg]
      refine end_to ⟨by simp [pFin], by simp [pFin, upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        (fun _ => ⟨by simp, by rw [e]; simp [upd]⟩) (fun x hx => ?_) h
      simp only [padCl, List.append_nil, List.mem_singleton] at hx
      subst hx; simp [pFin, pRest]
    · simp only [hf, ↓reduceIte] at h ⊢
      simp only [attCfg]
      refine end_to ⟨by simp, by simp [upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        (fun h' => absurd h' (by decide)) (fun x hx => ?_) h
      simp only [padCl, List.append_nil, List.mem_singleton] at hx
      subst hx; simp [pFin, pRest]
  · rw [hgen] at h
    dsimp only at h ⊢
    have e : G.randLen - (r'.drop (G.pLen * Generation.generatorCount pv (Spec.Dsa.decodeBE (qBytes G C))
          (Generation.windowCandidates G.pLen Spec.Dsa.generatorAttempts r'))).length =
        G.randLen - r'.length + G.pLen * Generation.generatorCount pv (Spec.Dsa.decodeBE (qBytes G C))
          (Generation.windowCandidates G.pLen Spec.Dsa.generatorAttempts r') := by
      rw [List.length_drop]; omega
    by_cases hv : Spec.Dsa.parametersValid ⟨pv, Spec.Dsa.decodeBE (qBytes G C), gv⟩
    · simp only [hv, ↓reduceIte] at h ⊢
      simp only [attCfg]
      refine end_to ⟨by simp, by simp [upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        (fun _ => ⟨by simp, by rw [e]; simp [upd]⟩) (fun x hx => ?_) h
      simp only [padCl, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp [pFin, pRest]
      · simp
    · simp only [hv, ↓reduceIte] at h ⊢
      simp only [attCfg]
      refine end_to ⟨by simp [pFin], by simp [pFin, upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        ⟨by simp [pFin], by simp [pFin, upd]⟩
        (fun _ => ⟨by simp, by rw [e]; simp [upd]⟩) (fun x hx => ?_) h
      simp only [padCl, List.append_nil, List.mem_singleton] at hx
      subst hx; simp [pFin, pRest]


/-- After q passes: the search for p, then the generator and the check. -/
theorem attemptP_vp {g : Geo} (HO : HashOk g.G) {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (A : AOk G g HO Lq Lp)
    {K C : Nat} {r : List Byte} (hk : C + G.qLen ≤ G.randLen) (hr : r <:+ G.randB)
    (hql : (qBytes G C).length = G.qLen) (hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G C)) :
    VP (St G (testCfg ((aBase G (padCl G HO.md) K C).setV fUsed (BitVec.ofNat 64 (C + G.qLen)))
        (qClaims HO.md G C) G.randLen (some (true, r))) X)
      (.seq g.pPart (.seq (.block (cmpF fP 0)) (.ite (.zero .t2) (.block (stImm fStatus 0))
        (.seq (.block (cmpF fP 1)) (.ite (.zero .t2) g.gCheck (.block []))))))
      (St G (attCfg G (padCl G HO.md) (K, C)
        (pTailS G.pLen G.qLen (Spec.Dsa.decodeBE (qBytes G C)) (seedAt G C) r)) X) := by
  have hrl : r.length ≤ G.randLen := by rw [← A.hwl]; exact hr.length_le
  have hd : G.randB.drop (G.randLen - r.length) = r := by
    rw [← A.hwl]; exact Generation.suffix_drop_length hr
  refine VP.seq (pPart_vp (c := aBase G (padCl G HO.md) K C) (k := C) (u0 := G.randLen - r.length) HO A.okp A.lay
    A.hp A.hq A.hk4 A.hH A.hwl (aBase_pnot _ _ _ _) hk (by simp) (by simp [upd]) (by omega)
    (pCand_spec HO A.hw A.hk4 A.hwl hk A.hH A.hlen) (by simp [testCfg]) (by simp [testCfg, upd])
    (fun o ho => ?_) (by simp [testCfg, qClaims]) (by simp [testCfg, qClaims])) ?_
  · rw [aBase_LS] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> exact ⟨by simp [testCfg], by simp [testCfg, upd]⟩
  have hS0 : pSpec HO G C (G.randLen - r.length) 0 = Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G C)) (seedAt G C) r := by
    rw [pSpec, Generation.primeSearch_start, pU, hd]
  rw [hS0]
  unfold pTailS
  rcases hR : Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G C)) (seedAt G C) r
    with _ | ⟨_ | pv, r'⟩
  · -- The tape ran out: `fStatus` := 0.
    refine br_vp (x := BitVec.ofNat 64 0) (by simp [pFin]) (by simp [pFin, upd]) (by decide) (by decide)
      (by decide) (fun _ => (status_vp (by decide)).mono (fun _ _ h => h) fun σ s h => ?_)
      (fun hb => absurd hb (by decide))
    simp only [attCfg]
    refine end_to ⟨by simp, by simp [upd]⟩ ⟨by simp [pFin], by simp [pFin, upd]⟩
      ⟨by simp [pFin], by simp [pFin, upd]⟩ (fun h' => absurd h' (by decide)) (fun x hx => ?_) h
    simp only [padCl, List.append_nil, List.mem_singleton] at hx
    subst hx; simp [pFin]
  · -- No p: the next seed.
    refine br_vp (x := BitVec.ofNat 64 2) (by simp [pFin]) (by simp [pFin, upd]) (by decide) (by decide)
      (by decide) (fun hb => absurd hb (by decide)) fun _ => ?_
    refine br_vp (x := BitVec.ofNat 64 2) (by simp [pFin]) (by simp [pFin, upd]) (by decide) (by decide)
      (by decide) (fun hb => absurd hb (by decide)) fun _ => VP.block_nil fun σ s h => ?_
    simp only [attCfg]
    refine end_to ⟨by simp [pFin], by simp [pFin, upd]⟩ ⟨by simp [pFin], by simp [pFin, upd]⟩
      ⟨by simp [pFin], by simp [pFin, upd]⟩ (fun _ => ⟨by simp [pFin], by simp [pFin, upd]⟩) (fun x hx => ?_) h
    simp only [padCl, List.append_nil, List.mem_singleton] at hx
    subst hx; simp [pFin]
  · -- p: the generator and the check.
    have hr' : r' <:+ G.randB := (Generation.primeSearch_suffix (seedAt G C) _ r hR).trans hr
    have hpd := Generation.primeSearch_domain A.hw A.hlen _ _ _ _ hR
    refine br_vp (x := BitVec.ofNat 64 1) (by simp [pFin]) (by simp [pFin, upd]) (by decide) (by decide)
      (by decide) (fun hb => absurd hb (by decide)) fun _ => ?_
    refine br_vp (x := BitVec.ofNat 64 1) (by simp [pFin]) (by simp [pFin, upd]) (by decide) (by decide)
      (by decide) (fun _ => ?_) (fun hb => absurd hb (by decide))
    exact attemptG_vp HO A hr' hpd hql hqlo

/-- A seed: q, its test, then p, g and the check, as `refillAttempt`. -/
theorem attempt_vp {g : Geo} (HO : HashOk g.G) {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (A : AOk G g HO Lq Lp)
    {K C : Nat} (hk : C + G.qLen ≤ G.randLen) :
    VP (St G ((aBase G (padCl G HO.md) K C).setV fUsed (BitVec.ofNat 64 (C + G.qLen))) X) g.attempt
      (St G (attCfg G (padCl G HO.md) (K, C) (Generation.attemptAt G.pLen G.randB C)) X) := by
  have hqc := G.qLen_cases
  have hsl : (seedAt G C).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, A.hwl]; omega
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G C)).length = G.qLen := by
    rw [← A.hH, HO.hash _ (by omega), HO.md.digest_length, A.hk4]
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G C) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega
  have ql : (qBytes G C).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G C) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G C) :=
    Generation.qCandidate_octets (by omega) _ (by rw [hHq])
  have qlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G C) := by
    rw [hqv]; exact (Generation.qCandidate_shape (n := 8 * G.qLen) (by omega) (seedAt G C)).2.1
  unfold Geo.attempt
  simp only [Impl.Rsa.RISCV64.Keys.seqs]
  refine VP.seq (qPart_vp (c := (aBase G (padCl G HO.md) K C).setV fUsed (BitVec.ofNat 64 (C + G.qLen))) (k := C)
    (u := C + G.qLen) HO A.okq A.hp A.hq A.hk4 A.hH A.hwl A.qBits A.qCand A.qSize A.qScr (by omega) hk
    (by simp) (by simp [upd]) (by simp) (by simp [upd]) (by simp; decide) (by simp; decide) (by simp [padCl])) ?_
  unfold Generation.attemptAt
  rw [refill_eq]
  rcases hpp : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G C)) (G.randB.drop (C + G.qLen))
    with _ | ⟨_ | _, r⟩
  · -- The tape ran out: `fStatus` := 0.
    refine br_vp (x := BitVec.ofNat 64 0) (by simp [testCfg]) (by simp [testCfg, upd]) (by decide) (by decide)
      (by decide) (fun _ => (status_vp (by decide)).mono (fun _ _ h => h) fun σ s h => ?_)
      (fun hb => absurd hb (by decide))
    simp only [attCfg]
    refine end_to ⟨by simp, by simp [upd]⟩ ⟨by simp [testCfg], by simp [testCfg, upd]⟩
      ⟨by simp [testCfg], by simp [testCfg, upd]⟩ (fun h' => absurd h' (by decide)) (fun x hx => ?_) h
    simp only [padCl, List.append_nil, List.mem_singleton] at hx
    subst hx; simp [testCfg, qClaims]
  · -- q is not prime: the next seed.
    refine br_vp (x := BitVec.ofNat 64 2) (by simp [testCfg]) (by simp [testCfg, upd]) (by decide) (by decide)
      (by decide) (fun hb => absurd hb (by decide)) fun _ => ?_
    refine br_vp (x := BitVec.ofNat 64 2) (by simp [testCfg]) (by simp [testCfg, upd]) (by decide) (by decide)
      (by decide) (fun hb => absurd hb (by decide)) fun _ => VP.block_nil fun σ s h => ?_
    simp only [attCfg]
    refine end_to ⟨by simp [testCfg], by simp [testCfg, upd]⟩ ⟨by simp [testCfg], by simp [testCfg, upd]⟩
      ⟨by simp [testCfg], by simp [testCfg, upd]⟩ (fun _ => ⟨by simp [testCfg], by simp [testCfg, upd]⟩)
      (fun x hx => ?_) h
    simp only [padCl, List.append_nil, List.mem_singleton] at hx
    subst hx; simp [testCfg, qClaims]
  · -- q: p, g and the check.
    have hr : r <:+ G.randB := (Generation.probablePrime_suffix hpp).trans (List.drop_suffix _ _)
    refine br_vp (x := BitVec.ofNat 64 1) (by simp [testCfg]) (by simp [testCfg, upd]) (by decide) (by decide)
      (by decide) (fun hb => absurd hb (by decide)) fun _ => ?_
    refine br_vp (x := BitVec.ofNat 64 1) (by simp [testCfg]) (by simp [testCfg, upd]) (by decide) (by decide)
      (by decide) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [← hqv]
    exact attemptP_vp HO A hk hr ql qlo

/-- The controller's `AttemptOk`, from a width's facts. -/
theorem attempt_ok {g : Geo} (HO : HashOk g.G) {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (A : AOk G g HO Lq Lp) :
    AttemptOk G (padCl G HO.md) X g.attempt := by
  intro p _ hc
  obtain ⟨K, C⟩ := p
  refine (attempt_vp (K := K) (C := C) HO A hc).mono
    (fun σ s h => St.to (d := seedCfg G (padCl G HO.md) (K, C))
      (d' := (aBase G (padCl G HO.md) K C).setV fUsed (BitVec.ofNat 64 (C + G.qLen))) (fun o ho => ?_) (fun x hx => hx) rfl rfl h)
    fun _ _ h => h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [ctlCfg], by simp [ctlCfg, upd]⟩

end

end VG.Proof.Dsa.RISCV64.PSearch
