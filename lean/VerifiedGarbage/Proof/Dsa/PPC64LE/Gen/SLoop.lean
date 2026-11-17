module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.QPart
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PPart
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GPow
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSStore
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
public import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.CheckCall
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PX
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.SeedSuffix
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch

/-! ### `Dsa.PPC64LE.Gen.Attempt`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.PLoop`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: an iteration of the search for p

`pGo_vp`: after a candidate that is not p, the next counter (or `fP` := 2
after the last); `pStop_vp`: after one that ends the search; `pBody_vp`:
the iteration, by the cases of `Spec.Dsa.primeFromSeed.search`; `pPart_vp`:
the search.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The loop's postcondition after an iteration with `r` left. -/
abbrev pPost (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧ (r = 0 → St G (pFin c HO G k (pSpec HO G k u0 0)) X σ s) ∧
    (0 < r → pInv c HO G k u0 N X r σ s)

/-- The search's claims, from a stage that has them. -/
theorem SS.pBase {STK : Nat} {σ s : State} {d : Cfg} (h : SS G STK σ d s) {HO : HashOk Gh} {k : Nat}
    (dpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    SS G STK σ { d with cl := [(sMsg + G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)] } s :=
  h.reclaim fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨h.sb _ dpad, h.clOk _ dpad⟩
    · have big := h.gi.wBig; have kb := h.gi.kBig
      obtain hkB : sX + G.pLen ≤ kB G.pLen := by rcases h.lens with e | e | e <;> rw [e] <;> decide
      exact ⟨by simp [Spec.Rsa.bytesAt], by simp only [ClOk, pStart, List.length_nil, hEnd, fSave, sX] at hkB ⊢; omega_using [big, kb, hkB]⟩
    · exact ⟨h.sb _ dq, h.clOk _ dq⟩

/-- After a candidate that is not p, the next counter (`u'` witnesses read). -/
theorem pGo_vp {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {k u0 N r j u' : Nat} {d : Cfg}
    (hjj : N - (r + 1) = j) (hr : r + 1 ≤ N) (hj : j < 32 * G.pLen) (hl : G.pLen ≤ 384)
    (hcnt : cnt G + 1 < 2 ^ 15) (hwl : G.witB.length = G.witLen)
    (hc : pCount HO G k u0 (32 * G.pLen - 1 - j) j = N) (hR : pSpec HO G k u0 j = pSpec HO G k u0 0)
    (hstep : ∀ m, pCount HO G k u0 (m + 1) j = pCount HO G k u0 m (j + 1))
    (hpu : pU HO G k u0 (j + 1) = u')
    (hspec : pSpec HO G k u0 j = VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (j + 1) (G.witB.drop u'))
    (hu' : u' ≤ G.witLen)
    (dP : fP ∈ d.LS) (dPv : d.V fP = BitVec.ofNat 64 4) (dC : fCounter ∈ d.LS) (dCv : d.V fCounter = BitVec.ofNat 64 j)
    (dO : fOffset ∈ d.LS) (dOv : d.V fOffset = BitVec.ofNat 64 (1 + j * (cnt G + 1)))
    (dU : fUsed ∈ d.LS) (dUv : d.V fUsed = BitVec.ofNat 64 u')
    (dLS : ∀ o ∈ c.LS, o ∈ d.LS ∧ d.V o = c.V o)
    (dpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    VP (St G d X) (pTail (cnt G + 1) G.pLen) (pPost c HO G k u0 N X r) := by
  refine (pCont_vp (X := X) hcnt dP dPv dC dCv dO dOv (by omega_using [hj, hl])).mono (fun _ _ h => h) fun σ s h => ?_
  split at h
  · -- The last counter: `fP` := 2.
    rename_i e
    obtain hN : N = j + 1 := by
      rw [show 32 * G.pLen - 1 - j = 0 by omega_using [e]] at hc; simp only [pCount] at hc; omega_using [hc]
    obtain r0 : r = 0 := by omega_using [hjj, hr, hN]
    subst r0
    refine ⟨by rw [h.2]; rfl, fun _ => ⟨?_, h.1.2⟩, fun h0 => absurd h0 (by decide)⟩
    obtain hd : pSpec HO G k u0 0 = some (none, G.witB.drop u') := by
      rw [← hR, hspec, VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega_using [e])]
    rw [hd]; simp only [pFin]
    obtain lu : G.witLen - (G.witB.drop u').length = u' := by rw [List.length_drop, hwl]; omega_using [hu']
    refine h.1.1.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
      (fun _ h' => absurd h' (by simp))
    · change o ∈ fP :: fUsed :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | ho
      · exact ⟨by simp, by simp [upd]⟩
      · refine ⟨by simp [dU], ?_⟩
        dsimp only [Cfg.setV]
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide),
          upd_self, dUv, lu]
      · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
        refine ⟨by simp [(dLS o ho).1], ?_⟩
        dsimp only [Cfg.setV]
        rw [upd_ne _ _ n4, upd_ne _ _ n3, upd_ne _ _ n2, upd_ne _ _ n4, upd_ne _ _ n1, (dLS o ho).2]
    · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; exact dpad
  · -- The next counter.
    rename_i e
    obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨32 * G.pLen - 1 - j - 1, by omega_using [hj, e]⟩
    rw [hm, hstep] at hc
    obtain hgt := pCount_gt HO G k u0 m (j + 1)
    obtain rpos : 0 < r := by omega_using [hjj, hc, hgt]
    obtain hNr : N - r = j + 1 := by omega_using [hjj, hr]
    refine ⟨by rw [h.2]; simp [rpos], fun h0 => absurd h0 (by omega_using [rpos]), fun _ => ?_⟩
    show (_ ∧ _) ∧ _
    rw [hNr, hpu]
    refine ⟨⟨by omega_using [hr], by omega_using [hj, e], by rw [show 32 * G.pLen - 1 - (j + 1) = m by omega_using [hm]]; exact hc,
      by rw [← hR, hspec]; simp only [pSpec, hpu], hu'⟩, ?_, h.1.2⟩
    obtain r1 := h.1.1.pBase (HO := HO) (k := k) (by exact dpad) (by exact dq)
    obtain eo : 1 + j * (cnt G + 1) + (cnt G + 1) = 1 + (j + 1) * (cnt G + 1) := by rw [Nat.succ_mul]; omega_using []
    refine r1.mono (pCfgJ_V hn (fun o ho => ?_) (by simp [dP]) (by simp) (by simp [dC]) (by simp [dU]) ?_ ?_ ?_ ?_ ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · simp [(dLS o ho).1]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), dPv]
    · dsimp only [Cfg.setV]
      rw [upd_self, eo]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_self]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), dUv]
    · intro o ho
      obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
      dsimp only [Cfg.setV]
      rw [upd_ne _ _ n3, upd_ne _ _ n2, (dLS o ho).2]

/-- After a candidate that ends the search. -/
theorem pStop_vp {c : Cfg} {HO : HashOk Gh} {k u0 N r j v C : Nat} {d : Cfg} (hjj : N - (r + 1) = j)
    (hr : r + 1 ≤ N) (hN : N = j + 1) (dP : fP ∈ d.LS) (dPv : d.V fP = BitVec.ofNat 64 v) (hv : v < 4)
    (fin : ∀ σ s, SS G 176 σ d s → SS G 176 σ (pFin c HO G k (pSpec HO G k u0 0)) s) :
    VP (St G d X) (pTail C G.pLen) (pPost c HO G k u0 N X r) := by
  obtain r0 : r = 0 := by omega_using [hjj, hr, hN]
  subst r0
  exact (pExit_vp dP dPv hv).mono (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, e⟩ =>
    ⟨by rw [e]; rfl, fun _ => ⟨fin σ s h, x⟩, fun h0 => absurd h0 (by decide)⟩

/-- What the search for p needs of its test, beyond `PrimeOk`. -/
structure PLay (G : GP) (g : Geo) (Lp : Impl.Dsa.ProbablePrime.Layout) : Prop where
  bits : Lp.bits = 8 * G.pLen
  cand : Lp.candidate = g.pCand
  size : Lp.size ≤ 8 * wWords G.pLen
  scratch : ∀ r ∈ Lp.scratch, r.1 + r.2 ≤ 8 * wWords G.pLen
  candFit : Lp.candidate + Lp.bits / 8 ≤ 8 * wWords G.pLen
  cand15 : wB G.pLen + Lp.candidate < 2 ^ 15

theorem pBody_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (lay : PLay G g Lp)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    {c : Cfg} (hn : PNot c) {k u0 N : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS)
    (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k)
    (hcand : ∀ j, Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j) (r : Nat) :
    VP (pInv c HO G k u0 N X (r + 1)) (VG.Impl.Rsa.PPC64LE.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
        .ite (.zero .d .r0) (.seq (.block g.pAdvance) (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block [])))
          (.block []),
        .block (cmpF fP 4)])
      (pPost c HO G k u0 N X r) := by
  refine VP.intro fun ⟨hr, hj, hc, hR, hu⟩ => ?_
  generalize hjj : N - (r + 1) = j at hj hc hR hu
  obtain hl : G.pLen ≤ 384 := by omega_using [hlq]
  obtain hcnt : cnt G + 1 ≤ 12 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  obtain hcount : g.count = cnt G := by simp only [Geo.count, hp, hq, cnt]
  obtain ecode : VG.Impl.Rsa.PPC64LE.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
      .ite (.zero .d .r0) (.seq (.block g.pAdvance) (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block [])))
        (.block []),
      .block (cmpF fP 4)] = .seq g.pAttempt (pTail (cnt G + 1) G.pLen) := by
    simp only [Geo.pAdvance, hcount, hp]; rfl
  rw [ecode]
  obtain hoffb : 1 + j * (cnt G + 1) + (cnt G + 1) < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hj) hcnt; omega_using [hlq, hcnt, this]
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
  -- The spec's step.
  obtain hstepS := VG.Proof.Dsa.Generation.primeSearch_step (l := 8 * G.pLen) (n := 8 * G.qLen)
    (q := Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (G.witB.drop (pU HO G k u0 j)) (by omega_using [hj] : j < 4 * (8 * G.pLen))
  dsimp only at hstepS
  rw [hcand j] at hstepS
  change pSpec HO G k u0 j = _ at hstepS
  -- The candidate.
  refine VP.seq ((pAttempt_vp (X := X) (c := pCfgJ c HO G k j (pU HO G k u0 j)) (off := 1 + j * (cnt G + 1))
    HO okp lay.bits lay.cand lay.size lay.scratch lay.candFit lay.cand15 hlq hp hq hk4 hsb hH hwl hk hu
    (by simp [hS]) (by simp [upd, ⟨n1, n2, n3, n4, n5, n6, n7⟩ |> fun hn : PNot c => hn.ne hS]; exact hSv)
    (by simp) (by simp [upd, fOffset, fP]) hoffb (by simp) (by simp [upd, fUsed, fCounter, fOffset, fP])
    (by
      intro o ho
      change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | rfl | rfl | ho
      · decide
      · decide
      · decide
      · decide
      · exact n7 o ho)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, n6⟩)).mono
    (fun _ _ h => h) fun _ _ h => h) ?_
  obtain hn : PNot c := ⟨n1, n2, n3, n4, n5, n6, n7⟩
  obtain hN1 : ∀ (hlast : ∀ m, pCount HO G k u0 (m + 1) j = j + 1), N = j + 1 := fun hlast => by
    rw [← hc]
    rcases Nat.eq_zero_or_pos (32 * G.pLen - 1 - j) with h0 | h0
    · rw [h0]; rfl
    · obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm, hlast]
  obtain padIn : ∀ x y : Nat × List Byte, (sMsg + G.qLen, padTail HO.md G.qLen) ∈ x :: y :: pRest HO.md G k := by
    simp [pRest]
  obtain qIn : ∀ x y : Nat × List Byte, (sQ, qBytes G k) ∈ x :: y :: pRest HO.md G k := by simp [pRest]
  by_cases hs : pShort HO G k j
  · -- Too short: the next counter.
    rw [pAttCfg, ite_eq_left_of_eq_true _ _ (eq_true hs)]
    refine pGo_vp hn hjj (by omega_using [hr]) hj hl (by omega_using [hcnt]) hwl hc hR
      (fun m => by simp only [pCount]; exact ite_eq_left_of_eq_true _ _ (eq_true hs))
      (by simp only [pU]; exact ite_eq_left_of_eq_true _ _ (eq_true hs))
      (by rw [hstepS]; exact ite_eq_left_of_eq_true _ _ (eq_true hs)) hu
      (by simp) (by simp [upd]) (by simp) (by simp [upd, fCounter, fOffset, fP]) (by simp)
      (by simp [upd, fOffset, fP]) (by simp) (by simp [upd, fUsed, fCounter, fOffset, fP])
      (fun o ho => ⟨by simp [ho], by obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho; simp [upd, m1, m2, m3, m4]⟩)
      (padIn _ _) (qIn _ _)
  rw [pAttCfg, ite_eq_right_of_eq_false _ _ (eq_false hs)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at hstepS
  rcases hpp : Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with _ | ⟨b, rr⟩
  · -- The witnesses ran out: `fP` := 0.
    rw [hpp] at hstepS
    refine pStop_vp (v := 0) hjj (by omega_using [hr]) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp [pRes]) (by simp [pRes, upd]) (by decide) fun σ s h => ?_
    rw [← hR, hstepS]; simp only [pFin]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fP :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨by simp [pRes], by simp [pRes, upd]⟩
      · obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho
        exact ⟨by simp [pRes, testCfg, ho], by simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩
    · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; exact padIn _ _
  rcases b
  · -- Not a prime: the next counter.
    rw [hpp] at hstepS
    simp only [Bool.false_eq_true, ↓reduceIte] at hstepS
    refine pGo_vp (u' := G.witLen - rr.length) hn hjj (by omega_using [hr]) hj hl (by omega_using [hcnt]) hwl hc hR
      (fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp only [pU, hs, hpp, ↓reduceIte])
      (by rw [hstepS, ← hwl, VG.Proof.Dsa.Generation.probablePrime_cursor hpp]) (by omega_using [])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fCounter, fOffset, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fOffset, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd])
      (fun o ho => ⟨by simp [pRes, testCfg, ho], by
        obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho; simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩)
      (by simp [pRes, testCfg, pRest]) (by simp [pRes, testCfg, pRest])
  · -- A probable prime: `fP` := 1.
    rw [hpp] at hstepS
    simp only [↓reduceIte] at hstepS
    refine pStop_vp (v := 1) hjj (by omega_using [hr]) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp [pRes]) (by simp [pRes, upd]) (by decide) fun σ s h => ?_
    rw [← hR, hstepS]; simp only [pFin]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => ⟨h', rfl⟩) (fun _ h' => absurd h' (by simp))
    change o ∈ fP :: fUsed :: c.LS at ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | rfl | ho
    · exact ⟨by simp [pRes], by simp [pRes, upd]⟩
    · exact ⟨by simp [pRes, testCfg], by simp [pRes, testCfg, upd, fUsed, fP]⟩
    · obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho
      exact ⟨by simp [pRes, testCfg, ho], by simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩

/-- The search for p from the seed at `k`, with `u0` witnesses read. -/
theorem pPart_vp {g : Geo} (HO : HashOk g.G) {Lp : Impl.Dsa.ProbablePrime.Layout} (okp : PrimeOk Lp g.pCode)
    (lay : PLay G g Lp)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    {c : Cfg} (hn : PNot c) {k u0 : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS)
    (hSv : c.V fSeed = G.seeds + BitVec.ofNat 64 k) (hu0 : u0 ≤ G.witLen)
    (hcand : ∀ j, Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j)
    {d : Cfg} (dU : fUsed ∈ d.LS) (dUv : d.V fUsed = BitVec.ofNat 64 u0)
    (dLS : ∀ o ∈ c.LS, o ∈ d.LS ∧ d.V o = c.V o)
    (dpad : (sMsg + G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    VP (St G d X) g.pPart (St G (pFin c HO G k (pSpec HO G k u0 0)) X) := by
  unfold Geo.pPart
  simp only [VG.Impl.Rsa.PPC64LE.Keys.seqs]
  obtain hN := pCount_gt HO G k u0 (32 * G.pLen - 1) 0
  generalize hNN : pCount HO G k u0 (32 * G.pLen - 1) 0 = N at hN
  obtain hl : G.pLen ≤ 384 := by omega_using [hlq]
  obtain hpL : 0 < G.pLen := by omega_using [hlq]
  refine VP.seq ?_ ?_ (G := pInv c HO G k u0 N X N)
  · rw [List.append_assoc]
    refine VP.block_append (G := St G (d.setV fCounter (BitVec.ofNat 64 0)) X)
      (stImm_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.2⟩) ?_
    refine VP.block_append (G := St G ((d.setV fCounter (BitVec.ofNat 64 0)).setV fOffset (BitVec.ofNat 64 1)) X)
      (stImm_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 0)) (fun σ s h => h.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.2⟩) ?_
    refine stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 0)).setV fOffset (BitVec.ofNat 64 1))
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨⟨Nat.le_refl _, by simp; omega_using [hlq],
        by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self], by simp only [Nat.sub_self]; exact hu0⟩,
        ?_, h.2⟩
    obtain r1 := h'.pBase (HO := HO) (k := k) (by exact dpad) (by exact dq)
    rw [Nat.sub_self]
    refine r1.mono (pCfgJ_V hn (fun o ho => by simp [(dLS o ho).1]) (by simp) (by simp) (by simp) (by simp [dU])
      (by simp [upd]) (by simp [upd, fOffset, fP]) (by simp [upd, fCounter, fOffset, fP])
      (by simp [upd, fUsed, fCounter, fOffset, fP, pU]; exact dUv) fun o ho => ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho
    simp [upd, m2, m3, m4]; exact (dLS o ho).2
  rw [show N = N - 1 + 1 by omega_using [hN]]
  exact VP.loop (I := pInv c HO G k u0 (N - 1 + 1) X)
    (pBody_vp HO okp lay hlq hp hq hk4 hsb hH hwl hn hk hS hSv hcand) _

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.GPart`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.GStep`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Gen.GCmp`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: comparisons of arrays

`ltS_vp`: the header word `d` := `[a] < [b]`, the borrow of `[a] − [b]` into
the array `aTmp`, which no stage keeps. `andCmp_vp`: the header word `d` :=
the header words `a` and `b` and'ed, and into `r0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (num slot)
open VG.Proof.Rsa.PPC64LE.Keys (Ws opRegs sub3_ok stBorrow_ok andS_ok)
open VG.Impl.Rsa.PPC64LE.Keys (seqs sub3 stBorrow andS)
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `[a] − [b]` into `aTmp`: the borrow, `[a] < [b]`, in `r9`. -/
theorem sub3b_vp {a b : Nat} (cert : CertK (sub3 aTmp a b)) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live) :
    VP (KSt G c X) (sub3 aTmp a b)
      (fun σ t => KSt G c X σ t ∧ (t.gpr .r9).toNat = if c.A a < c.A b then 1 else 0) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  obtain hw := h.ws kr
  obtain va := h.arrs.get ha
  obtain vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w aTmp + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r9).toNat ∧ (t.gpr .r9).toNat ≤ 1) rfl
    ((sub3_ok hw (by decide) (h.liveOk a ha) (h.liveOk b hb) (by decide) hta htb).mono
      fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R sp f => ⟨⟨⟨(h.of_op R sp f (by decide) k rfl).mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ⟨List.mem_cons_of_mem _ hj,
        VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ fun e => htl (e ▸ hj)⟩) (fun d hd => ⟨hd, rfl⟩), x⟩,
      kr.of_keep R⟩, ?_⟩
  simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
  rw [va, vb] at v
  obtain lt : num t.mem G.KB G.w aTmp < 2 ^ (32 * G.w) := val32_lt _ _ _ _
  obtain blt : c.A b < 2 ^ (32 * G.w) := vb ▸ val32_lt _ _ _ _
  generalize 2 ^ (32 * G.w) = M at v lt blt
  obtain m1 : M * 1 = M := Nat.mul_one M
  obtain m0 : M * 0 = 0 := Nat.mul_zero M
  rcases (by omega_using [br] : (t.gpr .r9).toNat = 0 ∨ (t.gpr .r9).toNat = 1) with e | e <;> rw [e] at v ⊢ <;> split <;> omega_arith

/-- The header word `d` := `[a] < [b]`. -/
theorem ltS_vp {d a b : Nat} (c1 : CertK (sub3 aTmp a b)) (c2 : CertK (.block (stBorrow d)))
    (ha : a ∈ c.live) (hb : b ∈ c.live) (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live)
    (hd : KlsOk d) :
    VP (KSt G c X) (seqs (ltS d a b))
      (KSt G { c with KV := KU c.KV d (if c.A a < c.A b then 1 else 0), kls := d :: c.kls } X) := by
  rw [show seqs (ltS d a b) = .seq (sub3 aTmp a b) (.block (stBorrow d)) from rfl]
  refine VP.seq (sub3b_vp c1 ha hb hta htb htl) ?_
  refine ks_vp c2 (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, b9⟩ => ?_
  obtain hw := h.ws kr
  refine h.ksOp (js := []) (ds := [d]) (P := fun t => slot t.mem G.KB d = (s.gpr .r9).toNat) rfl
    (by rw [← List.append_nil (stBorrow d)]
        exact stBorrow_ok hw hd.1 (by show (s.gpr .r9).toNat ≤ 1; rw [b9]; split <;> decide)
          fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_opS R sp f hd k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, b9]), x⟩, kr.of_keep R⟩

/-- The header word `d` := the header words `a` and `b` (each 0 or 1)
and'ed, and `r0` := it. -/
theorem andCmp_vp {d a b : Nat} (cert : CertK (.block (andS d a b ++ ([.load .w .r0 .r31 d] : List Instr))))
    (hd : KlsOk d) (ha : a ∈ c.kls) (hb : b ∈ c.kls) (ba : c.KV a ≤ 1) (bb : c.KV b ≤ 1) :
    VP (KSt G c X) (.block (andS d a b ++ ([.load .w .r0 .r31 d] : List Instr)))
      (fun σ t => KSt G { c with KV := KU c.KV d (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0), kls := d :: c.kls } X σ t ∧
        isa.eval (.zero .d .r0) t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  obtain hw := h.ws kr
  obtain va : slot (G.ksState s).mem G.KB a = c.KV a := h.ksl a ha
  obtain vb : slot (G.ksState s).mem G.KB b = c.KV b := h.ksl b hb
  have hz : 160 ≤ kz G.pLen := hw.hdr_le
  have d4 : d + 4 ≤ 160 := hd.1
  refine h.ksOp (js := []) (ds := [d]) (ws := opRegs ++ [.r0]) (P := fun t =>
      slot t.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) ∧
      isa.eval (.zero .d .r0) t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) rfl ?_
    fun t k ⟨e, z⟩ R sp f => ⟨⟨⟨h.of_opS R sp f hd k e, x⟩, kr.of_keep R⟩, z⟩
  refine andS_ok hw hd.1 (h.kslOk a ha).1 (h.kslOk b hb).1 (by rw [va]; exact ba) (by rw [vb]; exact bb)
    fun t₁ w₁ k₁ v₁ R₁ => ?_
  obtain hx : WP isa (.block [.load .w .r0 .r31 d]) t₁ fun t₂ =>
      (t₂.gpr .r0 = (t₁.mem.readW (t₁.gpr .r31 + BitVec.ofNat 64 d) 32).setWidth 64 ∧ t₂.mem = t₁.mem) ∧
        VG.Proof.Bignum.PPC64LE.Keep [.r0] t₁ t₂ :=
    WP.wr (exec_load_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega_using [d4])
      (by rw [w₁.r31]; exact w₁.scr.ld (show d + 4 ≤ kz G.pLen by omega_using [hz, d4]))) fun t₂ u sp lr => WP.block_nil
      ⟨⟨u.gpr, u.mem⟩, ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr, sp, lr⟩⟩
  refine WP.mono hx fun t₂ ⟨⟨u0, m2⟩, k2⟩ => ?_
  obtain v : slot t₂.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by rw [m2, v₁, va, vb]
  refine ⟨w₁.of_keep k2, by rw [m2]; exact k₁, ⟨v, ?_⟩, R₁.trans k2⟩
  obtain r : t₂.gpr .r0 = BitVec.ofNat 64 (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
    obtain rd : (t₁.mem.readW (t₁.gpr .r31 + BitVec.ofNat 64 d) 32).toNat =
        (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
      rw [w₁.r31]; have := v; rw [m2] at this; exact this
    refine BitVec.eq_of_toNat_eq ?_
    rw [u0, VG.Proof.Bignum.PPC64LE.toNat_ext32, rd, BitVec.toNat_ofNat]
    split <;> rfl
  rw [eval_zero_ofNat _ _ (by split <;> decide) r]
  by_cases hc : c.KV a = 1 ∧ c.KV b = 1 <;> simp [hc]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: one `h` of the generator search

`gStep` (`gStep_vp`): `h`, the `pLen` bytes at `fH` of `rand`, into
array `aH` of the key working space (zeroed first); unless `1 < h < p − 1`,
nothing more; else `g = h^((p−1)/q) mod p` by the power in the P space, and
if `g > 1`, `g` big-endian at `sG` and `fG` := 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 stBorrow andS)
open VG.Proof.Mont (off)

/-- The `h` at byte `i` of `rand`. -/
abbrev hAt (G : GP) (i : Nat) : List Byte := (G.witB.drop i).take G.pLen

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

/-- The `h` at byte `i`, in memory. -/
theorem GI.hBytes (h : GI G STK σ V LS s) {i : Nat} (hi : i + G.pLen ≤ G.witLen) :
    Spec.Rsa.bytesAt s.mem (G.wit + BitVec.ofNat 64 i) G.pLen = hAt G i := by
  have fit := h.witFit
  obtain hw : Spec.Rsa.bytesAt s.mem G.wit G.witLen = G.witB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.wit_apart (by omega_using [fit]), ← h.hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.witLen = i + G.pLen + d := ⟨G.witLen - i - G.pLen, by omega_using [hi]⟩
  show _ = (G.witB.drop i).take G.pLen
  rw [← hw, hd, VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.append_assoc, List.drop_left' (by simp [Spec.Rsa.bytesAt]),
    List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The `h` at byte `i`, as a source of a load. -/
theorem GI.hSrc (h : GI G STK σ V LS s) {i : Nat} (hi : i + G.pLen ≤ G.witLen) (hp : 0 < G.pLen) :
    Covers [⟨G.wit + BitVec.ofNat 64 i, G.pLen⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨G.wit + BitVec.ofNat 64 i, G.pLen⟩ G.rScr ∧
      (G.wit + BitVec.ofNat 64 i).toNat + G.pLen ≤ 2 ^ 64 ∧
      Spec.Rsa.bytesAt s.mem (G.wit + BitVec.ofNat 64 i) G.pLen = hAt G i := by
  have fit := h.witFit
  obtain sub : Region.Sub ⟨G.wit + BitVec.ofNat 64 i, G.pLen⟩ G.rWit := Offset.sub_base _ hi
  obtain hC := h.pre.wC; rw [h.hG] at hC
  refine ⟨Covers.left (Covers.one ⟨G.rWit, by rw [h.rd, h.pre.rd, h.hG]; simp,
    Offset.contains_base _ hi (by omega_using [hi, hp, fit])⟩), hC.sub_left sub, ?_, h.hBytes hi⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi, hp, fit]),
    Nat.mod_eq_of_lt (by omega_using [hi, hp, fit])]
  omega_using [hi, fit]

/-- The bytes of a covered region, one by one. -/
theorem covers_bytes {rs : List Region} {P : Addr} {n : Nat} (hc : Covers [⟨P, n⟩] rs)
    (hfit : P.toNat + n ≤ 2 ^ 64) : ∀ i < n, InRegions rs (off P i) 1 := fun i hi =>
  hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (show i + 1 ≤ n by omega_using [hi]) (by omega_using [hfit, hi])⟩

end

/-- The stage after an `h` (`hv`), from `p` (`pv`) and `(p − 1) / q` (`ev`). -/
def gOut (c : Cfg) (G : GP) (hv pv ev : Nat) : Cfg :=
  if 1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv then
    ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1
  else c

/-- Simplifies the arrays and key header words of `gStep`'s stages. -/
syntax "g_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| g_simp $[$loc]?) => `(tactic| simp only [KU, VG.Proof.Rsa.KeyWorkspace.upd, aPm1, aH, aOne,
    aZero, aTmp, slLo, slHi, Nat.reduceEqDiff, ↓reduceIte] $[$loc]?)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `h`'s pointer and its length, in the key working space. -/
theorem hPtrK_vp {H : Addr} (hH : fH ∈ c.LS) (hHv : c.V fH = H) :
    VP (KSt G c X) (.block [ld .r6 fH, .li .r8 G.pLen])
      (fun σ s => KSt G c X σ s ∧ s.gpr .r6 = H ∧ s.gpr .r8 = BitVec.ofNat 64 G.pLen) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block [ld .r6 fH, .li .r8 G.pLen]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have l := h.lens
  have hE := h.gi.hEnd_le
  obtain p15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.cons (s' := s.write .r6 H) ?_ (WP.cons (s' := (s.write .r6 H).write .r8 (BitVec.ofNat 64 G.pLen))
    (exec_li p15) (WP.block_nil ?_))
  · rw [show ld .r6 fH = .load .d .r6 .r28 fH from rfl, exec_load_d (by decide) ⟨by decide, by decide⟩
      (by rw [h.gi.r28]; exact h.gi.inRdWr (by simp only [hEnd, fSave, fH] at hE ⊢; omega_using [hE])), h.gi.r28,
      show s.mem.readW (G.scr + BitVec.ofNat 64 fH) 64 = H from (h.gi.slotV hH).trans hHv]
  obtain k : BKeep [.r6, .r8] s ((s.write .r6 H).write .r8 (BitVec.ofNat 64 G.pLen)) :=
    (VG.Proof.Bignum.PPC64LE.Keep.write s .r6 H).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r8 _)
  refine ⟨⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ rfl k.sp, x⟩, kr.of_keep ⟨k.gpr, k.rd, k.wr⟩⟩, ?_, (Upd.write _ _ _).gpr⟩
  rw [(Upd.write _ .r8 _).other .r6 (by decide), (Upd.write _ _ _).gpr]

/-- A stage with more arrays than `c₀` and the same header words and claims is `c₀`'s. -/
theorem SS.back {σ s : State} {c' c₀ : Cfg} (h : SS G 176 σ c' s) (hk : c₀.kls = []) (eV : c'.V = c₀.V)
    (eLS : c'.LS = c₀.LS) (ecl : c'.cl = c₀.cl) (eA : ∀ j ∈ c₀.live, j ∈ c'.live ∧ c'.A j = c₀.A j) :
    SS G 176 σ c₀ s :=
  h.mono (fun o ho => ⟨eLS ▸ ho, by rw [eV]⟩) (fun y hy => ecl ▸ hy) eA (fun d hd => by simp [hk] at hd)

theorem beq_zero_of_iff {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) : (x == 0) = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]; exact beq_iff_eq.mpr (h.mpr hp)
  · rw [decide_eq_false hp]; exact beq_false_of_ne fun e => hp (h.mp e)

theorem ite01_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0) = 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite01_le (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  by_cases hp : p <;> simp [hp]

/-- One `h` (the `pLen` bytes at byte `i` of the tape, which `fH` points at):
the stage `gOut`. -/
theorem gStep_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {pv ev i : Nat} (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hZ : aZero ∈ c.live) (hZv : c.A aZero = 0) (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hkls : c.kls = [])
    (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x ∧ Apart sG G.pLen x)
    (hH : fH ∈ c.LS) (hHv : c.V fH = G.wit + BitVec.ofNat 64 i) (hi : i + G.pLen ≤ G.witLen) :
    VP (St G c X) g.gStep (St G (gOut c G (Spec.Dsa.decodeBE (hAt G i)) pv ev) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  unfold Geo.gStep
  rw [hg, hgq]
  obtain hplt : pv < 2 ^ (8 * G.pLen) := by rwa [Nat.pow_mul]
  generalize hhv : Spec.Dsa.decodeBE (hAt G i) = hv
  have eos : Spec.Rsa.os2ip (hAt G i) = hv := hhv
  obtain kc : ∀ (v : Nat), ∀ j ∈ c.live, j ∈ aH :: aH :: c.live ∧ KU (KU c.A aH (c.A aZero)) aH v j = c.A j :=
    fun v j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj), by
      have : j ≠ aH := fun e => hHl (e ▸ hj)
      show VG.Proof.Rsa.KeyWorkspace.upd (VG.Proof.Rsa.KeyWorkspace.upd c.A aH _) aH v j = _
      rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ this, VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ this]⟩
  -- Into the key working space; `aH` := 0, then `h`.
  refine VP.seq ksEnter_vp ?_
  refine VP.seq (copy_vp (o := aH) (a := aZero) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31]) (copy aH aZero), by kernel_rfl⟩ (by decide) hZ (by decide)) ?_
  refine VP.seq (hPtrK_vp hH hHv) ?_
  refine VP.seq (loadZ_vp (j := aH) (n := G.pLen) (bs := hAt G i) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6,
          .r8]) (VG.Impl.Rsa.PPC64LE.CrtValues.load aH), by kernel_rfl⟩
    (by decide) List.mem_cons_self (by g_simp; exact hZv)
    (by rcases l with e | e | e <;> rw [e] <;> decide)
    (by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide) fun σ s h => ?_) ?_
  · obtain ⟨cov, dj, _, b⟩ := h.1.gi.hSrc hi (by rcases l with e | e | e <;> rw [e] <;> decide)
    exact ⟨cov, dj.sub_right h.1.gi.kSub, b⟩
  rw [hhv]
  -- `1 < h`, `h < p − 1` and both.
  refine VP.seq (ltS_vp (d := slLo) (a := aOne) (b := aH) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31]) (sub3 aTmp aOne aH), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31]) (.block (stBorrow slLo)),
        by kernel_rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hTl⟩) ⟨by decide, by decide⟩) ?_
  refine VP.seq (ltS_vp (d := slHi) (a := aH) (b := aPm1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31]) (sub3 aTmp aH aPm1), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31]) (.block (stBorrow slHi)),
        by kernel_rfl⟩
    (by simp) (by simp [hM]) (by decide) (by decide)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hTl⟩) ⟨by decide, by decide⟩) ?_
  refine VP.seq (andCmp_vp (d := slLo) (a := slLo) (b := slHi) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31])
      (.block (andS slLo slLo slHi ++ ([.load .w .r0 .r31 slLo] : List Instr))), by kernel_rfl⟩
    ⟨by decide, by decide⟩ (by simp) (by simp) (by g_simp; exact ite01_le _) (by g_simp; exact ite01_le _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- Out of range: nothing more.
    refine VP.block_nil fun σ s hh => ⟨?_, hh.1.1.1.2⟩
    obtain ⟨⟨⟨⟨h, _⟩, _⟩, e⟩, z⟩ := hh
    rw [e] at z
    obtain nr : ¬(1 < hv ∧ hv < pv - 1) := by
      intro hr; simp only [Option.some.injEq, decide_eq_true_eq] at z
      g_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact z ⟨(ite01_eq_one _).mpr hr.1, (ite01_eq_one _).mpr hr.2⟩
    obtain nc : ¬(1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv) := fun hc => nr ⟨hc.1, hc.2.1⟩
    simp only [gOut, nc, ↓reduceIte]
    exact h.back hkls rfl rfl rfl (kc hv)
  · by_cases hr : 1 < hv ∧ hv < pv - 1
    swap
    · refine VP.of_false fun σ s hh => ?_
      obtain ⟨⟨_, e⟩, z⟩ := hh
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at z
      g_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact hr ⟨(ite01_eq_one _).mp z.1, (ite01_eq_one _).mp z.2⟩
    obtain eq : gOut c G hv pv ev = if 1 < hv ^ ev % pv then
        ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1 else c := by
      simp only [gOut, hr, true_and]
    rw [eq]
    generalize hgv : hv ^ ev % pv = gv
    obtain glt : gv < pv := hgv ▸ Nat.mod_lt _ (by omega_using [hp2])
    -- `g`, back at the stage `c`.
    refine VP.seq ((power_vp (c := c) (X := X) (H := G.wit + BitVec.ofNat 64 i) (hb := hAt G i) cert hPc hpv hp2
      hpo hEc hev hH hHv (fun x hx => (hcl x hx).1) fun σ s h => ?_).mono
      (fun σ s hh => ⟨hh.1.1.1.1.back hkls rfl rfl rfl (kc hv), hh.1.1.1.2⟩)
      (G' := fun σ t => St G c X σ t ∧ VG.Proof.MillerRabin.PPC64LE.Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
        VG.Proof.MillerRabin.PPC64LE.arr t.mem G.pS (pw G.pLen) 4 = gv ∧ (t.gpr .r0 = 0 ↔ 1 < gv ∧ gv < pv))
      fun σ t ⟨h, en, v4, r0⟩ => ⟨h, en, by rw [v4, eos, hgv], by rw [← hgv, ← eos, ← v4]; exact r0⟩) ?_
    · obtain ⟨cov, dj, fit, b⟩ := h.1.gi.hSrc hi (by rcases l with e | e | e <;> rw [e] <;> decide)
      exact ⟨covers_bytes cov fit, dj, fit, b⟩
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [eval_zero, eval_zero, beq_zero_of_iff h₁.2.2.2, beq_zero_of_iff h₂.2.2.2]) ?_ ?_
    · -- 1 < g: stored.
      by_cases h1 : 1 < gv
      · simp only [h1, ↓reduceIte]
        exact (gOut_vp (c := c) (g := gv) (by omega_using [hplt, glt]) fun x hx => (hcl x hx).2).mono
          (fun σ s ⟨⟨h, en, v4, _⟩, _⟩ => ⟨h, en, v4⟩) fun _ _ h => h
      · refine VP.of_false fun σ s ⟨⟨_, _, _, r0⟩, z⟩ => h1 ?_
        rw [eval_zero, beq_zero_of_iff r0] at z
        simp only [Option.some.injEq, decide_eq_true_eq] at z
        exact z.1
    · by_cases h1 : 1 < gv
      · refine VP.of_false fun σ s ⟨⟨_, _, _, r0⟩, z⟩ => ?_
        rw [eval_zero, beq_zero_of_iff r0] at z
        simp only [Option.some.injEq, decide_eq_false_iff_not] at z
        exact z ⟨h1, glt⟩
      · simp only [h1, ↓reduceIte]
        exact VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => h

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: the search for g

`gPart_vp`: the window of `rand` at `w` (`fHs`, of `HL` octets, `fHsLen`) read
candidate by candidate, `gStep` on each, until one gives a g above 1 (`fG`
:= 1, g at `sG`) or fewer than `p_len` octets are left (`fG` := 2), as
`Spec.Dsa.generator` searches its candidates; `fH` then points past the
candidates read (`generatorCount`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- The window's octets. -/
abbrev hsW (G : GP) (w HL : Nat) : List Byte := (G.witB.drop w).take HL

/-- The window's candidates from the `k`-th. -/
abbrev gCands (G : GP) (w HL k : Nat) : List Nat :=
  (Spec.Dsa.generationChunks G.pLen ((hsW G w HL).drop (k * G.pLen))).map Spec.Dsa.decodeBE

/-- The search's header words at the `k`-th h. -/
abbrev gCfg (c : Cfg) (G : GP) (w HL k : Nat) : Cfg :=
  ((c.setV fH (G.wit + BitVec.ofNat 64 (w + k * G.pLen))).setV fHLeft (BitVec.ofNat 64 (HL - k * G.pLen))).setV fG 4

/-- Whether the h at byte `i` of `rand` gives a g above 1. -/
abbrev gOk (G : GP) (pv ev i : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (hAt G i) ∧ Spec.Dsa.decodeBE (hAt G i) < pv - 1 ∧
    1 < Spec.Dsa.decodeBE (hAt G i) ^ ev % pv

/-- The search's iterations from the `k`-th h, with `m` left. -/
def gCount (G : GP) (w pv ev : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | m + 1, k => if gOk G pv ev (w + k * G.pLen) then k + 1 else gCount G w pv ev m (k + 1)

theorem gCount_gt (G : GP) (w pv ev : Nat) : ∀ m k, k < gCount G w pv ev m k
  | 0, k => by simp [gCount]
  | m + 1, k => by
    simp only [gCount]; split
    · omega_using []
    · exact Nat.lt_of_succ_lt (gCount_gt G w pv ev m (k + 1))

/-- The generator the spec finds from the `k`-th h. -/
abbrev gRes (G : GP) (w HL pv qv k : Nat) : Option Nat := Spec.Dsa.generator pv qv (gCands G w HL k)

/-- The candidates the spec reads from the `k`-th h. -/
abbrev gNum (G : GP) (w HL pv qv k : Nat) : Nat :=
  VG.Proof.Dsa.Generation.generatorCount pv qv (gCands G w HL k)

/-- The stage after the search: `fH` past the candidates read. -/
def gFin (c : Cfg) (G : GP) (w HL pv qv : Nat) : Cfg :=
  match gRes G w HL pv qv 0 with
  | some g => ((({ c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 64 (w + gNum G w HL pv qv 0 * G.pLen)))
  | none => (c.setV fG 2).setV fH (G.wit + BitVec.ofNat 64 (w + gNum G w HL pv qv 0 * G.pLen))

/-- The search with `r` iterations left of `N`. -/
abbrev gInv (c : Cfg) (G : GP) (w HL pv ev qv N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ HL / G.pLen ∧ gCount G w pv ev (HL / G.pLen - (N - r)) (N - r) = N ∧
    gRes G w HL pv qv (N - r) = gRes G w HL pv qv 0 ∧
    N - r + gNum G w HL pv qv (N - r) = gNum G w HL pv qv 0) ∧ St G (gCfg c G w HL (N - r)) X σ s

/-- A candidate of the window is the `h` at its place in `rand`. -/
theorem hsW_take {G : GP} {w HL i : Nat} (hi : i + G.pLen ≤ HL) :
    ((hsW G w HL).drop i).take G.pLen = hAt G (w + i) := by
  simp only [hsW, hAt, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega_using [hi]), Nat.add_comm]

theorem hsW_length {G : GP} {w HL : Nat} (hw : w + HL ≤ G.witLen) (hl : G.witB.length = G.witLen) :
    (hsW G w HL).length = HL := by
  simp only [hsW, List.length_take, List.length_drop, hl]; omega_using [hw]

section
variable {G : GP} {X : State → Prop}

/-- `r3` := `f r3`, from a known `r3`. -/
theorem r3op_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G 176 σ (c σ) s)
    {i : Instr} (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r3]) (.block [i]) hc).isSome = true)
    {f : BitVec 64 → BitVec 64} (he : ∀ s : State, exec i s = some (s.write .r3 (f (s.gpr .r3))))
    {x : BitVec 64} (hx : ∀ σ s, P σ s → s.gpr .r3 = x)
    (k : ∀ σ s t, P σ s → SS G 176 σ (c σ) t → t.gpr .r3 = f x → Q σ t) : VP P (.block [i]) Q := by
  refine VP.pub (SS.pub hF) [.r3] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx _ _ h₁, hx _ _ h₂]) fun σ s hs => ?_
  refine WP.wr (he s) fun t u sp _ => WP.block_nil (k σ s t hs ((hF σ s hs).of_upd u sp (by decide)) ?_)
  rw [u.gpr, hx σ s hs]

/-- The next `h`: `fH` := `fH` + `pLen`, `fHLeft` := `fHLeft` − `pLen`. -/
theorem adv_vp {d : Cfg} (hH : fH ∈ d.LS) (hL : fHLeft ∈ d.LS) :
    VP (St G d X) (.block [ld .r3 fH, .addi .r3 .r3 G.pLen, st .r3 fH, ld .r3 fHLeft, .subi .r3 .r3 G.pLen,
        st .r3 fHLeft])
      (St G ((d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)).setV fHLeft (d.V fHLeft - BitVec.ofNat 64 G.pLen)) X) := by
  by_cases l : G.pLen < 2 ^ 15
  swap
  · exact VP.of_false fun σ s h => l (by rcases h.1.lens with e | e | e <;> rw [e] <;> decide)
  rw [show ([ld .r3 fH, .addi .r3 .r3 G.pLen, st .r3 fH, ld .r3 fHLeft, .subi .r3 .r3 G.pLen, st .r3 fHLeft] :
      List Instr) = [ld .r3 fH] ++ ([.addi .r3 .r3 G.pLen] ++ ([st .r3 fH] ++ ([ld .r3 fHLeft] ++
        ([.subi .r3 .r3 G.pLen] ++ [st .r3 fHLeft])))) from rfl]
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = d.V fH)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => h.1.gi.slotV hH) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r3 = d.V fH + BitVec.ofNat 64 G.pLen)
    (r3op_vp (c := fun _ => d) (f := (· + BitVec.ofNat 64 G.pLen)) (fun σ s h => h.1.1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3]) (.block [.addi .r3 .r3 G.pLen]), rfl⟩ (fun s => exec_addi (d := .r3) (n := .r3) (by decide) l)
      (fun σ s h => h.2) fun σ s t ⟨⟨_, x⟩, _⟩ h' e => ⟨⟨h', x⟩, e⟩) ?_
  obtain hHL : fHLeft ∈ (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)).LS := List.mem_cons_of_mem _ hL
  refine VP.block_append (G := St G (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) X)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩) ?_
  refine VP.block_append (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) X σ s ∧
      s.gpr .r3 = d.V fHLeft)
    (ld_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) (fun σ s h => h.1) (by decide) (by decide)
      (by decide) (fun σ s h => (h.1.gi.slotV hHL).trans (by simp [upd, fHLeft, fH]))
      fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
  refine VP.block_append (G := fun σ s => St G (d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) X σ s ∧
      s.gpr .r3 = d.V fHLeft - BitVec.ofNat 64 G.pLen)
    (r3op_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) (f := (· - BitVec.ofNat 64 G.pLen))
      (fun σ s h => h.1.1)
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r3]) (.block [.subi .r3 .r3 G.pLen]), rfl⟩
      (fun s => exec_subi (d := .r3) (n := .r3) (by decide) (Nat.le_of_lt l)) (fun σ s h => h.2)
      fun σ s t ⟨⟨_, x⟩, _⟩ h' e => ⟨⟨h', x⟩, e⟩) ?_
  exact st_vp (c := fun _ => d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)) (fun σ s h => h.1.1)
    (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩

/-- The search's header words agree with `c`'s but for `fH`, `fHLeft` and
`fG`, with `fG` and `fH` as the search leaves them. -/
theorem gV {c : Cfg} (hfH : fH ∉ c.LS) (hfL : fHLeft ∉ c.LS) {V : Nat → BitVec 64} {LS : List Nat}
    {v x : BitVec 64} (hLS : ∀ o ∈ c.LS, o ∈ LS) (hV : ∀ o, o ≠ fH → o ≠ fHLeft → o ≠ fG → V o = c.V o)
    (hG : fG ∈ LS) (hVG : V fG = v) (hH : fH ∈ LS) (hVH : V fH = x) :
    ∀ o ∈ fH :: fG :: c.LS, o ∈ LS ∧ V o = upd (upd c.V fG v) fH x o := by
  intro o ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | ho
  · exact ⟨hH, by rw [hVH, upd_self]⟩
  · exact ⟨hG, by rw [hVG, upd_ne _ _ (by decide), upd_self]⟩
  · refine ⟨hLS o ho, ?_⟩
    obtain e1 : o ≠ fH := fun h => hfH (h ▸ ho)
    by_cases e : o = fG
    · subst e; rw [hVG, upd_ne _ _ (by decide), upd_self]
    · rw [upd_ne _ _ e1, upd_ne _ _ e, hV o e1 (fun h => hfL (h ▸ ho)) e]

/-- What `gStep` needs of the stage the search starts from. -/
structure GReq (G : GP) (c : Cfg) (pv ev : Nat) : Prop where
  hM : aPm1 ∈ c.live
  hMv : c.A aPm1 = pv - 1
  hO : aOne ∈ c.live
  hOv : c.A aOne = 1
  hZ : aZero ∈ c.live
  hZv : c.A aZero = 0
  hHl : aH ∉ c.live
  hTl : aTmp ∉ c.live
  hkls : c.kls = []
  hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl
  hpv : pv < 256 ^ G.pLen
  hp2 : 2 ≤ pv
  hpo : pv % 2 = 1
  hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl
  hev : ev < 256 ^ eBytes G.pLen G.qLen
  hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x ∧ Apart sG G.pLen x
  hfH : fH ∉ c.LS
  hfL : fHLeft ∉ c.LS

theorem gBody_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {c : Cfg} {pv ev qv N w HL : Nat} (R : GReq G c pv ev) (hw : w + HL ≤ G.witLen)
    (hwl : G.witB.length = G.witLen) (h64 : HL < 2 ^ 64) (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G w HL pv ev qv N X (r + 1)) (seqs [.block ([ld .r3 fHLeft, .li .r4 g.pLen] ++ ltR),
        .ite (.zero .d .r0) (.block (stImm fG 2))
          (seqs [g.gStep, .block [ld .r3 fH, .addi .r3 .r3 g.pLen, st .r3 fH, ld .r3 fHLeft,
            .subi .r3 .r3 g.pLen, st .r3 fHLeft]]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧
        (r = 0 → St G (gFin c G w HL pv qv) X σ s) ∧ (0 < r → gInv c G w HL pv ev qv N X r σ s)) := by
  refine VP.intro fun ⟨hr, hk, hc, hres, hnum⟩ => ?_
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  obtain hpL : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  obtain hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  generalize hMM : HL / G.pLen = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres hnum
  obtain kL : ∀ j, j ≤ M → j * G.pLen ≤ HL := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  obtain hlen := hsW_length (G := G) hw hwl
  rw [hg]
  -- Whether an h is left.
  refine VP.seq (G := fun σ s => St G (gCfg c G w HL k) X σ s ∧
      isa.eval (.zero .d .r0) s = some (decide (HL - k * G.pLen < G.pLen)))
    (ltF_vp (c := fun _ => gCfg c G w HL k) (x := BitVec.ofNat 64 (HL - k * G.pLen)) (fun σ s h => h.1)
      (by decide) (by decide) hp15 (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fHLeft, fG]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h64])]⟩) ?_
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- An h: `gStep`, then the next.
    obtain hi : k * G.pLen + G.pLen ≤ HL := by have := kL (k + 1) hkM; rwa [Nat.succ_mul] at this
    obtain e0 : decide (HL - k * G.pLen < G.pLen) = false := decide_eq_false (by omega_using [hi])
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega_using [hkM]⟩
    rw [hm] at hc; simp only [gCount] at hc
    obtain hbl : G.pLen ≤ ((hsW G w HL).drop (k * G.pLen)).length := by
      simp only [List.length_drop, hlen]; omega_using [hi]
    obtain hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL hbl
    obtain cstep := VG.Proof.Dsa.Generation.generatorCount_chunks_step (p := pv) (q := qv) hpL hbl
    rw [hsW_take hi, List.drop_drop] at hstep cstep
    simp only [VG.Proof.Dsa.powMod_eq, ← hev'] at hstep cstep
    obtain stepVP := gStep_vp (c := gCfg c G w HL k) (X := X) (i := w + k * G.pLen) hg hgq cert R.hM R.hMv R.hO
      R.hOv R.hZ R.hZv R.hHl R.hTl R.hkls R.hPc R.hpv R.hp2 R.hpo R.hEc R.hev R.hcl (by simp)
      (by simp [upd, fH, fHLeft, fG]) (by omega_using [hw, hi])
    obtain notLeft : ∀ σ s, ¬((St G (gCfg c G w HL k) X σ s ∧
        isa.eval (.zero .d .r0) s = some (decide (HL - k * G.pLen < G.pLen))) ∧
        isa.eval (.zero .d .r0) s = some true) := fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    obtain eH : G.wit + BitVec.ofNat 64 (w + k * G.pLen) + BitVec.ofNat 64 G.pLen =
        G.wit + BitVec.ofNat 64 (w + (k + 1) * G.pLen) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul, Nat.add_assoc]
    by_cases hok : gOk G pv ev (w + k * G.pLen)
    · -- It gives g: done.
      obtain r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega_using [hr, hkk, hc]
      subst r0
      obtain some0 : gRes G w HL pv qv 0 = some (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen)) ^ ev % pv) := by
        rw [← hres, gRes, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      obtain num0 : gNum G w HL pv qv 0 = k + 1 := by
        rw [← hnum, gNum, cstep, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      obtain hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev =
          ({ gCfg c G w HL k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G w HL k).cl }).setV fG 1 := by
        simp only [gOut]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      simp only [gFin, some0, num0]
      exact h'.mono (gV R.hfH R.hfL (fun o ho => by simp [ho]) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3])
        (by simp) (by simp [upd, fH, fHLeft, fG]) (by simp) (by simp [upd, fH, fHLeft, fG, eH]))
        (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · -- It does not: the next h.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      obtain rpos : 0 < r := by have := gCount_gt G w pv ev m (k + 1); omega_using [hw, h64, hr, l, hpL, hp15, hMM, hkk, hk, hnum, hkM, hi, hc, hm, hbl, this]
      obtain hNr : N - r = k + 1 := by omega_using [hr, hkk]
      obtain hG1 : gOut (gCfg c G w HL k) G (Spec.Dsa.decodeBE (hAt G (w + k * G.pLen))) pv ev = gCfg c G w HL k := by
        simp only [gOut]; exact ite_eq_right_of_eq_false _ _ (eq_false hok)
      rw [hG1] at stepVP
      refine VP.seq (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => h.1.1) fun _ _ h => h) (adv_vp (by simp) (by simp)))) ?_
      obtain eL : BitVec.ofNat 64 (HL - k * G.pLen) - BitVec.ofNat 64 G.pLen =
          BitVec.ofNat 64 (HL - (k + 1) * G.pLen) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.succ_mul]; omega_using [hw, h64, l, hpL, hp15, hMM, hkk, hk, hnum, hkM, hi, hm, hbl, hNr]
      refine cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_using [rpos]), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega_using [hr], by omega_using [hw, h64, l, hpL, hp15, hMM, hkk, hk, hnum, hkM, hi, hm, hbl, hNr, eL], by rw [hMM, show M - (k + 1) = m by omega_using [hm]]; exact hc, ?_, ?_⟩, ?_, x⟩
      · rw [← hres]; simp only [gRes, gCands]
        rw [hstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]
      · rw [← hnum]; simp only [gNum, gCands]
        rw [cstep, ite_eq_right_of_eq_false _ _ (eq_false hok), Nat.succ_mul]; omega_using []
      · refine h'.mono (fun o ho => ⟨?_, ?_⟩) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
        · simp only [List.mem_cons] at ho ⊢
          rcases ho with h' | h' | h' | h' <;> simp [h']
        · simp only [upd]
          by_cases a : o = fHLeft
          · subst a; simp [eL, fHLeft, fG]
          · by_cases b : o = fH
            · subst b; simp [eH, fH, fHLeft, fG]
            · simp [a, b]
  · -- Fewer than `p_len` octets left: `fG` := 2.
    obtain hkM' : k = M := by omega_using [hk, hkM]
    subst hkM'
    obtain r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega_using [hr, hkk, hc]
    subst r0
    obtain hz : decide (HL - k * G.pLen < G.pLen) = true := by
      refine decide_eq_true ?_
      rw [← hMM, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]; exact Nat.mod_lt _ hpL
    obtain hsh : ((hsW G w HL).drop (k * G.pLen)).length < G.pLen := by
      simp only [List.length_drop, hlen]; exact of_decide_eq_true hz
    obtain none0 : gRes G w HL pv qv 0 = none := by
      rw [← hres]
      show Spec.Dsa.generator pv qv ((Spec.Dsa.generationChunks _ _).map _) = none
      rw [VG.Proof.Dsa.Generation.generationChunks_done hsh]
      rfl
    obtain num0 : gNum G w HL pv qv 0 = k := by
      rw [← hnum, gNum, VG.Proof.Dsa.Generation.generatorCount_chunks_done hsh, Nat.add_zero]
    refine VP.seq (G := St G ((gCfg c G w HL k).setV fG (BitVec.ofNat 64 2)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => gCfg c G w HL k) (o := fG) (v := 2) (fun σ s h => h.1.1.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, hz] at z; simp at z)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G w HL k).setV fG (BitVec.ofNat 64 2)) (x := BitVec.ofNat 64 2)
      (fun σ s h => h.1) (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    simp only [gFin, none0, num0]
    exact h'.mono (gV R.hfH R.hfL (by simp_all) (fun o h1 h2 h3 => by simp [upd, h1, h2, h3]) (by simp)
      (by simp [upd]) (by simp) (by simp [upd, fH, fHLeft, fG])) (fun y hy => hy) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)

/-- The search for g over the window of `HL` octets at `w`. -/
theorem gPart_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {c : Cfg} {pv ev qv w HL : Nat} (R : GReq G c pv ev) (hS : fHs ∈ c.LS)
    (hSv : c.V fHs = G.wit + BitVec.ofNat 64 w) (hL : fHsLen ∈ c.LS) (hLv : c.V fHsLen = BitVec.ofNat 64 HL)
    (hw : w + HL ≤ G.witLen) (hwl : G.witB.length = G.witLen) (h64 : HL < 2 ^ 64) (hev' : ev = (pv - 1) / qv) :
    VP (St G c X) g.gPart (St G (gFin c G w HL pv qv) X) := by
  unfold Geo.gPart
  rw [show ([ld .r3 fHs, st .r3 fH, ld .r3 fHsLen, st .r3 fHLeft] : List Instr) =
    [ld .r3 fHs] ++ ([st .r3 fH] ++ ([ld .r3 fHsLen] ++ [st .r3 fHLeft])) from rfl]
  obtain hHs : fHsLen ∈ (c.setV fH (G.wit + BitVec.ofNat 64 w)).LS := List.mem_cons_of_mem _ hL
  refine VP.seq (G := St G ((c.setV fH (G.wit + BitVec.ofNat 64 w)).setV fHLeft (BitVec.ofNat 64 HL)) X)
    (VP.block_append (G := fun σ s => St G c X σ s ∧ s.gpr .r3 = G.wit + BitVec.ofNat 64 w)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV hS).trans hSv) fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_) ?_
  · refine VP.block_append (G := St G (c.setV fH (G.wit + BitVec.ofNat 64 w)) X)
      (st_vp (c := fun _ => c) (fun σ s h => h.1.1) (varOk_of (by decide))
        fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩) ?_
    refine VP.block_append (G := fun σ s => St G (c.setV fH (G.wit + BitVec.ofNat 64 w)) X σ s ∧
        s.gpr .r3 = BitVec.ofNat 64 HL)
      (ld_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1) (by decide) (by decide)
        (by decide) (fun σ s h => (h.1.gi.slotV hHs).trans ((upd_ne (o := fH) _ (G.wit + BitVec.ofNat 64 w) (by decide)).trans hLv))
        fun σ s t ⟨_, x⟩ h' u => ⟨⟨h', x⟩, u.gpr⟩) ?_
    exact st_vp (c := fun _ => c.setV fH (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1.1) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨by rw [r3] at h'; exact h', x⟩
  obtain hN := gCount_gt G w pv ev (HL / G.pLen) 0
  generalize hNN : gCount G w pv ev (HL / G.pLen) 0 = N at hN
  refine VP.seq (G := gInv c G w HL pv ev qv N X N)
    (stImm_vp (c := fun _ => (c.setV fH (G.wit + BitVec.ofNat 64 w)).setV fHLeft (BitVec.ofNat 64 HL)) (o := fG)
      (v := 4) (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ =>
        ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self],
          by rw [Nat.sub_self, Nat.zero_add]⟩, by simpa [gCfg] using h', h.2⟩) ?_
  rw [show N = N - 1 + 1 by omega_using [hN]]
  exact VP.loop (I := gInv c G w HL pv ev qv (N - 1 + 1) X) (gBody_vp hg hgq cert R hw hwl h64 hev') _

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.CheckPart`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: checking p‖q‖g

`checkPart_vp`: p (at `sPBE`), q (at `sQ`) and g (at `sG`) copied side by
side to `sPacked`, checked by a verified `vg_dsa_check_parameters`
(`CheckOk`): `fStatus` := 1 if `Spec.Dsa.checkParametersBytes` accepts them.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A claim copied to `dst`, the claims apart from it kept. -/
theorem copyCl_vp {dst src n : Nat} {bs : List Byte} (hs : (src, bs) ∈ c.cl) (hl : bs.length = n) (hn : 0 < n)
    (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15) (hs15 : src < 2 ^ 15) (hdE : hEnd ≤ dst) (hdK : dst + n ≤ pB)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst) (hcl : ∀ x ∈ c.cl, Apart dst n x) :
    VP (St G c X) (copyS dst src n) (St G { c with cl := (dst, bs) :: c.cl } X) := by
  refine copyS_vp (c := fun _ => c) (fun σ s h => h.1) hn hn15 hd15 hs15 (fun σ s h => ?_) (fun σ s h => ?_) hsep
    fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
  · have ⟨pb, pk⟩ := h.1.gi.pBig
    exact ⟨hdE, .inl (by simp only [List.length_replicate]; omega_using [hdK, pk]), by simp only [List.length_replicate]; omega_using [hdK, pb]⟩
  · have := (h.1.clOk _ hs).2.2; rw [hl] at this; exact this
  · have hf : c.cl.filter (fun x => decide (Apart dst n x)) = c.cl :=
      List.filter_eq_self.mpr fun x hx => decide_eq_true (hcl x hx)
    rw [hf] at h'
    have ⟨pb, pk⟩ := h.gi.pBig
    obtain b := h.sb _ hs
    simp only at b
    obtain e' : Spec.Rsa.bytesAt t.mem (G.sa dst) bs.length = bs := by rw [hl, e, ← hl]; exact b
    exact h'.addCl e' ⟨hdE, .inl (show dst + bs.length ≤ kB G.pLen by omega_using [hl, hdK, pk]),
      show dst + bs.length ≤ G.scrLen * 8 by omega_using [hl, hdK, pb]⟩

/-- The check's arguments. -/
theorem cargs_vp :
    VP (St G c X) (.block [scr .r3 sPacked, .li .r4 (2 * G.pLen + G.qLen), .li .r5 G.pLen, .li .r6 G.qLen,
        scr .r7 (wB G.pLen), .li .r8 (wWords G.pLen)])
      (fun σ s => St G c X σ s ∧ CArgs G s) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block [scr .r3 sPacked, .li .r4 (2 * G.pLen + G.qLen), .li .r5 G.pLen, .li .r6 G.qLen,
        scr .r7 (wB G.pLen), .li .r8 (wWords G.pLen)]), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  obtain ⟨_, w15, _, _, _, _, n15⟩ := ck_sizes h.gi.lens
  obtain hp15 : G.pLen < 2 ^ 15 := by rcases h.gi.lens3 with e | e | e <;> rw [e] <;> decide
  obtain hq15 : G.qLen < 2 ^ 15 := by rcases h.gi.lens with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> decide
  obtain wb15 : wB G.pLen < 2 ^ 15 := by rcases h.gi.lens3 with e | e | e <;> rw [e] <;> decide
  obtain hb : WP isa (.block [scr .r3 sPacked, .li .r4 (2 * G.pLen + G.qLen), .li .r5 G.pLen, .li .r6 G.qLen,
      scr .r7 (wB G.pLen), .li .r8 (wWords G.pLen)]) s fun u =>
      (CArgs G u ∧ u.mem = s.mem) ∧ VG.Proof.Bignum.PPC64LE.Keep [.r3, .r4, .r5, .r6, .r7, .r8] s u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by rfl)
    simp only [scr]
    prun [h.gi.r28, exec_addi (show Reg.r28 ≠ .r0 by decide) (show sPacked < 2 ^ 15 by decide),
      exec_addi (show Reg.r28 ≠ .r0 by decide) wb15, exec_li (show nPk G < 2 ^ 15 from n15), exec_li hp15,
      exec_li hq15, exec_li w15]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.write, GP.sa]
  exact WP.mono hb fun u ⟨⟨a, m⟩, k⟩ => ⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ m k.sp, x⟩, a⟩

/-- The call of the check on the claim `pk` at `sPacked`. -/
theorem checkCall_vp {code : Prog isa} {name : String} (ok : CheckOk code) {pk : List Byte}
    (hpk : (sPacked, pk) ∈ c.cl) (hpkl : pk.length = nPk G) (hcl : ∀ x ∈ c.cl, Apart (wB G.pLen) (wWords G.pLen * 8) x) :
    VP (fun σ s => St G c X σ s ∧ CArgs G s) (.call name code)
      (fun σ t => St G c X σ t ∧
        ((t.gpr .r3).setWidth 32).toNat = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0)) := by
  obtain bytes : ∀ σ s, SS G 176 σ c s → Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk := fun σ s h => by
    have := h.sb _ hpk; rw [hpkl] at this; exact this
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (cRd G) (cWr G) fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ =>
      ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    obtain p₁ := pre_of_ckin (h₁.cEntry_ckin g₁)
    obtain p₂ := pre_of_ckin (h₂.cEntry_ckin g₂)
    obtain ⟨cr₁, cw₁⟩ := h₁.cCovers
    obtain ⟨cr₂, cw₂⟩ := h₂.cCovers
    obtain ⟨a3, a4, a5, a6, a7, a8⟩ := g₁
    obtain ⟨b3, b4, b5, b6, b7, b8⟩ := g₂
    refine ⟨p₁, p₂, cpub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, cr₁, cw₁, cr₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      obtain e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a3, b3]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a4, b4]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a5, b5]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a6, b6]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a7, b7]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a8, b8]
    · obtain ⟨_, _, _, _, _, _, n15⟩ := ck_sizes h₁.gi.lens
      obtain e4 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [n15])]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), a3, a4, b3, b4, e4,
        bytes _ _ h₁, bytes _ _ h₂]
  refine h.checkCall_ok (name := name) ok regs (bytes _ _ h) fun t g rd wr sp f st => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  obtain ⟨_, _, _, _, _, hEs, _⟩ := ck_sizes h.gi.lens
  exact h.of_scrs (keep_of_preserved g rd wr) sp (os := [(wB G.pLen, wWords G.pLen * 8)])
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨by simp only [hEnd, wB, kB, pB, fSave] at hE ⊢; omega_using [], .inr (Nat.le_refl _),
        by simp only [List.length_replicate]; omega_using [big]⟩)
    f (cl' := c.cl) (fun y hy => .inl ⟨hy, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl y hy⟩)

/-- p‖q‖g. -/
abbrev pkOf (pB qB gB : List Byte) : List Byte := pB ++ qB ++ gB

/-- The stage after the check. -/
abbrev ckCfg (c : Cfg) (pk : List Byte) (ok : Bool) : Cfg :=
  if ok then ({ c with cl := (sPacked, pk) :: c.cl }).setV fStatus 1 else { c with cl := (sPacked, pk) :: c.cl }

/-- The verdict, zero-extended, compared with 1. -/
theorem verdict_vp {c' : Cfg} {b : Bool} :
    VP (fun σ t => St G c' X σ t ∧ ((t.gpr .r3).setWidth 32).toNat = (if b then 1 else 0))
      (.block [.lsr .w .r3 .r3 0, .subi .r0 .r3 1])
      (fun σ t => St G c' X σ t ∧ isa.eval (.zero .d .r0) t = some b) := by
  refine VP.pub (SS.pub (c := fun _ => c') fun σ s h => h.1.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.lsr .w .r3 .r3 0, .subi .r0 .r3 1]),
      rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  refine WP.wr (exec_lsr_w (by decide)) fun s₁ u₁ sp₁ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun t u sp _ => WP.block_nil ?_
  refine ⟨⟨(h.of_upd u₁ sp₁ (by decide)).of_upd u sp (by decide), x⟩, ?_⟩
  obtain hv : ((s.gpr .r3).setWidth 32 >>> 0).setWidth 64 = BitVec.ofNat 64 (if b then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ushiftRight_zero, BitVec.toNat_setWidth, r3, BitVec.toNat_ofNat]
  rw [eval_zero, u.gpr, u₁.gpr, hv]
  cases b <;> decide

theorem checkPart_vp {g : Geo} (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hck : CheckOk g.checkCode)
    {pB qB gB : List Byte} (hP : (sPBE, pB) ∈ c.cl) (hQ : (sQ, qB) ∈ c.cl) (hG : (sG, gB) ∈ c.cl)
    (hPl : pB.length = G.pLen) (hQl : qB.length = G.qLen) (hGl : gB.length = G.pLen)
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sPacked) :
    VP (St G c X) g.checkPart
      (St G (ckCfg c (pkOf pB qB gB) (Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB))) X) := by
  by_cases l : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  swap
  · exact VP.of_false fun σ s h => l h.1.gi.lens
  unfold Geo.checkPart
  rw [hp, hq]
  obtain hb : 0 < G.pLen ∧ 0 < G.qLen ∧ G.pLen ≤ 384 ∧ G.qLen ≤ 32 := by
    rcases l with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> decide
  have e1 : sPacked = 2208 := rfl
  have e2 : sPBE = 1056 := rfl
  have e3 : sQ = 608 := rfl
  have e4 : sG = 1824 := rfl
  have hE : hEnd = 352 := rfl
  have hpb : VG.Impl.Dsa.PPC64LE.Generation.pB = 3072 := rfl
  -- The copies.
  refine VP.seq (copyCl_vp (dst := sPacked) hP hPl hb.1 (by omega_using [l]) (by decide) (by decide) (by omega_using [e1, hE]) (by omega_using [l, e1, hpb])
    (by omega_using [l, e1, e2]) fun x hx => .inl (hcl x hx)) ?_
  refine VP.seq (copyCl_vp (dst := sPacked + G.pLen) (List.mem_cons_of_mem _ hQ) hQl hb.2.1 (by omega_using [l]) (by omega_using [l, e1])
    (by decide) (by omega_using [e1, hE]) (by omega_using [l, e1, hpb]) (by omega_using [l, e1, e3]) fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hPl]; omega_using [])
    · exact .inl (by have := hcl x hx; omega_using [this])
  refine VP.seq (copyCl_vp (dst := sPacked + G.pLen + G.qLen) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hG))
    hGl hb.1 (by omega_using [l]) (by omega_using [l, e1]) (by decide) (by omega_using [e1, hE]) (by omega_using [l, e1, hpb]) (by omega_using [e1, e4]) fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hQl]; omega_using [])
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hPl]; omega_using [])
    · exact .inl (by have := hcl x hx; omega_using [this])
  -- p‖q‖g, as one claim.
  obtain hsz := (ck_sizes l).1
  obtain hpkl : (pkOf pB qB gB).length = nPk G := by simp only [pkOf, List.length_append, hPl, hQl, hGl, nPk]; omega_using []
  obtain offe : ∀ o n, VG.Proof.Bignum.off (G.sa o) n = G.sa (o + n) := fun o n => by
    rw [VG.Proof.Bignum.off, GP.sa_add]
  obtain join : ∀ σ s, SS G 176 σ { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl } s → SS G 176 σ { c with cl := (sPacked, pkOf pB qB gB) :: c.cl } s := fun σ s h => by
    obtain bp := h.sb (sPacked, pB) (by simp)
    obtain bq := h.sb (sPacked + G.pLen, qB) (by simp)
    obtain bg := h.sb (sPacked + G.pLen + G.qLen, gB) (by simp)
    simp only at bp bq bg
    obtain hc : Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pkOf pB qB gB).length = pkOf pB qB gB := by
      show Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pB ++ qB ++ gB).length = pB ++ qB ++ gB
      rw [List.length_append, List.length_append, VG.Proof.Dsa.Generation.bytesAt_append,
        VG.Proof.Dsa.Generation.bytesAt_append, offe, offe, ← Nat.add_assoc, bp, hPl, bq, hQl, bg]
    have ⟨pb', pk'⟩ := h.gi.pBig
    exact (h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => by simp [hy]) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩) (c' := c)).addCl hc ⟨by show hEnd ≤ sPacked; decide,
        .inl (show sPacked + (pkOf pB qB gB).length ≤ kB G.pLen by rw [hpkl]; simp only [nPk]; omega_using [l, e1, hpb, pk']),
        show sPacked + (pkOf pB qB gB).length ≤ G.scrLen * 8 by rw [hpkl]; simp only [nPk]; omega_using [l, e1, hpb, pb']⟩
  refine VP.seq ((cargs_vp (c := { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl }) (X := X)).mono (G' := fun σ s => St G { c with cl := (sPacked, pkOf pB qB gB) ::
        c.cl } X σ s ∧ CArgs G s) (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, a⟩ => ⟨⟨join σ s h, x⟩, a⟩) ?_
  -- The check.
  refine VP.seq (checkCall_vp (c := { c with cl := (sPacked, pkOf pB qB gB) :: c.cl }) hck (by simp) hpkl
    fun y hy => .inl (by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hpkl]; omega_using [hsz]
      · have := hcl y hy; omega_using [hsz, this])) ?_
  generalize hbv : Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB) = b
  refine VP.seq verdict_vp ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · cases b
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
    · exact stImm_vp (c := fun _ => { c with cl := (sPacked, pkOf pB qB gB) :: c.cl }) (o := fStatus) (v := 1)
        (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩
  · cases b
    · exact VP.block_nil fun σ s h => h.1.1
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


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
  obtain hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
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
    obtain e3 : s₃.gpr .r3 = G.wit + BitVec.ofNat 64 w := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
    refine h₃.stF (o := fHs) (varOk_of (by decide)) fun s₄ h₄ m₄ _ => ?_
    rw [e3] at h₄
    refine h₄.ldK (o := fWitLen) (by decide) (by decide) (h₄.gi.fixedV (v := BitVec.ofNat 64 G.witLen) (by simp [fixedWords])) (by decide)
      fun s₅ h₅ u₅ => ?_
    refine h₅.wrK exec_sub (by decide) fun s₆ h₆ u₆ => ?_
    obtain e6 : s₆.gpr .r3 = BitVec.ofNat 64 (G.witLen - w) := by
      rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.gpr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_using [hw]
    refine shl_ok h₆ (r := .r4) (by decide) hp15 (by decide) fun s₇ h₇ K₇ e₇ _ => ?_
    refine ltR_ok (by rw [K₇.gpr (by decide), e6]) e₇ fun t K m sp _ e =>
      WP.block_nil ⟨⟨h₇.of_keep K m sp, x⟩, ?_, ?_, ?_⟩
    · rw [K.gpr (by decide), K₇.gpr (by decide), e6]
    · rw [K.gpr (by decide), e₇]
    · refine e.trans ?_
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h64]),
        Nat.mod_eq_of_lt (by rcases l with e | e | e <;> rw [e] <;> decide)]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2]) ?_ ?_
  · refine st_vp (c := fun _ => c.setV fHs (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1.1.1)
      (varOk_of (by decide)) fun σ s t ⟨⟨⟨_, x⟩, r3, _, e⟩, z⟩ h' _ => ⟨?_, x⟩
    obtain hl : G.witLen - w < G.pLen * 2 ^ 7 := by rw [e] at z; simpa using z
    rw [r3] at h'
    rw [Nat.min_eq_left (Nat.le_of_lt hl)]; exact h'
  · refine st_vp (c := fun _ => c.setV fHs (G.wit + BitVec.ofNat 64 w)) (fun σ s h => h.1.1.1)
      (varOk_of (by decide)) fun σ s t ⟨⟨⟨_, x⟩, _, r4, e⟩, z⟩ h' _ => ⟨?_, x⟩
    obtain hl : ¬G.witLen - w < G.pLen * 2 ^ 7 := by rw [e] at z; simpa using z
    rw [r4] at h'
    rw [Nat.min_eq_right (by omega_using [hl])]; exact h'

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
  obtain e3 : s₃.gpr .r3 = BitVec.ofNat 64 x := by
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
  obtain hp15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
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
  obtain hq0 : 0 < G.qLen := by omega_using [hlq]
  obtain hq32 : G.qLen ≤ 32 := by omega_using [hlq]
  obtain hl384 : G.pLen ≤ 384 := by omega_using [hlq]
  obtain hrl : rest.length ≤ G.witLen := by
    have := congrArg List.length hrest; simp only [List.length_drop, hwl] at this; omega_using [this]
  generalize hqv : Spec.Dsa.decodeBE (qBytes G k) = qv at hqlo ⊢
  obtain qpos : 0 < qv := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hqlo
  obtain pl := padTail_length HO.md (n := G.qLen) (by omega_using [hlq]) hL
  -- (p − 1) / q fits its octets.
  obtain hev : (p - 1) / qv < 256 ^ eBytes G.pLen G.qLen := by
    have hp := hpd.upper
    rw [show (256 : Nat) ^ eBytes G.pLen G.qLen = 2 ^ (8 * eBytes G.pLen G.qLen) from (Nat.pow_mul 2 8 _).symm]
    refine Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul qpos).mpr ?_) (Nat.pow_le_pow_right (by decide)
      (show 8 * G.pLen - 8 * G.qLen + 1 ≤ 8 * eBytes G.pLen G.qLen by simp only [eBytes]; omega_using []))
    calc p - 1 < 2 ^ (8 * G.pLen) := by omega_using [hp]
      _ = 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * 2 ^ (8 * G.qLen - 1) := by rw [← Nat.pow_add]; congr 1; omega_using [hlq]
      _ ≤ 2 ^ (8 * G.pLen - 8 * G.qLen + 1) * qv := Nat.mul_le_mul_left _ hqlo
  obtain hpv : p < 256 ^ G.pLen := by
    rw [show (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) from (Nat.pow_mul 2 8 _).symm]; exact hpd.upper
  generalize hw : G.witLen - rest.length = w at hrest
  generalize hHL : min (G.witLen - w) (G.pLen * 2 ^ 7) = HL
  let c₁ : Cfg := ((aPCfg G HO k n p rest).setV fHs (G.wit + BitVec.ofNat 64 w)).setV fHsLen (BitVec.ofNat 64 HL)
  obtain R : GReq G c₁ p ((p - 1) / qv) := by
    refine ⟨by simp [c₁], by simp [c₁, pAp, KU, VG.Proof.Rsa.KeyWorkspace.upd, aP, aE, aPm1], by simp [c₁],
      by simp [c₁, pAp, KU, VG.Proof.Rsa.KeyWorkspace.upd, aP, aE, aPm1, aOne], by simp [c₁],
      by simp [c₁, pAp, KU, VG.Proof.Rsa.KeyWorkspace.upd, aP, aE, aPm1, aOne, aZero],
      by simp [c₁, aH, aP, aE, aPm1, aOne, aZero], by simp [c₁, aTmp, aP, aE, aPm1, aOne, aZero], rfl, by simp [c₁],
      hpv, by have := hpd.lower; have : 1 < 2 ^ (8 * G.pLen - 1) := Nat.one_lt_two_pow (by omega_using [hlq]); omega_arith,
      hpd.odd, by simp [c₁, hqv], hev, fun x hx => ?_, by simp [c₁]; decide, by simp [c₁]; decide⟩
    simp only [c₁, pRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [VG.Proof.Rsa.i2osp_length, Apart, sE, sG, pB, eBytes]; omega_using [hlq]
    · simp only [VG.Proof.Rsa.i2osp_length, Apart, sPBE, sG, pB]; omega_using [hlq]
    · simp only [pl, Apart, sMsg, sG, pB]; omega_using [hlq]
    · simp only [hql, Apart, sQ, sG, pB]; omega_using [hlq]
  obtain hHL64 : HL < 2 ^ 64 := by omega_using [hlq, hHL]
  obtain hwHL : w + HL ≤ G.witLen := by omega_using [hw, hHL]
  refine VP.seq (G := St G c₁ X) ((gWindow_vp (w := w) hp (by simp) (by simp [upd, fP, fUsed, ← hw]) (by omega_using [hw]) h64).mono
    (fun _ _ h => h) fun σ s h => by rw [hHL] at h; exact h) ?_
  refine VP.seq (gPart_vp (c := c₁) (pv := p) (ev := (p - 1) / qv) (qv := qv) (w := w) (HL := HL) hp hq gcert R
    (by simp [c₁]) (by simp [c₁, upd, fHs, fHsLen]) (by simp [c₁]) (by simp [c₁]) hwHL hwl hHL64 rfl) ?_
  -- The window's candidates are the spec's.
  obtain hcand : gCands G w HL 0 = windowCandidates G.pLen Spec.Dsa.generatorAttempts rest := by
    simp only [gCands, hsW, Nat.zero_mul, List.drop_zero, hrest, windowCandidates]
    rw [← hHL, show G.witLen - w = rest.length by omega_using [hrl, hw], take_window,
      show G.pLen * 2 ^ 7 = Spec.Dsa.generatorAttempts * G.pLen by simp only [Spec.Dsa.generatorAttempts]; omega_using []]
  obtain hcnt : gNum G w HL p qv 0 * G.pLen ≤ rest.length := by
    obtain h1 := VG.Proof.Dsa.Generation.generatorCount_le p qv (gCands G w HL 0)
    obtain h2 : (gCands G w HL 0).length * G.pLen ≤ rest.length := by
      rw [hcand]
      simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range]
      exact Nat.le_trans (Nat.div_mul_le_self _ _) (by simp only [List.length_take]; exact Nat.min_le_right _ _)
    exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
  unfold winResult
  rw [← hcand]
  rcases hgv : Spec.Dsa.generator p qv (gCands G w HL 0) with _ | gv
  · -- No g: a short window ran out.
    obtain hfin : gFin c₁ G w HL p qv = (c₁.setV fG 2).setV fH
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
    obtain hnum : gNum G w HL p qv 0 = (gCands G w HL 0).length :=
      generatorCount_none hgv
    by_cases hs : HL < G.pLen * 2 ^ 7
    · have hshort : ¬Spec.Dsa.generatorAttempts * G.pLen ≤ rest.length := by
        simp only [Spec.Dsa.generatorAttempts]; omega_using [hrl, hw, hHL, hs]
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
        simp only [Spec.Dsa.generatorAttempts]; omega_using [hw, hHL, hs]
      obtain hHLv : HL = G.pLen * 2 ^ 7 := by omega_using [hHL, hs]
      obtain hlen : (gCands G w HL 0).length = 128 := by
        rw [hcand]
        simp only [windowCandidates, Spec.Dsa.generationChunks, List.length_map, List.length_range,
          List.length_take, Spec.Dsa.generatorAttempts]
        rw [Nat.min_eq_left (by omega_using [hw, hHL, hs]), Nat.mul_div_cancel _ (by omega_using [hlq])]
      simp only [hs, hfull, ↓reduceIte, aOut] at h ⊢
      refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
        (fun _ h' => absurd h' (by simp))
      · change o ∈ fUsed :: fStatus :: fSeedLeft :: fSeed :: fC :: [] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl
        · refine ⟨by simp, ?_⟩
          simp only [upd, ↓reduceIte, List.length_drop, hnum, hlen, Spec.Dsa.generatorAttempts]
          congr 1; omega_using [hrl, hw, hHL, hs]
        all_goals exact ⟨by simp [c₁], by simp [c₁, upd, fUsed, fG, fH, fHs, fHsLen, fP, fStatus, fSeedLeft,
          fSeed, fC]⟩
      · change y ∈ [(sMsg + G.qLen, padTail HO.md G.qLen)] at hy
        rw [List.mem_singleton] at hy; subst hy; simp [c₁, pRest]
  · -- g: the check.
    obtain hgb := VG.Proof.Dsa.Generation.generator_bounds (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hpd.lower) _ hgv
    obtain hpl8 : (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) := by rw [Nat.pow_mul]
    obtain hql8 : (256 : Nat) ^ G.qLen = 2 ^ (8 * G.qLen) := by rw [Nat.pow_mul]
    obtain qlt : qv < 2 ^ (8 * G.qLen) := by
      rw [← hqv, ← hql8, ← hql]; exact VG.Proof.Dsa.decodeBE_lt _
    obtain hpk : pkOf (Spec.Rsa.i2osp p G.pLen) (qBytes G k) (Spec.Rsa.i2osp gv G.pLen) =
        Spec.Dsa.encodeParams G.pLen G.qLen ⟨p, qv, gv⟩ := by
      obtain hqb : qBytes G k = Spec.Rsa.i2osp qv G.qLen := by
        rw [← hqv, ← VG.Proof.Dsa.encodeBE_i2osp, ← hql, VG.Proof.Dsa.encodeBE_decodeBE]
      simp only [pkOf, Spec.Dsa.encodeParams, VG.Proof.Dsa.encodeBE_i2osp, hqb]
    obtain hok : Spec.Dsa.checkParametersBytes G.pLen G.qLen
        (pkOf (Spec.Rsa.i2osp p G.pLen) (qBytes G k) (Spec.Rsa.i2osp gv G.pLen)) =
        decide (Spec.Dsa.parametersValid ⟨p, qv, gv⟩) := by
      rw [hpk]
      exact VG.Proof.Dsa.Generation.check_encodedParams (by
          unfold Spec.Dsa.lengthsValid; omega_using [hlq])
        (by rw [hpl8]; exact hpd.upper) (by rw [hql8]; exact qlt) (by rw [hpl8]; exact Nat.lt_trans hgb.2 hpd.upper)
    let xu := w + gNum G w HL p qv 0 * G.pLen
    let Dg : Cfg := ((({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV fH
      (G.wit + BitVec.ofNat 64 xu)).setV fUsed (BitVec.ofNat 64 xu)
    obtain hfin : gFin c₁ G w HL p qv = (({ c₁ with cl := (sG, Spec.Rsa.i2osp gv G.pLen) :: c₁.cl }).setV fG 1).setV
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
      · simp only [pl, sPacked, sMsg]; omega_using [hlq]
      · simp only [hql, sQ, sPacked]; omega_arith
    obtain hU : G.witLen - (rest.drop (G.pLen * gNum G w HL p qv 0)).length = xu := by
      simp only [List.length_drop, xu]; rw [Nat.mul_comm G.pLen]; omega_using [hrl, hw, hcnt]
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
  obtain hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_using [hk]
  obtain hc : G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  refine pCandidate_xBytes HO (fun i => ?_) hH hsl hlen (by omega_using [hlq]) hc _
  rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_using [hlq]), HO.md.digest_length, HO.hN, hk4]

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
  obtain hw : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega_using [hlq]
  obtain pl := padTail_length HO.md (n := G.qLen) (by omega_using [hlq]) HO.hL
  refine VP.seq (pPart_vp (c := aBase G HO k n) (u0 := G.witLen - r.length) (d := aQCfg G HO k n u r) HO okp lay hlq
    hp hq hk4 hsb hH hwl (aBase_pnot G HO k n) hk (by simp) (by simp [upd, fSeed, fStatus, fSeedLeft])
    (by omega_using []) (pCand_spec HO hlq hk4 hsb hk hH hlen) (by simp [testCfg])
    (by simp [testCfg, upd]) (fun o ho => ⟨by simp [testCfg, ho], by
      change o ∈ [fStatus, fSeedLeft, fSeed, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp [testCfg, upd, fUsed, fRes, fStatus, fSeedLeft, fSeed, fC]⟩)
    (by simp [testCfg, qClaims]) (by simp [testCfg, qClaims])) ?_
  obtain hS0 : pSpec HO G k (G.witLen - r.length) 0 = Spec.Dsa.primeFromSeed (8 * G.pLen) (8 * G.qLen)
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
    obtain hpd := VG.Proof.Dsa.Generation.primeSearch_domain hw hlen _ _ _ _ hR
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
  obtain hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by have := hlen (seedAt G k); omega_using [this]
  obtain hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_using [hlq, hHq]
  obtain ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_using [hlq, hHq]),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  obtain hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_using [hlq]) _ (by rw [hHq])
  obtain hqlo : 2 ^ (8 * G.qLen - 1) ≤ Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; exact (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_using [hlq]) (seedAt G k)).2.1
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
    obtain hr : G.witB.drop (G.witLen - r.length) = r := by
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

end

end


/-! # DSA parameter generation on PPC64LE: the controller

`sLoop_vp`: the seeds, one at a time from the cursor `fC`, with `fSeedLeft`
seeds left, until one gives a domain (`fStatus` := 1, p‖q‖g at `sPacked`),
`rand` runs out (2) or the seeds do (3), as `Spec.Dsa.parameterSearch` tries
them (`Proof/Dsa/Generation/RefillSearch.lean`): the stage it ends at is
`cFin`, and its result as the spec states it `cRes`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Dsa.Generation (refillAttempt ranOutResult)

/-- What a geometry's code and the tape give the search. -/
structure GenOk (G : GP) (g : Geo) (HO : HashOk g.G) (Lq Lp : Impl.Dsa.ProbablePrime.Layout) : Prop where
  okq : PrimeOk Lq g.qCode
  qlay : QLay G g Lq
  okp : PrimeOk Lp g.pCode
  lay : PLay G g Lp
  gcert : CertC G.pLen G.qLen
  hck : CheckOk g.checkCode
  hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  hp : g.pLen = G.pLen
  hq : g.qLen = G.qLen
  hk4 : 4 * g.G.k = G.qLen
  hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m
  hwl : G.witB.length = G.witLen
  hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen
  h64 : G.witLen < 2 ^ 64
  hqL : G.qLen = Spec.Dsa.generationQLen G.pLen
  k0 : G.k0 ≤ Spec.Dsa.parameterSeeds

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

theorem GenOk.attempt_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout}
    (O : GenOk G g HO Lq Lp) {k u : Nat} {n : BitVec 64} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) X) g.attempt
      (St G (aOut G HO k n (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) :=
  VG.Proof.Dsa.PPC64LE.Gen.attempt_vp HO O.okq O.qlay O.okp O.lay O.gcert O.hck O.hlq O.hp O.hq O.hk4 O.hwl O.hH
    O.hwl O.hlen O.h64 hk hu

/-! ## The controller's pieces -/

/-- Whether a seed's octets are left after the cursor `c`. -/
theorem avail_vp {d : Cfg} {c q : Nat} (hC : fC ∈ d.LS) (hCv : d.V fC = BitVec.ofNat 64 c) (hc : c ≤ G.witLen)
    (h64 : G.witLen < 2 ^ 64) (hq : q < 2 ^ 15) :
    VP (St G d X) (.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 q] ++ ltR))
      (fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some (decide (G.witLen - c < q))) := by
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 q] ++ ltR)), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine h.ldK (o := fWitLen) (by decide) (by decide) (h.gi.fixedV (v := BitVec.ofNat 64 G.witLen)
    (by simp [fixedWords])) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fC) (by decide) (by decide) ((h₁.gi.slotV hC).trans hCv) (by decide) fun s₂ h₂ u₂ => ?_
  refine h₂.wrK exec_sub (by decide) fun s₃ h₃ u₃ => ?_
  refine h₃.wrK (exec_li hq) (by decide) fun s₄ h₄ u₄ => ?_
  obtain e3 : s₄.gpr .r3 = BitVec.ofNat 64 (G.witLen - c) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hc]
  refine ltR_ok e3 u₄.gpr fun t K m sp _ e => WP.block_nil ⟨⟨h₄.of_keep K m sp, x⟩, e.trans ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h64]), Nat.mod_eq_of_lt (by omega_using [hq])]

/-- The seed at the cursor `c`: `fSeed` := `rand + c`, its witnesses from `c + q_len`. -/
theorem seedStart_vp {g : Geo} (hq : g.qLen = G.qLen) {d : Cfg} {c : Nat} (hC : fC ∈ d.LS)
    (hCv : d.V fC = BitVec.ofNat 64 c) (hq15 : G.qLen < 2 ^ 15) :
    VP (St G d X) (.block g.seedStart)
      (St G ((d.setV fSeed (G.seeds + BitVec.ofNat 64 c)).setV fUsed (BitVec.ofNat 64 (c + G.qLen))) X) := by
  unfold Geo.seedStart
  rw [hq]
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block [ld .r3 fWit, ld .r4 fC, .add .r3 .r3 .r4, st .r3 fSeed, .addi .r4 .r4 G.qLen,
      st .r4 fUsed]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fC) (by decide) (by decide) ((h₁.gi.slotV hC).trans hCv) (by decide) fun s₂ h₂ u₂ => ?_
  refine h₂.wrK exec_add (by decide) fun s₃ h₃ u₃ => ?_
  obtain e3 : s₃.gpr .r3 = G.seeds + BitVec.ofNat 64 c := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
  refine h₃.stF (o := fSeed) (varOk_of (by decide)) fun s₄ h₄ m₄ _ => ?_
  rw [e3] at h₄
  refine h₄.wrK (exec_addi (by decide) hq15) (by decide) fun s₅ h₅ u₅ => ?_
  obtain e5 : s₅.gpr .r4 = BitVec.ofNat 64 (c + G.qLen) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.gpr, BitVec.ofNat_add]
  refine h₅.stF (o := fUsed) (varOk_of (by decide)) fun t ht _ _ => WP.block_nil ⟨?_, x⟩
  rw [e5] at ht; exact ht

/-- A rejected seed: the cursor past it, one seed fewer left. -/
theorem rejected_vp {d : Cfg} {u j : Nat} (hU : fUsed ∈ d.LS) (hUv : d.V fUsed = BitVec.ofNat 64 u)
    (hL : fSeedLeft ∈ d.LS) (hLv : d.V fSeedLeft = BitVec.ofNat 64 (j + 1)) (hj : j + 1 < 2 ^ 64) :
    VP (St G d X) (.block Geo.rejected)
      (St G ((d.setV fC (BitVec.ofNat 64 u)).setV fSeedLeft (BitVec.ofNat 64 j)) X) := by
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block Geo.rejected), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fUsed) (by decide) (by decide) ((h.gi.slotV hU).trans hUv) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.stF (o := fC) (varOk_of (by decide)) fun s₂ h₂ m₂ _ => ?_
  rw [u₁.gpr] at h₂
  refine h₂.ldK (o := fSeedLeft) (by decide) (by decide)
    ((h₂.gi.slotV (List.mem_cons_of_mem _ hL)).trans ((upd_ne (o := fC) d.V (BitVec.ofNat 64 u) (by decide)).trans hLv)) (by decide)
    fun s₃ h₃ u₃ => ?_
  refine h₃.wrK (exec_subi (by decide) (by decide)) (by decide) fun s₄ h₄ u₄ => ?_
  obtain e4 : s₄.gpr .r3 = BitVec.ofNat 64 j := by
    rw [u₄.gpr, u₃.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := hj
    omega_using []
  refine h₄.stF (o := fSeedLeft) (varOk_of (by decide)) fun t ht _ _ => WP.block_nil ⟨?_, x⟩
  rw [e4] at ht; exact ht

/-! ## The controller's spec -/

/-- The seed at the cursor `c`, as the code runs it. -/
abbrev sR (G : GP) (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  refillAttempt G.pLen G.qLen (seedAt G c) (G.witB.drop (c + G.qLen))

/-- The controller's seeds left and cursor after `i` iterations. -/
def sPos (G : GP) : Nat → Nat × Nat
  | 0 => (G.k0, 0)
  | i + 1 => match sR G (sPos G i).2 with
    | some (none, rest) => ((sPos G i).1 - 1, G.witLen - rest.length)
    | _ => sPos G i

/-- The iterations, from the `i`-th at the cursor `c` with `j` seeds left. -/
def sCount (G : GP) : Nat → Nat → Nat → Nat
  | 0, _, i => i + 1
  | j + 1, c, i => if G.witLen - c < G.qLen then i + 1 else match sR G c with
    | some (none, rest) => sCount G j (G.witLen - rest.length) (i + 1)
    | _ => i + 1

theorem sCount_gt (G : GP) : ∀ j c i, i < sCount G j c i
  | 0, c, i => by simp [sCount]
  | j + 1, c, i => by
    have := sCount_gt G j
    simp only [sCount]; split
    · omega_using []
    · split
      · exact Nat.lt_of_succ_lt (this _ _)
      all_goals omega_using []

/-- How the controller ends. -/
inductive COut where
  | found (a : Spec.Dsa.Params) (u : Nat)
  | noSeeds (c : Nat)
  | ranOut (j c : Nat)

/-- The controller's end from seeds left `j` and the cursor `c`. -/
def cOutAt (G : GP) : Nat × Nat → COut
  | (0, c) => .noSeeds c
  | (j + 1, c) => if G.witLen - c < G.qLen then .ranOut (j + 1) c else match sR G c with
    | some (some a, rest) => .found a (G.witLen - rest.length)
    | _ => .ranOut (j + 1) c

/-- The stage it ends at. -/
def cFin (G : GP) : COut → Cfg
  | .found a u => ({ cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] } : Cfg).setV fUsed
      (BitVec.ofNat 64 u) |>.setV fStatus 1
  | .noSeeds c => (({} : Cfg).setV fC (BitVec.ofNat 64 c)).setV fStatus 3
  | .ranOut j c => ((({} : Cfg).setV fC (BitVec.ofNat 64 c)).setV fSeedLeft (BitVec.ofNat 64 j)).setV fStatus 2

/-- Its result, as the spec states it. -/
def cRes (G : GP) : COut → Spec.Dsa.ParameterSearchResult
  | .found a u => ⟨.accepted a, u, []⟩
  | .noSeeds c => ⟨.exhausted, c, []⟩
  | .ranOut j c => ranOutResult G.pLen j (G.witLen - c) c

/-- Its words' bounds. -/
def cOk (G : GP) : COut → Prop
  | .found _ u => u ≤ G.witLen
  | .noSeeds c => c ≤ G.witLen
  | .ranOut j c => c ≤ G.witLen ∧ j ≤ Spec.Dsa.parameterSeeds

/-- The whole search's result. -/
abbrev sW (G : GP) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch G.pLen G.k0 G.witB

/-- The controller's stage at the cursor `c` with `j` seeds left. -/
abbrev cBase (G : GP) (HO : HashOk Gh) (c j : Nat) : Cfg :=
  ((({ cl := [(sMsg + G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 64 c)).setV fSeedLeft
    (BitVec.ofNat 64 j)).setV fStatus 0

/-- The search with `r` iterations left of `N`. -/
abbrev sInv (G : GP) (HO : HashOk Gh) (N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ sCount G (sPos G (N - r)).1 (sPos G (N - r)).2 (N - r) = N ∧
    (Spec.Dsa.parameterSearch G.pLen (sPos G (N - r)).1 (G.witB.drop (sPos G (N - r)).2)).consume
      (sPos G (N - r)).2 [] = sW G ∧
    (sPos G (N - r)).2 ≤ G.witLen ∧ (sPos G (N - r)).1 ≤ Spec.Dsa.parameterSeeds) ∧
    St G (cBase G HO (sPos G (N - r)).2 (sPos G (N - r)).1) X σ s

/-- The controller's end. -/
abbrev cOut (G : GP) (N : Nat) : COut := cOutAt G (sPos G (N - 1))

theorem sBody_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp)
    {N : Nat} (r : Nat) :
    VP (sInv G HO N X (r + 1)) (seqs [.block (cmpF fSeedLeft 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 3))
          (seqs [.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 g.qLen] ++ ltR),
            .ite (.zero .d .r0) (.block (stImm fStatus 2))
              (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite (.zero .d .r0) (.block Geo.rejected) (.block [])])]),
        .block (cmpF fStatus 0)])
      (fun σ s => isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧
        (r = 0 → St G (cFin G (cOut G N)) X σ s ∧ cRes G (cOut G N) = sW G ∧ cOk G (cOut G N)) ∧
        (0 < r → sInv G HO N X r σ s)) := by
  refine VP.intro fun ⟨hr, hc, hW, hcw, hj⟩ => ?_
  obtain hq0 : 0 < G.qLen := by have := O.hlq; omega_using [this]
  obtain hq15 : G.qLen < 2 ^ 15 := by have := O.hlq; omega_using [this]
  obtain hpL : 0 < G.pLen := by have := O.hlq; omega_using [this]
  have h64 := O.h64
  have hwl := O.hwl
  have hqL := O.hqL
  generalize hii : N - (r + 1) = i at hc hW hcw hj
  generalize hp : sPos G i = jc at hc hW hcw hj
  obtain ⟨j, c⟩ := jc
  dsimp only at hc hW hcw hj
  obtain hNi : N - 1 = i + r := by omega_using [hr, hii]
  rw [O.hq]
  refine VP.seq (G := fun σ s => St G (cBase G HO c j) X σ s ∧
      isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 j == BitVec.ofNat 64 0))
    (cmpF_vp (x := BitVec.ofNat 64 j) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fSeedLeft, fStatus]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, e⟩) ?_
  obtain jl : j < 2 ^ 64 := by simp only [Spec.Dsa.parameterSeeds] at hj; omega_using [hj]
  rcases j with _ | j
  · -- No seeds left: `fStatus` := 3.
    obtain r0 : r = 0 := by simp only [sCount] at hc; omega_using [hr, hii, hc]
    subst r0
    obtain hout : cOut G N = .noSeeds c := by simp only [cOut, hNi, Nat.add_zero, hp, cOutAt]
    refine VP.seq (G := St G ((cBase G HO c 0).setV fStatus (BitVec.ofNat 64 3)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => cBase G HO c 0) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)) ?_
    refine cmpF_vp (x := BitVec.ofNat 64 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
    · rw [hout]
      refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
        (fun _ h' => absurd h' (by simp [cFin]))
      change o ∈ [fStatus, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
    · rw [hout, ← hW]; exact (VG.Proof.Dsa.Generation.search_zero _ _ _).symm
    · rw [hout]; exact hcw
  · have e0 : (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega_using [hr, hq0, hq15, hpL, h64, hwl, hqL, hii, hcw, hNi, hc, hj, jl, e, this]
    obtain notZ : ∀ {G₁ : State → State → Prop} {c' : Prog isa}, VP (fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0)) ∧
        isa.eval (.zero .d .r0) s = some true) c' G₁ :=
      VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    obtain avail := (avail_vp (X := X) (d := cBase G HO c (j + 1)) (by simp) (by simp [upd, fC, fSeedLeft, fStatus])
      hcw h64 hq15).mono (F' := fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0)) ∧
        isa.eval (.zero .d .r0) s = some false) (fun σ s h => h.1.1) fun _ _ h => h
    by_cases hshort : G.witLen - c < G.qLen
    · -- Too few octets for a seed: `fStatus` := 2.
      obtain r0 : r = 0 := by simp only [sCount, hshort, ↓reduceIte] at hc; omega_using [hr, hii, hc]
      subst r0
      obtain hout : cOut G N = .ranOut (j + 1) c := by
        simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte]
      refine VP.seq (G := St G ((cBase G HO c (j + 1)).setV fStatus (BitVec.ofNat 64 2)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (stImm_vp (c := fun _ => cBase G HO c (j + 1)) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
            fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
      · rw [hout]
        refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
          (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
        change o ∈ [fStatus, fSeedLeft, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
      · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_short (by rw [hwl, ← hqL]; exact hshort), hwl]
      · rw [hout]; exact ⟨hcw, hj⟩
    · -- A seed.
      obtain hcq : c + G.qLen ≤ G.witLen := by omega_using [hq0, hshort]
      obtain attempt := O.attempt_vp (X := X) (k := c) (u := c + G.qLen) (n := BitVec.ofNat 64 (j + 1)) hcq hcq
      obtain hmono : ∀ σ s, St G (((cBase G HO c (j + 1)).setV fSeed (G.seeds + BitVec.ofNat 64 c)).setV fUsed
          (BitVec.ofNat 64 (c + G.qLen))) X σ s →
          St G ((aBase G HO c (BitVec.ofNat 64 (j + 1))).setV fUsed (BitVec.ofNat 64 (c + G.qLen))) X σ s := by
        intro σ s h
        refine ⟨h.1.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
          (fun _ h' => absurd h' (by simp)), h.2⟩
        change o ∈ [fUsed, fStatus, fSeedLeft, fSeed, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
      obtain start := (seedStart_vp (X := X) O.hq (d := cBase G HO c (j + 1)) (c := c) (by simp)
        (by simp [upd, fC, fSeedLeft, fStatus]) hq15).mono (F' := fun σ s =>
          (St G (cBase G HO c (j + 1)) X σ s ∧ isa.eval (.zero .d .r0) s = some (decide (G.witLen - c < G.qLen))) ∧
          isa.eval (.zero .d .r0) s = some false) (fun σ s h => h.1.1) hmono
      obtain wrap : ∀ {G₁ : State → State → Prop}, VP (St G ((aBase G HO c (BitVec.ofNat 64 (j + 1))).setV fUsed
          (BitVec.ofNat 64 (c + G.qLen))) X) (seqs [g.attempt, .block (cmpF fStatus 0),
            .ite (.zero .d .r0) (.block Geo.rejected) (.block [])]) G₁ →
          VP (fun σ s => St G (cBase G HO c (j + 1)) X σ s ∧
            isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0))
            (.ite (.zero .d .r0) (.block (stImm fStatus 3))
              (seqs [.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 G.qLen] ++ ltR),
                .ite (.zero .d .r0) (.block (stImm fStatus 2))
                  (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                    .ite (.zero .d .r0) (.block Geo.rejected) (.block [])])])) G₁ := fun k =>
        VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z) (VP.seq start k)))
      obtain hRc : (G.witB.drop c).take (Spec.Dsa.generationQLen G.pLen) = seedAt G c := by
        show _ = (G.witB.drop c).take G.qLen; rw [hqL]
      obtain hcq' : c + Spec.Dsa.generationQLen G.pLen ≤ G.witB.length := by rw [hwl, ← hqL]; exact hcq
      obtain suffix : ∀ {x : Option Spec.Dsa.Params} {rest : List Byte}, sR G c = some (x, rest) →
          G.witB.drop (G.witLen - rest.length) = rest := fun {x rest} e => by
        rw [← hwl]
        exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.refillAttempt_suffix e).trans (List.drop_suffix _ _))
      obtain rlen : ∀ {x : Option Spec.Dsa.Params} {rest : List Byte}, sR G c = some (x, rest) →
          G.witLen - rest.length ≤ G.witLen := fun _ => Nat.sub_le _ _
      change VP _ _ (St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) (sR G c)) X) at attempt
      rcases hR : sR G c with _ | ⟨_ | a, rest⟩ <;> rw [hR] at attempt
      · -- `rand` ran out inside the seed.
        obtain r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega_using [hr, hii, hc]
        subst r0
        obtain hout : cOut G N = .ranOut (j + 1) c := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) none) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
          (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;> exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fC, fSeedLeft, fSeed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_attemptNone hpL hcq' (by rw [hRc, ← hqL]; exact hR),
            hwl]
        · rw [hout]; exact ⟨hcw, hj⟩
      · -- Rejected: the next seed.
        obtain hsuf := suffix hR
        obtain hcs : sCount G (j + 1) c i = sCount G j (G.witLen - rest.length) (i + 1) := by
          simp only [sCount, hshort, ↓reduceIte, hR]
        obtain hgt := sCount_gt G j (G.witLen - rest.length) (i + 1)
        obtain rpos : 0 < r := by omega
        obtain hNr : N - r = i + 1 := by omega_using [hr, hii]
        obtain hp1 : sPos G (i + 1) = (j, G.witLen - rest.length) := by
          simp only [sPos, hp, hR, Nat.add_sub_cancel]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) (some (none, rest))) X σ s ∧
            isa.eval (.zero .d .r0) s = some true)
          (cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus]))
            fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            ((rejected_vp (u := G.witLen - rest.length) (j := j) (by simp [aOut]) (by simp [aOut, upd])
              (by simp [aOut]) (by simp [aOut, upd, fUsed, fStatus, fSeedLeft]) (by omega_using [jl])).mono
                (fun σ s h => h.1.1) fun _ _ h => h)
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus, fC, fSeedLeft]))
          fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega_using [rpos]), fun _ => ?_⟩
        simp only [sInv, hNr, hp1]
        refine ⟨⟨by omega_using [hr], by rw [← hcs]; exact hc, ?_, Nat.sub_le _ _, by omega_using [hj]⟩, ?_, x⟩
        · rw [← hW, VG.Proof.Dsa.Generation.search_rejected hpL hcq' (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm))
            (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
            (fun _ h' => absurd h' (by simp))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;>
            exact ⟨by simp [aOut], by simp [aOut, upd, fStatus, fC, fSeedLeft, fUsed]⟩
      · -- Parameters: `fStatus` = 1.
        obtain hsuf := suffix hR
        obtain r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega_using [hr, hii, hc]
        subst r0
        obtain hout : cOut G N = .found a (G.witLen - rest.length) := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) (some (some a, rest))) X σ s ∧
            isa.eval (.zero .d .r0) s = some false)
          (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine h'.mono (fun o ho => ?_) (fun y hy => hy)
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fUsed] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fUsed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_accepted hpL hcq' (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm))
            (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · rw [hout]; exact Nat.sub_le _ _

/-- The seeds, from the cursor 0 with `state[0]` seeds left. -/
theorem sLoop_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp) :
    VP (St G (cBase G HO 0 G.k0) X)
      (.loop (seqs [.block (cmpF fSeedLeft 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 3))
          (seqs [.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 g.qLen] ++ ltR),
            .ite (.zero .d .r0) (.block (stImm fStatus 2))
              (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite (.zero .d .r0) (.block Geo.rejected) (.block [])])]),
        .block (cmpF fStatus 0)]) (.zero .d .r0))
      (fun σ s => St G (cFin G (cOut G (sCount G G.k0 0 0))) X σ s ∧
        cRes G (cOut G (sCount G G.k0 0 0)) = sW G ∧ cOk G (cOut G (sCount G G.k0 0 0))) := by
  obtain hN := sCount_gt G G.k0 0 0
  generalize hNN : sCount G G.k0 0 0 = N at hN ⊢
  refine VP.mono (F := sInv G HO N X (N - 1 + 1)) ?_ (fun σ s h => ⟨⟨by omega_using [hN],
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; exact hNN,
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; simp [sPos, sW, Spec.Entropy.Result.consume],
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; simp [sPos], by rw [show N - (N - 1 + 1) = 0 by omega_using []]; exact O.k0⟩,
    by rw [show N - (N - 1 + 1) = 0 by omega_using []]; exact h⟩) fun _ _ h => h
  exact VP.loop (I := sInv G HO N X) (fun r => (sBody_vp O r).mono (fun _ _ h => h)
    fun σ s ⟨e, h0, hp⟩ => ⟨e, fun z => h0 z, hp⟩) _

end

end VG.Proof.Dsa.PPC64LE.Gen
