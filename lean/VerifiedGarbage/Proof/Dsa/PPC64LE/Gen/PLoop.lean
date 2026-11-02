module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PPart
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Omega

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
      have hkB : sX + G.pLen ≤ kB G.pLen := by rcases h.lens with e | e | e <;> rw [e] <;> decide
      exact ⟨by simp [Spec.Rsa.bytesAt], by simp only [ClOk, pStart, List.length_nil, hEnd, fSave, sX] at hkB ⊢; omega⟩
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
  refine (pCont_vp (X := X) hcnt dP dPv dC dCv dO dOv (by omega)).mono (fun _ _ h => h) fun σ s h => ?_
  split at h
  · -- The last counter: `fP` := 2.
    rename_i e
    have hN : N = j + 1 := by
      rw [show 32 * G.pLen - 1 - j = 0 by omega] at hc; simp only [pCount] at hc; omega
    have r0 : r = 0 := by omega
    subst r0
    refine ⟨by rw [h.2]; rfl, fun _ => ⟨?_, h.1.2⟩, fun h0 => absurd h0 (by decide)⟩
    have hd : pSpec HO G k u0 0 = some (none, G.witB.drop u') := by
      rw [← hR, hspec, VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega)]
    rw [hd]; simp only [pFin]
    have lu : G.witLen - (G.witB.drop u').length = u' := by rw [List.length_drop, hwl]; omega
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
    obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨32 * G.pLen - 1 - j - 1, by omega⟩
    rw [hm, hstep] at hc
    have hgt := pCount_gt HO G k u0 m (j + 1)
    have rpos : 0 < r := by omega
    have hNr : N - r = j + 1 := by omega
    refine ⟨by rw [h.2]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
    show (_ ∧ _) ∧ _
    rw [hNr, hpu]
    refine ⟨⟨by omega, by omega, by rw [show 32 * G.pLen - 1 - (j + 1) = m by omega]; exact hc,
      by rw [← hR, hspec]; simp only [pSpec, hpu], hu'⟩, ?_, h.1.2⟩
    have r1 := h.1.1.pBase (HO := HO) (k := k) (by exact dpad) (by exact dq)
    have eo : 1 + j * (cnt G + 1) + (cnt G + 1) = 1 + (j + 1) * (cnt G + 1) := by rw [Nat.succ_mul]; omega
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
  have r0 : r = 0 := by omega
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
  have hl : G.pLen ≤ 384 := by omega
  have hcnt : cnt G + 1 ≤ 12 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  have hcount : g.count = cnt G := by simp only [Geo.count, hp, hq, cnt]
  have ecode : VG.Impl.Rsa.PPC64LE.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
      .ite (.zero .d .r0) (.seq (.block g.pAdvance) (.ite (.zero .d .r0) (.block (stImm fP 2)) (.block [])))
        (.block []),
      .block (cmpF fP 4)] = .seq g.pAttempt (pTail (cnt G + 1) G.pLen) := by
    simp only [Geo.pAdvance, hcount, hp]; rfl
  rw [ecode]
  have hoffb : 1 + j * (cnt G + 1) + (cnt G + 1) < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hj) hcnt; omega
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
  -- The spec's step.
  have hstepS := VG.Proof.Dsa.Generation.primeSearch_step (l := 8 * G.pLen) (n := 8 * G.qLen)
    (q := Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (G.witB.drop (pU HO G k u0 j)) (by omega : j < 4 * (8 * G.pLen))
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
  have hn : PNot c := ⟨n1, n2, n3, n4, n5, n6, n7⟩
  have hN1 : ∀ (hlast : ∀ m, pCount HO G k u0 (m + 1) j = j + 1), N = j + 1 := fun hlast => by
    rw [← hc]
    rcases Nat.eq_zero_or_pos (32 * G.pLen - 1 - j) with h0 | h0
    · rw [h0]; rfl
    · obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm, hlast]
  have padIn : ∀ x y : Nat × List Byte, (sMsg + G.qLen, padTail HO.md G.qLen) ∈ x :: y :: pRest HO.md G k := by
    simp [pRest]
  have qIn : ∀ x y : Nat × List Byte, (sQ, qBytes G k) ∈ x :: y :: pRest HO.md G k := by simp [pRest]
  by_cases hs : pShort HO G k j
  · -- Too short: the next counter.
    rw [pAttCfg, ite_eq_left_of_eq_true _ _ (eq_true hs)]
    refine pGo_vp hn hjj (by omega) hj hl (by omega) hwl hc hR
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
    refine pStop_vp (v := 0) hjj (by omega) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
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
    refine pGo_vp (u' := G.witLen - rr.length) hn hjj (by omega) hj hl (by omega) hwl hc hR
      (fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp only [pU, hs, hpp, ↓reduceIte])
      (by rw [hstepS, ← hwl, VG.Proof.Dsa.Generation.probablePrime_cursor hpp]) (by omega)
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
    refine pStop_vp (v := 1) hjj (by omega) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
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
  have hN := pCount_gt HO G k u0 (32 * G.pLen - 1) 0
  generalize hNN : pCount HO G k u0 (32 * G.pLen - 1) 0 = N at hN
  have hl : G.pLen ≤ 384 := by omega
  have hpL : 0 < G.pLen := by omega
  refine VP.seq ?_ ?_ (G := pInv c HO G k u0 N X N)
  · rw [List.append_assoc]
    refine VP.block_append (G := St G (d.setV fCounter (BitVec.ofNat 64 0)) X)
      (stImm_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.2⟩) ?_
    refine VP.block_append (G := St G ((d.setV fCounter (BitVec.ofNat 64 0)).setV fOffset (BitVec.ofNat 64 1)) X)
      (stImm_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 64 0)) (fun σ s h => h.1) (by decide)
        (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.2⟩) ?_
    refine stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 64 0)).setV fOffset (BitVec.ofNat 64 1))
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨⟨Nat.le_refl _, by simp; omega,
        by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self], by simp only [Nat.sub_self]; exact hu0⟩,
        ?_, h.2⟩
    have r1 := h'.pBase (HO := HO) (k := k) (by exact dpad) (by exact dq)
    rw [Nat.sub_self]
    refine r1.mono (pCfgJ_V hn (fun o ho => by simp [(dLS o ho).1]) (by simp) (by simp) (by simp) (by simp [dU])
      (by simp [upd]) (by simp [upd, fOffset, fP]) (by simp [upd, fCounter, fOffset, fP])
      (by simp [upd, fUsed, fCounter, fOffset, fP, pU]; exact dUv) fun o ho => ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho
    simp [upd, m2, m3, m4]; exact (dLS o ho).2
  rw [show N = N - 1 + 1 by omega]
  exact VP.loop (I := pInv c HO G k u0 (N - 1 + 1) X)
    (pBody_vp HO okp lay hlq hp hq hk4 hsb hH hwl hn hk hS hSv hcand) _

end

end VG.Proof.Dsa.PPC64LE.Gen
