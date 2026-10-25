module
public import VerifiedGarbage.Proof.Rsa.Arm.RvCand1
public import VerifiedGarbage.Proof.Rsa.RecoverExp

import VerifiedGarbage.Proof.Rsa.Arm.RvSq1
import VerifiedGarbage.Proof.Rsa.Arm.RvCand2
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # `vg_rsa_recover_primes` on ARMv7: a squaring under masks (`sqStep_vp`)

`Qs j k`: after `k` squarings of the candidate `j`, `y` (in Montgomery form),
`done` and `ok` are those of `sqIter n t k (sqStart n (g^r mod n))`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n sqIter sqStep sqStart)

/-- `y = g^r mod n`. -/
def y0 (P : RP) (σ : State) (j : Nat) : Nat := Spec.Rsa.powMod (j + 2) (rv P σ) P.n

/-- After `k` squarings: `(y, done, ok)`. -/
def sqst (P : RP) (σ : State) (j k : Nat) : Nat × Bool × Bool := sqIter P.n (tv P σ) k (sqStart P.n (y0 P σ j))

/-- The header words after `k` squarings. -/
def Vq (P : RP) (σ : State) (j k : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (fun _ => 0) sTc (tv P σ)) sCand j) sCnt (P.c - k)) sK k) sDone
    (b2n (sqst P σ j k).2.1)) sOk (b2n (sqst P σ j k).2.2)
abbrev LSq : List Nat := [sOk, sDone, sK, sCnt, sCand, sTc]

/-- The arrays after `k` squarings. -/
def Aq (P : RP) (σ : State) (j k : Nat) : Nat → Nat := upd (AM P) mY ((sqst P σ j k).1 * Rm P % P.n)
abbrev Lq : List Nat := mY :: liveM

/-- After `k` squarings of the candidate `j`. -/
abbrev Qs (P : RP) (E : State → Prop) (j k : Nat) : State → State → Prop :=
  St P E (fun σ => Aq P σ j k) Lq (fun σ => AWh P σ P.c) [wR] (fun σ => Vq P σ j k) LSq P.w nArr

/-- `y²`. -/
abbrev xq (P : RP) (σ : State) (j k : Nat) : Nat := (sqst P σ j k).1 * (sqst P σ j k).1 % P.n

/-- Whether the squaring `k` replaces `y`. -/
def liveB (P : RP) (σ : State) (j k : Nat) : Bool :=
  !(sqst P σ j k).2.1 && decide (k < tv P σ) && !decide (xq P σ j k = 1) &&
    !(decide (xq P σ j k = P.n - 1) || decide (k + 1 = tv P σ))

/-- After the masks of the squaring `k`. -/
abbrev Qm (P : RP) (E : State → Prop) (j k : Nat) : State → State → Prop :=
  St P E (fun σ => upd (Aq P σ j k) mX (xq P σ j k * Rm P % P.n)) (mX :: Lq) (fun σ => AWh P σ P.c) [wR]
    (fun σ => upd (upd (upd (Vq P σ j k) sOk (b2n (sqst P σ j (k + 1)).2.2)) sDone (b2n (sqst P σ j (k + 1)).2.1))
      sLive (b2n (liveB P σ j k)))
    (sLive :: sDone :: sOk :: LSq) P.w nArr

section
variable {P : RP}

theorem sqst_succ (σ : State) (j k : Nat) : sqst P σ j (k + 1) = sqStep P.n (tv P σ) k (sqst P σ j k) := rfl

theorem sqst_lt (hn0 : 0 < P.n) (σ : State) (j k : Nat) : (sqst P σ j k).1 < P.n :=
  VG.Proof.Rsa.sqIter_lt hn0 k _ (by simp only [sqStart, y0]; rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hn0)

/-- The squaring, `x = 1`, `x = -1` and the masks. -/
theorem sqM_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hcl : P.c < 2 ^ 31) {E : State → Prop} {j k : Nat}
    (hk : k < P.c) (ht : ∀ σ, E σ → tv P σ ≤ P.c) {R : Prog isa} {G : State → State → Prop}
    (hR : VP (Qm P E j k) R G) :
    VP (Qs P E j k) (.seq (seqs (mmul iX iY iY)) (.seq (eqAt sE1 mX aO) (.seq (eqAt sE2 mX aNg)
      (.seq (.block sqMasks) R)))) G := by
  have hn0 : 0 < P.n := by omega_arith
  have hR' : Nat.Coprime (Rm P) P.n := VG.Proof.Bignum.coprime_pow2 hn.1 _
  refine VP.seq (St.pmmul (o := iX) (a := iY) (b := iY) (by decide) hn.1 (T := fun σ => xq P σ j k * Rm P % P.n)
    (by decide) (by decide) (by decide) (by decide) (by decide) fun σ _ => ?_) ?_
  · have eY : Aq P σ j k (mBase + iY) = (sqst P σ j k).1 * Rm P % P.n := by simp [Aq, upd, mY, mBase, iY]
    rw [eY]
    exact ⟨Nat.mod_lt _ hn0, Nat.mod_lt _ hn0, Nat.mod_lt _ hn0, VG.Proof.Rsa.mont_sq_eq _ _ _ _⟩
  refine VP.seq (St.peqS eqX1_taint (d := sE1) (a := mX) (b := aO) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.peqS eqX2_taint (d := sE2) (a := mX) (b := aNg) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq ((St.pmasks (kf := fun _ => k) (tf := fun σ => tv P σ) (dn := fun σ => (sqst P σ j k).2.1)
    (ok := fun σ => (sqst P σ j k).2.2) (e1 := fun σ => decide (xq P σ j k = 1))
    (e2 := fun σ => decide (xq P σ j k = P.n - 1)) (by decide) fun σ e => ?_).mono (fun _ _ h => h)
    fun σ s h => St.mono h ?_ ?_ ?_) hR
  · have htc := ht σ e
    have ex := Nat.mod_lt ((sqst P σ j k).1 * (sqst P σ j k).1) hn0
    have eX : upd (Aq P σ j k) (mBase + iX) (xq P σ j k * Rm P % P.n) mX = xq P σ j k * Rm P % P.n :=
      upd_self _ _ _
    have eO : upd (Aq P σ j k) (mBase + iX) (xq P σ j k * Rm P % P.n) aO = Ov P := by
      simp [upd, Aq, AM, aO, mBase, iX, mY, aNg]
    have eN : upd (Aq P σ j k) (mBase + iX) (xq P σ j k * Rm P % P.n) aNg = P.n - Ov P := by
      simp [upd, Aq, AM, mBase, iX, mY, aNg]
    have i1 : (if xq P σ j k * Rm P % P.n = Ov P then 1 else 0) = b2n (decide (xq P σ j k = 1)) := by
      have := VG.Proof.Rsa.eq_one_mont hR' hn.2 ex (X := xq P σ j k * Rm P % P.n) rfl
      simp only [show (xq P σ j k * Rm P % P.n = Ov P) ↔ xq P σ j k = 1 from this]
      by_cases h : xq P σ j k = 1 <;> simp only [h, b2n, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true]
    have i2 : (if xq P σ j k * Rm P % P.n = P.n - Ov P then 1 else 0) = b2n (decide (xq P σ j k = P.n - 1)) := by
      have := VG.Proof.Rsa.eq_neg_mont hR' hn.2 ex (X := xq P σ j k * Rm P % P.n) rfl
      simp only [show (xq P σ j k * Rm P % P.n = P.n - Ov P) ↔ xq P σ j k = P.n - 1 from this]
      by_cases h : xq P σ j k = P.n - 1 <;> simp only [h, b2n, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true]
    rw [eX, eO, eN, i1, i2]
    refine ⟨by omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [upd, Vq, sE1, sE2, sK, sTc, sDone, sOk, sCnt, sCand]
  · exact fun x hx => ⟨hx, rfl⟩
  · exact fun x hx => ⟨hx, rfl⟩
  · intro d hd
    refine ⟨by simp only [List.mem_cons] at hd ⊢; grind, ?_⟩
    simp only [LSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [upd_self, liveB]
    · simp only [upd_ne _ _ (show sDone ≠ sLive by decide), upd_self, sqst_succ, sqStep]
    · simp only [upd_ne _ _ (show sOk ≠ sLive by decide), upd_ne _ _ (show sOk ≠ sDone by decide), upd_self,
        sqst_succ, sqStep]
    all_goals simp [upd, sqst_succ, sqStep, sOk, sDone, sK, sCnt, sCand, sTc, sLive, sE1, sE2]

end

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- `k += 1` and the count. -/
theorem St.psqNext (hk : sK ∈ LS) (hc : sCnt ∈ LS) (hv : ∀ σ, E σ → V σ sK + 1 < 2 ^ 32 ∧ 1 ≤ V σ sCnt ∧
      V σ sCnt < 2 ^ 32) :
    VP (St P E A L AW LW V LS P.w nArr) (.block sqNext) (fun σ s =>
      St P E A L AW LW (fun σ => upd (upd (V σ) sK (V σ sK + 1)) sCnt (V σ sCnt - 1)) (sCnt :: sK :: LS)
        P.w nArr σ s ∧ s.z = decide (V σ sCnt - 1 = 0)) := by
  refine VP.ctx sqNext_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  obtain ⟨h1, h2, h3⟩ := hv σ e
  unfold sqNext
  refine h.ldrSlot hw hk (r := .r1) (by decide) fun s1 g1 hw1 u1 => ?_
  have m1 := hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨g2, hw2⟩ := g1.reg hw1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have m2 := m1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine g2.strSlot_m m2 hw2 (d := sK) (r := .r1) (by decide) fun t ht mt hwt _ _ => ?_
  have e2 : (s2.gpr .r1).toNat = V σ sK + 1 := by
    rw [u2.gpr, dpVal, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  rw [e2] at ht
  have c1 : upd (V σ) sK (V σ sK + 1) sCnt = V σ sCnt := upd_ne _ _ (by decide)
  refine WP.mono (ht.cntNext_m mt hwt (List.mem_cons_of_mem _ hc) (by rw [c1]; exact h2) (by rw [c1]; exact h3))
    fun t' ⟨ht', mt', hwt', z⟩ => ⟨⟨e, ?_, mt', hwt'⟩, by rw [z, c1]⟩
  rw [c1] at ht'; exact ht'

end

section
variable {P : RP}

/-- `y := y²` under the mask, and the counts. -/
theorem sqB_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hcl : P.c < 2 ^ 31) {E : State → Prop} {j k : Nat} (hk : k < P.c) :
    VP (Qm P E j k) (.seq (copy aU mY) (.seq (sel mY aU mX sLive) (.block sqNext)))
      (fun σ s => isa.eval .ne s = some (decide (k + 1 < P.c)) ∧ Qs P E j (k + 1) σ s) := by
  have hn0 : 0 < P.n := by omega_arith
  refine VP.seq (St.pcopy uY_taint (o := aU) (a := mY) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_
  refine VP.seq (St.psel selY_taint (o := mY) (a := aU) (b := mX) (sl := sLive) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ _ => by simp only [upd_self]; exact VG.Proof.Rsa.b2n_le _)
    (by decide)) ?_
  refine (St.psqNext (by decide) (by decide) fun σ _ => ?_).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ =>
    ⟨?_, St.mono h ?_ (fun x hx => ⟨hx, rfl⟩) ?_⟩
  · simp [upd, Vq, sK, sCnt, sOk, sDone, sLive]; omega_arith
  · show some (!s.z) = some (decide (k + 1 < P.c))
    rw [z]
    by_cases hh : k + 1 < P.c <;> simp [hh, upd, Vq, sK, sCnt, sOk, sDone, sLive] <;> omega_arith
  · intro x hx
    refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)), ?_⟩
    simp only [Lq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [upd_self, Aq, sqst_succ, sqStep]
      have ey : upd (upd (AM P) mY ((sqst P σ j k).1 * Rm P % P.n)) mX (xq P σ j k * Rm P % P.n) mY =
          (sqst P σ j k).1 * Rm P % P.n := by simp [upd, mY, mX]
      have ex : upd (upd (upd (AM P) mY ((sqst P σ j k).1 * Rm P % P.n)) mX (xq P σ j k * Rm P % P.n)) aU
          (upd (upd (AM P) mY ((sqst P σ j k).1 * Rm P % P.n)) mX (xq P σ j k * Rm P % P.n) mY) mX =
          xq P σ j k * Rm P % P.n := by simp [upd, mX, aU]
      rw [ex, ey]
      show (if b2n (liveB P σ j k) = 0 then _ else _) =
        (if liveB P σ j k = true then xq P σ j k else (sqst P σ j k).1) * Rm P % P.n
      cases liveB P σ j k <;> rfl
    all_goals simp [upd, Aq, mY, aU, mX, aNg, aO, mR2, aOne, aZ, aN]
  · intro d hd
    refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hd)))), ?_⟩
    simp only [LSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [upd, Vq, sK, sCnt, sOk, sDone, sLive, sCand, sTc]
    omega_arith

/-- The squaring `k`. -/
theorem sqStep_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hcl : P.c < 2 ^ 31) {E : State → Prop} {j k : Nat} (hk : k < P.c)
    (ht : ∀ σ, E σ → tv P σ ≤ P.c) :
    VP (Qs P E j k) sqBody (fun σ s => isa.eval .ne s = some (decide (k + 1 < P.c)) ∧ Qs P E j (k + 1) σ s) := by
  simp only [sqBody, seqs]
  exact sqM_vp hn hcl hk ht (sqB_vp hn hcl hk)

/-- The `c` squarings. -/
theorem sqLoop_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hcl : P.c < 2 ^ 31) (hc0 : 0 < P.c) {E : State → Prop}
    (ht : ∀ σ, E σ → tv P σ ≤ P.c) {j : Nat} : VP (Qs P E j 0) sqLoop (Qs P E j P.c) := by
  have hl := VP.loop (I := fun m σ s => m ≤ P.c ∧ Qs P E j (P.c - m) σ s) (body := sqBody) (c := .ne)
    (Q := Qs P E j P.c) (fun n => VP.pure fun hle => (sqStep_vp hn hcl (k := P.c - (n + 1)) (by omega_arith) ht).mono
      (fun _ _ h => h) fun σ s ⟨ev, h⟩ => ⟨by rw [ev]; congr 1; simp only [decide_eq_decide]; omega_arith,
        fun h0 => by subst h0; rwa [show P.c - (0 + 1) + 1 = P.c by omega_arith] at h,
        fun _ => ⟨by omega_arith, by rwa [show P.c - (n + 1) + 1 = P.c - n by omega_arith] at h⟩⟩) (P.c - 1)
  exact hl.mono (fun σ s h => ⟨by omega_arith, by rwa [show P.c - (P.c - 1 + 1) = 0 by omega_arith]⟩) fun _ _ h => h

end

end VG.Proof.Rsa.Arm.Recover
