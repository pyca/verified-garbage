module
-- separate module: its stages build in parallel with the correctness proofs, `Sized`, and the taint checks, `TimeCheck`

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Rsa.X86.RvResult
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Twos
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Product
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Sqrt
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Count
import VerifiedGarbage.Proof.Rsa.X86.Rd.Gcd
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86.Rd.Stages2
import VerifiedGarbage.Proof.Rsa.RecoverDetModel
import VerifiedGarbage.Proof.Rsa.X86.RvLoads
import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
import VerifiedGarbage.Proof.Rsa.X86.RvArguments
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Appendix C.2 on i686: each run's stages, for its timing

The timing of `RecoverDetRt.sized` follows each run from the stage before a
loop to the loop's invariant, and from its end to the next loop: the stages
here (`D0` … `M4`) and the loops' invariants (`TwI`, `PI`, `SqI`) state only
what those steps need, every value but the modulus's oddness (for the GCD)
hidden.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet
open VG.Proof.Rsa (b2n sub32)

/-- The modulus: odd, at least 3, and narrow. -/
def NF (g : Geo) (n : Nat) : Prop := n % 2 = 1 ∧ 3 ≤ n ∧ n < 2 ^ (32 * g.w)

/-- Before `det`: `n` (narrow) and `d e` (wide), and a wide zero. -/
def D0 (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW [VG.Impl.Rsa.X86.Recover.wM,
    VG.Impl.Rsa.X86.Recover.wZ] V [] s ∧ AW VG.Impl.Rsa.X86.Recover.wZ = 0 ∧
    NF g (A VG.Impl.Rsa.X86.Recover.aN)

/-- After `d e - 1`. -/
def D1 (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [VG.Impl.Rsa.X86.Recover.aN] AW [wX, VG.Impl.Rsa.X86.Recover.wZ] V [sOkDE] s ∧
    AW VG.Impl.Rsa.X86.Recover.wZ = 0 ∧ NF g (A VG.Impl.Rsa.X86.Recover.aN)

/-- The halvings after `k` steps. -/
def TwI (g : Geo) (k : Nat) (u : State) : Prop :=
  ∃ s0 A AW V n x X, A VG.Impl.Rsa.X86.Recover.aN = n ∧ NF g n ∧ x < 2 ^ (32 * g.w) ∧
    TwoS g s0 A [aU, aX2, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sK, sOkDE] (32 * g.w) k
      ((twoStep (32 * g.W))^[k] (sub32 g.w n 1, x, X)) u

/-- Before the GCD: its odd input. -/
def Gpre (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [VG.Impl.Rsa.X86.Keys.aM, 0, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] s ∧
    A VG.Impl.Rsa.X86.Keys.aM % 2 = 1 ∧ NF g (A VG.Impl.Rsa.X86.Recover.aN)

/-- After the GCD. -/
def Gpost (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wX3] V [sOkDE] s ∧
    A aZero = 0 ∧ NF g (A VG.Impl.Rsa.X86.Recover.aN)

/-- Before a product: its sum and zero zeroed, and facts `F` it keeps. -/
def PP (g : Geo) (a z : Nat) (live liveW ls : List Nat) (F : (Nat → Nat) → (Nat → Nat) → Prop)
    (u : State) : Prop :=
  ∃ s0 A AW V, F A AW ∧ AW z = 0 ∧ AW a = 0 ∧ KS g s0 A live AW liveW V ls u

/-- A product after `k` steps. -/
def PI (g : Geo) (y x a z : Nat) (live liveW ls : List Nat) (F : (Nat → Nat) → (Nat → Nat) → Prop)
    (k : Nat) (u : State) : Prop :=
  ∃ s0 A AW V st, F A AW ∧ AW z = 0 ∧ ProdS g s0 A live AW liveW V ls y x a (32 * g.w) k st u

/-- After `m` and `r`. -/
def DA (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wA, wR, wN, wZ2] V [sLt, sOkDE] s ∧
    A aZero = 0 ∧ AW wN = A VG.Impl.Rsa.X86.Recover.aN ∧ AW wZ2 = 0

/-- After the second division. -/
def DB (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] AW [wN, wZ2] V
    [sExact, sLt, sOkDE] s ∧ A aOne1 = 1 ∧ A aZero = 0 ∧ AW wZ2 = 0

/-- After `b² - 4 n`. -/
def M4 (g : Geo) (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A [aD, aZero] AW [wR] V sqSlots s ∧ A aZero = 0

/-- The square root after `k` steps. -/
def SqI (g : Geo) (k : Nat) (u : State) : Prop :=
  ∃ s0 A AW V X, X < 2 ^ (32 * g.W) ∧
    SqS g s0 A AW V (16 * g.W) k ((sqrtStep (32 * g.w) (32 * g.W))^[k] (X, 0, 0)) u

/-- What `aProduct`'s product keeps. -/
def FA (g : Geo) (A _ : Nat → Nat) : Prop := A aZero = 0 ∧ NF g (A VG.Impl.Rsa.X86.Recover.aN)

/-- What `square`'s product keeps. -/
def FS (A _ : Nat → Nat) : Prop := A aZero = 0

/-! ## Each stage to the next -/

section
variable {g : Geo} {s : State}

theorem deMinus_step (h : D0 g s) : WP isa deMinus s (D1 g) := by
  obtain ⟨s0, A, AW, V, h, z, nf⟩ := h
  exact WP.mono (deMinus_ok h rfl z) fun t ⟨_, ht, _, zt⟩ => ⟨_, _, _, _, ht, zt, nf⟩

theorem twosHead_step (h : D1 g s) : WP isa (.seq twosInit (.block countN)) s (TwI g 0) := by
  obtain ⟨s0, A, AW, V, h, z, nf⟩ := h
  have z' : AW 0 = 0 := z
  have h1v := (h.view (j := VG.Impl.Rsa.X86.Recover.wZ) (by simp)).view (j := wX) (by simp)
  have h1t := h1v.mono (live' := [aZ0, aX2, VG.Impl.Rsa.X86.Recover.aN]) (liveW' := [wX])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (twosHead_ok h1t (n := A VG.Impl.Rsa.X86.Recover.aN) (x := AW wX % 2 ^ (32 * g.w)) (X := AW wX)
    (by simp [upd, aZ0, wX, VG.Impl.Rsa.X86.Recover.wZ, z']) rfl rfl rfl)
    fun t ht => ⟨_, _, _, _, _, _, _, ?_, nf, Nat.mod_lt _ (Nat.two_pow_pos _), ht⟩
  rfl

theorem twosBody_step {k : Nat} (hk : k < 32 * g.w) (h : TwI g k s) :
    WP isa twosBody s fun v => TwI g (k + 1) v ∧ v.zf = some (decide (32 * g.w - k - 1 = 0)) := by
  obtain ⟨s0, A, AW, V, n, x, X, hn, nf, xl, h⟩ := h
  have up := h.upper
  refine WP.mono (twosBody_ok twosIdx hk (by change 32 * (2 * g.n + 2) < _; omega) h) fun v ⟨hv, zv⟩ => ?_
  refine ⟨⟨s0, A, AW, V, n, x, X, hn, nf, xl, ?_⟩, zv⟩
  rw [Function.iterate_succ_apply']
  exact hv

theorem gcdSet_step (h : TwI g (32 * g.w) s) : WP isa gcdSet s (Gpre g) := by
  obtain ⟨s0, A, AW, V, n, x, X, hn, nf, xl, h⟩ := h
  have up := h.upper
  obtain ⟨odd, three, small⟩ := nf
  unfold TwoS at h
  refine WP.mono (gcdSetD_ok h rfl rfl) fun t ⟨A', ht, m, _, nt⟩ => ⟨_, _, _, _, ht, ?_, ?_⟩
  · rw [m, upd_ne _ _ (show aU ≠ aX2 by decide), upd_self]
    have nm1 : sub32 g.w n 1 = n - 1 := wsub_of_le small (by omega)
    have wle : 32 * g.w ≤ 32 * g.W := by change 32 * (2 * g.n + 2) ≤ 32 * (2 * (2 * g.n + 2) + 2); omega
    have xlt : x < 2 ^ (32 * g.W) := Nat.lt_of_lt_of_le xl (Nat.pow_le_pow_right (by decide) wle)
    rw [(twos_proj _ _ _ _ _ x).1, nm1]
    exact (twos_iter (by omega) (by omega) xlt).1
  · rw [nt, upd_ne _ _ (show VG.Impl.Rsa.X86.Recover.aN ≠ aX2 by decide),
      upd_ne _ _ (show VG.Impl.Rsa.X86.Recover.aN ≠ aU by decide), hn]
    exact ⟨odd, three, small⟩

end

section
variable [VG.Proof.Rsa.X86.BatchLaw] {g : Geo} {s : State}

theorem gcd_step (h : Gpre g s) : WP isa (VG.Impl.Rsa.X86.GcdBatchRt.body wid) s (Gpost g) := by
  obtain ⟨s0, A, AW, V, h, odd, nf⟩ := h
  refine WP.mono (gcdDet_ok h rfl rfl odd) fun t ht => ⟨_, _, _, _, ht, by simp [upd], ?_⟩
  simpa [upd, aZero, VG.Impl.Rsa.X86.Recover.aN] using nf

end

section
variable {g : Geo} {s : State}

theorem prodCount_step {y x a z : Nat} {live liveW ls : List Nat} {F : (Nat → Nat) → (Nat → Nat) → Prop}
    (h : PP g a z live liveW ls F s) : WP isa (.block countN) s (PI g y x a z live liveW ls F 0) := by
  obtain ⟨s0, A, AW, V, f, z0, a0, h⟩ := h
  refine WP.mono h.countN_ok fun t ht => ⟨s0, A, AW, V, (A y, AW x, 0), f, z0, ?_⟩
  unfold ProdS
  rw [upd_noop rfl, upd_noop rfl, upd_noop a0]
  exact ht

theorem prodBody_step {y x a t z k : Nat} {live liveW ls : List Nat} {F : (Nat → Nat) → (Nat → Nat) → Prop}
    (I : ProdIdx y x a t z live liveW ls) (hk : k < 32 * g.w) (h : PI g y x a z live liveW ls F k s) :
    WP isa (productStep y x a t z) s fun v =>
      PI g y x a z live liveW ls F (k + 1) v ∧ v.zf = some (decide (32 * g.w - k - 1 = 0)) := by
  obtain ⟨s0, A, AW, V, st, f, z0, h⟩ := h
  have up := h.upper
  exact WP.mono (productStep_ok I z0 hk (by change 32 * (2 * g.n + 2) < _; omega) h)
    fun v ⟨hv, zv⟩ => ⟨⟨_, _, _, _, _, f, z0, hv⟩, zv⟩

theorem aProductHead_step (h : Gpost g s) :
    WP isa (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide wid wZ2) (VG.Impl.Rsa.X86.KeyRt.zeroWide wid wA)) s
      (PP g wA wZ2 [1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wZ2, wX3] [sOkDE] (FA g)) := by
  obtain ⟨s0, A, AW, V, h, z, nf⟩ := h
  refine WP.mono (aProductHead_ok h rfl rfl) fun t ht => ⟨_, _, _, _, ⟨?_, ?_⟩, by simp [upd, wZ2, wA, wX3], by simp [upd], ht⟩
  · simpa [upd, aG, aZero] using z
  · simpa [upd, aG, VG.Impl.Rsa.X86.Recover.aN] using nf

theorem divA_step (h : PI g aG wX3 wA wZ2 [1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wZ2, wX3] [sOkDE] (FA g)
    (32 * g.w) s) : WP isa divA s (DA g) := by
  obtain ⟨s0, A, AW, V, st, ⟨z, nf⟩, z2, h⟩ := h
  unfold ProdS at h
  have h' := h.mono (live' := [aZero, VG.Impl.Rsa.X86.Recover.aN]) (liveW' := [wA, wZ2]) (ls' := [sOkDE])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩)
  have pos : 0 < upd A aG st.1 VG.Impl.Rsa.X86.Recover.aN := by
    rw [upd_ne _ _ (show VG.Impl.Rsa.X86.Recover.aN ≠ aG by decide)]; have := nf.2.1; omega
  refine WP.mono (divA_ok h' rfl (by simpa [upd, wZ2, wA, wX3] using z2) rfl pos)
    fun t ⟨_, ht, _, _, nt, zt⟩ => ⟨_, _, _, _, ht, ?_, nt, zt⟩
  simpa [upd, aG, aZero] using z

theorem divB_step (h : DA g s) : WP isa divB s (DB g) := by
  obtain ⟨s0, A, AW, V, h, z, nw, z2⟩ := h
  exact WP.mono (divB_ok h z rfl rfl rfl nw z2) fun t ⟨_, _, _, _, ht, _, _, one, zt, _, _, z2t⟩ =>
    ⟨_, _, _, _, ht, one, zt, z2t⟩

theorem squareHead_step (h : DB g s) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.chain nar .adc aD aD aOne1 false, VG.Impl.Rsa.X86.KeyRt.copy nar aBy aD,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid wB, VG.Impl.Rsa.X86.KeyRt.copy nar (2 * wB) aD,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid wA]) s
      (PP g wA wZ2 [aBy, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN] [wA, wB, wN, wZ2]
        [sExact, sLt, sOkDE] FS) := by
  obtain ⟨s0, A, AW, V, h, one, z, z2⟩ := h
  exact WP.mono (squareHead_ok h rfl one z rfl z2) fun t ⟨_, _, ht, _, _, a0, z20, _, zt, _⟩ =>
    ⟨_, _, _, _, zt, z20, a0, ht⟩

theorem minus4n_step (h : PI g aBy wB wA wZ2 [aBy, aD, aOne1, aZero, VG.Impl.Rsa.X86.Recover.aN]
    [wA, wB, wN, wZ2] [sExact, sLt, sOkDE] FS (32 * g.w) s) : WP isa minus4n s (M4 g) := by
  obtain ⟨s0, A, AW, V, st, z, _, h⟩ := h
  have z' : A aZero = 0 := z
  unfold ProdS at h
  have h' := h.mono (live' := [aD, aZero]) (liveW' := [wA, wN]) (ls' := [sK, sExact, sLt, sOkDE])
    (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩)
    (fun d hd => ⟨by revert hd; revert d; decide, rfl⟩)
  refine WP.mono (minus4n_ok h' rfl rfl) fun t ⟨_, ht, _⟩ => ⟨_, _, _, _, ht, ?_⟩
  simpa [upd, aBy, aZero] using z'

theorem sqrtHead_step (h : M4 g s) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.copy nar aRm aZero, VG.Impl.Rsa.X86.KeyRt.copy nar aY aZero,
      .block countW]) s (SqI g 0) := by
  obtain ⟨s0, A, AW, V, h, z⟩ := h
  exact WP.mono (sqrtHead_ok h z rfl) fun t ht =>
    ⟨_, _, _, _, _, by rw [← h.arrsW wR (by simp)]; exact val32_lt _ _ _ _, ht⟩

theorem sqrtBody_step {k : Nat} (hk : k < 16 * g.W) (h : SqI g k s) :
    WP isa sqrtBody s fun v => SqI g (k + 1) v ∧ v.zf = some (decide (16 * g.W - k - 1 = 0)) := by
  obtain ⟨s0, A, AW, V, X, xl, h⟩ := h
  have up := h.upper
  refine WP.mono (sqrtBody_ok hk (by change 16 * (2 * (2 * g.n + 2) + 2) < _; omega) (sqrtIter_lt xl k) h)
    fun v ⟨hv, zv⟩ => ⟨⟨s0, A, AW, V, X, xl, ?_⟩, zv⟩
  rw [Function.iterate_succ_apply']
  exact hv

end

/-- From the inputs to `det`'s stage: the modulus, and `d e` (wide). -/
theorem pre_step {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true) :
    WP isa (seqs [VG.Impl.Rsa.X86.RecoverRt.loads, VG.Impl.Rsa.X86.RecoverRt.prod]) s (D0 g.toGeo) := by
  have facts := valid
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at facts
  have odd : inputValue g s.mem 0 % 2 = 1 := facts.1.1.1
  have large : 3 ≤ inputValue g s.mem 0 := by
    have lower := facts.1.1.2
    have power (k : Nat) (hk : 2 ≤ k) : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (by decide) hk
    have bigger := power 511 (by decide)
    omega
  have up := h.upper
  have nb : inputValue g s.mem 0 < 2 ^ (64 * g.n) := by
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    omega
  have small : inputValue g s.mem 0 < 2 ^ (32 * g.toGeo.w) :=
    Nat.lt_of_lt_of_le nb (Nat.pow_le_pow_right (by decide) (by change 64 * g.n ≤ 32 * (2 * g.n + 2); omega))
  simp only [seqs]
  refine WP.seq (WP.mono (loads_ok h len) fun s1 h1 => ?_)
  have arg : VG.Proof.Bignum.X86.CallArgument s1 g.B g.Z 7 (BitVec.ofNat 32 ((g.args 7).toNat)) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      h1.argument (h.arguments 7 (by decide)) (h.stageApart (by decide))
  refine WP.mono (prod_ok h1 arg (h.inputPositive 1) (h.inputBound 1) (h.inputBound 2)
    (inputValue_lt g s.mem 1) (inputValue_lt g s.mem 2)) fun s2 h2 => ?_
  have h2' := h2.mono (liveW' := [VG.Impl.Rsa.X86.Recover.wM, VG.Impl.Rsa.X86.Recover.wZ])
    (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by revert hj; revert j; decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  exact ⟨_, _, _, _, h2', by simp [AWp, AW1, upd, VG.Impl.Rsa.X86.Recover.wZ, VG.Impl.Rsa.X86.Recover.wM,
    VG.Impl.Rsa.X86.Recover.wMod, VG.Impl.Rsa.X86.Recover.wE, VG.Impl.Rsa.X86.Recover.wD], odd, large, small⟩

end VG.Proof.Rsa.X86.Recover
