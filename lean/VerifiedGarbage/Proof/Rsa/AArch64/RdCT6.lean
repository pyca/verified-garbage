module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
public import VerifiedGarbage.Proof.Rsa.AArch64.RdOps
import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdOps
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT4
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCTSqrt
public import VerifiedGarbage.Proof.Rsa.AArch64.RdFin
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
public import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT4
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCTSqrt
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdFin
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
public import VerifiedGarbage.Proof.Rsa.AArch64.RdGcd
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdGcd
import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.KeepLanesOnce
import VerifiedGarbage.Proof.Rsa.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrtDigits
import VerifiedGarbage.Proof.Rsa.RecoverRoot
meta import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Proof.Rsa.TwosMath
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
meta import VerifiedGarbage.Proof.Bignum.CrtFrame
meta import VerifiedGarbage.Proof.Rsa.AArch64.Div
meta import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.AArch64.KeepLanesOnce
meta import VerifiedGarbage.Proof.Rsa.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrtDigits
meta import VerifiedGarbage.Proof.Rsa.RecoverRoot

/-! ### `Rsa.AArch64.RdCode`, which this module and modules that import it used -/

section

/-! ### `Rsa.AArch64.RdMain`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_recover_primes_det` on AArch64: `main`

`mid_ok`: from `d e` and `n`, the pieces from `d e - 1` to the square root
compute `RecoverDetModel`'s mask, `b` and `ϒ`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet
open VG.Spec.Rsa (isqrt)

/-- A wide array as its two narrow halves. -/
theorem wide_split (m : Mem) (B : Addr) (v i : Nat) :
    wv m B (slot (2 * v + 2) i) (2 * v + 2) =
      wv m B (slot v (2 * i)) (v + 2) + 2 ^ (64 * (v + 2)) * wv m B (slot v (2 * i + 1)) v := by
  rw [slot_wide, show 2 * v + 2 = (v + 2) + v by omega_using [], wv_add, slot_succ]

theorem bool_shuffle (a l r f x z : Bool) :
    (a && l && (r && (f && x) && z)) = (z && (r && (true && a && l) && f && x)) := by
  cases a <;> cases l <;> cases r <;> cases f <;> cases x <;> cases z <;> rfl

theorem mask_eq {nb wb N de q rem k : Nat} (hk : k = wb / 2) :
    (okDE wb de && ltOf nb wb N de && (stage2 nb wb N q rem).1) =
      (decide (((sqrtStep nb wb)^[k] (xOf nb wb N (bOf nb q), 0, 0)).2.1 = 0) &&
        (decide (rem = 0) && (true && okDE wb de && ltOf nb wb N de) &&
          decide (fourN wb N ≤ sqOf nb wb (bOf nb q)) && decide (1 ≤ xOf nb wb N (bOf nb q)))) := by
  subst hk
  unfold stage2 ok4Of rootOf
  dsimp only
  rw [ok4_eq]
  exact bool_shuffle _ _ _ _ _ _


theorem m1_pos {nb wb N de : Nat} (hN : N < 2 ^ nb) (hl : ltOf nb wb N de = true) : 0 < m1Of nb wb N de := by
  have hm : mOf nb wb N de < N := of_decide_eq_true hl
  unfold m1Of
  rw [Nat.mod_eq_of_lt (show mOf nb wb N de < 2 ^ nb by omega_using [hN, hm]),
    Nat.mod_eq_of_lt (show mOf nb wb N de + 1 < 2 ^ nb by omega_using [hN, hm])]
  omega_using []

/-- Under the earlier checks, the model's root by bit pairs is `isqrt`: the mask with its test is the mask with
`⌊√X⌋² = X`. -/
theorem mask_root {nb wb N de q rem : Nat} (three : 3 ≤ N) (hn : 8 * (N + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hwe : wb % 2 = 0) (hN : N < 2 ^ nb)
    (hdiv : 0 < m1Of nb wb N de → q = dOf nb wb N de / m1Of nb wb N de ∧ rem = dOf nb wb N de % m1Of nb wb N de) :
    (decide (((sqrtStep nb wb)^[wb / 2] (xOf nb wb N (bOf nb q), 0, 0)).2.1 = 0) &&
      (decide (rem = 0) && (true && okDE wb de && ltOf nb wb N de) &&
        decide (fourN wb N ≤ sqOf nb wb (bOf nb q)) && decide (1 ≤ xOf nb wb N (bOf nb q)))) =
    (decide (Spec.Rsa.isqrt (xOf nb wb N (bOf nb q)) * Spec.Rsa.isqrt (xOf nb wb N (bOf nb q)) =
        xOf nb wb N (bOf nb q)) &&
      (decide (rem = 0) && (true && okDE wb de && ltOf nb wb N de) &&
        decide (fourN wb N ≤ sqOf nb wb (bOf nb q)) && decide (1 ≤ xOf nb wb N (bOf nb q)))) := by
  generalize hC : (decide (rem = 0) && (true && okDE wb de && ltOf nb wb N de) &&
    decide (fourN wb N ≤ sqOf nb wb (bOf nb q)) && decide (1 ≤ xOf nb wb N (bOf nb q))) = C
  cases C
  · simp
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.true_and] at hC
    obtain ⟨⟨⟨_, _, hl⟩, h1⟩, h2⟩ := hC
    have h4 : ok4Of nb wb N (bOf nb q) = true := by
      unfold ok4Of; rw [ok4_eq]; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩
    have hr := root_bridge three hn hw hwe hl (hdiv (m1_pos hN hl)).1 h4
    exact congrArg (· && true) (decide_eq_decide.mpr hr.2.1)

theorem y_root {nb wb N de q rem : Nat} (three : 3 ≤ N) (hn : 8 * (N + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hwe : wb % 2 = 0) (hN : N < 2 ^ nb)
    (hdiv : 0 < m1Of nb wb N de → q = dOf nb wb N de / m1Of nb wb N de ∧ rem = dOf nb wb N de % m1Of nb wb N de)
    (hm : (okDE wb de && ltOf nb wb N de && (stage2 nb wb N q rem).1) = true) :
    Spec.Rsa.isqrt (xOf nb wb N (bOf nb q)) % 2 ^ nb = (rootOf nb wb N (bOf nb q)).2.2 := by
  unfold stage2 at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨_, hl⟩, ⟨_, h4⟩, _⟩ := hm
  have hr := root_bridge three hn hw hwe hl (hdiv (m1_pos hN hl)).1 h4
  rw [hr.1, Nat.mod_eq_of_lt hr.2.2]

/-- The pieces from `d e - 1` to `a`. -/
theorem mid4_ok [GcdLaw gcdB] {I : RpIn} {m₀ : Mem} {s : State} (h : G I m₀ (vk I.k) true s) (L : RpLens I) {N de : Nat}
    (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N) (hodd : N % 2 = 1) (h3 : 3 ≤ N)
    (hNlt : N < 2 ^ (64 * vk I.k))
    (hM : wv s.mem I.B (slot (vk I.k) 10) (2 * (vk I.k + 2)) = de) (hde : de < 2 ^ (64 * vk I.k)) :
    WP isa (seqs [deMinus, twos, gcd, aProd]) s fun t => G I m₀ (vk I.k) (true && okDE (64 * Wk I.k) de) t ∧
      wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k) = aOf (64 * vk I.k) (64 * Wk I.k) N de ∧
      wv t.mem I.B (slot (vk I.k) 0) (vk I.k) = N ∧ wv t.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1 := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega_using []
  have hb32 := hb32_of h L
  simp only [seqs]
  -- `d e - 1`.
  refine WP.seq (WP.mono (deMinus_ok h L hM hde) fun s₂ ⟨g₂, X₂, F₂⟩ => ?_)
  have n₂ : wv s₂.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by
    rw [Frm.hdr_wv F₂ (slot_ge _ _) (by have := slot_lt (w := vk I.k) (show 0 < 32 by decide); omega_using [hb32, this]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact .inr (hdr_lt_slot _ _ (by decide))
      all_goals exact nw_sep (by decide) (by decide) (by omega_using []) (by omega)), hN]
  -- The halvings.
  refine WP.seq (WP.mono (twos_ok g₂ L n₂ (by omega_using [h3]) X₂) fun s₃ hT => ?_)
  have hnb : 2 ^ (64 * vk I.k) ≤ 2 ^ (64 * Wk I.k) := Nat.pow_le_pow_right (by decide) (by omega_using [hW])
  have hstart : twosOut (64 * vk I.k) (64 * Wk I.k) N de =
      (twoStep (64 * Wk I.k))^[64 * vk I.k] (N - 1, deX (64 * Wk I.k) de % 2 ^ (64 * vk I.k), deX (64 * Wk I.k) de) := by
    unfold twosOut; rw [wsub_of_le hNlt (by omega_using [hodd])]
  have hval := hT.val
  generalize hst : (twoStep (64 * Wk I.k))^[64 * vk I.k] (N - 1, deX (64 * Wk I.k) de % 2 ^ (64 * vk I.k),
    deX (64 * Wk I.k) de) = st at hval hstart
  -- `u` is odd.
  have uodd : st.1 % 2 = 1 := by
    have xlt : deX (64 * Wk I.k) de % 2 ^ (64 * vk I.k) < 2 ^ (64 * Wk I.k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hnb
    rw [← hst, (twos_proj _ _ _ _ _ (deX (64 * Wk I.k) de % 2 ^ (64 * vk I.k))).1]
    exact (twos_iter (by omega_using [h3]) (by omega_using [hNlt]) xlt).1
  rw [Prod.ext_iff, Prod.ext_iff] at hval
  obtain ⟨vU, vXn, vX3⟩ := hval
  -- The GCD.
  refine WP.seq (WP.mono (gcd_ok hT.g L vU uodd vXn hT.zX hT.one) fun s₄ ⟨g₄, vg₄, zg₄, F₄⟩ => ?_)
  obtain ⟨kN₄, kO₄, kX₄⟩ := gcd_keep hb32 F₄
  -- `a`.
  refine WP.mono (aProd_ok g₄ L) fun s₅ ⟨g₅, vA₅, k₅⟩ => ?_
  have hA : wv s₅.mem I.B (slot (Wk I.k) wA) (Wk I.k) = aOf (64 * vk I.k) (64 * Wk I.k) N de := by
    rw [vA₅, vg₄, show wv s₄.mem I.B (slot (Wk I.k) wX) (Wk I.k) = st.2.2 by rw [hW, kX₄, ← hW]; exact vX3,
      aOf, hstart]
  have n₅ : wv s₅.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by
    rw [k₅ 0 _ (by decide) (by omega_using []), kN₄]; exact hT.n
  have o₅ : wv s₅.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1 := by
    rw [k₅ nOne _ (by decide) (by omega_using []), kO₄]; exact hT.one
  exact ⟨g₅, hA, n₅, o₅⟩

/-- The pieces from `d e - 1` to the square root. -/
theorem mid_ok [GcdLaw gcdB] {I : RpIn} {m₀ : Mem} {s : State} (h : G I m₀ (vk I.k) true s) (L : RpLens I) {N de : Nat}
    (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N) (hodd : N % 2 = 1) (h3 : 3 ≤ N)
    (hNlt : N < 2 ^ (64 * vk I.k)) (hlo : 256 ^ (I.k - 1) ≤ N) (hNk : N < 2 ^ (8 * I.k))
    (hn8 : 8 * (N + 2) ≤ 2 ^ (64 * vk I.k))
    (hM : wv s.mem I.B (slot (vk I.k) 10) (2 * (vk I.k + 2)) = de) (hde : de < 2 ^ (64 * vk I.k)) :
    WP isa (seqs [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt]) s fun t => ∃ q rem,
      (0 < m1Of (64 * vk I.k) (64 * Wk I.k) N de →
        q = dOf (64 * vk I.k) (64 * Wk I.k) N de / m1Of (64 * vk I.k) (64 * Wk I.k) N de ∧
        rem = dOf (64 * vk I.k) (64 * Wk I.k) N de % m1Of (64 * vk I.k) (64 * Wk I.k) N de) ∧
      G I m₀ (vk I.k) (okDE (64 * Wk I.k) de && ltOf (64 * vk I.k) (64 * Wk I.k) N de &&
        (stage2 (64 * vk I.k) (64 * Wk I.k) N q rem).1) t ∧
      wv t.mem I.B (slot (vk I.k) nB) (vk I.k) = bOf (64 * vk I.k) q ∧
      ∃ Y, wv t.mem I.B (slot (vk I.k) nY) (vk I.k) = Y ∧
        ((okDE (64 * Wk I.k) de && ltOf (64 * vk I.k) (64 * Wk I.k) N de &&
          (stage2 (64 * vk I.k) (64 * Wk I.k) N q rem).1) = true →
          Y = (rootOf (64 * vk I.k) (64 * Wk I.k) N (bOf (64 * vk I.k) q)).2.2) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega_using []
  have hb32 := hb32_of h L
  rw [show seqs [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt] =
    seqs ([deMinus, twos, gcd, aProd] ++ [divA, divB, square, minus4n, sqrt]) from rfl]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (mid4_ok h L hN hodd h3 hNlt hM hde) fun s₅ ⟨g₅, hA, n₅, o₅⟩ => ?_)
  simp only [seqs]
  -- `m` and `r`.
  refine WP.seq (WP.mono (divA_ok g₅ L hA n₅ hlo hNk) fun s₆ ⟨g₆, vM₆, vR₆, vN₆, k₆⟩ => ?_)
  have n₆ : wv s₆.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by rw [k₆ 0 _ (by decide) (by omega_using [])]; exact n₅
  have o₆ : wv s₆.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1 := by
    rw [k₆ nOne _ (by decide) (by omega_using [])]; exact o₅
  refine WP.seq (WP.mono (divB_ok g₆ L vM₆ vR₆ n₆ o₆) fun s₇ ⟨q, rem, g₇, vq₇, hdiv, k₇⟩ => ?_)
  -- `b`, `b²`, `b² - 4 n`.
  have o₇ : wv s₇.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1 := by
    rw [k₇ nOne _ (.inl (by decide)) (by omega_using [])]; exact o₆
  refine WP.seq (WP.mono (square_ok g₇ L vq₇ o₇) fun s₈ ⟨g₈, vb₈, vS₈, k₈⟩ => ?_)
  have N₈ : wv s₈.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N := by
    have e := wide_split s₈.mem I.B (vk I.k) wN
    have e6 := wide_split s₆.mem I.B (vk I.k) wN
    rw [← hW] at e e6
    rw [e, k₈ (2 * wN) (vk I.k + 2) (.inr (.inl rfl)) (Nat.le_refl _), k₈ (2 * wN + 1) (vk I.k) (.inr (.inr rfl)) (by omega_using []),
      k₇ (2 * wN) (vk I.k + 2) (.inr ⟨by decide, by decide⟩) (Nat.le_refl _),
      k₇ (2 * wN + 1) (vk I.k) (.inr ⟨by decide, by decide⟩) (by omega_using []), ← e6, vN₆]
  refine WP.seq (WP.mono (minus4n_ok g₈ L N₈ vS₈) fun s₉ ⟨g₉, vX₉, k₉⟩ => ?_)
  refine WP.mono (sqrt_ok g₉ L vX₉) fun t ⟨gt, vyt, kt⟩ => ⟨q, rem, ?_, ?_, ?_, _, vyt, fun hm => ?_⟩
  · intro hpos; exact hdiv hpos
  · rw [mask_eq (k := 64 * Wk I.k / 2) rfl, mask_root h3 hn8 (by omega_using [hW]) (by omega_using []) hNlt hdiv]
    exact gt
  · rw [kt nB _ (.inr (.inr ⟨by decide, by decide⟩)) (by omega_using []), k₉ nB _ (by decide) (by omega_using []), vb₈]; rfl
  · exact y_root h3 hn8 (by omega_using [hW]) (by omega_using []) hNlt hdiv hm

/-- The factors written, or 0. -/
def fstOr' : Option (Nat × Nat) → Nat
  | some v => v.1
  | none => 0

def sndOr' : Option (Nat × Nat) → Nat
  | some v => v.2
  | none => 0

theorem main_eq : main = seqs ((([.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)] : List (Prog isa)) ++
    (loadA Public.aN Public.sN Public.sK ++ (loadA VG.Impl.Rsa.AArch64.Recover.aE Public.sE Public.sElen ++
      (loadA VG.Impl.Rsa.AArch64.Recover.aD VG.Impl.Rsa.AArch64.Recover.sD VG.Impl.Rsa.AArch64.Recover.sDl ++
        VG.Impl.Rsa.AArch64.Recover.prod)))) ++
    ([deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt] ++ (factorsA ++
      (storeA nP VG.Impl.Rsa.AArch64.Recover.sP Public.sK Public.sMask ++
        (storeA nQ VG.Impl.Rsa.AArch64.Recover.sQ Public.sK Public.sMask ++ ([.block retMask] : List (Prog isa))))))) := by
  simp only [main, factors, factorsA, List.append_assoc, List.cons_append, List.nil_append]

theorem pow_v (k : Nat) : 2 ^ (8 * k + 64) ≤ 2 ^ (64 * vk k) :=
  Nat.pow_le_pow_right (by decide) (by simp only [vk]; omega_using [])

/-- `main`, from a valid modulus: Appendix C.2's factors written, or zeros. -/
theorem rdMain_ok [GcdLaw gcdB] {I : RpIn} {s : State} (h : DPre I s) (hv : Spec.Rsa.modulusValid (numN I) I.k = true) :
    WP isa main s fun t => ∃ res : Option (Nat × Nat),
      Spec.Rsa.recoverDet (numN I) (numE I) (numD I) = res ∧
      (List.range I.k).map (fun i => t.mem (I.pP + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (fstOr' res) I.k ∧
      (List.range I.k).map (fun i => t.mem (I.pQ + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (sndOr' res) I.k ∧
      t.gpr .x0 = BitVec.ofNat 64 res.isSome.toNat ∧
      (∀ x, I.Z ≤ ofs I.B x → (∀ i < I.k, x ≠ I.pP + BitVec.ofNat 64 i) →
        (∀ i < I.k, x ≠ I.pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) := by
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  obtain ⟨hodd, hlo⟩ := rvalid_lo hv
  have hNlt : numN I < 2 ^ (8 * I.k) := by have := os2ip_lt I.nb; rw [L.nbl, pow256_eq] at this; exact this
  have hpv := pow_v I.k
  have hpk : 2 ^ (8 * I.k + 64) = 2 ^ (8 * I.k) * 2 ^ 64 := Nat.pow_add _ _ _
  have h3 : 3 ≤ numN I := by
    have : 2 ^ 8 ≤ 256 ^ (I.k - 1) := by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_using [k1])
    omega_using [hlo, this]
  have hD : numD I < 2 ^ (8 * I.k) := by
    have := os2ip_lt I.db; rw [L.dbl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.dl2; omega_using [this]))
  have hE : numE I < 2 ^ 64 := by
    have := os2ip_lt I.eb; rw [L.ebl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := h.el8; omega_using [this]))
  have hde : numD I * numE I < 2 ^ (64 * vk I.k) :=
    Nat.lt_of_lt_of_le (by rw [hpk]; exact Nat.mul_lt_mul'' hD hE) hpv
  have hn8 : 8 * (numN I + 2) ≤ 2 ^ (64 * vk I.k) := by
    have : 8 * (numN I + 2) ≤ 2 ^ (8 * I.k + 64) := by rw [hpk]; have := Nat.one_le_two_pow (n := 8 * I.k); omega_using [hNlt]
    omega_using [hpv, this]
  rw [main_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (prefix_ok h) fun s₁ ⟨g₁, n₁, M₁⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (mid_ok g₁ L n₁ hodd h3 (by omega_using [hn8]) hlo hNlt hn8 M₁ hde)
    fun s₂ ⟨q, rem, hdiv, g₂, b₂, Y, y₂, hY⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp [storeA]) (WP.mono (factorsA_ok g₂ L b₂ y₂) fun s₃ ⟨g₃, p₃, q₃⟩ => ?_)
  have hkv : I.k ≤ 8 * vk I.k := by simp only [vk]; omega_using []
  refine WP.mono (stores_ok g₃.ws g₃.args g₃.msk (by omega_using [k1]) hkv
    ⟨fun i hi => by rw [g₃.wr, ← h.wr]; exact h.oP.wr i hi, h.oP.sep⟩
    ⟨fun i hi => by rw [g₃.wr, ← h.wr]; exact h.oQ.wr i hi, h.oQ.sep⟩ h.a) fun t ⟨bP, bQ, hax, hfr, _⟩ => ?_
  have hres := model_correct (nb := 64 * vk I.k) (wb := 64 * Wk I.k) (e := numE I) (d := numD I) hodd h3
    (by have : 8 * (numN I + 2) ≤ 2 ^ (8 * I.k + 64) := by rw [hpk]; have := Nat.one_le_two_pow (n := 8 * I.k); omega_using [hNlt]
        omega_using [hn8]) hde (by omega_using [hW]) (by omega_using []) hdiv
  suffices H : (List.range I.k).map (fun i => t.mem (I.pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (fstOr' (Spec.Rsa.recoverDet (numN I) (numE I) (numD I))) I.k ∧
      (List.range I.k).map (fun i => t.mem (I.pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (sndOr' (Spec.Rsa.recoverDet (numN I) (numE I) (numD I))) I.k ∧
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Rsa.recoverDet (numN I) (numE I) (numD I)).isSome.toNat from
    ⟨_, rfl, H.1, H.2.1, H.2.2, fun x hx n1 n2 => by rw [hfr x n1 n2]; exact g₃.inScr x hx⟩
  have hP : (okDE (64 * Wk I.k) (numD I * numE I) && ltOf (64 * vk I.k) (64 * Wk I.k) (numN I) (numD I * numE I) &&
      (stage2 (64 * vk I.k) (64 * Wk I.k) (numN I) q rem).1) = true →
      wv s₃.mem I.B (slot (vk I.k) nP) (vk I.k) = (stage2 (64 * vk I.k) (64 * Wk I.k) (numN I) q rem).2.1 := fun hm => by
    rw [p₃, hY hm]; rfl
  have hQ : (okDE (64 * Wk I.k) (numD I * numE I) && ltOf (64 * vk I.k) (64 * Wk I.k) (numN I) (numD I * numE I) &&
      (stage2 (64 * vk I.k) (64 * Wk I.k) (numN I) q rem).1) = true →
      wv s₃.mem I.B (slot (vk I.k) nQ) (vk I.k) = (stage2 (64 * vk I.k) (64 * Wk I.k) (numN I) q rem).2.2 := fun hm => by
    rw [q₃, hY hm]; rfl
  -- When found, the factors are below `n`.
  have hbound : ∀ P Q, Spec.Rsa.recoverDet (numN I) (numE I) (numD I) = some (P, Q) →
      P < 2 ^ (64 * ((I.k + 7) / 8)) ∧ Q < 2 ^ (64 * ((I.k + 7) / 8)) := by
    intro P Q hs
    have hm := recoverDet_mul hs
    have hk8 : 2 ^ (8 * I.k) ≤ 2 ^ (64 * ((I.k + 7) / 8)) := Nat.pow_le_pow_right (by decide) (by omega_using [])
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · rw [h0] at hm; omega_using [hodd, hm]
    rcases Nat.eq_zero_or_pos Q with h1 | h1
    · rw [h1] at hm; omega_using [hodd, hm]
    exact ⟨by have := Nat.le_mul_of_pos_right P h1; omega_using [hNlt, hm, hk8, this], by have := Nat.le_mul_of_pos_left Q h0; omega_using [hNlt, hm, hk8, this]⟩
  have hk8v : (I.k + 7) / 8 ≤ vk I.k := by simp only [vk]; omega_using []
  rw [← hres]
  unfold result
  split
  · rename_i hc
    have hs : Spec.Rsa.recoverDet (numN I) (numE I) (numD I) =
        some ((stage2 (64 * vk I.k) (64 * Wk I.k) (numN I) q rem).2.1,
          (stage2 (64 * vk I.k) (64 * Wk I.k) (numN I) q rem).2.2) := by
      rw [← hres]; simp only [result, hc, ↓reduceIte]
    obtain ⟨bp, bq⟩ := hbound _ _ hs
    refine ⟨?_, ?_, ?_⟩
    · rw [bP, hc]; simp only [↓reduceIte, fstOr']; rw [wv_low_of_lt hk8v (by rw [hP hc]; exact bp), hP hc]
    · rw [bQ, hc]; simp only [↓reduceIte, sndOr']; rw [wv_low_of_lt hk8v (by rw [hQ hc]; exact bq), hQ hc]
    · rw [hax, hc]; rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    refine ⟨?_, ?_, ?_⟩
    · rw [bP, hc]; rfl
    · rw [bQ, hc]; rfl
    · rw [hax, hc]; rfl

end VG.Proof.Rsa.AArch64.Rd

end

end

/-! ### `Rsa.AArch64.RdEntry`, which only this module used -/

section

/-!
# `vg_rsa_recover_primes_det` on AArch64: the entry and the failure path

`rpPre`: the precondition on the registers and the stack (`rdA`'s but for
`e_len ≤ 8`), and `RpCtx`, what it gives (`rpCtx_of`). The entry and the
check of the modulus (`rpHead_ok'`) leave `RpPre`; zeros and 0 if the key
is refused (`rpFail_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `fail`: zeros to `p` and `q`, and 0 returned. -/
theorem rpFail_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {k el dl : Nat} {pP pQ pN pE pD : Addr} (ha : RpArgs s.mem B k el dl pP pQ pN pE pD) (hk1 : 1 ≤ k)
    (hk2 : k < 2 ^ 31) (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa fail s fun t =>
      (∀ i < k, t.mem (pP + BitVec.ofNat 64 i) = 0) ∧ (∀ i < k, t.mem (pQ + BitVec.ofNat 64 i) = 0) ∧
      t.gpr .x0 = 0 ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hn := hs.nowrap
  have fw : ∀ {m m' : Mem} {op : Addr} {len : Nat}, (∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j)) →
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hsep hx i hi => (frm_scr hsep hx).word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega_using [hi])
  unfold fail
  simp only [seqs]
  refine WP.seq (WP.mono (zeroOut_ok hs h0 hZ (by decide) (by decide) ha.p ha.k hk1 hk2 oP)
    fun s₁ ⟨z₁, x₁, k₁⟩ => ?_)
  have w₁ := fw oP.sep x₁
  have hs₁ := hs.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  refine WP.seq (WP.mono (zeroOut_ok hs₁ h0₁ hZ (by decide) (by decide) (by rw [w₁ _ (by decide)]; exact ha.q)
    (by rw [w₁ _ (by decide)]; exact ha.k) hk1 hk2 ⟨fun i hi => by rw [k₁.wr]; exact oQ.wr i hi, oQ.sep⟩)
    fun s₂ ⟨z₂, x₂, k₂⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ?_
  have kk := (k₁.trans k₂).trans k₃
  rw [hm]
  refine ⟨fun i hi => ?_, z₂, hx, fun x n1 n2 => by rw [x₂ x n2, x₁ x n1], kk.mono (by decide)⟩
  rw [x₂ _ (fun j hj => a i hi j hj)]
  exact z₁ i hi

end VG.Proof.Rsa.AArch64

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

/-- The inputs as numbers. -/
abbrev RpIn.N (I : RpIn) : Nat := Spec.Rsa.os2ip I.nb
/-- What `main` needs on entry. -/
structure RpPre (I : RpIn) (s : State) : Prop where
  scr : Scr s I.B I.Z
  x0 : s.gpr .x0 = I.B
  args : RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD
  n : Src s I.B I.Z I.pN I.nb
  e : Src s I.B I.Z I.pE I.eb
  d : Src s I.B I.Z I.pD I.db
  L : RpLens I
  oP : OutOk s I.B I.Z I.pP I.k
  oQ : OutOk s I.B I.Z I.pQ I.k
  a : Apart I.pP I.k I.pQ I.k
  wr : s.wr = I.W

end VG.Proof.Rsa.AArch64

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-! ## The contract on the registers and the stack -/

/-- The precondition, on the registers and the stack, of
`vg_rsa_recover_primes_det(p = x0, p_len = x1, q = x2, q_len = x3, n = x4,
n_len = x5, e = x6, e_len = x7, d = [sp], d_len = [sp + 8],
scratch = [sp + 16], scratch_len = [sp + 24])` but for `e_len ≤ 8`. -/
def rpPre : State → Prop := fun s =>
  let p : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let q : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let n : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let e : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let d : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 32⟩
  s.sp.toNat + 32 ≤ 2 ^ 64 ∧
    s.rd = [n, e, d, args] ∧ s.wr = [p, q, scr] ∧
    p.Disjoint q ∧ p.Disjoint n ∧ p.Disjoint e ∧ p.Disjoint d ∧ p.Disjoint scr ∧ p.Disjoint args ∧
    q.Disjoint n ∧ q.Disjoint e ∧ q.Disjoint d ∧ q.Disjoint scr ∧ q.Disjoint args ∧
    n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
    Spec.Rsa.lenValid (s.gpr .x5).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x5).toNat ∧
    (s.gpr .x3).toNat = (s.gpr .x5).toNat ∧ 1 ≤ (s.gpr .x7).toNat ∧
    (s.gpr .x7).toNat ≤ (s.gpr .x5).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
    (stackArg s 1).toNat ≤ (s.gpr .x5).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x5).toNat ≤ (stackArg s 3).toNat

/-! ## The entry -/

theorem rpEntry_eq : entry = ([.ldrSp .x8 16, .str .x .x0 .x8 (8 * sP), .str .x .x2 .x8 (8 * sQ),
    .str .x .x4 .x8 (8 * Public.sN), .str .x .x5 .x8 (8 * Public.sK), .str .x .x6 .x8 (8 * Public.sE),
    .str .x .x7 .x8 (8 * Public.sElen)] : List Instr) ++
    (hdrPairs [(0, sD), (1, sDl)] ++ ([mov .x0 .x8, mov .x2 .x4, mov .x3 .x5] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def rpEntryMemA (m : Mem) (B : Addr) (vp vq vn vk ve vel : BitVec 64) : Mem :=
  (((((m.writeW (off B (8 * sP)) vp).writeW (off B (8 * sQ)) vq).writeW (off B (8 * Public.sN)) vn).writeW
    (off B (8 * Public.sK)) vk).writeW (off B (8 * Public.sE)) ve).writeW (off B (8 * Public.sElen)) vel

/-- The header after the entry's stores. -/
def rpEntryMem (m : Mem) (B : Addr) (vp vq vn vk ve vel vd vdl : BitVec 64) : Mem :=
  ((rpEntryMemA m B vp vq vn vk ve vel).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDl)) vdl

theorem rpEntryMemA_outside (m : Mem) (B : Addr) (vp vq vn vk ve vel : BitVec 64) :
    Outside B 0 (8 * 32) m (rpEntryMemA m B vp vq vn vk ve vel) := by
  unfold rpEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem rpEntryMem_facts (m : Mem) (B : Addr) (vp vq vn vk ve vel vd vdl : BitVec 64) :
    let m' := rpEntryMem m B vp vq vn vk ve vel vd vdl
    word m' B (8 * sP) = vp ∧ word m' B (8 * sQ) = vq ∧ word m' B (8 * Public.sN) = vn ∧
    word m' B (8 * Public.sK) = vk ∧ word m' B (8 * Public.sE) = ve ∧ word m' B (8 * Public.sElen) = vel ∧
    word m' B (8 * sD) = vd ∧ word m' B (8 * sDl) = vdl ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' rpEntryMem rpEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, the working space's base
(stack argument 2) in `x0`, and `n` and `n_len` in `x2` and `x3`. -/
theorem rpEntry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 4, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧ t.gpr .x2 = s.gpr .x4 ∧ t.gpr .x3 = s.gpr .x5 ∧
      word t.mem B (8 * sP) = s.gpr .x0 ∧ word t.mem B (8 * sQ) = s.gpr .x2 ∧
      word t.mem B (8 * Public.sN) = s.gpr .x4 ∧ word t.mem B (8 * Public.sK) = s.gpr .x5 ∧
      word t.mem B (8 * Public.sE) = s.gpr .x6 ∧ word t.mem B (8 * Public.sElen) = s.gpr .x7 ∧
      word t.mem B (8 * sD) = stackArg s 0 ∧ word t.mem B (8 * sDl) = stackArg s 1 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x2, .x3, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = B := hB
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := ha 2 (by decide)
  have ho : 16 % 8 = 0 ∧ 16 < 32768 := ⟨rfl, by decide⟩
  rw [rpEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = rpEntryMemA s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ?_
      (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha2, hB', hdr_enc (show sP < 32 by decide), hdr_enc (show sQ < 32 by decide),
      hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (show Public.sE < 32 by decide), hdr_enc (show Public.sElen < 32 by decide),
      hw sP (by decide), hw sQ (by decide), hw Public.sN (by decide), hw Public.sK (by decide),
      hw Public.sE (by decide), hw Public.sElen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact rpEntryMemA_outside _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0, .x2, .x3] (Q := fun t => t.gpr .x0 = B ∧ t.gpr .x2 = s.gpr .x4 ∧
      t.gpr .x3 = s.gpr .x5 ∧ t.mem = t₂.mem)
    (by brun [h8₂, k12.gpr .x4 (by decide), k12.gpr .x5 (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0, h2, h3, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = rpEntryMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)
      (s.gpr .x7) (stackArg s 0) (stackArg s 1) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨hP, hQ, hN, hK, hE, hEl, hD, hDl, ho'⟩ :=
    rpEntryMem_facts s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
      (stackArg s 0) (stackArg s 1)
  exact ⟨h0, h2, h3, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho', (k12.trans k₃).mono (by decide)⟩

/-! ## The precondition, as the code uses it -/

/-- The inputs of `main`, from the entry state. -/
def rpIn (s : State) : RpIn where
  B := stackArg s 2
  Z := (stackArg s 3).toNat * 8
  k := (s.gpr .x5).toNat
  el := (s.gpr .x7).toNat
  dl := (stackArg s 1).toNat
  pP := s.gpr .x0
  pQ := s.gpr .x2
  pN := s.gpr .x4
  pE := s.gpr .x6
  pD := stackArg s 0
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  eb := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  W := s.wr

/-- What `Recover.code` uses of its contract's precondition. -/
structure RpCtx (s : State) : Prop where
  L : RpLens (rpIn s)
  x1 : (s.gpr .x1).toNat = (s.gpr .x5).toNat
  x3 : (s.gpr .x3).toNat = (s.gpr .x5).toNat
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 4, ∀ m', Outside (stackArg s 2) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x4) (rpIn s).nb
  e : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x6) (rpIn s).eb
  d : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0) (rpIn s).db
  oP : OutOk s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x0) (s.gpr .x5).toNat
  oQ : OutOk s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x2) (s.gpr .x5).toNat
  a : Apart (s.gpr .x0) (s.gpr .x5).toNat (s.gpr .x2) (s.gpr .x5).toNat

theorem rpCtx_of {s : State} (h : rpPre s) : RpCtx s := by
  simp only [rpPre] at h
  obtain ⟨hsp, hrd, hwr, dpq, dpn, dpe, dpd, dps, dpa, dqn, dqe, dqd, dqs, dqa, dns, des, dds, dsa,
    wP, wQ, wN, wE, wD, wS, hk, hx1, hx3, hel1, hel2, hdl1, hdl2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hx1] at dpq dpn dpe dpd dps dpa wP
  rw [hx3] at dpq dqn dqe dqd dqs dqa wQ
  refine ⟨⟨hk1, hk2, hel1, hel2, hdl1, hdl2, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, by simp only [rpIn]; omega_arith⟩, hx1, hx3, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 32) (by omega_arith) (by omega_arith))
      rw [← stkAddr_add s j b] at this; omega_arith)),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd]; simp) (by omega_arith) des,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hx1]; simp, contains_byte _ hj (by omega_arith)⟩,
      fun j hj => out_scr dps (contains_byte _ hj (by omega_arith))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hx3]; simp, contains_byte _ hj (by omega_arith)⟩,
      fun j hj => out_scr dqs (contains_byte _ hj (by omega_arith))⟩,
    apart_of dpq (by omega_arith) (by omega_arith)⟩

/-- After `entry`, from `s`. -/
structure RpHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 2) ((stackArg s 3).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 2
  x2 : t.gpr .x2 = s.gpr .x4
  x3 : t.gpr .x3 = BitVec.ofNat 64 (s.gpr .x5).toNat
  args : RpArgs t.mem (rpIn s).B (rpIn s).k (rpIn s).el (rpIn s).dl (rpIn s).pP (rpIn s).pQ (rpIn s).pN
    (rpIn s).pE (rpIn s).pD
  inScr : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x2, .x3, .x8, .x9] s t

/-- `entry`. -/
theorem rpHead_ok' {s : State} (c : RpCtx s) : WP isa (.block entry) s (RpHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .x5).toNat ≤ (stackArg s 3).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .x5).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.mono (rpEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, h2, h3, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho, k⟩ => ?_
  refine ⟨c.hs.congr k.wr, h0, h2, by rw [h3, ofNat_toNat64],
    ⟨hP, hQ, hN,
      show word _ (stackArg s 2) _ = BitVec.ofNat 64 (s.gpr .x5).toNat by rw [hK, ofNat_toNat64], hE,
      show word _ (stackArg s 2) _ = BitVec.ofNat 64 (s.gpr .x7).toNat by rw [hEl, ofNat_toNat64], hD,
      show word _ (stackArg s 2) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hDl, ofNat_toNat64]⟩,
    InScr.of_outside ho (by omega_arith), k⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem rpPre_of {s t₁ t : State} (c : RpCtx s) (h : RpHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t) : RpPre (rpIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.wr, x0 := (k.gpr .x0 (by decide)).trans h.x0, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, e := c.e.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oP := ⟨fun i hi => by rw [kk.wr]; exact c.oP.wr i hi, c.oP.sep⟩,
      oQ := ⟨fun i hi => by rw [kk.wr]; exact c.oQ.wr i hi, c.oQ.sep⟩,
      a := c.a, wr := kk.wr }

end VG.Proof.Rsa.AArch64

end

end


/-!
# `vg_rsa_recover_primes_det` on AArch64: correctness

`RecoverDet.code`, from a state its contract allows, writes `primesKeyDet`
of its inputs (`rdCode_correct`), against `rdA`: the precondition on the
registers and the stack (`rpPre`) with `e` at most 8 bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `vg_rsa_recover_primes_det`'s contract on the registers and the stack. -/
def rdA : Contract isa where
  pre s := rpPre s ∧ (s.gpr .x7).toNat ≤ 8
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .x0, (s.gpr .x5).toNat), (s.gpr .x2, (s.gpr .x5).toNat)]
      ((s'.gpr .x0).setWidth 32)
      ((Spec.Rsa.primesKeyDet (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)).map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x6) (s₁.gpr .x7).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x6) (s₂.gpr .x7).toNat

/-- What `RecoverDet.code` leaves, from a valid modulus. -/
theorem rdWritten_of {m : Mem} {pp pq : Addr} {x0 : BitVec 64} {nb eb db : List Byte}
    {res : Option (Nat × Nat)}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hres : Spec.Rsa.recoverDet (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db) = res)
    (b1 : Spec.Rsa.bytesAt m pp nb.length = Spec.Rsa.i2osp (fstOr' res) nb.length)
    (b2 : Spec.Rsa.bytesAt m pq nb.length = Spec.Rsa.i2osp (sndOr' res) nb.length)
    (hr : x0 = BitVec.ofNat 64 res.isSome.toNat) :
    Spec.Rsa.writtenAll m [(pp, nb.length), (pq, nb.length)] (x0.setWidth 32)
      ((Spec.Rsa.primesKeyDet nb eb db).map fun v => [v.1, v.2]) := by
  simp only [Spec.Rsa.primesKeyDet, hv, ite_true]
  rw [hr, setWidth_flag, hres]
  cases res with
  | none =>
    simp only [fstOr', sndOr', Option.isSome_none, Bool.false_eq_true, ite_false, Option.map_none, Spec.Rsa.writtenAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, i2osp_zero'], by rw [b2, i2osp_zero']⟩
  | some v =>
    obtain ⟨p, q⟩ := v
    simp only [fstOr', sndOr', Option.isSome_some, ite_true, Option.map_some, Spec.Rsa.writtenAll, List.map_cons,
      List.map_nil] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, b2]⟩

/-- `vg_rsa_recover_primes_det`. -/
theorem rdCode_correct [GcdLaw gcdB] (s : State) (h : rdA.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ rdA.post s s' := by
  have c := rpCtx_of h.1
  have hel8 := h.2
  clear h
  have hk1 : 64 ≤ (s.gpr .x5).toNat := c.L.k1
  have hk2 : (s.gpr .x5).toNat ≤ 1024 := c.L.k2
  suffices hwp : WP isa code s fun s' => abiPreserved s s' ∧ rdA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold RecoverDet.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rpHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (rpIn s).nb.length = (s.gpr .x5).toNat := bytesAt_length _ _ _
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h₁.x2 h₁.x3 hk1 hk2 hnl
    (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have hpre := rpPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  refine WP.ite (!Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat)
    (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .x5).toNat ≤ (stackArg s 3).toNat * 8 := c.L.z
    exact WP.mono (rpFail_ok hpre.scr hpre.x0 (show 8 * 32 ≤ (stackArg s 3).toNat * 8 by omega_using [hk1, z]) hpre.args
      (show 1 ≤ (s.gpr .x5).toNat by omega_using [hk1]) (show (s.gpr .x5).toNat < 2 ^ 31 by omega_using [hk2]) hpre.oP hpre.oQ hpre.a)
      fun t ⟨z1, z2, hax, _, kt⟩ => ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : Spec.Rsa.primesKeyDet (rpIn s).nb (rpIn s).eb (rpIn s).db = none := by
          simp only [Spec.Rsa.primesKeyDet]
          rw [hnl, hv]; simp
        simp only [rpIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z1, bytesAt_zero z2⟩⟩
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat = true := by simpa using hb
    have dpre : DPre (rpIn s) t₂ := ⟨hpre.scr, hpre.x0, hpre.args, hpre.n, hpre.e, hpre.d, hpre.L, hel8, hpre.oP,
      hpre.oQ, hpre.a, hpre.wr⟩
    refine WP.mono (WP.keepLanesO (.x0 :: mmRegs) [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]
      (rdMain_ok dpre hv) (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)) fun t ⟨⟨res, hres, b1, b2, hax, _⟩, kt⟩ =>
      ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), ?_⟩
    have := rdWritten_of (m := t.mem) (pp := s.gpr .x0) (pq := s.gpr .x2) (by rw [hnl]; exact hv) hres
      (by rw [hnl]; exact b1) (by rw [hnl]; exact b2) hax
    rw [hnl] at this
    exact this

end VG.Proof.Rsa.AArch64.Rd

end

end

/-! ### `Rsa.AArch64.RdCT3`, which only this module used -/

section

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the GCD

`gcdHead_ok`: the start of `gcd` gives `inverse` its inputs (`XInv`), whose
correctness then gives the rest.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.Recover (zeroMask)

/-- `inverse`'s inputs. -/
def XInv (a : Pub) (s : State) : Prop :=
  word s.mem a.1.B (slot (vk a.1.k) nXn + 8 * vk a.1.k) = 0 ∧
    wv s.mem a.1.B (slot (vk a.1.k) nU) (vk a.1.k) = wv s.mem a.1.B (slot (vk a.1.k) gM) (vk a.1.k) ∧
    wv s.mem a.1.B (slot (vk a.1.k) gX₁) (vk a.1.k) = 1 ∧ wv s.mem a.1.B (slot (vk a.1.k) gX₂) (vk a.1.k) = 0

/-- The start of `gcd`. -/
abbrev gcdHead : List (Prog isa) := [zeroA gM, copyA gM nU] ++ oneA gX₁ ++ [zeroA gX₂]

theorem gcdHead_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I)
    (hz : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0) (i : Nat) :
    WP isa (seqs gcdHead) s fun t => G I m₀ (vk I.k) c t ∧ XInv (dpub I, i) t := by
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega_using []
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
    have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega_arith
  have s2 := slot_lt (w := vk I.k) (show nU < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nXn < 32 by decide)
  have s4 := slot_lt (w := vk I.k) (show gM < 32 by decide)
  have s5 := slot_lt (w := vk I.k) (show gX₁ < 32 by decide)
  have s6 := slot_lt (w := vk I.k) (show gX₂ < 32 by decide)
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [oneA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := gM) (by decide)) fun s₁ ⟨_, o₁, _, _, _, k₁⟩ => ?_)
  have g₁ := h.out (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (copyA_ok g₁.ws (o := gM) (a := nU) (by decide) (by decide) (by decide))
    fun s₂ ⟨v₂, o₂, _, _, k₂⟩ => ?_
  have g₂ := g₁.out (by decide) (by omega_using []) o₂ k₂ (by decide)
  refine WP.mono (oneA_ok g₂ (j := gX₁) (by decide)) fun s₃ ⟨g₃, v₃, o₃, k₃⟩ => ?_
  refine WP.mono (zeroA_ok g₃.ws (j := gX₂) (by decide)) fun s₄ ⟨z₄, o₄, _, _, _, k₄⟩ => ?_
  refine ⟨g₃.out (by decide) (Nat.le_refl _) o₄ k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · show word s₄.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
    rw [o₄.word (wd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s3]),
      o₃.word (wd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s3]),
      o₂.word (wd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s3]),
      o₁.word (wd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s3]), hz]
  · show wv s₄.mem I.B (slot (vk I.k) nU) (vk I.k) = wv s₄.mem I.B (slot (vk I.k) gM) (vk I.k)
    rw [o₄.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s2]),
      o₃.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s2]),
      o₂.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s2]),
      o₄.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s4]),
      o₃.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s4]), v₂,
      o₁.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s2])]
  · show wv s₄.mem I.B (slot (vk I.k) gX₁) (vk I.k) = 1
    rw [o₄.wv (rd_sep (by decide) (by omega_using []) (by omega_using [])) (by omega_using [hb32, s5]),
      wv_low_of_lt (w := vk I.k + 2) (by omega_using []) (by rw [v₃]; exact Nat.one_lt_two_pow (by omega_using [hv1])), v₃]
  · show wv s₄.mem I.B (slot (vk I.k) gX₂) (vk I.k) = 0
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega_using []) (by rw [z₄]; exact Nat.two_pow_pos _), z₄]

theorem gcdHead_ct : CTW (GC vk fun a s => zX a.1 s) (GC vk XInv) (seqs gcdHead) := by
  refine CTW.wp (Φ := GC vk fun a s => zX a.1 s) (Ψ := GC vk XT) ?_ (fun _ _ h => h)
    fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
      subst e
      exact WP.mono (gcdHead_ok g L.1 x i) fun t ⟨g', xi⟩ => ⟨I, m₀, c, rfl, g', L, xi⟩
  simp only [gcdHead, oneA, List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide))

/-- The gcd's middle: the batches by words, or the inverse by bits where `v ≥ 2^21`. -/
abbrev gcdMid : Prog isa := .seq (.block (ws ++ [.lsr .x .x3 .x12 21]))
  (.ite (.zero .x .x3) (gcdB nU nXn gM) (inverseBits nXn nU gX₁ gX₂ gM gT))

theorem gcdMid_w [GcdLaw gcdB] : CTW (GC vk XInv) (GC vk XT) gcdMid :=
  wsop rfl (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
    subst e
    have hw := g.ws
    obtain ⟨zx, vm, x1, x2⟩ := x
    exact WP.mono (GcdLaw.gcdW_ok hw (iU := nXn) (iV := nU) (iX₁ := gX₁) (iX₂ := gX₂) (iM := gM) (iT := gT)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) zx vm x1 x2) fun t ⟨_, f, k, _⟩ =>
      ⟨I, m₀, c, rfl, g.step f (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact slot_ge _ _)
      (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hw.sl (by decide)) k (by decide), L, trivial⟩

theorem gcd_ct [GcdLaw gcdB] : CTW (GC vk fun a s => zX a.1 s) (GC vk XT) gcd := by
  have e : gcd = seqs (gcdHead ++ ([gcdMid] ++
      (eqA gM nOne ++ [.block zeroMask, selA nU nOne, zeroA gT, copyA gT nU]))) := by
    simp only [gcd, gcdHead, gcdMid, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine CTW.app (by simp) (by simp) gcdHead_ct (CTW.cons (by simp) gcdMid_w ?_)
  refine CTW.app (a := eqA gM nOne) (by simp [eqA]) (by simp) (eqA_w (b₁ := gM) (b₂ := nOne) (Y := XT) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (regs_w (Y := fun _ s => MR .x15 s) (by taint_decide) (rs := [.x3, .x4, .x7, .x15])
    (by decide) fun a s h => WP.mono (zeroMask_ok s) fun t ⟨⟨h15, _, hm⟩, k⟩ => ⟨⟨hm, _, h15⟩, k⟩) ?_
  refine CTW.cons (by simp) (selA_w (Y := XT) (by decide) (by decide) (by decide) (fun _ _ h => h.x)
    (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial) (by taint_decide))

end VG.Proof.Rsa.AArch64.Rd

end

end

/-! ### `Rsa.AArch64.RdCT5`, which only this module used -/

section

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the outputs

The factors and the stores, between `GS` (the working space, the arguments,
the outputs and the mask, which the stores keep).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The factors and the stores -/

theorem factors_ct : CTW (GC vk XT) (GC vk XT) (seqs factorsA) := by
  refine CTW.cons (by simp) (regs_w (Y := fun _ s => MR .x15 s) (by taint_decide) (rs := [.x7, .x15]) (by decide)
    fun a s h => WP.mono (ones_ok s) fun t ⟨⟨h15, _, hm⟩, k⟩ => ⟨⟨hm, _, h15⟩, k⟩) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := fun _ s => MR .x15 s) (by decide)
    (fun _ _ _ h _ k _ => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (addA_w (Y := fun _ s => MR .x15 s) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun _ _ h => h.x) (fun _ _ _ h _ k => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (halfA_w (Y := fun _ s => MR .x15 s) (by decide) (by decide)
    (fun _ _ _ h _ k => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (halfA_w (Y := XT) (by decide) (by decide) (by intros; trivial) (by taint_decide))

/-- Between the stores. -/
def GS (a : Pub) (s : State) : Prop :=
  ∃ (I : RpIn) (c : Bool), dpub I = a.1 ∧ Ws s I.B I.Z (vk I.k) ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD ∧ s.wr = I.W ∧ RpLens I ∧ DOuts I ∧
    word s.mem I.B (8 * Public.sMask) = mask c

theorem GS.ws {a : Pub} {s : State} (h : GS a s) : Ws s a.1.B a.1.Z (vk a.1.k) := by
  obtain ⟨I, c, e, h, -⟩ := h
  rw [← e]; exact h

theorem GC.gs {X : Pub → State → Prop} {a : Pub} {s : State} (h : GC vk X a s) : GS a s := by
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  exact ⟨I, c, e, g.ws, g.args, g.wr, L.1, L.2, g.msk⟩

theorem pins_GS : Pins GS [.x0] :=
  pins_ws (fun a => a.1.B) (fun a => a.1.Z) (fun a => vk a.1.k) fun _ _ h => h.ws

theorem storeA_w {j sPtr : Nat} (hj : j < 16) (hP : sPtr < 32) (ptr : DP → Addr) (ptrI : RpIn → Addr)
    (hpI : ∀ I, ptr (dpub I) = ptrI I)
    (hA : ∀ (I : RpIn) (m : Mem), RpArgs m I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD → word m I.B (8 * sPtr) = ptrI I)
    (hO : ∀ I : RpIn, DOuts I → (∀ i < I.k, InRegions I.W (ptrI I + BitVec.ofNat 64 i) 1) ∧
      (∀ i < I.k, I.Z ≤ ofs I.B (ptrI I + BitVec.ofNat 64 i)))
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 Public.sK,
      .add .x .x1 .x1 .x9, ldh .x15 Public.sMask])) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x9]) storeBE hc₂).isSome = true) :
    CTW GS GS (seqs (storeA j sPtr Public.sK Public.sMask)) := by
  refine ⟨(pin_ct [.x0] [.x0, .x8, .x1, .x9] (Ψ := GS)
    (fun a => soVal a.1.B (off a.1.B (slot (vk a.1.k) j)) (ptr a.1) a.1.k) pins_GS ht₁ ?_ ht₂ ?_).mono
      (fun _ _ h => h) fun _ _ _ => trivial, ?_⟩
  · rintro ⟨P, i⟩ s ⟨I, c, rfl, hw, ha, -⟩
    exact storeBlk_ok hw hP (by decide) ((hA I s.mem ha).trans (hpI I).symm) ha.k
  all_goals
    rintro ⟨P, i⟩ s ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩
    obtain ⟨hwr, hsep⟩ := hO I O
    have hn := hw.scr.nowrap
    have h256 := hw.h256
    refine WP.mono (storeA_ws hw hj hP (by decide) (hA I s.mem ha) ha.k hm (by have := L.k1; omega_using [this])
      (by have := L.k2; simp only [vk]; omega_using []) (fun i hi => by rw [hW]; exact hwr i hi) hsep)
      fun t ⟨_, _, ht, hf, k⟩ => ?_
    have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
      fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega_using [hi])
    exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold rArg at hi; omega_using [hi]), k.wr.trans hW, L, O,
      (fw _ (by decide)).trans hm⟩

theorem stores_ct : RelCT isa (Two (GC vk XT)) (seqs (storeA nP VG.Impl.Rsa.AArch64.Recover.sP Public.sK Public.sMask ++
    (storeA nQ VG.Impl.Rsa.AArch64.Recover.sQ Public.sK Public.sMask ++ ([.block retMask] : List (Prog isa)))))
    fun _ _ => True := by
  have h₁ := storeA_w (j := nP) (by decide) (by decide) DP.pP RpIn.pP (fun _ => rfl) (fun _ _ ha => ha.p)
    (fun I O => ⟨O.p, O.sp⟩) (by taint_decide) (by taint_decide)
  have h₂ := storeA_w (j := nQ) (by decide) (by decide) DP.pQ RpIn.pQ (fun _ => rfl) (fun _ _ ha => ha.q)
    (fun I O => ⟨O.q, O.sq⟩) (by taint_decide) (by taint_decide)
  have h₃ : CTW GS (fun _ _ => True) (seqs [.block retMask]) :=
    ⟨two_taint [.x0] pins_GS (by taint_decide), fun _ s ⟨_, _, _, hw, _, _, _, _, hm⟩ =>
      WP.mono (cvExit_ok hw hm) fun _ _ => trivial⟩
  exact ((h₁.mono (fun _ _ h => GC.gs h) fun _ _ h => h).app (by simp [storeA]) (by simp [storeA])
    (h₂.app (by simp [storeA]) (by simp) h₃)).1.mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64.Rd

end

end

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time

The prefix (`prefix_ct`: the head, the loads and `M = d e`), `main`
(`rdMain_ct`), the entry and the modulus' check (`rdCode_ct`), and the
contract's `ConstantTime` (`rdCode_constantTime`): the function leaks only
`n`, `e`, the pointers and the lengths.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Rsa.AArch64.Recover (aE aD aM sD sDl entry fail prod)

/-! ## The prefix -/

/-- On entry to `main`. -/
def GM (a : Pub) (s : State) : Prop :=
  ∃ I : RpIn, dpub I = a.1 ∧ DPre I s ∧ Spec.Rsa.modulusValid (numN I) I.k = true

theorem pins_GM : Pins GM [.x0] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg DP.B e₁).trans (congrArg DP.B e₂).symm

theorem head_w : CTW GM (GC vk XT) (.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)) :=
  ⟨two_taint [.x0] pins_GM (by taint_decide), fun _ s ⟨I, e, h, _⟩ =>
    WP.mono (head_ok h) fun _ ⟨g, _⟩ => ⟨I, s.mem, true, e, g, ⟨h.L, ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi,
      fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi, h.oP.sep, h.oQ.sep, h.a⟩⟩, trivial⟩⟩

/-- Leaking the same, then code the taint analysis checks from the pinned `rs`. -/
theorem pin_seq0 {Φ : Pub → State → Prop} {c₁ c₂ : Prog isa} (rs : List Reg) (f : Pub → Reg → BitVec 64)
    (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True) (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs) c₂ hc₂).isSome = true) :
    RelCT isa (Two Φ) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (two_post h₁ hp) (two_taint rs (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) ht₂)

/-- A `CTW` and then code leaking the same. -/
theorem ctr_app {Φ Ψ : Pub → State → Prop} {Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ [])
    (hb : b ≠ []) (hA : CTW Φ Ψ (seqs a)) (hB : RelCT isa (Two Ψ) (seqs b) Q) : RelCT isa (Two Φ) (seqs (a ++ b)) Q :=
  RelCT.seqs_append ha hb (RelCT.seq hA.ct hB)

theorem ctr_cons {Φ Ψ : Pub → State → Prop} {Q : State → State → Prop} {e : Prog isa} {l : List (Prog isa)}
    (hl : l ≠ []) (he : CTW Φ Ψ e) (hr : RelCT isa (Two Ψ) (seqs l) Q) : RelCT isa (Two Φ) (seqs (e :: l)) Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact RelCT.seq he.ct hr

theorem loadA_w {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : DP → Addr)
    (len : DP → Nat) (bs : RpIn → List Byte)
    (hA : ∀ (I : RpIn) (m₀ : Mem) (c : Bool) (s : State), G I m₀ (vk I.k) c s → RpLens I →
      word s.mem I.B (8 * sPtr) = ptr (dpub I) ∧ word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len (dpub I)) ∧
      Src s I.B I.Z (ptr (dpub I)) (bs I) ∧ (bs I).length = len (dpub I) ∧ 1 ≤ len (dpub I) ∧
      len (dpub I) ≤ 8 * vk I.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    CTW (GC vk XT) (GC vk XT) (seqs (loadA j sPtr sLen)) := by
  have hz := zeroA_w (w := vk) (X := XT) (Y := XT) hj (by intros; trivial) ht₁
  refine ⟨RelCT.assoc (pin_seq0 [.x0, .x8, .x1, .x2]
    (fun a => ioVal a.1.B (off a.1.B (slot (vk a.1.k) j)) (ptr a.1) (len a.1))
    (RelCT.seq hz.ct (two_taint [.x0] pins_GC ht₂)) (fun ⟨P, i⟩ s h => ?_) ht₃), fun ⟨P, i⟩ s h => ?_⟩
  · obtain ⟨I, m₀, c, e, g, L, -⟩ := h
    subst e
    refine WP.seq (WP.mono (zeroA_ok g.ws hj) fun t ⟨_, o, _, _, _, k⟩ => ?_)
    have gt := g.out hj (Nat.le_refl _) o k (by decide)
    obtain ⟨hp, hl, -⟩ := hA I m₀ c t gt L.1
    exact loadBlk_ok gt.ws hP hL hp hl
  · obtain ⟨I, m₀, c, e, g, L, -⟩ := h
    subst e
    obtain ⟨hp, hl, hsrc, hbl, hl1, hlw⟩ := hA I m₀ c s g L.1
    exact WP.mono (loadA_ok g.ws hj hP hL hp hl hsrc hbl hl1 hlw) fun t ⟨_, o, _, _, k⟩ =>
      ⟨I, m₀, c, rfl, g.out hj (Nat.le_refl _) o k (by decide), L, trivial⟩

/-- The registers `prod`'s rows need pinned, at the narrow width. -/
def pv (P : DP) : Reg → BitVec 64
  | .x0 => P.B
  | .x11 => off P.B (slot (vk P.k) aE)
  | .x9 => off P.B (slot (vk P.k) aD)
  | .x8 => off P.B (slot (vk P.k) aM)
  | .x12 => BitVec.ofNat 64 (vk P.k)
  | .x13 => BitVec.ofNat 64 ((P.el + 7) / 8)
  | _ => 0

theorem prodRows_ct : RelCT isa (Two (GC vk XT)) (seqs [.block VG.Proof.Rsa.AArch64.prodBlk,
    VG.Impl.Rsa.AArch64.Crt.mulRows]) fun _ _ => True :=
  pin_seq0 [.x0, .x11, .x9, .x8, .x12, .x13, .x7] (fun a => pv a.1) (two_taint [.x0] pins_GC (by taint_decide))
    (fun ⟨P, i⟩ s h => by
      obtain ⟨I, m₀, c, e, g, L, -⟩ := h
      subst e
      exact WP.mono (prodBlk_ok g.ws g.args.el (by have := L.1.el2; have := L.1.k2; omega_arith))
        fun t ⟨⟨h0, h11, h9, h8, h12, h13, h7, _⟩, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h0
          · exact h11
          · exact h9
          · exact h8
          · exact h12
          · exact h13
          · exact h7)
    (by taint_decide)

theorem prefix_ct : CTW GM (GC vk XT) (seqs (([.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)] : List (Prog isa)) ++
    (loadA Public.aN Public.sN Public.sK ++ (loadA aE Public.sE Public.sElen ++ (loadA aD sD sDl ++ prod))))) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * vk k := fun {k} => by simp only [vk]; omega_using []
  refine ⟨?_, fun _ s ⟨I, e, h, _⟩ => WP.mono (prefix_ok h) fun _ ⟨g, _⟩ => ⟨I, s.mem, true, e, g,
    ⟨h.L, ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi, h.oP.sep,
      h.oQ.sep, h.a⟩⟩, trivial⟩⟩
  refine ctr_cons (by simp [loadA]) head_w ?_
  refine ctr_app (a := loadA Public.aN Public.sN Public.sK) (by simp [loadA]) (by simp [loadA])
    (loadA_w (by decide) (by decide) (by decide) DP.pN DP.k
    RpIn.nb (fun I _ _ _ g L => ⟨g.args.n, g.args.k, g.n, L.nbl, Nat.le_trans (by decide) L.k1, k8⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine ctr_app (a := loadA aE Public.sE Public.sElen) (by simp [loadA]) (by simp [loadA])
    (loadA_w (by decide) (by decide) (by decide) DP.pE DP.el
    RpIn.eb (fun I _ _ _ g L => ⟨g.args.e, g.args.el, g.e, L.ebl, L.el1, show I.el ≤ 8 * vk I.k by have := L.el2; have := @k8 I.k; omega_arith⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine ctr_app (a := loadA aD sD sDl) (by simp [loadA]) (by simp [prod])
    (loadA_w (by decide) (by decide) (by decide) DP.pD DP.dl
    RpIn.db (fun I _ _ _ g L => ⟨g.args.d, g.args.dl, g.d, L.dbl, L.dl1, show I.dl ≤ 8 * vk I.k by have := L.dl2; have := @k8 I.k; omega_arith⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  rw [prod_eq]
  refine ctr_cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  exact ctr_cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) prodRows_ct

/-! ## `main` -/

theorem WP.seq_inv {c₁ c₂ : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq c₁ c₂) s Q) :
    WP isa c₁ s fun t => WP isa c₂ t Q := by
  obtain ⟨tr, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ => exact ⟨_, _, e₁, _, _, e₂, q⟩

/-- A piece that also carries what the pieces after it run to. -/
theorem CTW.thread {Φ Ψ : Pub → State → Prop} {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    {F : Pub → State → Prop} (h : CTW Φ Ψ c) :
    CTW (fun a s => Φ a s ∧ WP isa (seqs (c :: l)) s (F a)) (fun a s => Ψ a s ∧ WP isa (seqs l) s (F a)) c := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact CTW.wp h (fun _ _ h => h.1) fun a s ⟨hΦ, hw⟩ => WP.and (h.2 a s hΦ) (WP.seq_inv hw)

theorem CTW.threadLast {Φ Ψ : Pub → State → Prop} {c : Prog isa} {F : Pub → State → Prop} (h : CTW Φ Ψ c) :
    CTW (fun a s => Φ a s ∧ WP isa c s (F a)) (fun a s => Ψ a s ∧ F a s) c :=
  CTW.wp h (fun _ _ h => h.1) fun a s ⟨hΦ, hw⟩ => WP.and (h.2 a s hΦ) hw

/-- The pieces up to `a`. -/
abbrev mid4 : List (Prog isa) := [deMinus, twos, gcd, aProd]

/-- After the prefix: what the pieces up to `a` run to, for `divA`. -/
def XP (a : Pub) (s : State) : Prop := WP isa (seqs mid4) s (XA a)

theorem prefix_ct' [GcdLaw gcdB] : CTW GM (fun a s => GC vk XT a s ∧ XP a s) (seqs (([.block (VG.Impl.Rsa.AArch64.Keys.head ++
    setNar)] : List (Prog isa)) ++ (loadA Public.aN Public.sN Public.sK ++ (loadA aE Public.sE Public.sElen ++
    (loadA aD sD sDl ++ prod))))) := by
  refine CTW.wp prefix_ct (fun _ _ h => h) fun ⟨P, i⟩ s hg => WP.and (prefix_ct.2 _ s hg) ?_
  obtain ⟨I, e, h, hv⟩ := hg
  subst e
  have L := h.L
  have k1 := L.k1
  have k2 := L.k2
  obtain ⟨hodd, hlo⟩ := rvalid_lo hv
  have hNlt : numN I < 2 ^ (8 * I.k) := by have := os2ip_lt I.nb; rw [L.nbl, pow256_eq] at this; exact this
  have hpv := pow_v I.k
  have hpk : 2 ^ (8 * I.k + 64) = 2 ^ (8 * I.k) * 2 ^ 64 := Nat.pow_add _ _ _
  have h3 : 3 ≤ numN I := by
    have : 2 ^ 8 ≤ 256 ^ (I.k - 1) := by rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_using [k1])
    omega
  have hD : numD I < 2 ^ (8 * I.k) := by
    have := os2ip_lt I.db; rw [L.dbl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.dl2; omega_using [this]))
  have hE : numE I < 2 ^ 64 := by
    have := os2ip_lt I.eb; rw [L.ebl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := h.el8; omega_using [this]))
  have hde : numD I * numE I < 2 ^ (64 * vk I.k) :=
    Nat.lt_of_lt_of_le (by rw [hpk]; exact Nat.mul_lt_mul'' hD hE) hpv
  exact WP.mono (prefix_ok h) fun t ⟨g₁, n₁, M₁⟩ => WP.mono (mid4_ok g₁ L n₁ hodd h3 (by omega) M₁ hde)
    fun u ⟨_, _, n, o⟩ => ⟨o, numN I, n, hlo, hNlt⟩

theorem pieces_ct [GcdLaw gcdB] : CTW (fun a s => GC vk XT a s ∧ XP a s) (GC vk XT)
    (seqs [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt]) :=
  CTW.cons (by simp) (deMinus_ct.thread (l := [twos, gcd, aProd]) (by simp))
    (CTW.cons (by simp) (twos_ct.thread (l := [gcd, aProd]) (by simp))
    (CTW.cons (by simp) (gcd_ct.thread (l := [aProd]) (by simp))
    (CTW.cons (by simp) ((aProd_ct.threadLast (F := XA)).mono (fun _ _ h => h) fun _ _ h => h.1.map fun _ => h.2)
    (CTW.cons (by simp) divA_ct (CTW.cons (by simp) divB_ct (CTW.cons (by simp) square_ct
      (CTW.cons (by simp) minus4n_ct (CTW.one sqrt_ct))))))))

/-- `main` leaks the same in runs from a valid modulus with the same public data. -/
theorem rdMain_ct [GcdLaw gcdB] : RelCT isa (Two GM) main fun _ _ => True := by
  rw [main_eq]
  refine ctr_app (by simp) (by simp) prefix_ct' ?_
  refine ctr_app (a := [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt]) (by simp) (by simp)
    pieces_ct ?_
  exact ctr_app (a := factorsA) (by simp) (by simp [storeA]) factors_ct stores_ct

/-! ## The code -/

/-- A state the contract allows, with the public data `a.1`. -/
def RDRel (a : Pub) (s : State) : Prop := rdA.pre s ∧ dpub (rpIn s) = a.1

theorem rdEntry_split : entry = ([.ldrSp .x8 16] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def RD1 (a : Pub) (t : State) : Prop :=
  ∃ s, RDRel a s ∧ t.gpr .x8 = a.1.B ∧ t.gpr .x4 = a.1.pN ∧ t.gpr .x5 = BitVec.ofNat 64 a.1.k ∧
    WP isa (.block (entry.drop 1)) t (RpHeadPost s)

/-- After `entry`. -/
def RD2 (a : Pub) (t : State) : Prop := ∃ s, RDRel a s ∧ RpHeadPost s t

/-- After the modulus' check. -/
def RD3 (a : Pub) (t : State) : Prop :=
  ∃ s t₁, RDRel a s ∧ RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip a.1.nb) a.1.k).toNat

theorem rdRel_x4 {a : Pub} {s : State} (h : RDRel a s) : s.gpr .x4 = a.1.pN := congrArg DP.pN h.2

theorem rdRel_x5 {a : Pub} {s : State} (h : RDRel a s) : s.gpr .x5 = BitVec.ofNat 64 a.1.k := by
  rw [← congrArg DP.k h.2]; exact (ofNat_toNat64 _).symm

theorem rdEntry_ct : RelCT isa (Two RDRel) (.block entry) (Two RD2) := by
  rw [rdEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RD1) [.x4, .x5] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [rdRel_x4 h₁, rdRel_x4 h₂]
    · rw [rdRel_x5 h₁, rdRel_x5 h₂]) (by taint_decide) ?_)
    (two_piece [.x8, .x4, .x5] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := rpCtx_of hs.1.1
  have hh : WP isa (.block (([.ldrSp .x8 16] : List Instr) ++ entry.drop 1)) s (RpHeadPost s) := by
    rw [← rdEntry_split]; exact rpHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := c.ha 2 (by decide)
  have ho : 16 % 8 = 0 ∧ 16 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 2)
    (by brun [exec_ldrSp ho ha2, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg DP.B hs.2), (k.gpr .x4 (by decide)).trans (rdRel_x4 hs),
        (k.gpr .x5 (by decide)).trans (rdRel_x5 hs), hw⟩

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (a : Pub) (s : State) : Prop :=
  ∃ I : RpIn, dpub I = a.1 ∧ Scr s I.B I.Z ∧ s.gpr .x0 = I.B ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD ∧ s.wr = I.W ∧ RpLens I ∧ DOuts I

theorem pins_GFr : Pins GFr [.x0] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg DP.B e₁).trans (congrArg DP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : DP → Addr)
    (hA : ∀ (I : RpIn) (m : Mem), RpArgs m I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD → DOuts I →
      word m I.B (8 * sPtr) = ptr (dpub I) ∧
      (∀ i < I.k, InRegions I.W (ptr (dpub I) + BitVec.ofNat 64 i) 1) ∧
      (∀ i < I.k, I.Z ≤ ofs I.B (ptr (dpub I) + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 Public.sK, movi .x3 0]) hc).isSome
      = true) :
    RelCT isa (Two GFr) (zeroOut sPtr Public.sK) (Two GFr) :=
  pin_ct [.x0] [.x1, .x2] (fun a => zoVal (ptr a.1) a.1.k) pins_GFr ht
    (fun ⟨P, i⟩ s h => by
      obtain ⟨I, rfl, hs, h0, ha, -, L, O⟩ := h
      obtain ⟨hp, -⟩ := hA I s.mem ha O
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega_arith
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = ptr (dpub I) ∧
        t.gpr .x2 = BitVec.ofNat 64 I.k) (by
        brun [h0, hdr_enc hP, hdr_enc (show Public.sK < 32 by decide), hl' sPtr hP,
          hl' Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl rfl rfl)
        fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun ⟨P, i⟩ s h => by
      obtain ⟨I, rfl, hs, h0, ha, hW, L, O⟩ := h
      obtain ⟨hp, hwr, hsep⟩ := hA I s.mem ha O
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega_arith
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs h0 h256 hP (by decide) hp ha.k (by omega_using [hk1]) (by omega_using [hk2])
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega_using [hi])
      exact ⟨I, rfl, hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, ha.congr fun i hi => fw i (by
        unfold rArg at hi; omega_using [hi]), k.wr.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two GFr) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOutR_ct (by decide) DP.pP (fun I m ha O => ⟨ha.p, O.p, O.sp⟩) (by taint_decide))
    (ct_cons (by simp) (zeroOutR_ct (by decide) DP.pQ (fun I m ha O => ⟨ha.q, O.q, O.sq⟩) (by taint_decide))
    (ct_one (Ψ := fun (_ : Pub) (_ : State) => True) (two_post (two_taint [.x0] pins_GFr (by taint_decide))
      fun _ _ _ => WP.mono (WP.keep [.x0] (Q := fun _ => True) (by brun; exact ⟨_, rfl⟩) rfl rfl rfl)
        fun _ _ => trivial)))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- `vg_rsa_recover_primes_det` leaks the same in runs with the same public data. -/
theorem rdCode_ct [GcdLaw gcdB] : RelCT isa (Two RDRel) code fun _ _ => True := by
  unfold RecoverDet.code
  refine RelCT.seq (R := Two RD3) (RelCT.block_append (RelCT.seq rdEntry_ct ?_)) ?_
  -- The modulus' check.
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x2, h₂.x2, rdRel_x4 c₁, rdRel_x4 c₂]
      · rw [h₁.x3, h₂.x3, ofNat_toNat64, ofNat_toNat64, rdRel_x5 c₁, rdRel_x5 c₂])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of hs.1.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .x5).toNat := bytesAt_length _ _ _
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h.x2 h.x3 c.L.k1 c.L.k2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm, _⟩, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) ?_ ?_
  · refine failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => ?_) h) fun _ _ h => h
    have hpre := rpPre_of (rpCtx_of hs.1.1) h hm k
    have e : dpub (rpIn s) = p.1 := hs.2
    have z' : t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k).toNat := by
      rw [z, ← e]; rfl
    rw [eval_zero, z'] at hf
    have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k = false := by
      revert hf; cases Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k <;> simp
    exact ⟨rpIn s, e, hpre.scr, hpre.x0, hpre.args, hpre.wr, hpre.L, ⟨fun i hi => by rw [← hpre.wr]; exact hpre.oP.wr i hi,
      fun i hi => by rw [← hpre.wr]; exact hpre.oQ.wr i hi, hpre.oP.sep, hpre.oQ.sep, hpre.a⟩⟩
  · refine rdMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => ?_) h) fun _ _ h => h
    have hpre := rpPre_of (rpCtx_of hs.1.1) h hm k
    have e : dpub (rpIn s) = p.1 := hs.2
    have z' : t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k).toNat := by
      rw [z, ← e]; rfl
    rw [eval_zero, z'] at hf
    refine ⟨rpIn s, e, ⟨hpre.scr, hpre.x0, hpre.args, hpre.n, hpre.e, hpre.d, hpre.L, hs.1.2, hpre.oP, hpre.oQ,
      hpre.a, hpre.wr⟩, ?_⟩
    show Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k = true
    revert hf
    cases Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k <;> simp

/-- `vg_rsa_recover_primes_det` is constant time but for `n`, `e`, the
pointers and the lengths. -/
theorem rdCode_constantTime [GcdLaw gcdB] : ConstantTime isa rdA.pre rdA.pub code := by
  refine RelCT.constantTime (rdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(dpub (rpIn s₁), 0), ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn, he⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 4, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.1.2.2.1
  have w₂ := h₂.1.2.2.1
  simp only [dpub, rpIn, DP.mk.injEq]
  refine ⟨a 2 (by decide), by rw [a 3 (by decide)], by rw [r .x5 (by decide)], by rw [r .x7 (by decide)],
    by rw [a 1 (by decide)], r .x0 (by decide), r .x2 (by decide), r .x4 (by decide), r .x6 (by decide),
    a 0 (by decide), hn.symm, he.symm, ?_⟩
  rw [w₁, w₂, r .x0 (by decide), r .x1 (by decide), r .x2 (by decide), r .x3 (by decide), a 2 (by decide),
    a 3 (by decide)]

end VG.Proof.Rsa.AArch64.Rd
