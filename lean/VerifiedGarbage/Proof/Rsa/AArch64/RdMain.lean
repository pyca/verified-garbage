module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
public import VerifiedGarbage.Proof.Rsa.AArch64.RdGcd
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrt
import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrtDigits
import VerifiedGarbage.Proof.Rsa.RecoverRoot
public import VerifiedGarbage.Proof.Rsa.AArch64.RdFin
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
