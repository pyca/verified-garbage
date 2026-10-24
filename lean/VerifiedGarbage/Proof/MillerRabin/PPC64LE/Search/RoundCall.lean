module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Minv

/-!
# A prime search on PPC64LE: calling the round

`Prep`: a modulus's prepared working space (`montPrep_ok`'s result), what
the shared round's `Layout` and `Prepared` ask (`layout_of_prep`,
`prepared_of_prep`). `roundCall_ok`: a witness `a < c` in array 4, in
Montgomery form into array 5, and the round (a `RoundImpl`) called: `r3` is
1 exactly when `a` passes; the working space changes only where the round's
`Keeps` allows, and `Prep` still holds.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (mrE mrA mrSig sigOf)

/-- A byte the round keeps: not in its header words, its working arrays or
its table. -/
def Kept (w i : Nat) : Prop :=
  (∀ k ∈ [23, 26, 29, 30, 1], i < 8 * k ∨ 8 * k + 8 ≤ i) ∧
    (∀ j ∈ [2, 3, 5, 6, 8], i < slot w j ∨ slot w j + 8 * (w + 2) ≤ i) ∧ (i < slot w 11 ∨ slot w 27 ≤ i)

theorem keeps_byte {m m' : Mem} {B : Addr} {L w i : Nat}
    (h : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B L w m m') (hi : i < 8 * L) (hk : Kept w i) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) :=
  h i hi hk.1 hk.2.1 hk.2.2

/-- A word the round keeps. -/
theorem keeps_word {m m' : Mem} {B : Addr} {L w d : Nat}
    (h : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B L w m m') (hd : d + 8 ≤ 8 * L)
    (hk : ∀ i, d ≤ i → i < d + 8 → Kept w i) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => by
    rw [show off B d + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact (keeps_byte h (by omega) (hk _ (by omega) (by omega))).symm).symm

/-- A number of `2 w` digits the round keeps. -/
theorem keeps_val32 {m m' : Mem} {B : Addr} {L w d : Nat}
    (h : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B L w m m') (hd : d + 8 * w ≤ 8 * L)
    (hk : ∀ i, d ≤ i → i < d + 8 * w → Kept w i) :
    val32 m' B d (2 * w) = val32 m B d (2 * w) :=
  val32_congr (d := d) (k := 2 * w) fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => by
    rw [show off B (d + 4 * j) + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + 4 * j + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact keeps_byte (i := d + 4 * j + i) h (by omega) (hk _ (by omega) (by omega)))

/-- `Kept` for a range outside the round's, by `omega` on its offsets. -/
syntax "kept_tac" : tactic
macro_rules
  | `(tactic| kept_tac) => `(tactic| (
      intro i h1 h2
      simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        at h1 h2 ⊢
      and_intros <;> omega))

/-- A modulus `c` of `w` words prepared in the `L` words at `B` (`r31`). -/
structure Prep (s : State) (B : Addr) (L w c : Nat) : Prop where
  env : Env s B (8 * L) w
  len : word s.mem B 0 = BitVec.ofNat 64 L
  wW : word s.mem B 48 = BitVec.ofNat 64 w
  strideW : word s.mem B 224 = BitVec.ofNat 64 (8 * (w + 2))
  arrW : ∀ j < 8, word s.mem B (8 * (8 + j)) = off B (slot w j)
  n : arr s.mem B w 0 = c
  c3 : 3 ≤ c
  odd : c % 2 = 1
  inv : ((word s.mem B (slot w 0)).toNat * (word s.mem B 56).toNat + 1) % 2 ^ 64 = 0
  r12 : s.gpr .r12 = (word s.mem B 56 <<< 32) >>> 32
  r1 : arr s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % c
  r9 : arr s.mem B w 9 = 2 ^ (64 * w) % c
  r10 : arr s.mem B w 10 = c - 2 ^ (64 * w) % c
  e : arr s.mem B w aE = mrE c
  l : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)

theorem Prep.width {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) : Spec.Rsa.Mont.wOf s.mem B = w := by
  change (word s.mem B 48).toNat = w
  rw [h.wW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.env.hw'; omega)]

theorem Prep.layout {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem B L := by
  have hZ := h.env.hZ
  have h4 := h.env.hw
  have h128 := h.env.hw'
  simp only [slot, hdrBytes] at hZ
  simp only [Spec.MillerRabin.Layout, h.width, Spec.MillerRabin.compact, Spec.Rsa.Mont.Layout, Spec.Rsa.Mont.arrAt,
    Spec.Rsa.Mont.hdrBytes]
  refine ⟨Or.inr trivial, ⟨by omega, by omega, by omega, fun j hj => h.arrW j hj⟩, h4, h128,
    by rw [show max (11 + 16) (max (27 + 1) (max (9 + 1) (10 + 1))) = 28 from rfl]; omega, h.strideW⟩

theorem Prep.prepared {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (h5 : arr s.mem B w 5 < c) :
    Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem B := by
  have hn : Spec.Rsa.Mont.numAt s.mem B w 0 = c := (numAt_eq s.mem B w 0).trans h.n
  simp only [Spec.MillerRabin.Prepared, h.width, hn, Spec.MillerRabin.compact]
  refine ⟨h.c3, h.odd, h.inv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [numAt_eq]; exact h5
  · rw [numAt_eq]; exact h.r9
  · rw [numAt_eq]; exact h.r10
  · rw [numAt_eq]
    simpa only [Spec.MillerRabin.exponent, Spec.MillerRabin.shift, mrE, mrSig, sigOf, mrA, aE] using h.e
  · exact h.l

/-- `Prep` survives a change of memory that keeps the round's words and a
state that keeps `Env` and `r12`. -/
theorem Prep.transfer {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (env : Env t B (8 * L) w)
    (r12 : t.gpr .r12 = s.gpr .r12)
    (hw : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word t.mem B d = word s.mem B d)
    (hv : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 t.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w)) : Prep t B L w c := by
  have hZ := env.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have h56 := hw 56 (by omega) (by kept_tac)
  have h0 := hw (slot w 0) (by simp only [es]; omega) (by kept_tac)
  refine ⟨env, (hw 0 (by omega) (by kept_tac)).trans h.len, (hw 48 (by omega) (by kept_tac)).trans h.wW,
    (hw 224 (by omega) (by kept_tac)).trans h.strideW, fun j hj => ?_, ?_, h.c3, h.odd, by rw [h0, h56]; exact h.inv,
    by rw [r12, h56]; exact h.r12, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw _ (by omega) (by intro i h1 h2; simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]; and_intros <;> omega)]
    exact h.arrW j hj
  · show val32 _ _ _ _ = c; rw [hv 0 (by simp only [es]; omega) (by kept_tac)]; exact h.n
  · show val32 _ _ _ _ = _; rw [hv 1 (by simp only [es]; omega) (by kept_tac)]; exact h.r1
  · show val32 _ _ _ _ = _; rw [hv 9 (by simp only [es]; omega) (by kept_tac)]; exact h.r9
  · show val32 _ _ _ _ = _; rw [hv 10 (by simp only [es]; omega) (by kept_tac)]; exact h.r10
  · have he := h.e
    have e27 : aE = 27 := rfl
    rw [e27] at he ⊢
    show val32 _ _ _ _ = _
    have s27 := es 27
    have b27 : slot w 27 + 8 * w ≤ 8 * L := by omega
    have k27 : ∀ i, slot w 27 ≤ i → i < slot w 27 + 8 * w → Kept w i := by
      intro i h1 h2
      refine ⟨fun k hk => ?_, fun j hj => ?_, Or.inr h1⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        have := es 2; have := es 3; have := es 5; have := es 6; have := es 8
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
    rw [hv 27 b27 k27]; exact he
  · have hl := h.l
    have e27 : aE = 27 := rfl
    rw [e27] at hl ⊢
    have := hw (slot w 27 + 8 * w) (by simp only [es]; omega) (by kept_tac)
    simp only [word] at this
    rw [this]; exact hl

/-- What `roundCall` leaves: the prepared modulus, the result in `r3`, the
round's `Keeps`, and everything outside the working space and the round's
stack. -/
structure RcPost (s : State) (B : Addr) (L w c a : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  r3 : t.gpr .r3 = BitVec.ofNat 64 (if Spec.MillerRabin.round c a then 1 else 0)
  keeps : Spec.MillerRabin.Keeps Spec.MillerRabin.compact B L w s.mem t.mem
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, t.gpr r = s.gpr r

theorem roundCall_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a : Nat} (h : Prep s B L w c)
    (ha : arr s.mem B w 4 = a) (hac : a < c) (hwr : (⟨B, 8 * L⟩ : Region) ∈ s.wr)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩) :
    WP isa (roundCall R.name R.code) s (RcPost s B L w c a) := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 h.odd _
  obtain ⟨i12, iinv⟩ := r12_inv h.inv
  unfold roundCall
  -- The witness in Montgomery form.
  refine WP.seq (WP.mono (Pub.montOp_ok e.hs (o := 5) (a := 4) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by simp only [es]; omega) e.h10 e.h29
    e.h11 (by rw [h.r12]; exact i12) (by rw [h.r12, w32_eq_mod]; exact iinv)
    (by show arr s.mem B w 1 < arr s.mem B w 0; rw [h.r1, h.n]; exact Nat.mod_lt _ (by have := h.c3; omega)))
    fun s₁ ⟨⟨lt₁, eq₁, o₁⟩, k₁⟩ => ?_)
  have hn0 : val32 s.mem B (slot w 0) (2 * w) = c := h.n
  rw [hn0] at lt₁ eq₁
  rw [show val32 s.mem B (slot w 4) (2 * w) = a from ha, show val32 s.mem B (slot w 1) (2 * w) = _ from h.r1] at eq₁
  have h5 : val32 s₁.mem B (slot w 5) (2 * w) = a % c * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt lt₁, Nat.mod_eq_of_lt hac]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [eq₁, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  -- What `montOp` keeps.
  have sep₁ : ∀ d k, 0 < k → (∀ i, d ≤ i → i < d + k → Kept w i) → ∀ r ∈ [(slot w 2, 8 * (w + 2)),
      (slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2))], d + k ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d k hk0 hk r hr
    have hj : ∃ j ∈ [2, 3, 5, 6, 8], r = (slot w j, 8 * (w + 2)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [⟨2, by simp, rfl⟩, ⟨3, by simp, rfl⟩, ⟨5, by simp, rfl⟩]
    obtain ⟨j, hjm, rfl⟩ := hj
    show d + k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d
    by_contra hc
    simp only [not_or, Nat.not_le] at hc
    by_cases hd : d ≤ slot w j
    · have := (hk (slot w j) hd (by omega)).2.1 j hjm; omega
    · have := (hk d (Nat.le_refl _) (by omega)).2.1 j hjm; omega
  have w₁ : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word s₁.mem B d = word s.mem B d :=
    fun d hd hk => Outs.word o₁ (sep₁ d 8 (by decide) hk) (by omega)
  have v₁ : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun j hd hk => Outs.val32 o₁ (by have := sep₁ _ _ (by omega) hk; simpa only [show 4 * (2 * w) = 8 * w by omega])
      (by omega)
  have p₁ : Prep s₁ B L w c := h.transfer (e.keep k₁ (by decide)) (k₁.gpr .r12 (by decide)) w₁ v₁
  sorry

end VG.Proof.MillerRabin.PPC64LE.Search
