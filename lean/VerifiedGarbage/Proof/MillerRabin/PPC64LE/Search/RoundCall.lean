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
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w m m') (hi : i < 8 * L) (hk : Kept w i) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) :=
  h i hi hk.1 hk.2.1 hk.2.2

/-- A word the round keeps. -/
theorem keeps_word {m m' : Mem} {B : Addr} {L w d : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w m m') (hd : d + 8 ≤ 8 * L)
    (hk : ∀ i, d ≤ i → i < d + 8 → Kept w i) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => by
    rw [show off B d + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact (keeps_byte h (by omega_arith) (hk _ (by omega_arith) (by omega_arith))).symm).symm

/-- A number of `2 w` digits the round keeps. -/
theorem keeps_val32 {m m' : Mem} {B : Addr} {L w d : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w m m') (hd : d + 8 * w ≤ 8 * L)
    (hk : ∀ i, d ≤ i → i < d + 8 * w → Kept w i) :
    val32 m' B d (2 * w) = val32 m B d (2 * w) :=
  val32_congr (d := d) (k := 2 * w) fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => by
    rw [show off B (d + 4 * j) + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + 4 * j + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact keeps_byte (i := d + 4 * j + i) h (by omega_arith) (hk _ (by omega_arith) (by omega_arith)))

/-- `Kept` for a range outside the round's, by `omega` on its offsets. -/
syntax "kept_tac" : tactic
macro_rules
  | `(tactic| kept_tac) => `(tactic| (
      intro i h1 h2
      simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        at h1 h2 ⊢
      and_intros <;> omega_arith))

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
  r1 : arr s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % c
  r9 : arr s.mem B w 9 = 2 ^ (64 * w) % c
  r10 : arr s.mem B w 10 = c - 2 ^ (64 * w) % c
  e : arr s.mem B w aE = mrE c
  l : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)

theorem Prep.width {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) : Proof.Rsa.Mont.wOf s.mem B = w := by
  change (word s.mem B 48).toNat = w
  rw [h.wW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.env.hw'; omega_arith)]

theorem Prep.layout {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) :
    Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact s.mem B L := by
  have hZ := h.env.hZ
  have h4 := h.env.hw
  have h128 := h.env.hw'
  simp only [slot, hdrBytes] at hZ
  simp only [Proof.MillerRabin.Round.Layout, h.width, Proof.MillerRabin.Round.compact, Proof.Rsa.Mont.Layout, Proof.Rsa.Mont.arrAt,
    Proof.Rsa.Mont.hdrBytes]
  refine ⟨Or.inr trivial, ⟨by omega_arith, by omega_arith, by omega_arith, fun j hj => h.arrW j hj⟩, h4, h128,
    by rw [show max (11 + 16) (max (27 + 1) (max (9 + 1) (10 + 1))) = 28 from rfl]; omega_arith, h.strideW⟩

theorem Prep.prepared {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (h5 : arr s.mem B w 5 < c) :
    Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact s.mem B := by
  have hn : Proof.Rsa.Mont.numAt s.mem B w 0 = c := (numAt_eq s.mem B w 0).trans h.n
  simp only [Proof.MillerRabin.Round.Prepared, h.width, hn, Proof.MillerRabin.Round.compact]
  refine ⟨h.c3, h.odd, h.inv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [numAt_eq]; exact h5
  · rw [numAt_eq]; exact h.r9
  · rw [numAt_eq]; exact h.r10
  · rw [numAt_eq]
    simpa only [Proof.MillerRabin.Round.exponent, Proof.MillerRabin.Round.shift, mrE, mrSig, sigOf, mrA, aE] using h.e
  · exact h.l

/-- `Prep` survives a state that keeps `Env` and the words and
numbers `Prep` reads. -/
theorem Prep.keep {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (env : Env t B (8 * L) w)
    (hw : ∀ d, (d = 0 ∨ d = 48 ∨ d = 56 ∨ d = 224 ∨ (∃ j < 8, d = 8 * (8 + j)) ∨ d = slot w 0 ∨
      d = slot w 27 + 8 * w) → word t.mem B d = word s.mem B d)
    (hv : ∀ j, (j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) →
      val32 t.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w)) : Prep t B L w c := by
  have h56 := hw 56 (by simp)
  have h0 := hw (slot w 0) (by simp)
  refine ⟨env, (hw 0 (by simp)).trans h.len, (hw 48 (by simp)).trans h.wW, (hw 224 (by simp)).trans h.strideW,
    fun j hj => (hw _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩)))))).trans (h.arrW j hj),
    (hv 0 (by simp)).trans h.n, h.c3, h.odd, by rw [h0, h56]; exact h.inv,
    (hv 1 (by simp)).trans h.r1, (hv 9 (by simp)).trans h.r9, (hv 10 (by simp)).trans h.r10, ?_, ?_⟩
  · have he := h.e
    have e27 : aE = 27 := rfl
    rw [e27] at he ⊢
    exact (hv 27 (by simp)).trans he
  · have hl := h.l
    have e27 : aE = 27 := rfl
    rw [e27] at hl ⊢
    have := hw (slot w 27 + 8 * w) (by simp)
    simp only [word] at this
    rw [this]; exact hl

/-- `Prep` survives a change of memory that keeps the round's words and a
state that keeps `Env`. -/
theorem Prep.transfer {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (env : Env t B (8 * L) w)
    (hw : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word t.mem B d = word s.mem B d)
    (hv : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 t.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w)) : Prep t B L w c := by
  have hZ := env.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  refine h.keep env (fun d hd => ?_) (fun j hj => ?_)
  · rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    · exact hw 0 (by omega_arith) (by kept_tac)
    · exact hw 48 (by omega_arith) (by kept_tac)
    · exact hw 56 (by omega_arith) (by kept_tac)
    · exact hw 224 (by omega_arith) (by kept_tac)
    · exact hw _ (by omega_arith) (by intro i h1 h2; simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq]; and_intros <;> omega_arith)
    · exact hw (slot w 0) (by simp only [es]; omega_arith) (by kept_tac)
    · have s27 := es 27
      exact hw (slot w 27 + 8 * w) (by omega_arith) (by kept_tac)
  · have s27 := es 27
    have k27 : ∀ i, slot w 27 ≤ i → i < slot w 27 + 8 * w → Kept w i := by
      intro i h1 h2
      refine ⟨fun k hk => ?_, fun j hj => ?_, Or.inr h1⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega_arith
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        have := es 2; have := es 3; have := es 5; have := es 6; have := es 8
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega_arith
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact hv 0 (by simp only [es]; omega_arith) (by kept_tac)
    · exact hv 1 (by simp only [es]; omega_arith) (by kept_tac)
    · exact hv 9 (by simp only [es]; omega_arith) (by kept_tac)
    · exact hv 10 (by simp only [es]; omega_arith) (by kept_tac)
    · exact hv 27 (by omega_arith) k27

/-- What `roundCall` leaves: the prepared modulus, the result in `r3`, the
round's `Keeps`, and everything outside the working space and the round's
stack. -/
structure RcPost (s : State) (B : Addr) (L w c a : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  r3 : t.gpr .r3 = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then 1 else 0)
  keeps : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w s.mem t.mem
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → t.gpr r = s.gpr r

/-- Before the call: the witness in Montgomery form in array 5, and the
arguments in `r3` and `r4`. -/
structure RcMid (s : State) (B : Addr) (L w c a : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  a5 : val32 t.mem B (slot w 5) (2 * w) = a % c * 2 ^ (64 * w) % c
  r3 : t.gpr .r3 = B
  r4 : t.gpr .r4 = BitVec.ofNat 64 L
  outs : Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2))] s.mem t.mem
  keep : Keep (Pub.montRegs ++ ([.r3, .r4] : List Reg)) s t

/-- The arrays `montOp` changes are not kept by the round. -/
theorem kept_sep {w : Nat} : ∀ d k, 0 < k → (∀ i, d ≤ i → i < d + k → Kept w i) → ∀ r ∈ [(slot w 2, 8 * (w + 2)),
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
  · have := (hk (slot w j) hd (by omega_arith)).2.1 j hjm; omega_arith
  · have := (hk d (Nat.le_refl _) (by omega_arith)).2.1 j hjm; omega_arith

theorem rcHead_ok {s : State} {B : Addr} {L w c a : Nat} (h : Prep s B L w c)
    (h12 : s.gpr .r12 = (word s.mem B 56 <<< 32) >>> 32)
    (ha : arr s.mem B w 4 = a) (hac : a < c) :
    WP isa (.seq (PublicChecked.montOp 5 4 1) (.block [.addi .r3 .r31 0, ldh .r4 hWsLen])) s
      (RcMid s B L w c a) := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 h.odd _
  obtain ⟨i12, iinv⟩ := r12_inv h.inv
  -- The witness in Montgomery form.
  refine WP.seq (WP.mono (Pub.montOp_ok e.hs (o := 5) (a := 4) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith) (by simp only [es]; omega_arith) e.h10 e.h29
    e.h11 (by rw [h12]; exact i12) (by rw [h12, w32_eq_mod]; exact iinv)
    (by show arr s.mem B w 1 < arr s.mem B w 0; rw [h.r1, h.n]; exact Nat.mod_lt _ (by have := h.c3; omega_arith)))
    fun s₁ ⟨⟨lt₁, eq₁, o₁⟩, k₁⟩ => ?_)
  have hn0 : val32 s.mem B (slot w 0) (2 * w) = c := h.n
  rw [hn0] at lt₁ eq₁
  rw [show val32 s.mem B (slot w 4) (2 * w) = a from ha, show val32 s.mem B (slot w 1) (2 * w) = _ from h.r1] at eq₁
  have h5 : val32 s₁.mem B (slot w 5) (2 * w) = a % c * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt lt₁, Nat.mod_eq_of_lt hac]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [eq₁, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  -- What `montOp` keeps.
  have sep₁ := @kept_sep w
  have w₁ : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word s₁.mem B d = word s.mem B d :=
    fun d hd hk => Outs.word o₁ (sep₁ d 8 (by decide) hk) (by omega_arith)
  have v₁ : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun j hd hk => Outs.val32 o₁ (by have := sep₁ _ _ (by omega_arith) hk; simpa only [show 4 * (2 * w) = 8 * w by omega_arith])
      (by omega_arith)
  have p₁ : Prep s₁ B L w c := h.transfer (e.keep k₁ (by decide)) w₁ v₁
  -- The arguments.
  have h31₁ : s₁.gpr .r31 = B := (k₁.gpr .r31 (by decide)).trans e.h31
  have l0 : InRegions (s₁.rd ++ s₁.wr) B 8 := by
    have := (e.hs.congr k₁.wr).ld (d := 0) (n := 8) (by omega_arith)
    simpa only [off, BitVec.add_zero] using this
  have r0 : s₁.mem.readW B 64 = BitVec.ofNat 64 L := by
    have := p₁.len
    simpa only [word, off, BitVec.add_zero] using this
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun u => u.gpr .r3 = B ∧ u.gpr .r4 = BitVec.ofNat 64 L ∧
      u.mem = s₁.mem) (by simp only [ldh, hWsLen]; prun [h31₁, BitVec.add_zero, l0, r0]) (by decide))
    fun s₂ ⟨⟨r3₂, r4₂, m₂⟩, k₂⟩ => ?_
  have p₂ : Prep s₂ B L w c := p₁.transfer (p₁.env.keep k₂ (by decide))
    (fun d _ _ => by rw [m₂]) (fun j _ _ => by rw [m₂])
  have k12 := k₁.trans k₂
  exact ⟨p₂, by rw [m₂]; exact h5, r3₂, r4₂, by rw [m₂]; exact o₁, k12⟩

/-- The working space's bytes are writable. -/
theorem scr_covers {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {x : Addr} {n : Nat}
    (h : InRegions [⟨B, Z⟩] x n) : InRegions s.wr x n := by
  obtain ⟨B₀, o, L', hm, hb, hoL, -⟩ := hs.wr
  obtain ⟨r, hr, hc⟩ := h
  rw [List.mem_singleton] at hr
  subst hr hb
  refine ⟨⟨B₀, L'⟩, hm, ?_⟩
  simp only [Region.Contains, off] at hc ⊢
  have e : x - B₀ = (x - (B₀ + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o := by bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((x - (B₀ + BitVec.ofNat 64 o)).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega

theorem roundCallTail_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a : Nat} (h : Prep s B L w c)
    (h12 : s.gpr .r12 = (word s.mem B 56 <<< 32) >>> 32)
    (ha : arr s.mem B w 4 = a) (hac : a < c)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩) :
    WP isa (.seq (PublicChecked.montOp 5 4 1) (.seq (.block [.addi .r3 .r31 0, ldh .r4 hWsLen])
      (.seq (.call R.name R.code) (.block (([.lsl .r3 .r3 32, .lsr .d .r3 .r3 32] : List Instr) ++ regsBack))))) s
      (RcPost s B L w c a) := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  refine WP.assoc (WP.seq (WP.mono (rcHead_ok h h12 ha hac) fun s₂ mid => ?_))
  have sep₁ := @kept_sep w
  have p₂ := mid.prep
  have k12 := mid.keep
  have r3₂ := mid.r3
  have r4₂ := mid.r4
  have hL64 : L < 2 ^ 64 := by omega_arith
  have hwr₂ : ∀ x n, InRegions [⟨B, 8 * L⟩] x n → InRegions s₂.wr x n := fun _ _ => scr_covers p₂.env.hs
  -- The round.
  refine WP.seq (WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176) R.verified.1
    (rd := []) (wr := [⟨B, 8 * L⟩]) ?_ ?_ ?_ (fun s₃ hrd hwr₃ hsp₃ hf hcs hpost => ?_) (by have := R.stack; omega_arith))
  · sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [r3₂, r4₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64, Nat.mul_comm L 8, k12.sp]
    exact ⟨hsp, trivial, hstk, by omega_arith, p₂.layout, p₂.prepared (by
      show val32 s₂.mem B (slot w 5) (2 * w) < c; rw [mid.a5]; exact Nat.mod_lt _ (by have := h.c3; omega_arith))⟩
  · intro x n hx
    obtain ⟨r, hr, hc⟩ := hwr₂ x n (by simpa only [List.nil_append] using hx)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · exact hwr₂
  sig_post [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs] at hpost
  obtain ⟨hres, hk3⟩ := hpost
  rw [r3₂, p₂.width] at hres hk3
  rw [r4₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64] at hk3
  have hn₂ : Proof.Rsa.Mont.numAt s₂.mem B w 0 = c := (numAt_eq _ _ _ _).trans p₂.n
  have h5₂ : Proof.Rsa.Mont.numAt s₂.mem B w 5 = a % c * 2 ^ (64 * w) % c := by
    rw [numAt_eq]; exact mid.a5
  rw [hn₂] at hres
  have hr3 := hres a h5₂
  have h31₃ : s₃.gpr .r31 = B := (hcs .r31 (by decide)).trans ((k12.gpr .r31 (by decide)).trans e.h31)
  have kw : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word s₃.mem B d = word s₂.mem B d :=
    fun d hd hk => keeps_word hk3 hd hk
  have kv : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 s₃.mem B (slot w j) (2 * w) = val32 s₂.mem B (slot w j) (2 * w) :=
    fun j hd hk => keeps_val32 hk3 hd hk
  have hs₃ : Scr s₃ B (8 * L) := e.hs.congr (hwr₃.trans k12.wr)
  have rd48 : s₃.mem.readW (B + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 w := (kw 48 (by omega_arith) (by kept_tac)).trans p₂.wW
  have rd224 : s₃.mem.readW (B + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 (8 * (w + 2)) :=
    (kw 224 (by omega_arith) (by kept_tac)).trans p₂.strideW
  have rd56 : s₃.mem.readW (B + BitVec.ofNat 64 56) 64 = word s₂.mem B 56 := kw 56 (by omega_arith) (by kept_tac)
  -- The result and the registers back.
  refine WP.mono (WP.keep [.r3, .r10, .r11, .r29, .r12] (Q := fun u =>
      u.gpr .r3 = (s₃.gpr .r3 <<< 32) >>> 32 ∧ u.gpr .r10 = off B (slot w 0) ∧
      u.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ u.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      u.gpr .r12 = (word s₂.mem B 56 <<< 32) >>> 32 ∧ u.mem = s₃.mem) ?_ (by decide))
    fun t ⟨⟨t3, t10, t11, t29, t12, tm⟩, kt⟩ => ?_
  · simp only [regsBack, minv32, ldh, hW, hStride, hMinv, hdrBytes]
    prun [h31₃, hs₃.ld (d := 48) (n := 8) (by omega_arith), hs₃.ld (d := 224) (n := 8) (by omega_arith),
      hs₃.ld (d := 56) (n := 8) (by omega_arith), rd48, rd224, rd56, shl1_ofNat]
    simp only [es, Nat.zero_mul, Nat.add_zero]
  have ofs_add : ∀ i, i < 2 ^ 64 → ofs B (B + BitVec.ofNat 64 i) = i := fun i hi => ofs_off0 B hi
  have env_t : Env t B (8 * L) w := ⟨e.hs.congr (kt.wr.trans (hwr₃.trans k12.wr)), t10, t29, t11,
    (kt.gpr .r31 (by decide)).trans h31₃, hw4, hw128, hZ⟩
  refine ⟨p₂.transfer env_t (fun d hd hk => by rw [tm]; exact kw d hd hk)
    (fun j hd hk => by rw [tm]; exact kv j hd hk), ?_, ?_, ?_, kt.rd.trans (hrd.trans k12.rd),
    kt.wr.trans (hwr₃.trans k12.wr), kt.sp.trans (hsp₃.trans k12.sp), fun r hr hm => ?_⟩
  · have hx : ((s₃.gpr .r3 <<< 32) >>> 32).toNat = (s₃.gpr .r3).toNat % 2 ^ 32 := by
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      have := (s₃.gpr .r3).isLt
      omega_arith
    rw [t3]
    apply BitVec.eq_of_toNat_eq
    rw [hx, ← BitVec.toNat_setWidth, hr3]
    split <;> rfl
  · intro i hi hk hj ht
    rw [tm, hk3 i hi hk hj ht]
    refine mid.outs _ fun r hr => ?_
    rw [ofs_add i (by omega_arith)]
    have := sep₁ i 1 (by decide) (fun i' h1 h2 => by
      rw [show i' = i by omega_arith]; exact ⟨hk, hj, ht⟩) r hr
    omega_arith
  · intro x hx
    have hx1 : ¬ (⟨B, 8 * L⟩ : Region).Contains x 1 := hx _ (List.mem_cons_self)
    have hx2 : ¬ (below s.sp 176).Contains x 1 := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [tm, hf x fun r hr => ?_]
    · refine mid.outs _ fun r hr => ?_
      simp only [Region.Contains] at hx1
      simp only [ofs]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [es] <;> omega_arith
    · rcases List.mem_append.mp hr with hr | hr
      · rw [List.mem_singleton] at hr; subst hr; exact hx1
      · rw [List.mem_singleton] at hr; subst hr
        exact fun hc => hx2 (below_sub (by have := R.stack; omega_arith) (by decide) _ (by rw [← k12.sp]; exact hc))
  · by_cases h29 : r = .r29
    · subst h29; rw [t29, e.h29]
    have p1 : ∀ r ∈ preserved, r ≠ .r29 → r ∉ ([.r3, .r10, .r11, .r29, .r12] : List Reg) := by decide
    have p2 : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ Pub.montRegs ++ ([.r3, .r4] : List Reg) := by decide
    rw [kt.gpr r (p1 r hr h29), hcs r hr, k12.gpr r (p2 r hr hm)]

theorem roundCall_ok (R : RoundImpl) {s : State} {B : Addr} {L w c a : Nat} (h : Prep s B L w c)
    (ha : arr s.mem B w 4 = a) (hac : a < c)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩) :
    WP isa (roundCall R.name R.code) s (RcPost s B L w c a) := by
  have e := h.env
  unfold roundCall
  have l56 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 56) 8 := e.hs.ld (d := 56) (by
    have := e.hZ; simp only [slot, hdrBytes] at this; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = (word s.mem B 56 <<< 32) >>> 32 ∧
      u.mem = s.mem) (by simp only [minv32, ldh, hMinv]; prun [e.h31, l56]) (by decide))
    fun u ⟨⟨u12, um⟩, ku⟩ => ?_)
  have hu : Prep u B L w c := h.transfer (e.keep ku (by decide)) (fun d _ _ => by rw [um])
    (fun j _ _ => by rw [um])
  refine WP.mono (roundCallTail_ok R hu (by rw [um]; exact u12) (by rw [um]; exact ha) hac
    (by rw [ku.sp]; exact hsp) (by rw [ku.sp]; exact hstk)) fun t ht => ?_
  have p12 : ∀ r ∈ preserved, r ∉ ([.r12] : List Reg) := by decide
  exact ⟨ht.prep, ht.r3, by have := ht.keeps; rwa [um] at this, by have := ht.frame; rwa [um, ku.sp] at this, ht.rd.trans ku.rd, ht.wr.trans ku.wr, ht.sp.trans ku.sp,
    fun r hr hm => (ht.cs r hr hm).trans (ku.gpr r (p12 r hr))⟩

end VG.Proof.MillerRabin.PPC64LE.Search
