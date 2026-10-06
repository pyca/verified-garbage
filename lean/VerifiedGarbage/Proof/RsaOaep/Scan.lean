import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption: the masks and the scan, whatever the target

What the accumulators an implementation computes without branches say,
whatever the target: masks of all ones or zero (`mk`, `zM`); the scan of
`T` (`scanS`): all ones while no `0x01` has been seen, the index of the
first, and an accumulator ORed with a mask for each byte before it that is
neither `0x00` nor `0x01` (`scanS_inv`); which is when the decoding's
`dropWhile` finds `0x01` and the message after it (`scan_found`,
`scan_fail`).
-/

namespace VG.Proof.RsaOaep

open VG
open VG.Proof.Mgf1 (ifp ifn)

theorem xor_eq_zero (a b : BitVec 64) : (a ^^^ b = 0) ↔ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]

/-! ## Masks -/

theorem zx_eq_zero (b : Byte) : BitVec.setWidth 64 b = 0 ↔ b = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rw [Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
    simpa using this
  · intro h; subst h; rfl

theorem zx_inj {a b : Byte} : BitVec.setWidth 64 a = BitVec.setWidth 64 b ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by have := a.isLt; omega), Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
  · intro h; rw [h]

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun x => x.getLsbD i) h <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

/-- All ones if `x` is zero, as a borrow computes it. -/
abbrev zM (x : BitVec 64) : BitVec 64 := if x = 0 then BitVec.allOnes 64 else 0

/-- The scan's registers after `j` bytes of `f`, from the accumulator `c₀`:
`rdx` all ones while no `0x01` has been seen, `rsi` the index of the first,
`rcx` the accumulator, ORed with a mask for each byte before it that is
neither `0x00` nor `0x01`. -/
def scanS (f : Nat → Byte) (c₀ : BitVec 64) : Nat → BitVec 64 × BitVec 64 × BitVec 64
  | 0 => (BitVec.allOnes 64, 0, c₀)
  | j + 1 =>
    let p := scanS f c₀ j
    let b := (f j).setWidth 64
    let z := zM b
    let o := zM (b ^^^ 1)
    (p.1 &&& (o ^^^ BitVec.allOnes 64), p.2.1 ||| (BitVec.ofNat 64 j &&& p.1 &&& o),
      p.2.2 ||| (((z ||| o) ^^^ BitVec.allOnes 64) &&& p.1))

/-! ## The scan -/

/-- No `0x01` among the first `n` bytes. -/
def lk (f : Nat → Byte) (n : Nat) : Prop := ∀ j < n, f j ≠ 1

/-- A byte other than `0x00` and `0x01` before the first `0x01` (or the end). -/
def bad (f : Nat → Byte) (n : Nat) : Prop := ∃ j < n, (∀ i < j, f i ≠ 1) ∧ f j ≠ 0 ∧ f j ≠ 1

instance (f : Nat → Byte) (n : Nat) : Decidable (lk f n) := by unfold lk; infer_instance
instance (f : Nat → Byte) (n : Nat) : Decidable (bad f n) := by unfold bad; infer_instance

/-- All ones if `p`, else zero. -/
def mk (p : Prop) [Decidable p] : BitVec 64 := if p then BitVec.allOnes 64 else 0

theorem mk_and (p q : Prop) [Decidable p] [Decidable q] : mk p &&& mk q = mk (p ∧ q) := by
  unfold mk; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem mk_or (p q : Prop) [Decidable p] [Decidable q] : mk p ||| mk q = mk (p ∨ q) := by
  unfold mk; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem mk_not (p : Prop) [Decidable p] : mk p ^^^ BitVec.allOnes 64 = mk (¬ p) := by
  unfold mk; by_cases hp : p <;> simp [hp]

theorem and_mk (x : BitVec 64) (p : Prop) [Decidable p] : x &&& mk p = if p then x else 0 := by
  unfold mk; by_cases hp : p
  · rw [ifp hp, BitVec.and_allOnes, ifp hp]
  · rw [ifn hp, ifn hp]; exact BitVec.and_zero

theorem mk_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : mk p = mk q := by
  unfold mk; by_cases hp : p
  · rw [ifp hp, ifp (h.mp hp)]
  · rw [ifn hp, ifn (fun hq => hp (h.mpr hq))]

theorem zM_zx (b : Byte) : zM (BitVec.setWidth 64 b) = mk (b = 0) := by
  simp only [zM, mk, zx_eq_zero]

theorem zM_zx1 (b : Byte) : zM (BitVec.setWidth 64 b ^^^ 1) = mk (b = 1) := by
  simp only [zM, mk]
  have : BitVec.setWidth 64 b ^^^ 1 = 0 ↔ b = 1 := by
    rw [xor_eq_zero, show (1 : BitVec 64) = BitVec.setWidth 64 (1 : Byte) from rfl, zx_inj]
  by_cases h : b = 1
  · rw [ifp (this.mpr h), ifp h]
  · rw [ifn (fun h' => h (this.mp h')), ifn h]

theorem scanS_inv (f : Nat → Byte) (c₀ : BitVec 64) : ∀ n,
    (scanS f c₀ n).1 = mk (lk f n) ∧
    (lk f n → (scanS f c₀ n).2.1 = 0) ∧
    (¬ lk f n → ∃ j₀ < n, f j₀ = 1 ∧ (∀ i < j₀, f i ≠ 1) ∧ (scanS f c₀ n).2.1 = BitVec.ofNat 64 j₀) ∧
    (scanS f c₀ n).2.2 = c₀ ||| mk (bad f n)
  | 0 => by
    have : ¬ bad f 0 := fun ⟨_, h, _⟩ => Nat.not_lt_zero _ h
    have hl : lk f 0 := fun _ h => absurd h (Nat.not_lt_zero _)
    refine ⟨by simp [scanS, mk, hl], fun _ => rfl, fun h => absurd hl h, by simp [scanS, mk, this]⟩
  | n + 1 => by
    obtain ⟨hd, hs0, hs1, hc⟩ := scanS_inv f c₀ n
    have hlk : lk f (n + 1) ↔ lk f n ∧ ¬ f n = 1 := ⟨fun h => ⟨fun j hj => h j (by omega), h n (by omega)⟩,
      fun ⟨h, h'⟩ j hj => if hjn : j < n then h j hjn else by rw [show j = n by omega]; exact h'⟩
    have hbad : bad f (n + 1) ↔ bad f n ∨ ¬ (f n = 0 ∨ f n = 1) ∧ lk f n :=
      ⟨fun ⟨j, hj, h1, h2, h3⟩ => if hjn : j < n then .inl ⟨j, hjn, h1, h2, h3⟩ else by
          have e : j = n := by omega
          subst e
          exact .inr ⟨fun h' => h'.elim h2 h3, h1⟩,
       fun h => h.elim (fun ⟨j, hj, h1, h2, h3⟩ => ⟨j, by omega, h1, h2, h3⟩)
        fun ⟨h1, h2⟩ => ⟨n, by omega, h2, fun e => h1 (.inl e), fun e => h1 (.inr e)⟩⟩
    simp only [scanS, zM_zx, zM_zx1, hd, hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mk_not, mk_and]; exact mk_congr hlk.symm
    · intro h
      have hl := (hlk.mp h).1
      rw [hs0 hl, BitVec.and_assoc, mk_and, and_mk, ifn (fun h' => (hlk.mp h).2 h'.2)]; rfl
    · intro h
      by_cases hl : lk f n
      · have h1 : f n = 1 := by
          by_contra h1; exact h (hlk.mpr ⟨hl, h1⟩)
        refine ⟨n, by omega, h1, hl, ?_⟩
        rw [hs0 hl, BitVec.and_assoc, mk_and, and_mk, ifp ⟨hl, h1⟩]; exact BitVec.zero_or
      · obtain ⟨j₀, hj₀, h1, h2, h3⟩ := hs1 hl
        refine ⟨j₀, by omega, h1, h2, ?_⟩
        rw [h3, BitVec.and_assoc, mk_and, and_mk, ifn (fun h' => hl h'.1)]; exact BitVec.or_zero
    · rw [mk_or, mk_not, mk_and, BitVec.or_assoc, mk_or]
      exact congrArg (c₀ ||| ·) (mk_congr hbad.symm)

/-! ## `dropWhile` -/

theorem exists_first {P : Nat → Prop} [DecidablePred P] :
    ∀ n j, j < n → P j → ∃ i ≤ j, P i ∧ ∀ i' < i, ¬ P i'
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, j, hj, pj => by
    by_cases hq : ∃ i < j, P i
    · obtain ⟨i, hi, pi⟩ := hq
      obtain ⟨i', hi', pi', m⟩ := exists_first n i (by omega) pi
      exact ⟨i', by omega, pi', m⟩
    · exact ⟨j, Nat.le_refl _, pj, fun i' hi' pi' => hq ⟨i', hi', pi'⟩⟩

theorem dropWhile_zeros : ∀ (T : List Byte) (j : Nat), (∀ i < j, T.getD i 0 = 0) → j ≤ T.length →
    T.dropWhile (· == 0) = (T.drop j).dropWhile (· == 0)
  | [], _, _, _ => by simp
  | a :: T, 0, _, _ => rfl
  | a :: T, j + 1, h, hl => by
    have ha : a = 0 := h 0 (by omega)
    subst ha
    rw [List.drop_succ_cons, ← dropWhile_zeros T j (fun i hi => h (i + 1) (by omega)) (by simp at hl; omega)]
    rfl

theorem drop_getD (T : List Byte) {j : Nat} (hj : j < T.length) : T.drop j = T.getD j 0 :: T.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem dropWhile_at (T : List Byte) {j : Nat} (hj : j < T.length) (h0 : ∀ i < j, T.getD i 0 = 0)
    (hn : T.getD j 0 ≠ 0) : T.dropWhile (· == 0) = T.getD j 0 :: T.drop (j + 1) := by
  have hb : (T.getD j 0 == 0) = false := by rw [beq_eq_false_iff_ne]; exact hn
  rw [dropWhile_zeros T j h0 (by omega), drop_getD T hj, List.dropWhile_cons, hb]
  rfl

/-- The decoding finds `0x01` after zeros. -/
theorem scan_found (T : List Byte) (c₀ : BitVec 64) (hl : ¬ lk (fun i => T.getD i 0) T.length)
    (hb : ¬ bad (fun i => T.getD i 0) T.length) :
    ∃ j₀ < T.length, (scanS (fun i => T.getD i 0) c₀ T.length).2.1 = BitVec.ofNat 64 j₀ ∧
      T.dropWhile (· == 0) = 1 :: T.drop (j₀ + 1) := by
  obtain ⟨-, -, hs1, -⟩ := scanS_inv (fun i => T.getD i 0) c₀ T.length
  obtain ⟨j₀, hj₀, h1, h2, h3⟩ := hs1 hl
  have h0 : ∀ i < j₀, T.getD i 0 = 0 := fun i hi => by
    by_contra hn; exact hb ⟨i, by omega, fun i' hi' => h2 i' (by omega), hn, h2 i hi⟩
  refine ⟨j₀, hj₀, h3, ?_⟩
  rw [dropWhile_at T hj₀ h0 (by rw [h1]; decide), h1]

/-- Otherwise it fails. -/
theorem scan_fail (T : List Byte)
    (h : lk (fun i => T.getD i 0) T.length ∨ bad (fun i => T.getD i 0) T.length) :
    ∀ m, T.dropWhile (· == 0) ≠ 1 :: m := by
  intro m hm
  by_cases hz : ∃ j < T.length, T.getD j 0 ≠ 0
  · obtain ⟨j, hj, hnz⟩ := hz
    obtain ⟨i, hi, hni, hfirst⟩ := exists_first (P := fun i => T.getD i 0 ≠ 0) T.length j hj hnz
    have h0 : ∀ i' < i, T.getD i' 0 = 0 := fun i' hi' => by
      have := hfirst i' hi'; simp only [ne_eq, Decidable.not_not] at this; exact this
    rw [dropWhile_at T (by omega) h0 hni] at hm
    have h1 : T.getD i 0 = 1 := (List.cons.inj hm).1
    rcases h with hl | ⟨j', hj', hp, hn0, hn1⟩
    · exact hl i (by omega) h1
    · by_cases hij : i < j'
      · exact hp i hij h1
      · have : i = j' := by
          by_contra hne
          exact hn0 (h0 j' (by omega))
        subst this; exact hn1 h1
  · have hall : ∀ i < T.length, T.getD i 0 = 0 := fun i hi => by
      by_contra hn; exact hz ⟨i, hi, hn⟩
    rw [dropWhile_zeros T T.length hall (Nat.le_refl _), List.drop_length] at hm
    cases hm

/-- The index the scan leaves. -/
theorem scan_idx (f : Nat → Byte) (c₀ : BitVec 64) (n : Nat) :
    ∃ idx, (scanS f c₀ n).2.1 = BitVec.ofNat 64 idx ∧ (idx < n ∨ idx = 0) := by
  obtain ⟨-, hs0, hs1, -⟩ := scanS_inv f c₀ n
  by_cases hl : lk f n
  · exact ⟨0, hs0 hl, .inr rfl⟩
  · obtain ⟨j₀, hj₀, -, -, h3⟩ := hs1 hl
    exact ⟨j₀, h3, .inl hj₀⟩

end VG.Proof.RsaOaep
