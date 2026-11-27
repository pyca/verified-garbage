module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds

/-! ### `Dsa.AArch64.Generation.NarrowDivision`, which this module and modules that import it used -/

section

/-!
# DSA parameter generation on AArch64: division by a narrow divisor

`divNarrow k` is `Keys.divmod` for a divisor of at most `64 k - 1` bits
(`divNarrow_ok`): the remainder and the quotient, in the same arrays.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A number of `n + 1` words is its low word and the `n` above. -/
theorem wv_cons (m : Mem) (B : Addr) (e n : Nat) :
    wv m B e (n + 1) = (word m B e).toNat + 2 ^ 64 * wv m B (e + 8) n := by
  rw [Nat.add_comm n 1, wv_add]
  simp [wv]

/-- `narrowShift i n`: the `n` words at `e = eR + 8 i` doubled, with the carry in. -/
theorem narrowShift_ok {B : Addr} {Z eR : Nat} : ∀ (n i : Nat) (s : State), Scr s B Z →
    s.gpr .x16 = off B eR → eR + 8 * (i + n) ≤ Z → i + n ≤ 4096 →
    WP isa (.block (narrowShift i n)) s fun t =>
      (wv t.mem B (eR + 8 * i) n + 2 ^ (64 * n) * t.c.toNat = 2 * wv s.mem B (eR + 8 * i) n + s.c.toNat ∧
        Outside B (eR + 8 * i) (8 * n) s.mem t.mem) ∧ Keep [.x3] s t
  | 0, i, s, _, _, _, _ => by
    rw [narrowShift]
    exact WP.block_nil ⟨⟨by simp [wv], Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | n + 1, i, s, hs, h16, hZ, hi => by
    have hn := hs.nowrap
    obtain h8 : 8 * i % 8 = 0 := Nat.mul_mod_right 8 i
    obtain hlt : 8 * i < 32768 := by omega_using [hi]
    rw [narrowShift, WP.block_append_iff]
    refine WP.mono (WP.keep [.x3] (Q := fun t₁ =>
        t₁.mem = s.mem.writeW (off B (eR + 8 * i)) (word s.mem B (eR + 8 * i) + word s.mem B (eR + 8 * i) +
          BitVec.ofNat 64 s.c.toNat) ∧
        t₁.c = decide (2 ^ 64 ≤ (word s.mem B (eR + 8 * i)).toNat + (word s.mem B (eR + 8 * i)).toNat +
          s.c.toNat))
      (by brun [h16, h8, hlt, hs.ld (show eR + 8 * i + 8 ≤ Z by omega_using [hZ]),
        hs.st (show eR + 8 * i + 8 ≤ Z by omega_using [hZ])])
      rfl rfl rfl) fun t₁ ⟨⟨hm, hc⟩, k₁⟩ => ?_
    refine WP.mono (narrowShift_ok n (i + 1) t₁ (hs.congr k₁.wr) ((k₁.gpr .x16 (by decide)).trans h16)
      (by omega_using [hZ]) (by omega_using [hi])) fun t ⟨⟨hv, ho⟩, k₂⟩ => ⟨⟨?_, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · have e1 : eR + 8 * (i + 1) = eR + 8 * i + 8 := by omega_using []
      rw [e1] at hv ho
      obtain ht0 : word t.mem B (eR + 8 * i) = word s.mem B (eR + 8 * i) + word s.mem B (eR + 8 * i) +
          BitVec.ofNat 64 s.c.toNat := by
        rw [ho.word (Or.inl (Nat.le_refl _)) (by omega_using [hZ, hn]), hm, word_writeW_self]
      obtain hup : wv t₁.mem B (eR + 8 * i + 8) n = wv s.mem B (eR + 8 * i + 8) n := by
        rw [hm]
        exact (writeW_outside s.mem B _ (by omega_using [hZ, hn])).wv (Or.inr (Nat.le_refl _)) (by omega_using [hZ, hn])
      obtain hs' := adcs_toNat (word s.mem B (eR + 8 * i)) (word s.mem B (eR + 8 * i)) s.c
      rw [wv_cons, wv_cons, ht0, pow64_succ]
      rw [hup, hc] at hv
      generalize wv t.mem B (eR + 8 * i + 8) n = X at hv ⊢
      generalize wv s.mem B (eR + 8 * i + 8) n = Y at hv ⊢
      generalize (word s.mem B (eR + 8 * i) + word s.mem B (eR + 8 * i) + BitVec.ofNat 64 s.c.toNat).toNat = a at hs' ⊢
      generalize (word s.mem B (eR + 8 * i)).toNat = b at hs' hv ⊢
      generalize 2 ^ (64 * n) = P at hv ⊢
      grind
    · intro x hx
      rw [ho x (by omega_using [hx]), hm, writeW_outside s.mem B _ (by omega_using [hZ, hn]) x (by omega_using [hx])]

/-- `narrowSub i n`: the `n` words at `eR + 8 i` less those at `eD + 8 i` and the
borrow in, to `eT + 8 i`. -/
theorem narrowSub_ok {B : Addr} {Z eR eD eT K : Nat} (sR : eR + 8 * K ≤ eT ∨ eT + 8 * K ≤ eR)
    (sD : eD + 8 * K ≤ eT ∨ eT + 8 * K ≤ eD) (hR : eR + 8 * K ≤ Z) (hD : eD + 8 * K ≤ Z) (hT : eT + 8 * K ≤ Z)
    (hK : K ≤ 4096) : ∀ (n i : Nat) (s : State), Scr s B Z →
    s.gpr .x16 = off B eR → s.gpr .x17 = off B eD → s.gpr .x8 = off B eT → i + n ≤ K →
    WP isa (.block (narrowSub i n)) s fun t =>
      (wv t.mem B (eT + 8 * i) n + wv s.mem B (eD + 8 * i) n + (!s.c).toNat =
          wv s.mem B (eR + 8 * i) n + 2 ^ (64 * n) * (!t.c).toNat ∧
        Outside B (eT + 8 * i) (8 * n) s.mem t.mem) ∧ Keep [.x3, .x4] s t
  | 0, i, s, _, _, _, _, _ => by
    rw [narrowSub]
    exact WP.block_nil ⟨⟨by simp [wv], Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | n + 1, i, s, hs, h16, h17, h8, hi => by
    have hn := hs.nowrap
    obtain h8m : 8 * i % 8 = 0 := Nat.mul_mod_right 8 i
    obtain hlt : 8 * i < 32768 := by omega_using [hi, hK]
    rw [narrowSub, WP.block_append_iff]
    refine WP.mono (WP.keep [.x3, .x4] (Q := fun t₁ =>
        t₁.mem = s.mem.writeW (off B (eT + 8 * i)) (word s.mem B (eR + 8 * i) + ~~~word s.mem B (eD + 8 * i) +
          BitVec.ofNat 64 s.c.toNat) ∧
        t₁.c = decide (2 ^ 64 ≤ (word s.mem B (eR + 8 * i)).toNat + (~~~word s.mem B (eD + 8 * i)).toNat +
          s.c.toNat))
      (by brun [h16, h17, h8, h8m, hlt, hs.ld (show eR + 8 * i + 8 ≤ Z by omega_using [hR, hi]),
        hs.ld (show eD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
        hs.st (show eT + 8 * i + 8 ≤ Z by omega_using [hT, hi])])
      rfl rfl rfl) fun t₁ ⟨⟨hm, hc⟩, k₁⟩ => ?_
    refine WP.mono (narrowSub_ok sR sD hR hD hT hK n (i + 1) t₁ (hs.congr k₁.wr) ((k₁.gpr .x16 (by decide)).trans h16)
      ((k₁.gpr .x17 (by decide)).trans h17) ((k₁.gpr .x8 (by decide)).trans h8) (by omega_using [hi]))
      fun t ⟨⟨hv, ho⟩, k₂⟩ => ⟨⟨?_, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · have eR1 : eR + 8 * (i + 1) = eR + 8 * i + 8 := by omega_using []
      obtain eD1 : eD + 8 * (i + 1) = eD + 8 * i + 8 := by omega_using []
      obtain eT1 : eT + 8 * (i + 1) = eT + 8 * i + 8 := by omega_using []
      rw [eR1, eD1, eT1] at hv
      rw [eT1] at ho
      obtain o₁ : Outside B (eT + 8 * i) 8 s.mem t₁.mem := by
        rw [hm]; exact writeW_outside s.mem B _ (by omega_using [hT, hi, hn])
      obtain ht0 : word t.mem B (eT + 8 * i) = word s.mem B (eR + 8 * i) + ~~~word s.mem B (eD + 8 * i) +
          BitVec.ofNat 64 s.c.toNat := by
        rw [ho.word (Or.inl (Nat.le_refl _)) (by omega_using [hT, hi, hn]), hm, word_writeW_self]
      obtain hRu : wv t₁.mem B (eR + 8 * i + 8) n = wv s.mem B (eR + 8 * i + 8) n :=
        o₁.wv (by omega_using [sR, hi]) (by omega_using [hR, hi, hn])
      obtain hDu : wv t₁.mem B (eD + 8 * i + 8) n = wv s.mem B (eD + 8 * i + 8) n :=
        o₁.wv (by omega_using [sD, hi]) (by omega_using [hD, hi, hn])
      obtain hs' := sbcs_toNat (word s.mem B (eR + 8 * i)) (word s.mem B (eD + 8 * i)) s.c
      rw [wv_cons, wv_cons, wv_cons, ht0, pow64_succ]
      rw [hRu, hDu, hc] at hv
      generalize wv t.mem B (eT + 8 * i + 8) n = X at hv ⊢
      generalize wv s.mem B (eR + 8 * i + 8) n = Y at hv ⊢
      generalize wv s.mem B (eD + 8 * i + 8) n = W at hv ⊢
      generalize (word s.mem B (eR + 8 * i) + ~~~word s.mem B (eD + 8 * i) + BitVec.ofNat 64 s.c.toNat).toNat = a
        at hs' ⊢
      generalize (!decide (2 ^ 64 ≤ (word s.mem B (eR + 8 * i)).toNat + (~~~word s.mem B (eD + 8 * i)).toNat +
        s.c.toNat)).toNat = b' at hs' hv
      generalize (word s.mem B (eR + 8 * i)).toNat = b at hs' ⊢
      generalize (word s.mem B (eD + 8 * i)).toNat = d at hs' ⊢
      generalize 2 ^ (64 * n) = P at hv ⊢
      grind
    · intro x hx
      rw [ho x (by omega_using [hx]), hm,
        writeW_outside s.mem B _ (by omega_using [hT, hi, hn]) x (by omega_using [hx])]

/-- `narrowSelect i n`: the `n` words at `eT + 8 i` to `eR + 8 i`, if the carry is set. -/
theorem narrowSelect_ok {B : Addr} {Z eR eT K : Nat} (sR : eR + 8 * K ≤ eT ∨ eT + 8 * K ≤ eR)
    (hR : eR + 8 * K ≤ Z) (hT : eT + 8 * K ≤ Z) (hK : K ≤ 4096) : ∀ (n i : Nat) (s : State), Scr s B Z →
    s.gpr .x16 = off B eR → s.gpr .x8 = off B eT → i + n ≤ K →
    WP isa (.block (narrowSelect i n)) s fun t =>
      (wv t.mem B (eR + 8 * i) n = (if s.c then wv s.mem B (eT + 8 * i) n else wv s.mem B (eR + 8 * i) n) ∧
        t.c = s.c ∧ Outside B (eR + 8 * i) (8 * n) s.mem t.mem) ∧ Keep [.x3, .x4] s t
  | 0, i, s, _, _, _, _ => by
    rw [narrowSelect]
    exact WP.block_nil ⟨⟨by simp [wv], rfl, Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | n + 1, i, s, hs, h16, h8, hi => by
    have hn := hs.nowrap
    obtain h8m : 8 * i % 8 = 0 := Nat.mul_mod_right 8 i
    obtain hlt : 8 * i < 32768 := by omega_using [hi, hK]
    rw [narrowSelect, WP.block_append_iff]
    refine WP.mono (WP.keep [.x3, .x4] (Q := fun t₁ =>
        t₁.mem = s.mem.writeW (off B (eR + 8 * i))
          (if s.c then word s.mem B (eT + 8 * i) else word s.mem B (eR + 8 * i)) ∧ t₁.c = s.c)
      (by brun [h16, h8, h8m, hlt, hs.ld (show eR + 8 * i + 8 ≤ Z by omega_using [hR, hi]),
        hs.ld (show eT + 8 * i + 8 ≤ Z by omega_using [hT, hi]),
        hs.st (show eR + 8 * i + 8 ≤ Z by omega_using [hR, hi])])
      rfl rfl rfl) fun t₁ ⟨⟨hm, hc⟩, k₁⟩ => ?_
    refine WP.mono (narrowSelect_ok sR hR hT hK n (i + 1) t₁ (hs.congr k₁.wr) ((k₁.gpr .x16 (by decide)).trans h16)
      ((k₁.gpr .x8 (by decide)).trans h8) (by omega_using [hi]))
      fun t ⟨⟨hv, hct, ho⟩, k₂⟩ => ⟨⟨?_, hct.trans hc, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · have eR1 : eR + 8 * (i + 1) = eR + 8 * i + 8 := by omega_using []
      obtain eT1 : eT + 8 * (i + 1) = eT + 8 * i + 8 := by omega_using []
      rw [eR1, eT1] at hv
      rw [eR1] at ho
      obtain o₁ : Outside B (eR + 8 * i) 8 s.mem t₁.mem := by
        rw [hm]; exact writeW_outside s.mem B _ (by omega_using [hR, hi, hn])
      obtain ht0 : word t.mem B (eR + 8 * i) =
          (if s.c then word s.mem B (eT + 8 * i) else word s.mem B (eR + 8 * i)) := by
        rw [ho.word (Or.inl (Nat.le_refl _)) (by omega_using [hR, hi, hn]), hm, word_writeW_self]
      obtain hRu : wv t₁.mem B (eR + 8 * i + 8) n = wv s.mem B (eR + 8 * i + 8) n :=
        o₁.wv (Or.inr (Nat.le_refl _)) (by omega_using [hR, hi, hn])
      obtain hTu : wv t₁.mem B (eT + 8 * i + 8) n = wv s.mem B (eT + 8 * i + 8) n :=
        o₁.wv (by omega_using [sR, hi]) (by omega_using [hT, hi, hn])
      rw [wv_cons, wv_cons, wv_cons, ht0, hv, hc, hRu, hTu]
      cases s.c <;> rfl
    · intro x hx
      rw [ho x (by omega_using [hx]), hm,
        writeW_outside s.mem B _ (by omega_using [hR, hi, hn]) x (by omega_using [hx])]

/-- One bit of the division: the remainder doubled with the carry, less the
divisor if it is not below it; that as the quotient's bit into `x15`, and
`x14`'s top bit into the carry. -/
theorem narrowBit_ok {s : State} {B : Addr} {Z eR eD eT k : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eR) (h17 : s.gpr .x17 = off B eD) (h8 : s.gpr .x8 = off B eT)
    (h7 : s.gpr .x7 = 0) (sR : eR + 8 * k ≤ eT ∨ eT + 8 * k ≤ eR) (sD : eD + 8 * k ≤ eT ∨ eT + 8 * k ≤ eD)
    (sRD : eR + 8 * k ≤ eD ∨ eD + 8 * k ≤ eR)
    (hR : eR + 8 * k ≤ Z) (hD : eD + 8 * k ≤ Z) (hT : eT + 8 * k ≤ Z) (hk : k ≤ 4096) :
    WP isa (.block (narrowBit k)) s fun t =>
      (2 * wv s.mem B eR k + s.c.toNat < 2 ^ (64 * k) →
        wv t.mem B eR k = (if 2 * wv s.mem B eR k + s.c.toNat < wv s.mem B eD k then
          2 * wv s.mem B eR k + s.c.toNat else 2 * wv s.mem B eR k + s.c.toNat - wv s.mem B eD k) ∧
        t.gpr .x15 = s.gpr .x15 + s.gpr .x15 + BitVec.ofNat 64
          (!decide (2 * wv s.mem B eR k + s.c.toNat < wv s.mem B eD k)).toNat) ∧
      t.gpr .x14 = s.gpr .x14 + s.gpr .x14 ∧ t.c = (s.gpr .x14).msb ∧
      Frm B [(eR, 8 * k), (eT, 8 * k)] s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x15] s t := by
  have hn := hs.nowrap
  unfold narrowBit
  simp only [List.append_assoc]
  -- The remainder doubled.
  refine WP.block_append_iff.mpr (WP.mono (narrowShift_ok k 0 s hs h16 (by omega_using [hR]) (by omega_using [hk]))
    fun s₁ ⟨⟨hv₁, o₁⟩, k₁⟩ => ?_)
  simp only [Nat.mul_zero, Nat.add_zero] at hv₁ o₁
  -- The carry set.
  refine WP.block_append_iff.mpr (WP.mono (WP.keep (c := .block [.subs .x .x3 .x7 .x7]) [.x3]
    (Q := fun t => t.c = true ∧ t.mem = s₁.mem) (by brun [(k₁.gpr .x7 (by decide)).trans h7]) rfl rfl rfl)
    fun s₂ ⟨⟨hc₂, m₂⟩, k₂⟩ => ?_)
  obtain k02 := k₁.trans k₂
  -- The divisor subtracted.
  refine WP.block_append_iff.mpr (WP.mono (narrowSub_ok sR sD hR hD hT hk k 0 s₂ (hs.congr k02.wr)
    ((k02.gpr .x16 (by decide)).trans h16) ((k02.gpr .x17 (by decide)).trans h17)
    ((k02.gpr .x8 (by decide)).trans h8) (by omega_using []))
    fun s₃ ⟨⟨hv₃, o₃⟩, k₃⟩ => ?_)
  simp only [Nat.mul_zero, Nat.add_zero] at hv₃ o₃
  obtain k03 := k02.trans k₃
  -- The selection.
  refine WP.block_append_iff.mpr (WP.mono (narrowSelect_ok sR hR hT hk k 0 s₃ (hs.congr k03.wr)
    ((k03.gpr .x16 (by decide)).trans h16) ((k03.gpr .x8 (by decide)).trans h8) (by omega_using []))
    fun s₄ ⟨⟨hv₄, hc₄, o₄⟩, k₄⟩ => ?_)
  simp only [Nat.mul_zero, Nat.add_zero] at hv₄ o₄
  obtain k04 := k03.trans k₄
  -- The quotient's bit and the dividend's.
  refine WP.mono (WP.keep (c := .block [.adcs .x .x15 .x15 .x15, .adds .x .x14 .x14 .x14]) [.x14, .x15]
    (Q := fun t => t.gpr .x15 = s₄.gpr .x15 + s₄.gpr .x15 + BitVec.ofNat 64 s₄.c.toNat ∧
      t.gpr .x14 = s₄.gpr .x14 + s₄.gpr .x14 ∧
      t.c = decide (2 ^ 64 ≤ (s₄.gpr .x14).toNat + (s₄.gpr .x14).toNat) ∧ t.mem = s₄.mem)
    (by brun; exact ⟨by simp, by simp⟩) rfl rfl rfl) fun t ⟨⟨h15, h14, hc, mt⟩, k₅⟩ => ?_
  obtain e14 : s₄.gpr .x14 = s.gpr .x14 := k04.gpr .x14 (by decide)
  obtain e15 : s₄.gpr .x15 = s.gpr .x15 := k04.gpr .x15 (by decide)
  -- The memory.
  obtain hD₁ : wv s₁.mem B eD k = wv s.mem B eD k := o₁.wv (by omega_using [sRD]) (by omega_using [hD, hn])
  refine ⟨fun hlt => ?_, by rw [h14, e14], ?_, ?_, (k04.trans k₅).mono (by decide)⟩
  · have hR₁lt := wv_lt s₁.mem B eR k
    obtain hc₁ : s₁.c.toNat = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Bool.toNat_le s₁.c) with h | h
      · exact h
      · rw [h] at hv₁; omega_using [hv₁, hlt]
    rw [hc₁, Nat.mul_zero, Nat.add_zero] at hv₁
    rw [m₂, hv₁, hD₁, hc₂] at hv₃
    simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at hv₃
    obtain hb : (!s₃.c) = decide (2 * wv s.mem B eR k + s.c.toNat < wv s.mem B eD k) :=
      lt_of_borrow (wv_lt s₃.mem B eT k) hv₃
    obtain hR₃ : wv s₃.mem B eR k = 2 * wv s.mem B eR k + s.c.toNat := by
      rw [o₃.wv (by omega_using [sR]) (by omega_using [hR, hn]), m₂, hv₁]
    obtain hc₃ : s₃.c = !decide (2 * wv s.mem B eR k + s.c.toNat < wv s.mem B eD k) := by
      rw [← hb, Bool.not_not]
    refine ⟨?_, by rw [h15, e15, hc₄, hc₃]⟩
    rw [mt, hv₄, hR₃]
    by_cases hlt' : 2 * wv s.mem B eR k + s.c.toNat < wv s.mem B eD k
    · rw [hc₃]; simp only [hlt', decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [hc₃]; simp only [hlt', decide_false, Bool.not_false, ↓reduceIte]
      rw [hc₃] at hv₃
      simp only [hlt', decide_false, Bool.not_false, Bool.not_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
        at hv₃
      omega_using [hv₃]
  · rw [hc, e14, BitVec.msb_eq_decide]
    congr 1
    apply propext
    have := (s.gpr .x14).isLt
    constructor <;> intro h <;> omega_using [h]
  · intro x hx
    obtain a := hx (eR, 8 * k) (by simp)
    obtain b := hx (eT, 8 * k) (by simp)
    dsimp only at a b
    rw [mt, o₄ x a, o₃ x b, m₂, o₁ x a]

/-! ## A word of the dividend -/

/-- The remainder `r` with the top `i` bits of the word `n` below it. -/
def narrowAcc (r n i : Nat) : Nat := r * 2 ^ i + n / 2 ^ (64 - i)

theorem getMsbD_toNat (N : BitVec 64) {i : Nat} (hi : i < 64) :
    (N.getMsbD i).toNat = N.toNat / 2 ^ (63 - i) % 2 := by
  rw [BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD, ← Nat.toNat_testBit]
  simp [hi]

theorem narrowAcc_succ (r : Nat) (N : BitVec 64) {i : Nat} (hi : i < 64) :
    narrowAcc r N.toNat (i + 1) = 2 * narrowAcc r N.toNat i + (N.getMsbD i).toNat := by
  rw [getMsbD_toNat N hi, narrowAcc, narrowAcc, show 64 - i = 63 - i + 1 by omega_using [hi],
    show 64 - (i + 1) = 63 - i by omega_using [hi], Nat.pow_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  rw [show r * (2 ^ i * 2) = 2 * (r * 2 ^ i) by rw [← Nat.mul_assoc, Nat.mul_comm]]
  generalize N.toNat / 2 ^ (63 - i) = X
  generalize r * 2 ^ i = Y
  omega_arith

theorem narrowAcc_zero {r : Nat} (N : BitVec 64) : narrowAcc r N.toNat 0 = r := by
  rw [narrowAcc, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt N.isLt, Nat.add_zero]

/-- One step of a restoring division. -/
theorem narrow_div_step {D A b : Nat} (hD : 0 < D) (hb : b ≤ 1) :
    (if 2 * (A % D) + b < D then 2 * (A % D) + b else 2 * (A % D) + b - D) = (2 * A + b) % D ∧
      2 * (A / D) + (!decide (2 * (A % D) + b < D)).toNat = (2 * A + b) / D := by
  obtain hA := Nat.div_add_mod A D
  obtain hm := Nat.mod_lt A hD
  generalize A % D = m at hA hm ⊢
  generalize hq : A / D = q at hA ⊢
  by_cases h : 2 * m + b < D
  · simp only [h, ↓reduceIte, decide_true, Bool.not_true, Bool.toNat_false, Nat.add_zero]
    have := (Nat.div_mod_unique (a := 2 * A + b) (d := 2 * q) (c := 2 * m + b) hD).mpr
      ⟨by rw [Nat.mul_left_comm]; omega_using [hA], h⟩
    exact ⟨this.2.symm, this.1.symm⟩
  · simp only [h, ↓reduceIte, decide_false, Bool.not_false, Bool.toNat_true]
    have := (Nat.div_mod_unique (a := 2 * A + b) (d := 2 * q + 1) (c := 2 * m + b - D) hD).mpr
      ⟨by rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]; omega_using [hA, h], by omega_using [h, hm, hb]⟩
    exact ⟨this.2.symm, this.1.symm⟩

theorem add_self_shl (x : BitVec 64) : x + x = x <<< 1 := by bv_omega

/-- After `i` bits of the word `N`, from `s`. -/
structure BitsInv (s : State) (B : Addr) (Z eR eD eT k : Nat) (N : BitVec 64) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x9, .x14, .x15] s t
  frm : Frm B [(eR, 8 * k), (eT, 8 * k)] s.mem t.mem
  x14 : t.gpr .x14 = N <<< (i + 1)
  c : t.c = N.getMsbD i
  val : 0 < wv s.mem B eD k → 2 * wv s.mem B eD k ≤ 2 ^ (64 * k) → wv s.mem B eR k < wv s.mem B eD k →
    wv t.mem B eR k = narrowAcc (wv s.mem B eR k) N.toNat i % wv s.mem B eD k ∧
    t.gpr .x15 = BitVec.ofNat 64 (narrowAcc (wv s.mem B eR k) N.toNat i / wv s.mem B eD k)

/-- The 64 bits of a word `N`, its top bit in the carry and the rest at the
top of `x14`: the remainder with `N` below it, by the divisor, and the
quotient in `x15`. -/
theorem narrowBits_ok {s : State} {B : Addr} {Z eR eD eT k : Nat} {N : BitVec 64} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eR) (h17 : s.gpr .x17 = off B eD) (h8 : s.gpr .x8 = off B eT)
    (h7 : s.gpr .x7 = 0) (h9 : s.gpr .x9 = BitVec.ofNat 64 64) (h14 : s.gpr .x14 = N <<< 1)
    (h15 : s.gpr .x15 = 0) (hc : s.c = N.msb)
    (sR : eR + 8 * k ≤ eT ∨ eT + 8 * k ≤ eR) (sD : eD + 8 * k ≤ eT ∨ eT + 8 * k ≤ eD)
    (sRD : eR + 8 * k ≤ eD ∨ eD + 8 * k ≤ eR)
    (hR : eR + 8 * k ≤ Z) (hD : eD + 8 * k ≤ Z) (hT : eT + 8 * k ≤ Z) (hk : k ≤ 4096) :
    WP isa (countLoop .x9 (narrowBit k)) s fun t =>
      Scr t B Z ∧ Frm B [(eR, 8 * k), (eT, 8 * k)] s.mem t.mem ∧ Keep [.x3, .x4, .x9, .x14, .x15] s t ∧
      (0 < wv s.mem B eD k → 2 * wv s.mem B eD k ≤ 2 ^ (64 * k) → wv s.mem B eR k < wv s.mem B eD k →
        wv t.mem B eR k = (wv s.mem B eR k * 2 ^ 64 + N.toNat) % wv s.mem B eD k ∧
        t.gpr .x15 = BitVec.ofNat 64 ((wv s.mem B eR k * 2 ^ 64 + N.toNat) / wv s.mem B eD k)) := by
  have hn := hs.nowrap
  obtain h0 : BitsInv s B Z eR eD eT k N 0 s :=
    ⟨hs, Keep.refl _ _, Frm.refl _ _ _, h14, hc, fun hD0 _ hr => by
      rw [narrowAcc_zero, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr]; exact ⟨rfl, h15⟩⟩
  unfold countLoop
  refine WP.mono (wp_countdown (N := 64) (by decide) (by decide) (BitsInv s B Z eR eD eT k N)
    (fun i hi t hI _ => ?_) h0 h9) fun t hI => ⟨hI.scr, hI.frm, hI.keep, fun hD0 hD2 hr => ?_⟩
  · have hDt : wv t.mem B eD k = wv s.mem B eD k :=
      hI.frm.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega_using [sD, sRD]) (by omega_using [hD, hn])
    refine WP.block_append_iff.mpr (WP.mono (narrowBit_ok hI.scr ((hI.keep.gpr .x16 (by decide)).trans h16)
      ((hI.keep.gpr .x17 (by decide)).trans h17) ((hI.keep.gpr .x8 (by decide)).trans h8)
      ((hI.keep.gpr .x7 (by decide)).trans h7) sR sD sRD hR hD hT hk)
      fun t₁ ⟨hv, h14₁, hc₁, f₁, k₁⟩ => ?_)
    refine WP.mono (dec_ok t₁ .x9) fun t' ⟨⟨h9', m', c'⟩, k'⟩ => ⟨?_, by rw [h9', k₁.gpr .x9 (by decide)]⟩
    refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
      by rw [m']; exact hI.frm.trans f₁,
      by rw [k'.gpr .x14 (by decide), h14₁, hI.x14, add_self_shl, ← BitVec.shiftLeft_add],
      by rw [c', hc₁, hI.x14, BitVec.msb_shiftLeft], fun hD0 hD2 hr => ?_⟩
    obtain ⟨hRt, h15t⟩ := hI.val hD0 hD2 hr
    obtain hb : t.c.toNat ≤ 1 := Bool.toNat_le _
    obtain hml := Nat.mod_lt (narrowAcc (wv s.mem B eR k) N.toNat i) hD0
    obtain ⟨hR₁, h15₁⟩ := hv (by rw [hRt]; omega_using [hml, hD2, hb])
    rw [hRt, hDt] at hR₁ h15₁
    obtain ⟨e₁, e₂⟩ := narrow_div_step (A := narrowAcc (wv s.mem B eR k) N.toNat i) hD0 hb
    rw [narrowAcc_succ _ N hi, ← hI.c, m', hR₁, e₁]
    refine ⟨rfl, ?_⟩
    rw [k'.gpr .x15 (by decide), h15₁, h15t, ofNat_add_ofNat, ofNat_add_ofNat, ← Nat.two_mul, e₂]
  · obtain ⟨hRt, h15t⟩ := hI.val hD0 hD2 hr
    rw [narrowAcc, Nat.sub_self, Nat.pow_zero, Nat.div_one] at hRt h15t
    exact ⟨hRt, h15t⟩

theorem off_sub8 (B : Addr) (e : Nat) : off B (e + 8) - BitVec.ofNat 64 8 = off B e := by
  simp only [off, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `narrowWord k`: the word below `x13` taken into the remainder, and the
quotient's word in its place. -/
theorem narrowWord_ok {s : State} {B : Addr} {Z eR eD eT k eW : Nat} (hs : Scr s B Z)
    (h13 : s.gpr .x13 = off B (eW + 8))
    (h16 : s.gpr .x16 = off B eR) (h17 : s.gpr .x17 = off B eD) (h8 : s.gpr .x8 = off B eT)
    (h7 : s.gpr .x7 = 0)
    (sR : eR + 8 * k ≤ eT ∨ eT + 8 * k ≤ eR) (sD : eD + 8 * k ≤ eT ∨ eT + 8 * k ≤ eD)
    (sRD : eR + 8 * k ≤ eD ∨ eD + 8 * k ≤ eR)
    (sWR : eW + 8 ≤ eR ∨ eR + 8 * k ≤ eW)
    (hW : eW + 8 ≤ Z) (hR : eR + 8 * k ≤ Z) (hD : eD + 8 * k ≤ Z) (hT : eT + 8 * k ≤ Z) (hk : k ≤ 4096) :
    WP isa (narrowWord k) s fun t =>
      t.gpr .x13 = off B eW ∧ t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      Frm B [(eW, 8), (eR, 8 * k), (eT, 8 * k)] s.mem t.mem ∧
      Keep [.x3, .x4, .x6, .x9, .x13, .x14, .x15] s t ∧
      (0 < wv s.mem B eD k → 2 * wv s.mem B eD k ≤ 2 ^ (64 * k) → wv s.mem B eR k < wv s.mem B eD k →
        wv t.mem B eR k = (wv s.mem B eR k * 2 ^ 64 + (word s.mem B eW).toNat) % wv s.mem B eD k ∧
        word t.mem B eW =
          BitVec.ofNat 64 ((wv s.mem B eR k * 2 ^ 64 + (word s.mem B eW).toNat) / wv s.mem B eD k)) := by
  have hn := hs.nowrap
  unfold narrowWord
  -- The word, its top bit in the carry.
  refine WP.seq (WP.mono (WP.keep [.x9, .x13, .x14, .x15] (Q := fun t => t.gpr .x13 = off B eW ∧
      t.gpr .x14 = word s.mem B eW <<< 1 ∧ t.gpr .x15 = 0 ∧ t.gpr .x9 = BitVec.ofNat 64 64 ∧
      t.c = (word s.mem B eW).msb ∧ t.mem = s.mem)
    (by
      brun [h13, off_sub8, hs.ld (show eW + 8 ≤ Z from hW), BitVec.msb_eq_decide]
      refine ⟨by rw [← add_self_shl]; simp [word], ?_⟩
      congr 1
      apply propext
      have := (s.mem.readW (off B eW) 64).isLt
      simp only [word, Bool.toNat_false, Nat.add_zero]
      constructor <;> intro h <;> omega_using [h, this])
    rfl rfl rfl) fun s₁ ⟨⟨h13₁, h14₁, h15₁, h9₁, hc₁, m₁⟩, k₁⟩ => ?_)
  -- Its 64 bits.
  refine WP.seq (WP.mono (narrowBits_ok (N := word s.mem B eW) (hs.congr k₁.wr)
    ((k₁.gpr .x16 (by decide)).trans h16) ((k₁.gpr .x17 (by decide)).trans h17)
    ((k₁.gpr .x8 (by decide)).trans h8) ((k₁.gpr .x7 (by decide)).trans h7) h9₁ h14₁ h15₁ hc₁
    sR sD sRD hR hD hT hk) fun s₂ ⟨hs₂, f₂, k₂, hv₂⟩ => ?_)
  rw [m₁] at f₂ hv₂
  obtain k02 := k₁.trans k₂
  -- The quotient's word.
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = s₂.gpr .x6 - BitVec.ofNat 64 1 ∧
      t.mem = s₂.mem.writeW (off B eW) (s₂.gpr .x15))
    (by brun [(k₂.gpr .x13 (by decide)).trans h13₁, hs₂.st (show eW + 8 ≤ Z from hW)])
    rfl rfl rfl) fun t ⟨⟨h6, mt⟩, k₃⟩ => ?_
  obtain ot : Outside B eW 8 s₂.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by omega_using [hW, hn])
  refine ⟨(k₃.gpr .x13 (by decide)).trans ((k₂.gpr .x13 (by decide)).trans h13₁),
    by rw [h6, k02.gpr .x6 (by decide)], ?_, (k02.trans k₃).mono (by decide), fun hD0 hD2 hr => ?_⟩
  · intro x hx
    obtain a := hx (eW, 8) (by simp)
    rw [ot x a, f₂ x (fun r hr => hx r (List.mem_cons_of_mem _ hr))]
  · obtain ⟨hR₂, h15₂⟩ := hv₂ hD0 hD2 hr
    refine ⟨?_, by rw [mt, word_writeW_self, h15₂]⟩
    rw [ot.wv (by omega_using [sWR]) (by omega_using [hR, hn]), hR₂]

/-! ## The division -/

/-- A word `n` below the dividend's top words `H`: the remainder and the
quotient's word from the remainder of `H`. -/
theorem narrow_word {H n D : Nat} (hD : 0 < D) :
    (H % D * 2 ^ 64 + n) % D = (n + 2 ^ 64 * H) % D ∧
      (H % D * 2 ^ 64 + n) / D + 2 ^ 64 * (H / D) = (n + 2 ^ 64 * H) / D := by
  obtain e : n + 2 ^ 64 * H = H % D * 2 ^ 64 + n + D * (2 ^ 64 * (H / D)) := by
    obtain hH := Nat.div_add_mod H D
    rw [Nat.mul_left_comm, Nat.mul_comm (H % D)]
    have : 2 ^ 64 * H = 2 ^ 64 * (D * (H / D)) + 2 ^ 64 * (H % D) := by rw [← Nat.mul_add, hH]
    omega_using [this]
  rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hD]
  exact ⟨rfl, rfl⟩

theorem narrow_word_lt {r n D : Nat} (hr : r < D) (hn : n < 2 ^ 64) : (r * 2 ^ 64 + n) / D < 2 ^ 64 := by
  apply Nat.div_lt_of_lt_mul
  have : (r + 1) * 2 ^ 64 ≤ D * 2 ^ 64 := Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_using [this, hn]

/-- After `j` words of the dividend at `eQ`, from the top, from `s`. -/
structure WordsInv (s : State) (B : Addr) (Z eQ eR eD eT k w : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x6, .x9, .x13, .x14, .x15] s t
  x13 : t.gpr .x13 = off B (eQ + 8 * (w - j))
  frm : Frm B [(eQ + 8 * (w - j), 8 * j), (eR, 8 * k), (eT, 8 * k)] s.mem t.mem
  val : 0 < wv s.mem B eD k → 2 * wv s.mem B eD k ≤ 2 ^ (64 * k) → wv s.mem B eR k = 0 →
    wv t.mem B eR k = wv s.mem B (eQ + 8 * (w - j)) j % wv s.mem B eD k ∧
    wv t.mem B (eQ + 8 * (w - j)) j = wv s.mem B (eQ + 8 * (w - j)) j / wv s.mem B eD k

/-- The loop over the dividend's words: its remainder by the divisor, from a
remainder of zero, and the quotient in its place. -/
theorem narrowWords_ok {s : State} {B : Addr} {Z eQ eR eD eT k w : Nat} (hs : Scr s B Z)
    (h13 : s.gpr .x13 = off B (eQ + 8 * w)) (h6 : s.gpr .x6 = BitVec.ofNat 64 w)
    (h16 : s.gpr .x16 = off B eR) (h17 : s.gpr .x17 = off B eD) (h8 : s.gpr .x8 = off B eT)
    (h7 : s.gpr .x7 = 0) (hw1 : 1 ≤ w) (hw : w < 2 ^ 24)
    (sR : eR + 8 * k ≤ eT ∨ eT + 8 * k ≤ eR) (sD : eD + 8 * k ≤ eT ∨ eT + 8 * k ≤ eD)
    (sRD : eR + 8 * k ≤ eD ∨ eD + 8 * k ≤ eR)
    (sQR : eQ + 8 * w ≤ eR ∨ eR + 8 * k ≤ eQ) (sQT : eQ + 8 * w ≤ eT ∨ eT + 8 * k ≤ eQ)
    (sQD : eQ + 8 * w ≤ eD ∨ eD + 8 * k ≤ eQ)
    (hQ : eQ + 8 * w ≤ Z) (hR : eR + 8 * k ≤ Z) (hD : eD + 8 * k ≤ Z) (hT : eT + 8 * k ≤ Z) (hk : k ≤ 4096) :
    WP isa (.loop (narrowWord k) (.nonzero .x .x6)) s fun t =>
      Frm B [(eQ, 8 * w), (eR, 8 * k), (eT, 8 * k)] s.mem t.mem ∧
      Keep [.x3, .x4, .x6, .x9, .x13, .x14, .x15] s t ∧
      (0 < wv s.mem B eD k → 2 * wv s.mem B eD k ≤ 2 ^ (64 * k) → wv s.mem B eR k = 0 →
        wv t.mem B eR k = wv s.mem B eQ w % wv s.mem B eD k ∧
        wv t.mem B eQ w = wv s.mem B eQ w / wv s.mem B eD k) := by
  have hn := hs.nowrap
  obtain h0 : WordsInv s B Z eQ eR eD eT k w 0 s :=
    ⟨hs, Keep.refl _ _, by rw [Nat.sub_zero]; exact h13, Frm.refl _ _ _, fun hD0 _ hr => by
      rw [hr]; simp [wv]⟩
  refine WP.mono (wp_countdown (N := w) (by omega_using [hw]) (by omega_using [hw1])
    (WordsInv s B Z eQ eR eD eT k w) (fun j hj t hI _ => ?_) h0 h6) fun t hI => ⟨?_, hI.keep, fun hD0 hD2 hr => ?_⟩
  · -- One word.
    obtain e₁ : eQ + 8 * (w - j) = eQ + 8 * (w - (j + 1)) + 8 := by omega_using [hj]
    have hI13 := hI.x13
    rw [e₁] at hI13
    obtain hDt : wv t.mem B eD k = wv s.mem B eD k :=
      hI.frm.wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [sD, sRD, sQD, hj]) (by omega_using [hD, hn])
    obtain hWt : word t.mem B (eQ + 8 * (w - (j + 1))) = word s.mem B (eQ + 8 * (w - (j + 1))) :=
      hI.frm.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [sQR, sQT, hj]) (by omega_using [hQ, hn, hj])
    refine WP.mono (narrowWord_ok (eW := eQ + 8 * (w - (j + 1))) hI.scr hI13
      ((hI.keep.gpr .x16 (by decide)).trans h16) ((hI.keep.gpr .x17 (by decide)).trans h17)
      ((hI.keep.gpr .x8 (by decide)).trans h8) ((hI.keep.gpr .x7 (by decide)).trans h7) sR sD sRD
      (by omega_using [sQR, hj]) (by omega_using [hQ, hj]) hR hD hT hk)
      fun t' ⟨h13', h6', f', k', hv'⟩ => ⟨⟨hI.scr.congr k'.wr, (hI.keep.trans k').mono (by decide), h13', ?_,
        fun hD0 hD2 hr => ?_⟩, h6'⟩
    · intro x hx
      obtain a := hx (eQ + 8 * (w - (j + 1)), 8 * (j + 1)) (by simp)
      obtain b := hx (eR, 8 * k) (by simp)
      obtain c := hx (eT, 8 * k) (by simp)
      dsimp only at a b c
      rw [f' x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_using [a, b, c]),
        hI.frm x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_using [a, b, c, hj])]
    · obtain ⟨hRt, hQt⟩ := hI.val hD0 hD2 hr
      obtain hml := Nat.mod_lt (wv s.mem B (eQ + 8 * (w - j)) j) hD0
      rw [hDt, hRt, hWt] at hv'
      obtain ⟨hR', hW'⟩ := hv' hD0 hD2 hml
      obtain hQ' : wv t'.mem B (eQ + 8 * (w - (j + 1)) + 8) j = wv t.mem B (eQ + 8 * (w - (j + 1)) + 8) j :=
        f'.wv_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [sQR, sQT, hj]) (by omega_using [hQ, hn, hj])
      obtain ⟨m₁, m₂⟩ := narrow_word (H := wv s.mem B (eQ + 8 * (w - j)) j)
        (n := (word s.mem B (eQ + 8 * (w - (j + 1)))).toNat) hD0
      obtain hlt := narrow_word_lt hml (word s.mem B (eQ + 8 * (w - (j + 1)))).isLt
      rw [wv_cons, wv_cons, hQ', hW', hR', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ← e₁, hQt]
      exact ⟨m₁, m₂⟩
  · have f := hI.frm
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at f
    exact f
  · have := hI.val hD0 hD2 hr
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at this
    exact this

/-- `divNarrow k`: as `divmod`, the remainder of `[q]` by `[d]` into `[r]`
(`w + 1` words) and the quotient into `[q]`, for a divisor `[d]` that is not
zero with `2 [d] ≤ 2^(64 k)`. -/
theorem divNarrow_ok {s : State} {B : Addr} {Z w k : Nat} {iQ iR iD iT : Nat} (h : Ws s B Z w) (hk : k ≤ w)
    (hk' : k ≤ 4096)     (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16) (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT)
    (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT) :
    WP isa (divNarrow k iQ iR iD iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iQ, ar w iR, ar w iT] s.mem t.mem ∧ Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (0 < wv s.mem B (slot w iD) w → 2 * wv s.mem B (slot w iD) w ≤ 2 ^ (64 * k) →
        wv t.mem B (slot w iR) (w + 1) = wv s.mem B (slot w iQ) w % wv s.mem B (slot w iD) w ∧
        wv t.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w / wv s.mem B (slot w iD) w) := by
  have hs := h.scr
  have hn := hs.nowrap
  obtain hw1 : 1 ≤ w := by have := h.w1; omega_using [this]
  have hw := h.w2
  obtain sQ := h.sl hQ
  obtain sR := h.sl hR
  obtain sD := h.sl hD
  obtain sT := h.sl hT
  obtain pQR := slot_sep (w := w) dQR
  obtain pQD := slot_sep (w := w) dQD
  obtain pQT := slot_sep (w := w) dQT
  obtain pRD := slot_sep (w := w) dRD
  obtain pRT := slot_sep (w := w) dRT
  obtain pDT := slot_sep (w := w) dDT
  unfold divNarrow
  simp only [List.append_assoc]
  -- `[r] := 0`.
  refine WP.seq (WP.mono (zeroA_ok h hR) fun s₁ ⟨hz, ho, h12₁, h11₁, h7₁, k₁⟩ => ?_)
  obtain h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  -- The bases, and the count.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iQ .x13 h0₁ h11₁) fun s₂ ⟨⟨h13₂, m₂, _⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x6, .x13] (Q := fun t =>
        t.gpr .x13 = off B (slot w iQ + 8 * w) ∧ t.gpr .x6 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem)
      (by
        brun [h13₂, (k₂.gpr .x12 (by decide)).trans h12₁, shl_ofNat (show w * 2 ^ 3 < 2 ^ 64 by omega_using [hw])]
        congr 2; omega_using [])
      rfl rfl rfl) fun s₃ ⟨⟨h13₃, h6₃, m₃⟩, k₃⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok iR .x16 ((k₂.trans k₃ |>.gpr .x0 (by decide)).trans h0₁)
      ((k₂.trans k₃ |>.gpr .x11 (by decide)).trans h11₁)) fun s₄ ⟨⟨h16₄, m₄, _⟩, k₄⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok iD .x17 (((k₂.trans k₃).trans k₄ |>.gpr .x0 (by decide)).trans h0₁)
      (((k₂.trans k₃).trans k₄ |>.gpr .x11 (by decide)).trans h11₁)) fun s₅ ⟨⟨h17₅, m₅, _⟩, k₅⟩ =>
    WP.mono (base_ok iT .x8 ((((k₂.trans k₃).trans k₄).trans k₅ |>.gpr .x0 (by decide)).trans h0₁)
      ((((k₂.trans k₃).trans k₄).trans k₅ |>.gpr .x11 (by decide)).trans h11₁)) fun s₆ ⟨⟨h8₆, m₆, _⟩, k₆⟩ => ?_)))))
  obtain k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  obtain m₆' : s₆.mem = s₁.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  -- The loop.
  refine WP.mono (narrowWords_ok (eQ := slot w iQ) (eR := slot w iR) (eD := slot w iD) (eT := slot w iT) (k := k)
    (w := w) (hs.congr (k₁.trans k26).wr) ((k₄.trans k₅ |>.trans k₆ |>.gpr .x13 (by decide)).trans h13₃)
    ((k₄.trans k₅ |>.trans k₆ |>.gpr .x6 (by decide)).trans h6₃)
    ((k₅.trans k₆ |>.gpr .x16 (by decide)).trans h16₄) ((k₆.gpr .x17 (by decide)).trans h17₅) h8₆
    ((k26.gpr .x7 (by decide)).trans h7₁) hw1 hw (by omega_using [pRT, hk]) (by omega_using [pDT, hk])
    (by omega_using [pRD, hk]) (by omega_using [pQR, hk]) (by omega_using [pQT, hk]) (by omega_using [pQD, hk])
    (by omega_using [sQ]) (by omega_using [sR, hk]) (by omega_using [sD, hk]) (by omega_using [sT, hk])
    hk') fun t ⟨ft, kt, hv⟩ => ?_
  rw [m₆'] at ft hv
  refine ⟨((k26.trans kt).gpr .x0 (by decide)).trans h0₁, ?_, (k₁.trans (k26.trans kt)).mono (by decide),
    fun hD0 hD2 => ?_⟩
  · intro x hx
    obtain a := hx (ar w iQ) (by simp)
    obtain b := hx (ar w iR) (by simp)
    obtain c := hx (ar w iT) (by simp)
    dsimp only at a b c
    rw [ft x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_using [a, b, c, hk]), ho x b]
  · have hDlt : wv s.mem B (slot w iD) w < 2 ^ (64 * k) := by omega_using [hD0, hD2]
    obtain hD₁ : wv s₁.mem B (slot w iD) k = wv s.mem B (slot w iD) w := by
      rw [ho.wv (by omega_using [pRD, hk]) (by omega_using [sD, hn, hk]), wv_low_of_lt hk hDlt]
    obtain hQ₁ : wv s₁.mem B (slot w iQ) w = wv s.mem B (slot w iQ) w :=
      ho.wv (by omega_using [pQR]) (by omega_using [sQ, hn])
    obtain hR₁ : wv s₁.mem B (slot w iR) k = 0 := by
      rw [wv_low_of_lt (w := w + 2) (by omega_using [hk]) (by rw [hz]; exact Nat.two_pow_pos _), hz]
    rw [hD₁, hQ₁] at hv
    obtain ⟨vr, vq⟩ := hv hD0 hD2 hR₁
    refine ⟨?_, vq⟩
    obtain hz' : ∀ q < w + 2, word s₁.mem B (slot w iR + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
    obtain e := wv_add t.mem B (slot w iR) k (w + 1 - k)
    rw [show k + (w + 1 - k) = w + 1 by omega_using [hk]] at e
    rw [e, vr, wv_zero (n := w + 1 - k) fun q hq => by
      rw [ft.word_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using [pQR, pRT, hk, hq])
        (by omega_using [sR, hn, hq]), Nat.add_assoc, ← Nat.mul_add]
      exact hz' _ (by omega_using [hq])]
    simp

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.Double`, which only this module used -/

section

/-! Doubling the subgroup order and the saved generator exponent in native code. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem doubleArray_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16)
    (hfit : 2 * wv s.mem B (slot w dst) w < 2 ^ (64 * w)) :
    WP isa (Impl.Dsa.AArch64.Generation.doubleArray dst) s fun t =>
      wv t.mem B (slot w dst) w = 2 * wv s.mem B (slot w dst) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have sd := h.sl hd
  unfold Impl.Dsa.AArch64.Generation.doubleArray
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, hm₁, _⟩, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x7, .x14, .x3]
    (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s₁.mem)
    (by brun [h12]) rfl rfl rfl) fun s₂ ⟨⟨h14, hc, hm₂⟩, k₂⟩ => ?_)
  refine WP.mono (base_ok dst .x16 (((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h16, hm₃, hc₃⟩, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  refine WP.mono (shl_ok (h.scr.congr k.wr) h16
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.w1; omega_using [this])
    (by have := h.w2; omega_using [this]) (by omega_using [sd])) fun t ⟨hv, _, ho, kt⟩ => ?_
  rw [hc₃, hc, hm₃, hm₂, hm₁] at hv
  rw [hm₃, hm₂, hm₁] at ho
  refine ⟨?_, ho, (k.trans kt).mono (by decide)⟩
  cases he : t.c <;> rw [he] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.CandidateReduction`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.Reduce`, which only this module used -/

section

/-! # Native remainder subtraction and increment implement p reduction -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Subtract.lean`, which only this module imported.
section

/-! Reuse RSA's array subtraction for the candidate's division remainder. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem subtractRemainder_ok {s : State} {B : Addr} {Z w dst src rem : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hle : wv s.mem B (slot w rem) w ≤ wv s.mem B (slot w src) w) :
    WP isa (seqs (subA dst src rem)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w src) w - wv s.mem B (slot w rem) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (subA_ok h hd hx hr (.inr hdx) hdr) fun t ⟨hv, ho, _, _, _, hk⟩ => ?_
  refine ⟨?_, ho, hk.mono (by decide)⟩
  have hxlt := wv_lt s.mem B (slot w src) w
  have holt := wv_lt t.mem B (slot w dst) w
  cases hc : (!t.c) <;> rw [hc] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Increment.lean`, which only this module imported.
section

/-! The even candidate difference can be incremented without carry propagation. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

private theorem low_word {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B e).toNat + 2 ^ 64 * wv m B (e + 8) (w - 1) := by
  have h := wv_add m B e 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at h
  simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one] using h

theorem incrementEven_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (heven : wv s.mem B (slot w dst) w % 2 = 0) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.incrementEven dst)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w dst) w + 1 ∧
      Outside B (slot w dst) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have sd := h.sl hd
  have hw : 1 ≤ w := by have := h.w1; omega
  unfold Impl.Dsa.AArch64.Generation.incrementEven
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, hm₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok dst .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, hm₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem =
    s.mem.writeW (off B (slot w dst)) (word s.mem B (slot w dst) + 1))
    (by brun [h16, hs₂.ld (d := slot w dst) (by omega), hs₂.st (d := slot w dst) (by omega), hm₂, hm₁]; rfl)
    rfl rfl rfl) fun t ⟨hm, k₃⟩ => ?_
  have ho : Outside B (slot w dst) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega)
  refine ⟨?_, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₀ := low_word (m := s.mem) (B := B) (e := slot w dst) hw
  have e₁ := low_word (m := t.mem) (B := B) (e := slot w dst) hw
  have hu := ho.wv (d := slot w dst + 8) (k := w - 1) (Or.inr (by omega)) (by omega)
  have hv : word t.mem B (slot w dst) = word s.mem B (slot w dst) + 1 := by
    rw [hm, word_writeW_self]
  have hlo := (word s.mem B (slot w dst)).isLt
  rw [e₀] at heven
  have hb : (word s.mem B (slot w dst)).toNat + 1 < 2 ^ 64 := by omega
  rw [e₁, hu, hv, BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using hb), e₀]
  change (word s.mem B (slot w dst)).toNat + 1 + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) =
    (word s.mem B (slot w dst)).toNat + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) + 1
  omega_using []

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.Generation VG.Proof.MlKem.AArch64

private theorem low_of_lt {m : Mem} {B : Addr} {e v w : Nat} (hv : v ≤ w)
    (h : wv m B e w < 2 ^ (64 * v)) : wv m B e v = wv m B e w := by
  have e1 := wv_add m B e v (w - v)
  rw [show v + (w - v) = w by omega_using [hv]] at e1
  have hz : wv m B (e + 8 * v) (w - v) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (e + 8 * v) (w - v)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * wv m B (e + 8 * v) (w - v) := Nat.le_mul_of_pos_right _ h0
      omega_using [h, e1, this]
  rw [e1, hz]; simp

theorem reduceRemainder_ok {s : State} {B : Addr} {Z w dst src rem x q : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hval : wv s.mem B (slot w src) w = x)
    (hrem : wv s.mem B (slot w rem) (w + 1) = x % (2 * q)) :
    WP isa (.seq (seqs (subA dst src rem))
      (.block (Impl.Dsa.AArch64.Generation.incrementEven dst))) s fun t =>
      wv t.mem B (slot w dst) w = x + 1 - x % (2 * q) ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hmod := Nat.mod_le x (2 * q)
  have hbound : x < 2 ^ (64 * w) := hval ▸ wv_lt s.mem B (slot w src) w
  have hrem' : wv s.mem B (slot w rem) w = x % (2 * q) := by
    rw [low_of_lt (Nat.le_succ w) (by rw [hrem]; omega_using [hmod, hbound]), hrem]
  refine WP.seq (WP.mono (subtractRemainder_ok h hd hx hr hdx hdr
    (by rw [hval, hrem']; exact hmod)) fun u ⟨hu, ho, ku⟩ => ?_)
  rw [hval, hrem'] at hu
  have hf : Frm B [(slot w dst, 8 * w)] s.mem u.mem := Frm.of_outside ho (by simp)
  have hwu := h.congr hf
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w dst (8 * w))
    ku (by decide)
  have he : wv u.mem B (slot w dst) w % 2 = 0 := by
    rw [hu]
    have hm := Nat.mod_add_div x (2 * q)
    have hv : x - x % (2 * q) = 2 * q * (x / (2 * q)) := by omega_using [hm]
    rw [hv]
    simp [Nat.mul_assoc]
  refine WP.mono (incrementEven_ok hwu hd he) fun t ⟨ht, hot, kt⟩ => ?_
  refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [ht, hu, pReduction_sub]
  · intro a ha
    rw [hot a (by have := h.w1; omega_using [ha, this]), ho a ha]

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Complete native p-candidate reduction, retaining the quotient -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum.AArch64
open VG.Impl.Rsa.AArch64.Keys VG.Proof.Dsa.Generation VG.Proof.Rsa

theorem reduceCandidate_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q)
    (hwide : Impl.Dsa.AArch64.Generation.reduceWords ≤ w)
    (hnarrow : 2 * (2 * q) ≤ 2 ^ (64 * Impl.Dsa.AArch64.Generation.reduceWords)) :
    WP isa Impl.Dsa.AArch64.Generation.reduceCandidate s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = x / (2 * q) ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hr : ∀ j < 16, slot w j + 8 * w ≤ 2 ^ 64 := by
    intro j hj; have := h.sl hj; omega_using [hn, this]
  unfold Impl.Dsa.AArch64.Generation.reduceCandidate
  refine WP.seq (WP.mono (copyA_ok h (by decide : 4 < 16) (by decide : 0 < 16) (by decide))
    fun u ⟨hu, hou, _, _, ku⟩ => ?_)
  have fu : Frm B [ar w 4] s.mem u.mem :=
    Frm.of_outside (hou.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have wu := h.congr fu (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w 4 _) ku (by decide)
  have ux : wv u.mem B (slot w 0) w = x := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 0 (by decide))]; exact hx
  have uq : wv u.mem B (slot w 2) w = 2 * q := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 2 (by decide))]; exact hq
  refine WP.seq (WP.mono (divNarrow_ok wu hwide (by decide) (iQ := 0) (iR := 1) (iD := 2) (iT := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun v ⟨_, fv, kv, hmath⟩ => ?_)
  obtain ⟨vr, vq⟩ := hmath (by rw [uq]; omega_using [hqpos]) (by rw [uq]; exact hnarrow)
  rw [ux, uq] at vr vq
  have wv' := wu.congr fv (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) kv (by decide)
  have vx : wv v.mem B (slot w 4) w = x := by
    rw [fv.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 4 (by decide)), hu, hx]
  refine WP.mono (reduceRemainder_ok wv' (by decide : 5 < 16) (by decide : 4 < 16)
    (by decide : 1 < 16) (by decide) (by decide) vx vr) fun t ⟨tp, hot, kt⟩ => ?_
  have ft : Frm B [ar w 5] v.mem t.mem :=
    Frm.of_outside (hot.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have wt := wv'.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, tp, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 0 (by decide)), vq]
  · exact (fu.append (fv.append ft)).mono (by simp)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The byte-to-integer bridge for p-candidate arithmetic -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ReductionExponent.lean`, which only this module imported.
section

/-! # Candidate reduction also produces the generator exponent -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Rsa VG.Proof.Dsa.Generation

theorem reduceExponent_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q)
    (hwide : Impl.Dsa.AArch64.Generation.reduceWords ≤ w)
    (hnarrow : 2 * (2 * q) ≤ 2 ^ (64 * Impl.Dsa.AArch64.Generation.reduceWords)) :
    WP isa (.seq Impl.Dsa.AArch64.Generation.reduceCandidate
      (Impl.Dsa.AArch64.Generation.doubleArray 0)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = (x + 1 - x % (2 * q) - 1) / q ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hxlt : x < 2 ^ (64 * w) := hx ▸ wv_lt s.mem B (slot w 0) w
  have he : 2 * (x / (2 * q)) ≤ x := by
    calc
      2 * (x / (2 * q)) ≤ q * (2 * (x / (2 * q))) := Nat.le_mul_of_pos_left _ hqpos
      _ = 2 * q * (x / (2 * q)) := by ac_rfl
      _ ≤ x := Nat.mul_div_le x (2 * q)
  refine WP.seq (WP.mono (reduceCandidate_ok h hx hq hqpos hwide hnarrow) fun u ⟨hu, hp, hquot, hf, hk⟩ => ?_)
  refine WP.mono (doubleArray_ok hu (by decide : 0 < 16) (by rw [hquot]; omega))
    fun t ⟨ht, ho, kt⟩ => ?_
  have ft : Frm B [ar w 0] u.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have wt := hu.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, ?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      simp only [slot, hdrBytes]; omega) (by have := h.sl (by decide : 5 < 16); have := h.scr.nowrap; omega), hp]
  · rw [ht, hquot, pReduction_generatorExponent x hqpos]
  · exact hf.trans (ft.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Rsa

private theorem pow_mul_pow_le {a b c : Nat} (h : a + b ≤ c) : 2 ^ a * 2 ^ b ≤ 2 ^ c := by
  rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) h

/-- A `q` of at most 32 bytes: `2 q` fits the narrow division's remainder. -/
theorem narrow_of_length {qb : List Byte} (h : qb.length ≤ 32) :
    2 * (2 * Spec.Rsa.os2ip qb) ≤ 2 ^ (64 * Impl.Dsa.AArch64.Generation.reduceWords) := by
  have h₁ := VG.Proof.Bignum.os2ip_lt qb
  have h₂ : 256 ^ qb.length ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) h
  have h₃ : (256 : Nat) ^ 32 = 2 ^ 256 := by rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  have h₄ : 2 ^ 256 * 2 ^ 2 ≤ 2 ^ (64 * Impl.Dsa.AArch64.Generation.reduceWords) :=
    pow_mul_pow_le (by decide)
  omega_using [h₁, h₂, h₃, h₄]

/-- Padded loads preserve the arithmetic header and every other array. -/
theorem loadCandidateArray_ok {s : State} {B p : Addr} {Z w a ptr len : Nat} {bs : List Byte}
    (h : Ws s B Z w) (ha : a < 16) (hptr : ptr < 32) (hlen : len < 32)
    (hp : word s.mem B (8 * ptr) = p) (hl : word s.mem B (8 * len) = BitVec.ofNat 64 bs.length)
    (src : Src s B Z p bs) (hpos : 1 ≤ bs.length) (hfit : bs.length ≤ 8 * w) :
    WP isa (seqs (Impl.Rsa.AArch64.Keys.loadA a ptr len)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Frm B [ar w a] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadA_ok h ha hptr hlen hp hl src rfl hpos hfit) fun t ⟨hv, ho, _, _, hk⟩ => ?_
  have hf : Frm B [ar w a] s.mem t.mem := Frm.of_outside ho (by simp [ar])
  exact ⟨h.congr hf (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide),
    hv, hf, hk.mono (by decide)⟩

theorem candidateArithmetic_ok {s : State} {B xp qp : Addr} {Z w : Nat} {xb qb : List Byte}
    (h : Ws s B Z w)
    (hxp : word s.mem B 128 = xp) (hxl : word s.mem B 136 = BitVec.ofNat 64 xb.length)
    (hqp : word s.mem B 144 = qp) (hql : word s.mem B 152 = BitVec.ofNat 64 qb.length)
    (sx : Src s B Z xp xb) (sq : Src s B Z qp qb)
    (hxpos : 1 ≤ xb.length) (hxf : xb.length ≤ 8 * w)
    (hqposlen : 1 ≤ qb.length) (hqf : qb.length ≤ 8 * w)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hwide : Impl.Dsa.AArch64.Generation.reduceWords ≤ w) (hnarrow : qb.length ≤ 32) :
    WP isa Impl.Dsa.AArch64.Generation.candidateArithmetic s fun t =>
      Ws t B Z w ∧
      wv t.mem B (slot w 5) w = Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) ∧
      wv t.mem B (slot w 0) w =
        (Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) - 1) / Spec.Rsa.os2ip qb ∧
      Frm B [ar w 0, ar w 1, ar w 2, ar w 3, ar w 4, ar w 5] s.mem t.mem ∧ Keep mmRegs s t := by
  change WP isa (.seq (seqs (Impl.Rsa.AArch64.Keys.loadA 0 16 17))
    (.seq (seqs (Impl.Rsa.AArch64.Keys.loadA 2 18 19))
      (.seq (Impl.Dsa.AArch64.Generation.doubleArray 2)
        (.seq Impl.Dsa.AArch64.Generation.reduceCandidate (Impl.Dsa.AArch64.Generation.doubleArray 0))))) s _
  refine WP.seq (WP.mono (loadCandidateArray_ok h (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) hxp hxl sx hxpos hxf) fun u ⟨hu, ux, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; simp [slot, hdrBytes]; omega_using [hd])
      (by have := h.scr.nowrap; have := h.h256; omega_using [hd])
  have squ : Src u B Z qp qb := sq.congrK (fun a ha => fu a (by
    simp only [List.mem_singleton]; rintro r rfl
    have := h.sl (by decide : 0 < 16)
    dsimp only at *
    omega_using [ha, this])) ku
  refine WP.seq (WP.mono (loadCandidateArray_ok hu (by decide : 2 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) (by rw [uh 144 (by decide)]; exact hqp)
    (by rw [uh 152 (by decide)]; exact hql) squ hqposlen hqf) fun v ⟨hv, vq, fv, kv⟩ => ?_)
  refine WP.seq (WP.mono (doubleArray_ok hv (by decide : 2 < 16) (by rw [vq]; exact hqfit))
    fun z ⟨zq, ho, kz⟩ => ?_)
  have fz : Frm B [ar w 2] v.mem z.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have hz := hv.congr fz (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kz (by decide)
  have zx : wv z.mem B (slot w 0) w = Spec.Rsa.os2ip xb := by
    have sep : ∀ r ∈ [ar w 2], slot w 0 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0 := by
      simp only [List.mem_singleton]; rintro r rfl; left; simp only [slot, hdrBytes]; omega_using []
    have room : slot w 0 + 8 * w ≤ 2 ^ 64 := by
      have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega_arith
    rw [fz.wv_eq sep room, fv.wv_eq sep room, ux]
  change WP isa (.seq Impl.Dsa.AArch64.Generation.reduceCandidate
    (Impl.Dsa.AArch64.Generation.doubleArray 0)) z _
  refine WP.mono (reduceExponent_ok hz zx (by rw [zq, vq]) hqpos hwide (narrow_of_length hnarrow))
    fun t ⟨ht, tp, te, ft, kt⟩ => ?_
  exact ⟨ht, tp, te, (fu.append (fv.append (fz.append ft))).mono (by simp),
    (((ku.trans kv).trans kz).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
