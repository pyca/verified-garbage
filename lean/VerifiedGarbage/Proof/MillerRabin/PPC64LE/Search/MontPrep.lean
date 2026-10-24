module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Minv
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A prime search on PPC64LE: a modulus's Montgomery constants

`montPrep_ok`: for an odd `N ≥ 3` in array 0, `−N⁻¹ mod 2⁶⁴` in header word
7 (its low half in `r12`), `R² mod N` in array 1, `R mod N` in array 9 (by
way of array 6), `N − R mod N` in array 10, and Miller–Rabin's exponent in
array 27 (`expSetup_ok`), `R = 2^(64 w)`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (Env arr expSetup_ok prepRegs)
open VG.Proof.Bignum (slot wv wv_lt wv_congr)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Proof.Mont (off Outside Outs word w32 val32 word_eq_w32)

/-- What `montPrep` changes: header word 7, arrays 1–3, 6–7, 9–10 and 27. -/
def mpRanges (w : Nat) : List (Nat × Nat) :=
  [(56, 8), (slot w 1, 24 * (w + 2)), (slot w 6, 16 * (w + 2)), (slot w 9, 16 * (w + 2)), (slot w aE, 8 * (w + 2))]

/-- The registers `montPrep` writes. -/
def mpRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- Numbers of equal words at different offsets are equal. -/
theorem wv_shift {m m' : Mem} {B : Addr} {d d' w : Nat}
    (h : ∀ i < w, VG.Proof.Bignum.word m' B (d' + 8 * i) = VG.Proof.Bignum.word m B (d + 8 * i)) :
    wv m' B d' w = wv m B d w := by
  induction w with
  | zero => rfl
  | succ k ih => rw [wv, wv, ih fun i hi => h i (by omega_arith), h k (by omega_arith)]

theorem montPrep_ok {s : State} {B : Addr} {Z w N : Nat} (h : Env s B Z w) (hn : arr s.mem B w 0 = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) :
    WP isa montPrep s fun t =>
      (Env t B Z w ∧ arr t.mem B w 0 = N ∧
        ((word t.mem B (slot w 0)).toNat * (word t.mem B 56).toNat + 1) % 2 ^ 64 = 0 ∧
        (t.gpr .r12).toNat < 2 ^ 32 ∧ (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧
        arr t.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧ arr t.mem B w 9 = 2 ^ (64 * w) % N ∧
        arr t.mem B w 10 = N - 2 ^ (64 * w) % N ∧ arr t.mem B w aE = mrE N ∧
        t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA N % 64) ∧
        Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t := by
  have hnw := h.hs.nowrap
  have hZ := h.hZ
  have hw4 := h.hw
  have hw128 := h.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  have hs := h.hs
  -- `N`'s low word is odd.
  have hwv : wv s.mem B (slot w 0) w = N := by rw [← Pre.val32_eq_wv]; exact hn
  have hodd0 : (word s.mem B (slot w 0)).toNat % 2 = 1 := by
    have e := VG.Proof.Bignum.wv_add s.mem B (slot w 0) 1 (w - 1)
    rw [show 1 + (w - 1) = w by omega_arith, hwv] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul] at e
    have : (word s.mem B (slot w 0)).toNat = (VG.Proof.Bignum.word s.mem B (slot w 0)).toNat := rfl
    omega_arith
  unfold montPrep
  -- `−N⁻¹`, and the arrays' addresses.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (minv64_ok hs h.h10 h.h31 (by simp only [es]; omega_arith) (by omega_arith) hodd0) fun s₁ ⟨⟨v, m₁, hv, h12₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k₁.gpr .r10 (by decide)).trans h.h10)
    ((k₁.gpr .r29 (by decide)).trans h.h29) 1) fun s₂ ⟨⟨a5, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr .r10 (by decide)).trans h.h10)
    ((k12.gpr .r29 (by decide)).trans h.h29) 2) fun s₃ ⟨⟨a8, m₃⟩, k₃⟩ => ?_
  have k13 := k12.trans k₃
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k13.gpr .r10 (by decide)).trans h.h10)
    ((k13.gpr .r29 (by decide)).trans h.h29) 3) fun s₄ ⟨⟨a9, m₄⟩, k₄⟩ => ?_
  have k14 := k13.trans k₄
  have m14 : s₄.mem = s.mem.writeW (B + BitVec.ofNat 64 56) v := by rw [m₄, m₃, m₂, m₁]
  have o14 : Outside B 56 8 s.mem s₄.mem := by rw [m14]; exact VG.Proof.Mont.writeW_outside _ _ _ (by omega_arith)
  have e₄ : Env s₄ B Z w := h.keep k14 (by decide)
  have n₄ : arr s₄.mem B w 0 = N := by
    rw [← hn]; exact o14.val32 (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
  have wd₄ : word s₄.mem B (slot w 0) = word s.mem B (slot w 0) :=
    o14.word (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
  -- `R² mod N`.
  have hN4v : val32 s₄.mem B (slot w 0) (2 * w) = N := n₄
  have hN2₄ : 2 ≤ val32 s₄.mem B (slot w 0) (2 * w) := by
    show 2 ≤ arr s₄.mem B w 0
    omega_arith
  refine WP.seq (WP.mono (r2_ok e₄.hs ((k₄.gpr .r8 (by decide)).trans a8) a9 e₄.h10 (((k₃.trans k₄).gpr .r5 (by decide)).trans a5) e₄.h11 (by omega_arith)
    (by omega_arith) (by simp only [es]; omega_arith) hN2₄) fun s₅ ⟨r₅, o₅, k₅⟩ => ?_)
  have e₅ : Env s₅ B Z w := e₄.keep k₅ (by decide)
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok e₅.hs (by omega_arith) (by omega_arith) (by simp only [es]; omega_arith) e₅.h10 e₅.h29 e₅.h11)
    fun s₆ ⟨⟨r₆, o₆'⟩, k₆⟩ => ?_)
  have o₆ : Outside B (slot w 7) (8 * w) s₅.mem s₆.mem := o₆'
  have e₆ : Env s₆ B Z w := e₅.keep k₆ (by decide)
  have k16 := (k14.trans k₅).trans k₆
  have n₆ : val32 s₆.mem B (slot w 0) (2 * w) = N := by
    rw [o₆.val32 (by simp only [es]; omega_arith) (by simp only [es]; omega_arith),
      o₅.val32 (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)]
    exact n₄
  have wd₆ : word s₆.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [o₆.word (by simp only [es]; omega_arith) (by simp only [es]; omega_arith),
      o₅.word (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), wd₄]
  have r1₆ : val32 s₆.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [o₆.val32 (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), r₅, hN4v, ← Nat.pow_add]
    congr 2; omega_arith
  have h12₆ : s₆.gpr .r12 = (v <<< 32) >>> 32 := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).gpr .r12 (by decide) |>.trans h12₁
  obtain ⟨i12, iinv⟩ := r12_inv hv
  have hw32 : ∀ m : Mem, w32 m B (slot w 0) = (word m B (slot w 0)).toNat % 2 ^ 32 := fun m => by
    have h2 : w32 m B (slot w 0) < 2 ^ 32 := (m.readW (off B (slot w 0)) 32).isLt
    rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  -- `R mod N` in array 6, the product of `R² mod N` and 1.
  refine WP.seq (WP.mono (Pub.montOp_ok e₆.hs (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith) (by simp only [es]; omega_arith) e₆.h10 e₆.h29
    e₆.h11 (by rw [h12₆]; exact i12) (by rw [h12₆, hw32, wd₆]; exact iinv) (by rw [r₆, n₆]; omega_arith))
    fun s₇ ⟨⟨lt₇, eq₇, o₇⟩, k₇⟩ => ?_)
  have e₇ : Env s₇ B Z w := e₆.keep k₇ (by decide)
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  rw [n₆, r1₆, r₆, Nat.mul_one, Nat.mod_mod] at eq₇
  rw [n₆] at lt₇
  have r6₇ : val32 s₇.mem B (slot w 6) (2 * w) = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt lt₇]; exact VG.Proof.Bignum.mont_cancel hR eq₇
  have sep7 : ∀ j, j = 0 ∨ j = 1 ∨ j = 7 → ∀ r ∈ [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)),
      (slot w 6, 8 * (w + 2))], slot w j + 4 * (2 * w) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp only [es] <;> omega_arith
  have n₇ : val32 s₇.mem B (slot w 0) (2 * w) = N := by
    rw [o₇.val32 (sep7 0 (by decide)) (by simp only [es]; omega_arith), n₆]
  have r1₇ : val32 s₇.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [o₇.val32 (sep7 1 (by decide)) (by simp only [es]; omega_arith), r1₆]
  have wd₇ : word s₇.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [o₇.word (fun r hr => by have := sep7 0 (by decide) r hr; omega_arith) (by simp only [es]; omega_arith), wd₆]
  -- `N − R mod N` in array 10.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) e₇.h10 e₇.h29 0) fun s₈ ⟨⟨b8, m₈⟩, k₈⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k₈.gpr .r10 (by decide)).trans e₇.h10)
    ((k₈.gpr .r29 (by decide)).trans e₇.h29) 10) fun s₉ ⟨⟨b9, m₉⟩, k₉⟩ => ?_
  have k89 := k₈.trans k₉
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k89.gpr .r10 (by decide)).trans e₇.h10)
    ((k89.gpr .r29 (by decide)).trans e₇.h29) 6) fun s₁₀ ⟨⟨b10, m₁₀⟩, k₁₀⟩ => ?_
  have k810 := k89.trans k₁₀
  have m810 : s₁₀.mem = s₇.mem := by rw [m₁₀, m₉, m₈]
  refine WP.seq (WP.mono (subMod_ok (e₇.hs.congr k810.wr) ((k₉.trans k₁₀).gpr .r8 (by decide) |>.trans b8)
    ((k₁₀.gpr .r9 (by decide)).trans b9) b10 ((k810.gpr .r11 (by decide)).trans e₇.h11) (by omega_arith) (by omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith)) fun s₁₁ ⟨⟨c, hc, hsub, _⟩, o₁₁, k₁₁⟩ => ?_)
  rw [m810, n₇, r6₇, show 32 * (2 * w) = 64 * w by omega_arith] at hsub
  have r10₁₁ : val32 s₁₁.mem B (slot w 10) (2 * w) = N - 2 ^ (64 * w) % N := by
    have hx : val32 s₁₁.mem B (slot w 10) (2 * w) < 2 ^ (64 * w) := by
      rw [Pre.val32_eq_wv]; exact wv_lt _ _ _ _
    have hm := Nat.mod_lt (2 ^ (64 * w)) (show 0 < N by omega_arith)
    have hNR : N < 2 ^ (64 * w) := by rw [← hwv]; exact wv_lt _ _ _ _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega_arith
  have k711 := k810.trans k₁₁
  have sep11 : ∀ j, j = 0 ∨ j = 1 ∨ j = 6 → slot w j + 4 * (2 * w) ≤ slot w 10 ∨ slot w 10 + 4 * (2 * w) ≤ slot w j := by
    intro j hj; rcases hj with rfl | rfl | rfl <;> simp only [es] <;> omega_arith
  have n₁₁ : val32 s₁₁.mem B (slot w 0) (2 * w) = N := by
    rw [o₁₁.val32 (sep11 0 (by decide)) (by simp only [es]; omega_arith), m810, n₇]
  have r1₁₁ : val32 s₁₁.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [o₁₁.val32 (sep11 1 (by decide)) (by simp only [es]; omega_arith), m810, r1₇]
  have r6₁₁ : ∀ i < w, word s₁₁.mem B (slot w 6 + 8 * i) = word s₇.mem B (slot w 6 + 8 * i) := fun i hi => by
    rw [o₁₁.word (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), m810]
  have wd₁₁ : word s₁₁.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [o₁₁.word (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), m810, wd₇]
  -- `R mod N` copied into array 9.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have h31₁₁ : s₁₁.gpr .r31 = B := (k711.gpr .r31 (by decide)).trans e₇.h31
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off B (slot w 0) ∧ u.mem = s₁₁.mem)
    (by prun [h31₁₁, hdrBytes]; simp only [es, Nat.zero_mul, Nat.add_zero]) (by decide)) fun s₁₂ ⟨⟨c10, m₁₂⟩, k₁₂⟩ => ?_
  have k712 := k711.trans k₁₂
  have c29 : s₁₂.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k712.gpr .r29 (by decide)).trans e₇.h29
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) c10 c29 6) fun s₁₃ ⟨⟨b15, m₁₃⟩, k₁₃⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k₁₃.gpr .r10 (by decide)).trans c10)
    ((k₁₃.gpr .r29 (by decide)).trans c29) 9) fun s₁₄ ⟨⟨b14, m₁₄⟩, k₁₄⟩ => ?_
  have k714 := (k712.trans k₁₃).trans k₁₄
  have m1114 : s₁₄.mem = s₁₁.mem := by rw [m₁₄, m₁₃, m₁₂]
  refine WP.seq (WP.mono (copyWithin_ok (e₇.hs.congr k714.wr) ((k₁₄.gpr .r15 (by decide)).trans b15) b14
    ((k714.gpr .r11 (by decide)).trans e₇.h11) (by omega_arith) (by omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)) fun s₁₅ ⟨⟨_, cp, o₁₅'⟩, k₁₅⟩ => ?_)
  have o₁₅ : Outside B (slot w 9) (8 * w) s₁₄.mem s₁₅.mem := o₁₅'
  have k715 := k714.trans k₁₅
  have e₁₅ : Env s₁₅ B Z w := ⟨e₇.hs.congr k715.wr, ((k₁₃.trans k₁₄).trans k₁₅).gpr .r10 (by decide) |>.trans c10,
    (k715.gpr .r29 (by decide)).trans e₇.h29, (k715.gpr .r11 (by decide)).trans e₇.h11,
    (k715.gpr .r31 (by decide)).trans e₇.h31, hw4, hw128, hZ⟩
  have sep15 : ∀ j, j = 0 ∨ j = 1 ∨ j = 10 → slot w j + 4 * (2 * w) ≤ slot w 9 ∨ slot w 9 + 8 * w ≤ slot w j := by
    intro j hj; rcases hj with rfl | rfl | rfl <;> simp only [es] <;> omega_arith
  have n₁₅ : val32 s₁₅.mem B (slot w 0) (2 * w) = N := by
    rw [o₁₅.val32 (sep15 0 (by decide)) (by simp only [es]; omega_arith), m1114, n₁₁]
  have r9₁₅ : val32 s₁₅.mem B (slot w 9) (2 * w) = 2 ^ (64 * w) % N := by
    rw [← r6₇, Pre.val32_eq_wv, Pre.val32_eq_wv]
    exact wv_shift fun i hi => by rw [cp i hi, m1114]; exact r6₁₁ i hi
  -- Miller–Rabin's exponent.
  refine WP.mono (expSetup_ok e₁₅ (by rw [← Pre.val32_eq_wv]; exact n₁₅) hodd (by omega_arith))
    fun t ⟨⟨eE, mE, oE⟩, kE⟩ => ?_
  have k7E := k715.trans kE
  have sepE : ∀ j, j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 → slot w j + 4 * (2 * w) ≤ slot w aE ∨
      slot w aE + 8 * (w + 2) ≤ slot w j := by
    intro j hj; rcases hj with rfl | rfl | rfl | rfl <;> simp only [es, aE] <;> omega_arith
  have tv : ∀ j, j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 → val32 t.mem B (slot w j) (2 * w) =
      val32 s₁₅.mem B (slot w j) (2 * w) := fun j hj => oE.val32 (sepE j hj) (by
        rcases hj with rfl | rfl | rfl | rfl <;> simp only [es] <;> omega_arith)
  have hsq : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∃ R ∈ mpRanges w, R.1 ≤ o ∧ o + n ≤ R.1 + R.2) →
      Outs B (mpRanges w) m m' := fun h hr =>
    Outs.cover (Outs.of_outside h (List.mem_singleton_self _)) fun r hr' => by
      rw [List.mem_singleton] at hr'; subst hr'; exact hr
  -- Word 56 and `N`'s low word, through the writes after `minv64`.
  have w56 : word t.mem B 56 = v := by
    rw [oE.word (by simp only [es, aE]; omega_arith) (by omega_arith), o₁₅.word (by simp only [es]; omega_arith) (by omega_arith), m1114,
      o₁₁.word (by simp only [es]; omega_arith) (by omega_arith), m810,
      o₇.word (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [es] <;> omega_arith) (by omega_arith),
      o₆.word (by simp only [es]; omega_arith) (by omega_arith), o₅.word (by simp only [es]; omega_arith) (by omega_arith), m14]
    exact Mem.readW_writeW_self64 _ _ _
  have w0 : word t.mem B (slot w 0) = word s.mem B (slot w 0) := by
    rw [oE.word (by simp only [es, aE]; omega_arith) (by simp only [es]; omega_arith),
      o₁₅.word (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), m1114, wd₁₁]
  have t12 : t.gpr .r12 = (v <<< 32) >>> 32 :=
    ((((k₁₃.trans k₁₄).trans k₁₅).trans kE).gpr .r12 (by decide)).trans
      ((k₁₂.gpr .r12 (by decide)).trans ((k₁₁.gpr .r12 (by decide)).trans ((k810.gpr .r12 (by decide)).trans
        ((k₇.gpr .r12 (by decide)).trans h12₆))))
  refine ⟨⟨e₁₅.keep kE (by decide), by show val32 _ _ _ _ = N; rw [tv 0 (by decide), n₁₅], by rw [w0, w56]; exact hv,
    by rw [t12]; exact i12, by rw [t12, hw32, w0]; exact iinv,
    by show val32 _ _ _ _ = _; rw [tv 1 (by decide), o₁₅.val32 (sep15 1 (by decide)) (by simp only [es]; omega_arith),
      m1114, r1₁₁],
    by show val32 _ _ _ _ = _; rw [tv 9 (by decide), r9₁₅],
    by show val32 _ _ _ _ = _; rw [tv 10 (by decide), o₁₅.val32 (sep15 10 (by decide)) (by simp only [es]; omega_arith),
      m1114, r10₁₁],
    eE, mE, ?_⟩, ?_⟩
  · refine (hsq o14 ⟨(56, 8), by simp [mpRanges], by omega_arith, by omega_arith⟩).trans
      ((hsq o₅ ⟨(slot w 1, 24 * (w + 2)), by simp [mpRanges], by omega_arith, by omega_arith⟩).trans
      ((hsq o₆ ⟨(slot w 6, 16 * (w + 2)), by simp [mpRanges], by simp only [es]; omega_arith, by simp only [es]; omega_arith⟩).trans
      ((Outs.cover o₇ fun r hr => ?_).trans ?_)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨(slot w 1, 24 * (w + 2)), by simp [mpRanges], by simp only [es]; omega_arith, by simp only [es]; omega_arith⟩
      · exact ⟨(slot w 1, 24 * (w + 2)), by simp [mpRanges], by simp only [es]; omega_arith, by simp only [es]; omega_arith⟩
      · exact ⟨(slot w 6, 16 * (w + 2)), by simp [mpRanges], by simp only [es]; omega_arith, by simp only [es]; omega_arith⟩
    rw [← m810]
    refine (hsq o₁₁ ⟨(slot w 9, 16 * (w + 2)), by simp [mpRanges], by simp only [es]; omega_arith,
      by simp only [es]; omega_arith⟩).trans ?_
    rw [← m1114]
    exact (hsq o₁₅ ⟨(slot w 9, 16 * (w + 2)), by simp [mpRanges], by omega_arith, by simp only [es]; omega_arith⟩).trans
      (hsq oE ⟨(slot w aE, 8 * (w + 2)), by simp [mpRanges], by omega_arith, by omega_arith⟩)
  · exact ((((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k810).trans k₁₁).trans
      ((k₁₂.trans k₁₃).trans k₁₄)).trans (k₁₅.trans kE)).mono (by decide)

end VG.Proof.MillerRabin.PPC64LE.Search
