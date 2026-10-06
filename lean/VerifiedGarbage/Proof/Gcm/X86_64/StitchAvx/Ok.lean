import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Dec
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash

/-!
# Interleaved counter mode and GHASH in AVX: the setup and the field

The only module of `Proof/Gcm/X86_64/StitchAvx/` that computes in the field
(`Proof/Gcm/Poly.lean`), so that few modules import its algebra:

* `setup_ok`: the setup stores `H'¹⁶⁻ᵏ` at `scratch + 16 k` (`x · H'ᵏ = Hᵏ`):
  `H'` from the hash subkey (`Pclmul.hInv_ok`), `H'²`–`H'⁸` in a tree
  (`tree_ok`, each step `Pclmul.mul_ok`), stored, and `H'⁹`–`H'¹⁶` as
  products with `H'⁸`, each stored as it is computed; all of it is the SSE
  code of the `VEX.128` instructions (`WP.lane0`). Then `Y`, the counter
  and the pointers (`Ready`).
* `finE`, `finD`: with those powers, the products of a group, in the order
  of an encryption or a decryption group, reduced, are `GHASH` over its
  sixteen blocks (`FinOk`).
* `stitch_ok`: both loops meet their contracts (`StitchOk`).
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod φ_reduce mul_ok const_ok ldrev_ok hInv_ok Only rev_eq)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (preg setupG lows highs setupC setup ordE ordD enc dec)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk kp nr cp yp dp nb pp kR cR yR dR pR hk y₀ bAddr blk
  in_sub in_sub_int in_rdwr ghash16)
open VG.Proof.Aes.X86_64.AesNi (one blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt ghashFrom mul)

/-! ## The powers -/

/-- A register of a power: none `mul` writes but its destination, nor the
mask, the reduction constant or `xmm2`. -/
theorem preg_ne (i : Nat) : preg i ≠ .xmm7 ∧ preg i ≠ .xmm8 ∧ preg i ≠ .xmm9 ∧ preg i ≠ .xmm10 ∧
    preg i ≠ .xmm11 ∧ preg i ≠ .xmm0 ∧ preg i ≠ .xmm1 ∧ preg i ≠ .xmm2 := by
  unfold preg; split <;> decide

theorem preg_inj : ∀ i < 8, ∀ j < 8, preg i = preg j → i = j := by decide

theorem pow_mul_pair {H a b d : Q} {m n : Nat} (hd : d = x * a * b) (ha : x * a = H ^ m) (hb : x * b = H ^ n) :
    x * d = H ^ (m + n) := by
  rw [hd, show x * (x * a * b) = (x * a) * (x * b) by ring, ha, hb, pow_add]

/-- One step of the tree: `H'ᵏ⁺¹ = mul(H'ᵃ⁺¹, H'ᵇ⁺¹)` into `preg k`. -/
theorem tree_ok {H : Q} (k a b : Nat) (hk8 : k < 8) (ha : a < k) (hb : b < k) (hab : a + b + 1 = k) (s : State)
    (h1 : s.xmm .xmm1 = poly) (hI : ∀ i < k, x * φ (s.xmm (preg i)) = H ^ (i + 1)) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul (preg k) (preg a) (preg b))) s fun s' =>
      s'.xmm .xmm1 = poly ∧ (∀ i < k + 1, i < 8 → x * φ (s'.xmm (preg i)) = H ^ (i + 1)) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11, preg k] s s' := by
  obtain ⟨-, a8, a9, a10, a11, -⟩ := preg_ne a
  obtain ⟨-, b8, b9, b10, b11, -⟩ := preg_ne b
  obtain ⟨-, k8, k9, k10, k11, -, k1, -⟩ := preg_ne k
  refine WP.mono (mul_ok (preg k) (preg a) (preg b) s a8 a9 a10 a11 b8 b9 b10 b11 k8 k9 k10 k11 h1)
    fun s' ⟨m, o⟩ => ⟨by rw [o.xmm _ (by simp [Ne.symm k1])]; exact h1, fun i hi hi8 => ?_, o⟩
  by_cases hik : i = k
  · subst hik
    rw [pow_mul_pair m (hI a ha) (hI b hb), show a + 1 + (b + 1) = i + 1 by omega]
  · rw [o.xmm _ (by
      obtain ⟨-, i8, i9, i10, i11, -⟩ := preg_ne i
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨i8, i9, i10, i11, fun h => hik (preg_inj i hi8 k hk8 h)⟩)]
    exact hI i (by omega)

/-- The SSE code of `setupG`. -/
def setupGS : List Instr :=
  Impl.Gcm.X86_64.Pclmul.const .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++
  Impl.Gcm.X86_64.Pclmul.const .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .rdi 240), .xop (.bin .pshufb .xmm7 .xmm0)] ++ Impl.Gcm.X86_64.Pclmul.hInv ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 1) (preg 0) (preg 0) ++ Impl.Gcm.X86_64.Pclmul.mul (preg 2) (preg 1) (preg 0) ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 3) (preg 1) (preg 1) ++ Impl.Gcm.X86_64.Pclmul.mul (preg 4) (preg 3) (preg 0) ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 5) (preg 3) (preg 1) ++ Impl.Gcm.X86_64.Pclmul.mul (preg 6) (preg 3) (preg 2) ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 7) (preg 3) (preg 3)

/-- The SSE code of `lows n`. -/
def lowsS (n : Nat) : List Instr :=
  (List.range n).map fun i => .movdquStore (at_ .r11 (16 * (15 - i))) (preg i)

/-- The SSE code of `highs n`. -/
def highsS (n : Nat) : List Instr :=
  (List.range n).flatMap fun i =>
    Impl.Gcm.X86_64.Pclmul.mul .xmm7 .xmm15 (preg i) ++ [.movdquStore (at_ .r11 (16 * (7 - i))) .xmm7]

theorem lane0_setup : lane0Block (setupG ++ lows 8 ++ highs 8) = some (setupGS ++ lowsS 8 ++ highsS 8) := by
  decide +kernel

theorem only_trans' {rs rs' : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs' s' s'') :
    Only (rs ++ rs') s s'' := h.trans h'

theorem setupGS_ok (t : State) (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)) 16) :
    WP isa (.block setupGS) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ i < 8, x * φ (t'.xmm (preg i)) =
        φ (blockAt t.mem (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ (i + 1)) ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [setupGS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 t₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun t₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok t₃) fun t₄ ⟨h₄, o₄⟩ => ?_
  have o₁₄ := (o₁₂.trans o₃).trans o₄
  rw [o₁₂.mem, o₁₂.gpr _ (by decide)] at l₃
  let H := φ (blockAt t.mem (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)))
  have hH : x * φ (t₄.xmm (preg 0)) = H := by rw [show preg 0 = .xmm3 from rfl, h₄, l₃]
  have p₄ : t₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  have m0 : t₄.xmm .xmm0 = revMask := by
    rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁, rev_eq]
  -- The tree.
  have step : ∀ {k a b : Nat} (hk8 : k < 8) (ha : a < k) (hb : b < k) (hab : a + b + 1 = k) {L : List Instr} {u : State}
      (h1 : u.xmm .xmm1 = poly) (h0 : u.xmm .xmm0 = revMask)
      (hI : ∀ i < k, x * φ (u.xmm (preg i)) = H ^ (i + 1))
      {Q : State → Prop}
      (hq : ∀ u', u'.xmm .xmm1 = poly → u'.xmm .xmm0 = revMask →
        (∀ i < k + 1, i < 8 → x * φ (u'.xmm (preg i)) = H ^ (i + 1)) →
        Only [.xmm8, .xmm9, .xmm10, .xmm11, preg k] u u' → WP isa (.block L) u' Q),
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul (preg k) (preg a) (preg b) ++ L)) u Q := by
    intro k a b hk8 ha hb hab L u h1 h0 hI Q hq
    rw [WP.block_append_iff]
    refine WP.mono (tree_ok k a b hk8 ha hb hab u h1 hI) fun u' ⟨h1', hI', o'⟩ => hq u' h1' ?_ hI' o'
    rw [o'.xmm _ (by obtain ⟨-, -, -, -, -, h, -⟩ := preg_ne k; simp [Ne.symm h])]; exact h0
  have f₀ : ∀ i < 1, x * φ (t₄.xmm (preg i)) = H ^ (i + 1) := fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [hH, pow_one]
  refine step (k := 1) (a := 0) (b := 0) (by decide) (by decide) (by decide) rfl p₄ m0 f₀ fun t₅ p₅ m₅ f₅ o₅ => ?_
  refine step (k := 2) (a := 1) (b := 0) (by decide) (by decide) (by decide) rfl p₅ m₅ (fun i hi => f₅ i hi (by omega))
    fun t₆ p₆ m₆ f₆ o₆ => ?_
  refine step (k := 3) (a := 1) (b := 1) (by decide) (by decide) (by decide) rfl p₆ m₆ (fun i hi => f₆ i hi (by omega))
    fun t₇ p₇ m₇ f₇ o₇ => ?_
  refine step (k := 4) (a := 3) (b := 0) (by decide) (by decide) (by decide) rfl p₇ m₇ (fun i hi => f₇ i hi (by omega))
    fun t₈ p₈ m₈ f₈ o₈ => ?_
  refine step (k := 5) (a := 3) (b := 1) (by decide) (by decide) (by decide) rfl p₈ m₈ (fun i hi => f₈ i hi (by omega))
    fun t₉ p₉ m₉ f₉ o₉ => ?_
  refine step (k := 6) (a := 3) (b := 2) (by decide) (by decide) (by decide) rfl p₉ m₉ (fun i hi => f₉ i hi (by omega))
    fun t₁₀ p₁₀ m₁₀ f₁₀ o₁₀ => ?_
  rw [← List.append_nil (Impl.Gcm.X86_64.Pclmul.mul (preg 7) (preg 3) (preg 3))]
  refine step (k := 7) (a := 3) (b := 3) (by decide) (by decide) (by decide) rfl p₁₀ m₁₀ (fun i hi => f₁₀ i hi (by omega))
    fun t' p' m' f' o' => WP.block_nil ?_
  have o := o₁₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans o'))))))
  exact ⟨m', p', fun i hi => f' i (by omega) hi, o.gpr, o.mem, o.rd, o.wr⟩

/-- A 16-byte store to `[r11 + d]`. -/
theorem st_ok (r : XReg) (d : Nat) (t : State)
    (hin : InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquStore (at_ .r11 d) r]) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .r11 + BitVec.ofInt 64 (d : Int)) (t.xmm r) ∧ t'.gpr = t.gpr ∧
      t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  rw [WP.block_cons_iff]
  refine ⟨{ t with mem := t.mem.writeW (t.gpr .r11 + BitVec.ofInt 64 (d : Int)) (t.xmm r) },
    by simp only [isa, exec, State.store128, Pclmul.ea_at, hin, ite_true], WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The address of slot `k` of the working space. -/
theorem slot_eq (p : Addr) (k : Nat) : p + BitVec.ofInt 64 ((16 * k : Nat) : Int) = p + BitVec.ofNat 64 (16 * k) := by
  rw [BitVec.ofInt_natCast]

theorem readW_slot_self {m : Mem} {p : Addr} {k : Nat} {v : BitVec 128} :
    (m.writeW (p + BitVec.ofNat 64 (16 * k)) v).readW (p + BitVec.ofNat 64 (16 * k)) 128 = v :=
  Mem.readW_writeW_self m _ 16 _ (by decide)

theorem readW_slot_sep {m : Mem} {p : Addr} {k j : Nat} {v : BitVec 128} (hk : k < 16) (hj : j < 16)
    (h : k ≠ j) :
    (m.writeW (p + BitVec.ofNat 64 (16 * j)) v).readW (p + BitVec.ofNat 64 (16 * k)) 128 =
      m.readW (p + BitVec.ofNat 64 (16 * k)) 128 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The stores of `lowsS n`, with the working space at `r11`. -/
theorem lowsS_ok (t : State) (hr : ∀ k < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (t.gpr .r11).toNat + 256 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block (lowsS n)) t fun t' =>
      (∀ j < n, t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * (15 - j))) 128 = t.xmm (preg j)) ∧
      (∀ k < 16, k + n < 16 → t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 =
        t.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128) ∧
      Frame [⟨t.gpr .r11, 256⟩] t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [lowsS, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (lowsS_ok t hr hp n (by omega)) fun t₁ ⟨v₁, k₁, f₁, g₁, x₁, rd₁, wr₁⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    refine WP.mono (st_ok (preg n) (16 * (15 - n)) t₁ (by rw [g₁, wr₁]; exact hr _ (by omega)))
      fun t' ⟨m', g', x', rd', wr'⟩ => ?_
    rw [g₁, x₁, slot_eq] at m'
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, g'.trans g₁, x'.trans x₁, rd'.trans rd₁, wr'.trans wr₁⟩
    · rw [m']
      by_cases hjn : j = n
      · subst hjn; exact readW_slot_self
      · rw [readW_slot_sep (by omega) (by omega) (by omega)]; exact v₁ j (by omega)
    · rw [m', readW_slot_sep hk (by omega) (by omega)]; exact k₁ k hk (by omega)
    · rw [m']
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- The registers `highsS` writes. -/
abbrev hregs : List XReg := [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11]

/-- The products and stores of `highsS n`, with `H'⁸` in `xmm15`. -/
theorem highsS_ok {H : Q} (t : State) (hr : ∀ k < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (t.gpr .r11).toNat + 256 ≤ 2 ^ 64) (h1 : t.xmm .xmm1 = poly)
    (hI : ∀ i < 8, x * φ (t.xmm (preg i)) = H ^ (i + 1)) :
    ∀ n ≤ 8, WP isa (.block (highsS n)) t fun t' =>
      (∀ j < n, x * φ (t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * (7 - j))) 128) = H ^ (9 + j)) ∧
      (∀ k < 16, k + n < 8 ∨ 8 ≤ k → t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 =
        t.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128) ∧
      Frame [⟨t.gpr .r11, 256⟩] t.mem t'.mem ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      (∀ r, r ∉ hregs → t'.xmm r = t.xmm r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [highsS, List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (highsS_ok t hr hp h1 hI n (by omega)) fun t₁ ⟨v₁, k₁, f₁, g₁, x₁, rd₁, wr₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    obtain ⟨n7, n8, n9, n10, n11, -⟩ := preg_ne n
    have e15 : t₁.xmm .xmm15 = t.xmm (preg 7) := x₁ _ (by decide)
    have en : t₁.xmm (preg n) = t.xmm (preg n) := x₁ _ (by simp [n7, n8, n9, n10, n11])
    refine WP.mono (mul_ok .xmm7 .xmm15 (preg n) t₁ (by decide) (by decide) (by decide) (by decide) n8 n9 n10 n11
      (by decide) (by decide) (by decide) (by decide) (by rw [x₁ _ (by decide)]; exact h1))
      fun t₂ ⟨m₂, o₂⟩ => ?_
    have hr₂ : t₂.gpr .r11 = t.gpr .r11 := by rw [o₂.gpr _ (by decide), g₁ _ (by decide)]
    refine WP.mono (st_ok .xmm7 (16 * (7 - n)) t₂ (by rw [hr₂, o₂.wr, wr₁]; exact hr _ (by omega)))
      fun t' ⟨m', g', x', rd', wr'⟩ => ?_
    rw [hr₂, slot_eq, o₂.mem] at m'
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, fun r hr' => by rw [g', o₂.gpr r hr', g₁ r hr'],
      fun r hr' => ?_, by rw [rd', o₂.rd, rd₁], by rw [wr', o₂.wr, wr₁]⟩
    · rw [m']
      by_cases hjn : j = n
      · subst hjn
        rw [readW_slot_self, pow_mul_pair m₂ (by rw [e15]; exact hI 7 (by decide)) (by rw [en]; exact hI j (by omega)),
          show 7 + 1 + (j + 1) = 9 + j by omega]
      · rw [readW_slot_sep (by omega) (by omega) (by omega)]; exact v₁ j (by omega)
    · rw [m', readW_slot_sep hk (by omega) (by omega)]; exact k₁ k hk (by omega)
    · rw [m']
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · simp only [hregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [x', o₂.xmm r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2]),
        x₁ r (by simp [hregs, hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2])]

/-! ## `Y`, the counter, the increment and the pointers -/

theorem setupC_ok (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupC) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm14 0 = blockAt s.mem (s.gpr .rdx) ∧
      s'.lane .xmm15 0 = one ∧ s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, ?_, trivial, ?_, trivial, trivial, fun r h1 h2 h3 => ?_, fun r h2 h14 h15 l hl => ?_, trivial,
    trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h14, h15]

/-! ## The setup -/

theorem setupS_ok {s₀ : State} (hp : SPre s₀) (t : State) (hg : t.gpr = s₀.gpr) (hm : t.mem = s₀.mem)
    (hrd : t.rd = s₀.rd) (hwr : t.wr = s₀.wr) :
    WP isa (.block (setupGS ++ lowsS 8 ++ highsS 8)) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ k < 16, x * φ (t'.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) = φ (hk s₀) ^ (16 - k)) ∧
      (∀ r, r ≠ .rax → t'.gpr r = s₀.gpr r) ∧ Frame [pR s₀] s₀.mem t'.mem ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have hwp := hp.wrap_p
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setupGS_ok t (by rw [hrd, hwr, hg]; exact in_sub_int hp.k_in (by decide)))
    fun t₁ ⟨m0, m1, pw₁, g₁, mm₁, rd₁, wr₁⟩ => ?_
  have hr11 : t₁.gpr .r11 = pp s₀ := by rw [g₁ _ (by decide), hg]
  have hin : ∀ k < 16, InRegions t₁.wr (t₁.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16 := fun k hk => by
    rw [wr₁, hwr, hr11]; exact in_sub_int hp.p_in (by omega)
  have hH : blockAt t.mem (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)) = hk s₀ := by
    rw [hm, hg, BitVec.ofInt_natCast]; rfl
  rw [hH] at pw₁
  refine WP.mono (lowsS_ok t₁ hin (by rw [hr11]; omega) 8 (Nat.le_refl _)) fun t₂ ⟨v₂, k₂, f₂, g₂, x₂, rd₂, wr₂⟩ => ?_
  have hin₂ : ∀ k < 16, InRegions t₂.wr (t₂.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16 := fun k hk => by
    rw [wr₂, g₂]; exact hin k hk
  refine WP.mono (highsS_ok (H := φ (hk s₀)) t₂ hin₂ (by rw [g₂, hr11]; omega) (by rw [x₂]; exact m1)
    (fun i hi => by rw [x₂]; exact pw₁ i hi) 8 (Nat.le_refl _)) fun t₃ ⟨v₃, k₃, f₃, g₃, x₃, rd₃, wr₃⟩ => ?_
  rw [g₂, hr11] at v₃ k₃ f₃
  rw [hr11] at v₂ k₂ f₂
  refine ⟨by rw [x₃ _ (by decide), x₂]; exact m0, by rw [x₃ _ (by decide), x₂]; exact m1, fun k hk => ?_,
    fun r hr => by rw [g₃ r hr, g₂, g₁ r hr, hg], ?_, by rw [rd₃, rd₂, rd₁, hrd], by rw [wr₃, wr₂, wr₁, hwr]⟩
  · by_cases h8 : 8 ≤ k
    · rw [k₃ k hk (.inr h8), show k = 15 - (15 - k) by omega, v₂ _ (by omega)]
      rw [pw₁ _ (by omega), show 15 - k + 1 = 16 - (15 - (15 - k)) by omega]
    · rw [show k = 7 - (7 - k) by omega, v₃ _ (by omega), show 9 + (7 - k) = 16 - (7 - (7 - k)) by omega]
  · rw [← hm, ← mm₁]
    exact (f₂.trans f₃).sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => Ready s₀ (fun k => s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) s ∧
      ∀ k < 16, x * φ (s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) = φ (hk s₀) ^ (16 - k) := by
  have hwd := hp.wrap_d
  rw [setup, WP.block_append_iff]
  refine WP.mono (WP.lane0 lane0_setup (setupS_ok hp (s₀.proj 0) rfl rfl rfl rfl))
    fun s₁ ⟨⟨m0, m1, pw, g₁, f₁, rd₁, wr₁⟩, _, _⟩ => ?_
  simp only [State.proj_xmm, State.proj_gpr, State.proj_mem, State.proj_rd, State.proj_wr] at m0 m1 pw g₁ f₁ rd₁ wr₁
  have hp₁ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₁.mem p = blockAt s₀.mem p :=
    fun hd => blockAt_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine WP.mono (setupC_ok s₁ m0 (by rw [wr₁, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₁, g₁ _ (by decide)]; exact hp.c_in))
    fun s₂ ⟨y0, c14, c15, r10, rax, rdx, gk, lk, m₂, rd₂, wr₂⟩ => ?_
  refine ⟨⟨⟨Nat.zero_le _, ?_, by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide)]; exact m0, c15,
    by rw [gk _ (by decide) (by decide) (by decide), g₁ _ (by decide)],
    by rw [gk _ (by decide) (by decide) (by decide), g₁ _ (by decide)],
    by rw [r10, g₁ _ (by decide), g₁ _ (by decide)], ?_, fun k hk => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩,
    by rw [rdx, g₁ _ (by decide)], by rw [rax, g₁ _ (by decide)],
    fun r h1 h2 h3 => by rw [gk r h1 h2 h3, g₁ r h1], fun k _ => by rw [m₂],
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide)]; exact m1,
    by rw [y0, g₁ _ (by decide), hp₁ hp.p_y.symm]⟩, fun k hk => by rw [m₂]; exact pw k hk⟩
  · rw [c14, g₁ _ (by decide), hp₁ hp.p_c.symm]; rfl
  · rw [m₂]; exact f₁.mono fun r hr => by simp at hr ⊢; exact Or.inr hr
  · rw [m₂, hp₁ (hp.d_p.sub_left (Offset.sub_base _ (by omega)))]
    simp only [Nat.not_lt_zero, ite_false]

/-! ## The products of a group, in the field -/

theorem zero_xor' (a : Block) : (0 : Block) ^^^ a = a := by simp

theorem finE {H : Block} {P : Nat → Block} (hP : ∀ k < 16, x * φ (P k) = φ H ^ (16 - k)) : FinOk ordE H P := by
  intro X y
  apply φ_inj
  rw [ghash16]
  simp only [accN, ordE, inp, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, zero_xor']
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  have h0 := hP 0 (by decide)
  have h1 := hP 1 (by decide)
  have h2 := hP 2 (by decide)
  have h3 := hP 3 (by decide)
  have h4 := hP 4 (by decide)
  have h5 := hP 5 (by decide)
  have h6 := hP 6 (by decide)
  have h7 := hP 7 (by decide)
  have h8 := hP 8 (by decide)
  have h9 := hP 9 (by decide)
  have h10 := hP 10 (by decide)
  have h11 := hP 11 (by decide)
  have h12 := hP 12 (by decide)
  have h13 := hP 13 (by decide)
  have h14 := hP 14 (by decide)
  have h15 := hP 15 (by decide)
  simp only [Nat.reduceSub, pow_one] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  linear_combination (φ y + φ (X 0)) * h0 + φ (X 1) * h1 + φ (X 2) * h2 + φ (X 3) * h3 + φ (X 4) * h4 + φ (X 5) * h5 + φ (X 6) * h6 + φ (X 7) * h7 + φ (X 8) * h8 + φ (X 9) * h9 + φ (X 10) * h10 + φ (X 11) * h11 + φ (X 12) * h12 + φ (X 13) * h13 + φ (X 14) * h14 + φ (X 15) * h15

theorem finD {H : Block} {P : Nat → Block} (hP : ∀ k < 16, x * φ (P k) = φ H ^ (16 - k)) : FinOk ordD H P := by
  intro X y
  apply φ_inj
  rw [ghash16]
  simp only [accN, ordD, inp, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, zero_xor']
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  have h0 := hP 0 (by decide)
  have h1 := hP 1 (by decide)
  have h2 := hP 2 (by decide)
  have h3 := hP 3 (by decide)
  have h4 := hP 4 (by decide)
  have h5 := hP 5 (by decide)
  have h6 := hP 6 (by decide)
  have h7 := hP 7 (by decide)
  have h8 := hP 8 (by decide)
  have h9 := hP 9 (by decide)
  have h10 := hP 10 (by decide)
  have h11 := hP 11 (by decide)
  have h12 := hP 12 (by decide)
  have h13 := hP 13 (by decide)
  have h14 := hP 14 (by decide)
  have h15 := hP 15 (by decide)
  simp only [Nat.reduceSub, pow_one] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  linear_combination (φ y + φ (X 0)) * h0 + φ (X 1) * h1 + φ (X 2) * h2 + φ (X 3) * h3 + φ (X 4) * h4 + φ (X 5) * h5 + φ (X 6) * h6 + φ (X 7) * h7 + φ (X 8) * h8 + φ (X 9) * h9 + φ (X 10) * h10 + φ (X 11) * h11 + φ (X 12) * h12 + φ (X 13) * h13 + φ (X 14) * h14 + φ (X 15) * h15

/-! ## The loops -/

theorem enc_ok {s₀ : State} (hp : SPre s₀) : WP isa enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨hR, hpw⟩ => encTail_ok hp (finE hpw) hR)

theorem dec_ok {s₀ : State} (hp : SPre s₀) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨hR, hpw⟩ => decTail_ok hp (finD hpw) hR)

/-- Both loops meet their contracts. -/
theorem stitch_ok : StitchOk enc dec := ⟨fun _ hp => enc_ok hp, fun _ hp => dec_ok hp⟩

end VG.Proof.Gcm.X86_64.StitchAvx
