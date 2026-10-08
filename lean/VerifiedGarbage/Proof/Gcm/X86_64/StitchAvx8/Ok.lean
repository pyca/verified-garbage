import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Dec
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.GhLoad
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupPrefix
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupTail
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ready
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.LoopStart
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.LoopRun
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.FinalEnc
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.FinalDec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Dispatch

/-! # Eight-state AES-NI/GHASH correctness

Field algebra is confined to this boundary module. The power-tree helpers
are reused from the retired sixteen-state AVX proof; loop modules use the
abstract `HashLaw` and never import polynomial algebra.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod φ_reduceB mul_ok const_ok ldrev_ok hInv_ok Only rev_eq)
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

end VG.Proof.Gcm.X86_64.StitchAvx

/-!
# The eight powers of the GHASH key

The pipeline uses the first half of the existing power tree. Its VEX.128
instructions have the same lower-lane behavior as the checked SSE tree.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupG lows preg)
open VG.Impl.Gcm.X86_64.Pclmul (poly revMask)
open VG.Spec.Gcm (blockAt)

theorem setupG_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 240) 16) :
    WP isa (.block setupG) s fun t =>
      t.lane .xmm0 0 = revMask ∧ t.lane .xmm1 0 = poly ∧
      (∀ i < 8, x * φ (t.lane (preg i) 0) =
        φ (blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 240)) ^ (i + 1)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.mono (WP.lane0 (ss := StitchAvx.setupGS) (by decide +kernel)
    (StitchAvx.setupGS_ok (s.proj 0) hin)) fun t ⟨⟨hm, hc, hp, hg, hmem, hrd, hwr⟩, _, _⟩ => ?_
  exact ⟨hm, hc, hp, hg, hmem, hrd, hwr⟩

theorem lows_ok (s : State)
    (hr : ∀ k < 16, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (s.gpr .r11).toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block (lows 8)) s fun t =>
      (∀ j < 8, t.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (16 * (15 - j))) 128 = s.lane (preg j) 0) ∧
      Frame [⟨s.gpr .r11, 256⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧
      (∀ r, t.lane r 0 = s.lane r 0) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.mono (WP.lane0 (ss := StitchAvx.lowsS 8) rfl
    (StitchAvx.lowsS_ok (s.proj 0) hr hp 8 (by decide)))
    fun t ⟨⟨hv, _, hf, hg, hx, hd, hw⟩, _, _⟩ => ?_
  exact ⟨hv, hf, hg, fun r => congrFun hx r, hd, hw⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

/-!
# The reordered eight-block GHASH sum

Block 1 initializes the sum; block 0, including the incoming hash value,
is added last. The powers compensate for this order, and one reduction
computes the same result as eight sequential GHASH steps.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB φ_reduceB)
open VG.Spec.Gcm (Block ghashFrom)

theorem finishHash (X P : Nat → Block) (H y : Block)
    (hP : ∀ k < 8, x * φ (P k) = φ H ^ (8 - k)) :
    reduceB (accN X P y 8) = ghashFrom H y ((List.range 8).map X) := by
  apply φ_inj
  simp only [accN, hashInput, ghashFrom, List.range_succ, List.range_zero,
    List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff,
    ite_true, ite_false]
  simp only [φ_reduceB, Prod.val_acc, Prod.val_zero, φ_xor, φ_mul, φ_zero]
  have h0 := hP 0 (by decide)
  have h1 := hP 1 (by decide)
  have h2 := hP 2 (by decide)
  have h3 := hP 3 (by decide)
  have h4 := hP 4 (by decide)
  have h5 := hP 5 (by decide)
  have h6 := hP 6 (by decide)
  have h7 := hP 7 (by decide)
  simp only [Nat.reduceSub, pow_one] at h0 h1 h2 h3 h4 h5 h6 h7
  linear_combination (φ (X 0) + φ y) * h0 + φ (X 1) * h1 + φ (X 2) * h2 + φ (X 3) * h3 +
    φ (X 4) * h4 + φ (X 5) * h5 + φ (X 6) * h6 + φ (X 7) * h7

end VG.Proof.Gcm.X86_64.StitchAvx8

/-! # Complete setup and the eight GHASH powers -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (setup setupG lows setupC initCounter)
open VG.Spec.Gcm (Block)

theorem setup_split : setup = setupG ++ lows 8 ++ (setupC ++ metaCode ++ counterHead) ++ counterTail := by
  simp only [setup, initCounter, metaCode, counterHead, counterTail, List.append_assoc,
    List.cons_append, List.nil_append]

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P : Nat → Block,
      Ready s₀ P s ∧ ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
  rw [setup_split, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupG_ok s₀ (in_sub hp.k_in (off := 240) (by decide)))
    fun t ⟨ht0, ht1, htP, htG, htM, htR, htW⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (lows_ok t (fun k hk => by
    rw [htW, htG .r11 (by decide)]
    exact in_sub_int hp.p_in (by omega)) (by
      rw [htG .r11 (by decide)]
      change (pp s₀).toNat + 256 ≤ 2 ^ 64
      have := hp.wrap_p; omega))
    fun u ⟨huP, huF, huG, huX, huR, huW⟩ => ?_
  let P : Nat → Block := fun k => u.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128
  have huF' : Frame [pR s₀] s₀.mem u.mem := by
    rw [htG .r11 (by decide), htM] at huF
    exact huF.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨pR s₀, List.mem_singleton_self _, by
        intro a ha
        simp only [Region.Contains, pp] at ha ⊢
        omega⟩
  have hP : ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
    intro k hk
    have he := huP (7 - k) (by omega)
    rw [htG .r11 (by decide), show 16 * (15 - (7 - k)) = 128 + 16 * k by omega] at he
    change x * φ (u.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128) = _
    rw [he]
    have hp' := htP (7 - k) (by omega)
    change x * φ (t.lane (Impl.Gcm.X86_64.StitchAvx8.preg (7 - k)) 0) = φ (Stitch.hk s₀) ^ (7 - k + 1) at hp'
    rw [show 7 - k + 1 = 8 - k by omega] at hp'
    exact hp'
  rw [WP.block_append_iff]
  refine WP.mono (setupPrefix_ok hp u P (fun r hr => by rw [huG]; exact htG r hr)
    huF' (huR.trans htR) (huW.trans htW) ((huX _).trans ht0) ((huX _).trans ht1)
    (fun _ _ => rfl)) fun v ⟨hvE, hvF, hvD, hvN, hv8, hvC, hvY⟩ => ?_
  refine WP.mono (counterTail_ok hp hvE hvC hv8) fun s ⟨hsE, hsT, hs8, hsG, hsX, hsF⟩ => ?_
  refine ⟨P, ⟨hsE, hsT, hs8, (hsG _ (by decide) (by decide)).trans hvD,
    (hsG _ (by decide) (by decide)).trans hvN, (hsX _ _).trans hvY,
    hvF.trans (hsF.sub fun r hr => ?_)⟩, hP⟩
  simp only [List.mem_singleton] at hr; subst r
  exact ⟨pR s₀, List.mem_singleton_self _, Offset.sub_base (pp s₀) (d := 640) (n := 128) (k := 1024) (by decide)⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

/-! # Complete fixed-key-size encrypt and decrypt loops -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (encFor decFor)

private theorem prefixContinue {a b z : Prog isa} {xs ys : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.block xs))) s (fun t => WP isa (.seq (.block ys) z) t Q)) :
    WP isa (.seq a (.seq b (.seq (.block (xs ++ ys)) z))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h =>
    WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h =>
      WP.seq (WP.block_append_iff.mpr (WP.mono h fun _ h => WP.seq_iff.mp h))))

theorem encFor_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (encFor (nr s₀)) s₀ (EPost s₀) := by
  rw [encFor]
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨P, hR, hP⟩ => ?_)
  have hlaw : HashLaw s₀ P := fun X y => finishHash X P (hk s₀) y hP
  apply prefixContinue
  refine WP.mono (firstEnc_ok hp hR) fun t hI => ?_
  refine WP.seq (WP.mono hI.compare fun u ⟨hu, hcf⟩ => ?_)
  refine WP.seq (WP.mono (loopMaybe_ok hp hlaw hu hcf) fun v ⟨g, hg, hv⟩ => ?_)
  exact finalEnc_ok hp hlaw hv hg

theorem decFor_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (decFor (nr s₀)) s₀ (DPost s₀) := by
  rw [decFor, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (setup_ok hp) fun s ⟨P, hR, hP⟩ => ?_
  have hlaw : HashLaw s₀ P := fun X y => finishHash X P (hk s₀) y hP
  refine WP.mono (firstDec_ok hp hR) fun t hI => ?_
  refine WP.seq (WP.mono (loopRun_ok hp hlaw hI hp.nb16) fun u ⟨g, hg, hu⟩ => ?_)
  exact WP.seq (WP.block_nil (finalDec_ok hp hlaw hu hg))

end VG.Proof.Gcm.X86_64.StitchAvx8

/-! # Correctness of the eight-state AES-NI/GHASH pipeline -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (enc dec)

theorem stitch_ok : StitchOk enc dec := by
  constructor
  · intro s₀ hp
    apply dispatch_ok hp <;> intro t hf hn
    all_goals
      have ht : nr t = nr s₀ := by simp only [nr, hf.gpr]
      have hw := encFor_ok (pre_same hp hf)
      rw [ht, hn] at hw
      exact WP.mono hw fun u hu => epost_same hf hu
  · intro s₀ hp
    apply dispatch_ok hp <;> intro t hf hn
    all_goals
      have ht : nr t = nr s₀ := by simp only [nr, hf.gpr]
      have hw := decFor_ok (pre_same hp hf)
      rw [ht, hn] at hw
      exact WP.mono hw fun u hu => dpost_same hf hu

end VG.Proof.Gcm.X86_64.StitchAvx8
