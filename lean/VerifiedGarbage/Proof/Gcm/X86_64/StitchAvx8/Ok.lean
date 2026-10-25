module

import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.TailD
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Small
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
public import VerifiedGarbage.Proof.Framework.X86_64.Lane0
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Tail
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Gcm.Precomputed

/-! # Eight-state AES-NI/GHASH correctness

Field algebra is confined to this boundary module. The power-tree helpers
are reused from the retired sixteen-state AVX proof; loop modules use the
abstract `HashLaw` and never import polynomial algebra.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod φ_reduceB mul_ok constImm_ok ldrev_ok hInvImm_ok Only rev_eq)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (preg setupG lows highs setupC setup ordE ordD enc dec)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk StitchOkSmall kp nr cp yp dp nb pp kR cR yR dR pR hk y₀ bAddr blk
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
  Impl.Gcm.X86_64.Pclmul.constImm .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++
  Impl.Gcm.X86_64.Pclmul.constImm .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .rdi 240), .xop (.bin .pshufb .xmm7 .xmm0)] ++ Impl.Gcm.X86_64.Pclmul.hInvImm ++
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
  refine WP.mono (constImm_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 t₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun t₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInvImm_ok t₃) fun t₄ ⟨h₄, o₄⟩ => ?_
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
open VG.Impl.Gcm.X86_64.StitchAvx8 (setup setupG lows setupC initCounter preg)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (blockAt)
open VG.Spec.Gcm (Block)

theorem setup_split : setup = setupG ++ lows 8 ++ (setupC ++ metaCode ++ counterHead) ++ counterTail := by
  simp only [setup, initCounter, metaCode, counterHead, counterTail, List.append_assoc,
    List.cons_append, List.nil_append]

/-- What `setupG` leaves: the constants, and `H'` … `H'⁸` in `preg`. -/
def GPost (s₀ t : State) : Prop :=
  t.lane .xmm0 0 = revMask ∧ t.lane .xmm1 0 = poly ∧
    (∀ i < 8, x * φ (t.lane (preg i) 0) = φ (blockAt s₀.mem (s₀.gpr .rdi + BitVec.ofNat 64 240)) ^ (i + 1)) ∧
    (∀ r, r ≠ .rax → t.gpr r = s₀.gpr r) ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

/-- The setup, from any code `g` that leaves what `setupG` does. -/
theorem setupWith_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {g : List Instr} (hg : WP isa (.block g) s₀ (GPost s₀)) :
    WP isa (.block (g ++ lows 8 ++ (setupC ++ metaCode ++ counterHead) ++ counterTail)) s₀ fun s =>
      ∃ P : Nat → Block, Ready s₀ P s ∧ ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono hg fun t ⟨ht0, ht1, htP, htG, htM, htR, htW⟩ => ?_
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
  have hsv : u.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
    have hF := huF
    rw [htG .r11 (by decide), htM] at hF
    exact hF.readW (r := ⟨pp s₀ + BitVec.ofNat 64 816, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint_base _ (by decide) (by have := hp.wrap_p; omega)) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setupPrefix_ok hp u P (fun r hr => by rw [huG]; exact htG r hr)
    huF' (huR.trans htR) (huW.trans htW) ((huX _).trans ht0) ((huX _).trans ht1)
    (fun _ _ => rfl) hsv) fun v ⟨hvE, hvF, hvD, hvN, hv8, hvC, hvY, hv0⟩ => ?_
  refine WP.mono (counterTail_ok hp hvE hvC hv8) fun s ⟨hsE, hsT, hs8, hsG, hsX, hsF⟩ => ?_
  refine ⟨P, ⟨hsE, hsT, hs8, (hsG _ (by decide) (by decide)).trans hvD,
    (hsG _ (by decide) (by decide)).trans hvN, (hsX _ _).trans hvY,
    hvF.trans (hsF.sub fun r hr => ?_), (hsX _ _).trans hv0, by rw [hsX]; exact hvC⟩, hP⟩
  simp only [List.mem_singleton] at hr; subst r
  exact ⟨pR s₀, List.mem_singleton_self _, Offset.sub_base (pp s₀) (d := 640) (n := 128) (k := 1024) (by decide)⟩


theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P : Nat → Block,
      Ready s₀ P s ∧ ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
  rw [setup_split]
  exact setupWith_ok hp (setupG_ok s₀ (in_sub hp.k_in (off := 240) (by decide)))
end VG.Proof.Gcm.X86_64.StitchAvx8

/-!
# The powers of the blocks after the pipeline's

The products of the last `r < 8` blocks with the powers `H'ʳ` … `H'` of the
pipeline (`P (8 - r)` … `P 7`), added and reduced, are `GHASH` over them.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (hk)
open VG.Proof.Gcm.X86_64.Pclmul (Prod φ_reduceB reduceB)
open VG.Proof.Gcm.X86_64.StitchZH (accR)
open VG.Spec.Gcm (Block ghashFrom)

/-- Products of `r` blocks with powers `T j` whose `x`-multiples are `Hʳ⁻ʲ`,
added and reduced, are `GHASH` over the blocks. -/
theorem accLaw {H : Block} {r : Nat} (hr1 : 1 ≤ r) {T : Nat → Block}
    (hT : ∀ j < r, x * φ (T j) = φ H ^ (r - j)) (X : Nat → Block) (y : Block) :
    reduceB (accR X T y r) = ghashFrom H y ((List.range r).map X) := by
  have key : ∀ n, 1 ≤ n → n ≤ r →
      (accR X T y n).val = φ H ^ (r - n) * φ (ghashFrom H y ((List.range n).map X)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have h0 := hT 0 (by omega)
        simp only [accR, ↓reduceIte, Prod.val_acc, Prod.val_zero, zero_add, List.range_one, List.map_cons,
          List.map_nil, ghashFrom, List.foldl_cons, List.foldl_nil, φ_mul, Nat.sub_zero] at h0 ⊢
        rw [show r = (r - (0 + 1)) + 1 by omega, pow_succ] at h0
        linear_combination φ (y ^^^ X 0) * h0
      · have hn' := hT n (by omega)
        rw [show r - n = (r - (n + 1)) + 1 by omega, pow_succ] at hn'
        simp only [accR, show n ≠ 0 by omega, ↓reduceIte, Prod.val_acc, ih hpos (by omega), List.range_succ,
          List.map_append, List.map_cons, List.map_nil, ghashFrom, List.foldl_append, List.foldl_cons,
          List.foldl_nil, φ_mul, φ_xor, φ_zero, zero_add]
        rw [show r - n = (r - (n + 1)) + 1 by omega, pow_succ]
        linear_combination φ (X n) * hn'
  apply φ_inj
  rw [φ_reduceB, key r hr1 (Nat.le_refl _), Nat.sub_self, pow_zero, one_mul]

theorem tailLaw {s₀ : X86_64.State} {P : Nat → Block}
    (hP : ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k)) : TailLaw s₀ P := by
  intro r hr1 hr7 X y
  refine accLaw hr1 (fun j hj => ?_) X y
  have := hP (8 - r + j) (by omega)
  rwa [show 8 - (8 - r + j) = r - j by omega] at this

end VG.Proof.Gcm.X86_64.StitchAvx8

/-! # Complete fixed-key-size encrypt and decrypt loops -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (encRest decRest)
open VG.Proof.Gcm.Poly
open VG.Spec.Gcm (Block)

/-- Encryption, from a state `s` (`s₀` itself in place) where the setup
has left what `setup` does of `s₀`, with the data where the loop reads it
(`srcBlk s₀ ix`); the 8 bytes at `scratch + 816` as in `s₀`. -/
theorem encRestI_ok {s₀ s : State} {ix : Bool} (hp : SPre s₀) (hS : SrcOk s₀ ix) {P : Nat → Block}
    (hR : ReadyC s₀ P s) (hsrc : ∀ k < nb s₀, Spec.Gcm.blockAt s.mem (srcBlk s₀ ix k) = blk s₀ k)
    (hP : ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k)) :
    WP isa (encRest (nr s₀) ix) s fun t =>
      EPost s₀ t ∧ t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
  rw [encRest, ← body8_enc]
  have hlaw : HashLaw s₀ P := fun X y => finishHash X P (hk s₀) y hP
  refine WP.seq (WP.mono (WP.seq_iff.mp (firstEnc_ok hp hS hR hsrc)) fun t ht =>
    WP.seq (WP.mono ht fun t hI => ?_))
  refine WP.seq (WP.mono hI.compare fun u ⟨hu, hcf⟩ => ?_)
  refine WP.seq (WP.mono (loopMaybe_ok hp hS hlaw hu hcf) fun v ⟨g, hg, hv⟩ => ?_)
  exact WP.seq (WP.mono (finalHash_ok hp hlaw hv hg) fun w hw => tail_ok hp hS (tailLaw hP) hw)

/-- Encryption in place, after a setup that leaves what `setup` does. -/
theorem encRest_ok {s₀ s : State} (hp : SPre s₀) {P : Nat → Block} (hR : Ready s₀ P s)
    (hP : ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k)) :
    WP isa (encRest (nr s₀)) s (EPost s₀) :=
  WP.mono (encRestI_ok (ix := false) hp (SrcOk.inplace hp) hR.toC (hR.src hp) hP) fun _ h => h.1

/-- Decryption, after a setup that leaves what `setup` does: of any number
of blocks from 16 on with `rem`, and of a multiple of 16 without it. -/
theorem decRest_ok {s₀ s : State} (hp : SPre s₀) {rem : Bool} (hm : rem = false → nb s₀ % 16 = 0)
    {P : Nat → Block} (hR : Ready s₀ P s) (hP : ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k)) :
    WP isa (decRest (nr s₀) rem) s (DPost s₀) := by
  rw [decRest]
  have hlaw : HashLaw s₀ P := fun X y => finishHash X P (hk s₀) y hP
  refine WP.seq (WP.mono (firstDec_ok hp hR) fun t hI => ?_)
  have hl := loopRun_ok hp (SrcOk.inplace hp) hlaw hI hp.nb16
  refine WP.seq (WP.mono hl fun u ⟨g, hg, hu⟩ => ?_)
  simp only [threshold, ite_true] at hg
  refine WP.seq (WP.block_nil (WP.seq (WP.mono (finalDec_ok hp hlaw hu hg) fun w hw => ?_)))
  cases rem with
  | false =>
    have h8 := hu.multiple
    have ht := hu.tail_le
    have h16 := hm rfl
    simp only [tailSize, ite_true] at ht
    exact WP.seq (WP.block_nil (tailNone_ok hp hw (by omega)))
  | true => exact tailD_ok hp (tailLaw hP) hw

/-- The setup leaves the end of the key schedule, which `dispatch` compares. -/
theorem ready_rounds {s₀ s : State} {P : Nat → Block} (h : Ready s₀ P s) :
    s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr s₀) := by
  rw [h.env.r10, h.env.rdi]

end VG.Proof.Gcm.X86_64.StitchAvx8

/-! # Correctness of the eight-state AES-NI/GHASH pipeline -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (enc dec)

/-- Encryption of any number of blocks from 16 on. -/
theorem enc_ok {s₀ : State} (hp : SPre s₀) : WP isa enc s₀ (EPost s₀) := by
  refine dispatch_ok hp (setup_ok hp) (fun s ⟨P, hR, _⟩ => ready_rounds hR) ?_ ?_ ?_
  all_goals
    intro s t ⟨P, hR, hP⟩ ht hn
    have hw := encRest_ok hp (hR.rax ht) hP
    rw [hn] at hw
    exact hw

theorem stitch_ok : StitchOk enc dec := by
  constructor
  · intro s₀ hp _
    exact enc_ok hp
  · intro s₀ hp hm
    refine dispatch_ok hp (setup_ok hp) (fun s ⟨P, hR, _⟩ => ready_rounds hR) ?_ ?_ ?_
    all_goals
      intro s t ⟨P, hR, hP⟩ ht hn
      have hw := decRest_ok hp (rem := false) (fun _ => hm) (hR.rax ht) hP
      rw [hn] at hw
      exact hw

end VG.Proof.Gcm.X86_64.StitchAvx8

/-!
# The eight-state loop with a prepared key context

Untrusted: everything here is checked by Lean. `encR` is `enc` with
`setupR`, which loads `H'` … `H'⁸` from the prepared key context
(`Spec.Gcm.PreparedPowersRepr`) rather than computing them: what it loads
is `hInvF (Hⁿ)` (`pair_values`), and `x · φ (hInvF (Hⁿ)) = φ (H)ⁿ`, so it
leaves what `setupG` does (`setupGR_ok`), and the rest is `enc`'s
(`setupWith_ok`, `encRest_ok`): `stitchR_ok`.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch
open VG.Proof.Gcm.X86_64.Pclmul (constImm_ok Only rev_eq)
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupGR setupR prepOff preg lows setupC initCounter encR dec decR encRS decRS)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Spec.Gcm (Block blockAt hpow)

/-- The SSE code of `setupGR`. -/
def setupGRS : List Instr :=
  Impl.Gcm.X86_64.Pclmul.constImm .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++
  Impl.Gcm.X86_64.Pclmul.constImm .xmm1 poly ++
  (List.range 8).map fun i => .movdquLoad (preg i) (at_ .rdi (prepOff (i + 1)))

theorem lane0_setupGR : lane0Block setupGR = some setupGRS := by decide +kernel

/-- The first `n` loads of `setupGRS`. -/
theorem loadsS_ok (s : State) (n : Nat) (hn : n ≤ 8)
    (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 16) :
    WP isa (.block ((List.range n).map fun i => .movdquLoad (preg i) (at_ .rdi (prepOff (i + 1))))) s fun t =>
      (∀ i < n, t.xmm (preg i) = s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 128) ∧
      Only ((List.range n).map preg) s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hv, ho⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    apply WP.of_runBlock
    have hi : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((prepOff (n + 1) : Nat) : Int)) 16 := by
      rw [ho.rd, ho.wr, ho.gpr .rdi (by decide)]; exact hin n (by omega)
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128,
      VG.Proof.Gcm.X86_64.Pclmul.ea_at, hi, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun i hi' => ?_, ?_⟩
    · by_cases he : i = n
      · subst he
        simp only [State.setXmm, ite_true, ho.mem, ho.gpr .rdi (by decide)]
      · have hne : preg i ≠ preg n := fun h => he (StitchAvx.preg_inj i (by omega) n (by omega) h)
        simp only [State.setXmm, hne, ite_false]
        exact hv i (by omega)
    · rw [List.map_append, List.map_cons, List.map_nil]
      refine ho.trans (rs' := [preg n]) ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      have : r ≠ preg n := fun h => hr (h ▸ List.mem_singleton_self _)
      simp only [State.setXmm, this, ite_false]

/-- `setupGRS`: the constants, and the eight powers loaded. -/
theorem setupGRS_ok (t : State)
    (hin : ∀ i < 8, InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 16) :
    WP isa (.block setupGRS) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ i < 8, t'.xmm (preg i) = t.mem.readW (t.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 128) ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [setupGRS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  refine WP.mono (loadsS_ok t₂ 8 (by decide) (fun i hi => by
    rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr .rdi (by decide)]; exact hin i hi)) fun t₃ ⟨l₃, o₃⟩ => ?_
  have hp : ∀ r ∈ List.map preg (List.range 8), r ≠ .xmm0 ∧ r ≠ .xmm1 := by decide
  refine ⟨?_, ?_, fun i hi => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [o₃.xmm _ (fun h => (hp _ h).1 rfl), o₂.xmm _ (by decide), c₁, rev_eq]
  · rw [o₃.xmm _ (fun h => (hp _ h).2 rfl), c₂]
  · rw [l₃ i hi, o₁₂.mem, o₁₂.gpr .rdi (by decide)]
  · rw [o₃.gpr r hr, o₁₂.gpr r hr]
  · rw [o₃.mem, o₁₂.mem]
  · rw [o₃.rd, o₁₂.rd]
  · rw [o₃.wr, o₁₂.wr]

/-- What a prepared key context holds at `prepOff n`. -/
theorem prep_val {np : Nat} {m : Mem} {p : Addr} (hp : Stitch.PowersN np m p) (hnp : 8 ≤ np)
    {n : Nat} (h1 : 1 ≤ n) (h8 : n ≤ 15) : m.readW (p + BitVec.ofNat 64 (prepOff n)) 128 = hInvF (hpow (Spec.Gcm.ctxH m p) n) := by
  by_cases he : n % 2 = 0
  · have h := StitchZR.pair_values hp (j := n - 1) (l := 0) (by omega) (by omega) (by decide)
    rw [show prepOff n = 240 + 16 * (n - 1) + 16 * 0 by simp only [prepOff, he, ite_true]; omega, h]
    congr 2; omega
  · have h := StitchZR.pair_values hp (j := n) (l := 1) (by omega) (by omega) (by decide)
    rw [show prepOff n = 240 + 16 * n + 16 * 1 by simp only [prepOff, he, ite_false]; omega, h]
    congr 2

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

/-- `setupGR` leaves what `setupG` does, from a prepared key context. -/
theorem setupGR_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (hnp : 8 ≤ np) : WP isa (.block setupGR) s₀ (GPost s₀) := by
  have hin : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 16 :=
    fun i hi => by
      rw [BitVec.ofInt_natCast]
      exact in_sub hp.k_in (by simp only [prepOff]; split <;> omega)
  refine WP.mono (WP.lane0 lane0_setupGR (setupGRS_ok (s₀.proj 0) hin))
    fun t ⟨⟨h0, h1, hl, hg, hm, hrd, hwr⟩, _, _⟩ => ⟨h0, h1, fun i hi => ?_, hg, hm, hrd, hwr⟩
  change x * φ ((t.proj 0).xmm (preg i)) = _
  rw [hl i hi, BitVec.ofInt_natCast]
  change x * φ (s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (prepOff (i + 1))) 128) = _
  rw [prep_val hp.pow hnp (by omega) (by omega), x_φ_hInvF]
  rfl

theorem setupR_split : setupR = setupGR ++ lows 8 ++ (setupC ++ metaCode ++ counterHead) ++ counterTail := by
  simp only [setupR, initCounter, metaCode, counterHead, counterTail, List.append_assoc,
    List.cons_append, List.nil_append]

theorem setupR_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (hnp : 8 ≤ np) :
    WP isa (.block setupR) s₀ fun s => ∃ P : Nat → Block,
      Ready s₀ P s ∧ ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
  rw [setupR_split]
  exact setupWith_ok hp.base (setupGR_ok hp hnp)

/-- The powers `smallPow` of a prepared key context: the setup's up to
`H'⁸`, the key context's above it. -/
theorem smallLaw {s₀ : State} {lo np : Nat} {P : Nat → Block} (hp : SPrePrepared s₀ lo np) (hnp : 8 ≤ np)
    (hP : ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k)) : SmallLaw s₀ P := by
  intro r hr1 hr15 X y
  refine accLaw hr1 (fun j hj => ?_) X y
  by_cases h8 : r - j ≤ 8
  · simp only [smallPow, h8, ↓reduceIte]
    have := hP (8 - (r - j)) (by omega)
    rwa [show 8 - (8 - (r - j)) = r - j by omega] at this
  · simp only [smallPow, h8, ↓reduceIte]
    rw [prep_val hp.pow hnp (by omega) (by omega), x_φ_hInvF]
    rfl

/-- Encryption with a prepared key context, of any number of blocks from 16 on. -/
theorem encR_ok {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 16 np) (hnp : 8 ≤ np) :
    WP isa encR s₀ (EPost s₀) := by
  refine dispatch_ok hp.base (setupR_ok hp hnp) (fun s ⟨P, hR, _⟩ => ready_rounds hR) ?_ ?_ ?_
  all_goals
    intro s t ⟨P, hR, hP⟩ ht hn
    have hw := encRest_ok hp.base (hR.rax ht) hP
    rw [hn] at hw
    exact hw

/-- Decryption with a prepared key context, of any number of blocks from 16 on. -/
theorem decR_ok {s₀ : State} {np : Nat} (hp : SPrePrepared s₀ 16 np) (hnp : 8 ≤ np) :
    WP isa decR s₀ (DPost s₀) := by
  refine dispatch_ok hp.base (setupR_ok hp hnp) (fun s ⟨P, hR, _⟩ => ready_rounds hR) ?_ ?_ ?_
  all_goals
    intro s t ⟨P, hR, hP⟩ ht hn
    have hw := decRest_ok hp.base (rem := true) (fun h => Bool.noConfusion h) (hR.rax ht) hP
    rw [hn] at hw
    exact hw

/-- Both in-place loops, for a prepared key context holding at least its
first 8 pairs (they read `H'⁹`–`H'¹⁵` from it). -/
theorem stitchR_okN (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) :
    StitchOkM (CtxMode.preparedN np hn) encR decR 1 1 :=
  ⟨fun _ hp _ => encR_ok hp.toPrepared hn.1, fun _ hp _ => decR_ok hp.toPrepared hn.1⟩

theorem stitchR_ok : StitchOkM CtxMode.prepared encR decR 1 1 := stitchR_okN 24

/-- Encryption with a prepared key context, of 1 to 15 blocks. -/
theorem encRS_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (hnp : 8 ≤ np) (h1 : 1 ≤ nb s₀)
    (h16 : nb s₀ < 16) : WP isa encRS s₀ (EPost s₀) := by
  refine dispatch_ok hp.base (setupR_ok hp hnp) (fun s ⟨P, hR, _⟩ => ready_rounds hR) ?_ ?_ ?_
  all_goals
    intro s t ⟨P, hR, hP⟩ ht hn
    have hw := smallE_ok hp (smallLaw hp hnp hP) (hR.rax ht) h1 h16
    rw [hn] at hw
    exact hw

/-- Decryption with a prepared key context, of 1 to 15 blocks. -/
theorem decRS_ok {s₀ : State} {lo np : Nat} (hp : SPrePrepared s₀ lo np) (hnp : 8 ≤ np) (h1 : 1 ≤ nb s₀)
    (h16 : nb s₀ < 16) : WP isa decRS s₀ (DPost s₀) := by
  refine dispatch_ok hp.base (setupR_ok hp hnp) (fun s ⟨P, hR, _⟩ => ready_rounds hR) ?_ ?_ ?_
  all_goals
    intro s t ⟨P, hR, hP⟩ ht hn
    have hw := smallD_ok hp (smallLaw hp hnp hP) (hR.rax ht) h1 h16
    rw [hn] at hw
    exact hw

/-- `stitchR_okN`'s loops on 1 to 15 blocks. -/
theorem stitchRS_okN (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) :
    StitchOkSmall (CtxMode.preparedN np hn) encRS decRS 1 1 :=
  ⟨fun _ hp h16 => encRS_ok hp.toPrepared hn.1 hp.base.nb16 h16,
    fun _ hp h16 => decRS_ok hp.toPrepared hn.1 hp.base.nb16 h16⟩

theorem stitchRS_ok : StitchOkSmall CtxMode.prepared encRS decRS 1 1 := stitchRS_okN 24

end VG.Proof.Gcm.X86_64.StitchAvx8

/-!
# Out of place

Untrusted: everything here is checked by Lean. `encToWith su` runs from a
state `s₀` meeting `SPreTo` (`src` in `r8`, `dst` in `r10`). `toEntry` keeps
`rbx` at `scratch + 816` and leaves `src - dst` in `rbx` and `dst` in `r8`
(`toEntry_ok`); from there the setup `su` runs, then the loop
`encRest nr true`, which reads the data at `rdx + rbx`. Its proof is the
in-place one (`encRestI_ok`) for the view `view t` of the state `t` the
setup starts from: `t` with the
output holding the data (`viewMem`), which meets `SPre` and on which the
data the loop reads (`srcBlk _ true`, at `src`) is the view's (`blk`). What
the in-place proof concludes of the view is `EPostTo` of `s₀`
(`epostTo_of_view`), once `toExit` has restored `rbx` from `scratch + 816`,
which the loop keeps (`Env.saved`).
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (toEntry toExit encToWith encTo encToR encRest setup setupR)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at blockAt_frame)
open VG.Spec.Gcm (Block blockAt blocksAt)

private theorem store64_eq' (s : State) (a : Addr) (v : BitVec 64) :
    s.store64 a v = if InRegions s.wr a 8 then some (s.setMem (s.mem.writeW a v)) else none := rfl

theorem toEntry_ok (s : State) (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 816) 8) :
    WP isa (.block toEntry) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 816) (s.gpr .rbx) ∧
      t.gpr .rbx = s.gpr .r8 - s.gpr .r10 ∧ t.gpr .r8 = s.gpr .r10 ∧
      (∀ r, r ≠ .rbx → r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toEntry, runBlock_cons, runStep_some, runBlock_nil, exec, isa, store64_eq', ea_at,
    BitVec.ofInt_natCast, hw, execAlu, readSrc, gpr_setReg, gpr_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, State.setMem_gpr, State.setMem_mem,
    State.setMem_rd, State.setMem_wr, reduceCtorEq, ↓reduceIte, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ↓reduceIte], trivial, trivial⟩

theorem toExit_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 816) 8) :
    WP isa (.block toExit) s fun t =>
      t.gpr .rbx = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 816) 64 ∧
      (∀ r, r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toExit, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc, State.load64, ea_at, BitVec.ofInt_natCast, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
    ↓reduceIte, hr, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h => by simp only [h, ite_false], trivial, trivial, trivial⟩

/-! ## The view -/

/-- `m` with the bytes of `R` replaced by those `δ` past them. -/
def viewMem (m : Mem) (R : Region) (δ : Addr) : Mem := fun a => if R.Contains a 1 then m (a + δ) else m a

theorem viewMem_frame (m : Mem) (R : Region) (δ : Addr) : Frame [R] m (viewMem m R δ) := fun x hx => by
  have : ¬ R.Contains x 1 := hx R (List.mem_singleton_self _)
  simp only [viewMem, this, ite_false]

theorem viewMem_frame' (m : Mem) (R : Region) (δ : Addr) : Frame [R] (viewMem m R δ) m :=
  fun x hx => (viewMem_frame m R δ x hx).symm

theorem viewMem_block (m : Mem) (p δ : Addr) {n d : Nat} (hd : d + 16 ≤ n) (hn : n ≤ 2 ^ 64) :
    blockAt (viewMem m ⟨p, n⟩ δ) (p + BitVec.ofNat 64 d) = blockAt m (p + BitVec.ofNat 64 d + δ) := by
  simp only [blockAt, Spec.Aes.bytesAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  have hc : (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1 := by
    rw [Offset.add_add]; exact Offset.contains_base p (by omega) (by omega)
  simp only [viewMem, hc, ite_true]
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]

/-- The view of the loop's start `t` (`dst` in `r8`, `src - dst` in `rbx`):
the output holding the data. -/
def view (t : State) : State :=
  t.setMem (viewMem t.mem ⟨t.gpr .r8, 16 * (t.gpr .r9).toNat⟩ (t.gpr .rbx))

theorem view_gpr (t : State) : (view t).gpr = t.gpr := rfl
theorem view_rd (t : State) : (view t).rd = t.rd := rfl
theorem view_wr (t : State) : (view t).wr = t.wr := rfl

/-- The view's memory is `t`'s but on the output. -/
theorem view_frame (t : State) : Frame [dR t] (view t).mem t.mem := viewMem_frame' _ _ _
theorem view_frame' (t : State) : Frame [dR t] t.mem (view t).mem := viewMem_frame _ _ _

theorem spre_view {t : State} (hp : SPre t) : SPre (view t) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩ := hp
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩

/-! ## The start of the loop -/

private theorem inRegions_prefix' {rs : List Region} {a : Addr} {n L : Nat} (h : InRegions rs a L)
    (hn : n ≤ L) : InRegions rs a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, hr, by unfold Region.Contains at *; omega⟩

/-- The state `t` the setup starts from, after `toEntry`, from `s₀`. -/
structure Start (M : CtxMode) (s₀ t : State) : Prop where
  pre : SPreTo M s₀
  rbx : t.gpr .rbx = sp s₀ - op s₀
  r8 : t.gpr .r8 = op s₀
  gpr : ∀ r, r ≠ .rbx → r ≠ .r8 → t.gpr r = s₀.gpr r
  mem : t.mem = s₀.mem.writeW (pp s₀ + BitVec.ofNat 64 816) (s₀.gpr .rbx)
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr

section
variable {M : CtxMode} {s₀ t : State} (h : Start M s₀ t)
include h

theorem Start.kp_eq : kp t = kp s₀ := h.gpr _ (by decide) (by decide)
theorem Start.nr_eq : nr t = nr s₀ := by simp only [Stitch.nr, h.gpr .rsi (by decide) (by decide)]
theorem Start.cp_eq : cp t = cp s₀ := h.gpr _ (by decide) (by decide)
theorem Start.yp_eq : yp t = yp s₀ := h.gpr _ (by decide) (by decide)
theorem Start.dp_eq : dp t = op s₀ := h.r8
theorem Start.nb_eq : nb t = nb s₀ := by simp only [Stitch.nb, h.gpr .r9 (by decide) (by decide)]
theorem Start.pp_eq : pp t = pp s₀ := h.gpr _ (by decide) (by decide)

omit h in
/-- The 8 bytes at `scratch + 816`, where `rbx` is kept. -/
theorem Start.slotR : Region.Sub ⟨pp s₀ + BitVec.ofNat 64 816, 8⟩ (pR s₀) :=
  Offset.sub_base (pp s₀) (d := 816) (n := 8) (k := 1024) (by decide)

theorem Start.frame : Frame [⟨pp s₀ + BitVec.ofNat 64 816, 8⟩] s₀.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Start.spre : SPre t := by
  have hp := h.pre
  have ek := h.kp_eq; have er := h.nr_eq; have ec := h.cp_eq; have ey := h.yp_eq; have ed := h.dp_eq; have en := h.nb_eq
  have ep := h.pp_eq
  exact { rounds := by rw [er]; exact hp.rounds
          nb16 := by rw [en]; exact hp.nb16
          k_in := by rw [h.rd, h.wr, ek]; exact inRegions_prefix' hp.k_in M.ge
          c_in := by rw [h.wr, ec]; exact hp.c_in
          y_in := by rw [h.wr, ey]; exact hp.y_in
          d_in := by rw [h.wr, ed, en]; exact hp.o_in
          p_in := by rw [h.wr, ep]; exact hp.p_in
          d_k := by
            simp only [Stitch.dR, Stitch.kR, ed, en, ek]
            exact hp.k_o.symm.sub_right (Region.sub_prefix M.ge)
          d_c := by simp only [Stitch.dR, Stitch.cR, ed, en, ec]; exact hp.o_c
          d_y := by simp only [Stitch.dR, Stitch.yR, ed, en, ey]; exact hp.o_y
          d_p := by simp only [Stitch.dR, Stitch.pR, ed, en, ep]; exact hp.o_p
          p_k := by
            simp only [Stitch.pR, Stitch.kR, ep, ek]
            exact hp.k_p.symm.sub_right (Region.sub_prefix M.ge)
          p_c := by simp only [Stitch.pR, Stitch.cR, ep, ec]; exact hp.p_c
          p_y := by simp only [Stitch.pR, Stitch.yR, ep, ey]; exact hp.p_y
          c_y := by simp only [Stitch.cR, Stitch.yR, ec, ey]; exact hp.c_y
          c_k := by
            simp only [Stitch.cR, Stitch.kR, ec, ek]
            exact hp.k_c.symm.sub_right (Region.sub_prefix M.ge)
          y_k := by
            simp only [Stitch.yR, Stitch.kR, ey, ek]
            exact hp.k_y.symm.sub_right (Region.sub_prefix M.ge)
          wrap_d := by rw [ed, en]; exact hp.wrap_o
          wrap_k := by rw [ek]; have := hp.wrap_k; have := M.ge; omega
          wrap_p := by rw [ep]; exact hp.wrap_p }

theorem Start.spreM : SPreM M t := by
  have hp := h.pre
  refine ⟨h.spre, by rw [h.rd, h.wr, h.kp_eq]; exact hp.k_in, by rw [h.kp_eq]; exact hp.wrap_k, ?_, ?_, ?_⟩
  · simp only [kMR, Stitch.dR, h.dp_eq, h.nb_eq, h.kp_eq]; exact hp.k_o.symm
  · simp only [kMR, Stitch.pR, h.pp_eq, h.kp_eq]; exact hp.k_p.symm
  · rw [h.kp_eq]
    exact M.frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hp.k_p.sub_right (Start.slotR (s₀ := s₀))) hp.wrap_k hp.ok

end

/-! ## The view of the start -/

section
variable {M : CtxMode} {s₀ t : State} (h : Start M s₀ t)
include h

/-- Out of place, block `k`'s data is at `src + 16 k`. -/
theorem Start.srcBlk_eq (k : Nat) : srcBlk (view t) true k = sp s₀ + BitVec.ofNat 64 (16 * k) := by
  simp only [srcBlk, off, ite_true, view_gpr, Stitch.bAddr, Stitch.dp, h.r8, h.rbx]
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (16 * k)), ← BitVec.add_assoc,
    BitVec.add_comm (op s₀), BitVec.sub_add_cancel]

theorem Start.srcOk : SrcOk (view t) true where
  rd k hk := by
    rw [h.srcBlk_eq, view_rd, view_wr, h.rd, h.wr]
    have hn : k < nb s₀ := by rw [← h.nb_eq]; exact hk
    exact in_sub h.pre.s_in (by omega)
  sep k hk := by
    rw [h.srcBlk_eq]
    have hn : k < nb s₀ := by rw [← h.nb_eq]; exact hk
    have hw := h.pre.wrap_s
    show Region.Disjoint ⟨t.gpr .r8, 16 * k⟩ _
    rw [h.r8]
    exact (h.pre.s_o.symm.sub_left (Region.sub_prefix (by omega))).sub_right
      (Offset.sub_base (sp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))
  p k hk := by
    rw [h.srcBlk_eq]
    have hn : k < nb s₀ := by rw [← h.nb_eq]; exact hk
    show Region.Disjoint _ ⟨t.gpr .r11, 1024⟩
    rw [h.gpr .r11 (by decide) (by decide)]
    exact h.pre.s_p.sub_left (Offset.sub_base (sp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))

omit h in
/-- The view keeps all but the output. -/
theorem Start.blockAt_view {a : Addr} (hd : Region.Disjoint ⟨a, 16⟩ (dR t)) :
    blockAt (view t).mem a = blockAt t.mem a :=
  blockAt_frame (view_frame' t) (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hd)

theorem Start.cb_view : cb (view t) = cb t := Start.blockAt_view h.spre.d_c.symm
theorem Start.y₀_view : y₀ (view t) = y₀ t := Start.blockAt_view h.spre.d_y.symm
theorem Start.hk_view : hk (view t) = hk t :=
  Start.blockAt_view (h.spre.d_k.symm.sub_left (Offset.sub_base (kp t) (d := 240) (n := 16) (k := 256) (by decide)))

theorem Start.env {P : Nat → Block} {u : State} (hE : Env t P u) : Env (view t) P u := by
  have hp := h.spre
  refine ⟨hE.rdi, hE.rsi, hE.rcx, hE.r11, hE.r10, hE.other,
    ((view_frame t).mono (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)).trans hE.frame, hE.powers, hE.mask, hE.poly, hE.rounds, hE.data,
    hE.saved.trans ((view_frame t).readW (r := ⟨pp t + BitVec.ofNat 64 816, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact hp.d_p.symm.sub_left (Offset.sub_base (pp t) (d := 816) (n := 8) (k := 1024) (by decide)))
      (by decide)), hE.rd, hE.wr⟩

theorem Start.readyC {P : Nat → Block} {u : State} (hR : Ready t P u) : ReadyC (view t) P u :=
  ⟨h.env hR.env, by unfold Templates; rw [h.cb_view]; exact hR.templates, by rw [h.cb_view]; exact hR.counter,
    hR.cursor, hR.remaining, by rw [h.y₀_view]; exact hR.hash, hR.mask, by rw [h.cb_view]; exact hR.base⟩

theorem Start.src {P : Nat → Block} {u : State} (hR : Ready t P u) :
    ∀ k < nb (view t), blockAt u.mem (srcBlk (view t) true k) = blk (view t) k := by
  intro k hk
  have hn : k < nb s₀ := by rw [← h.nb_eq]; exact hk
  have hw := h.pre.wrap_o
  have hsp : Region.Disjoint ⟨sp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀) :=
    h.pre.s_p.sub_left (Offset.sub_base (sp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))
  rw [h.srcBlk_eq, blockAt_frame hR.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; rw [Stitch.pR, h.pp_eq]; exact hsp),
    show blk (view t) k = blockAt (viewMem t.mem ⟨t.gpr .r8, 16 * (t.gpr .r9).toNat⟩ (t.gpr .rbx))
      (t.gpr .r8 + BitVec.ofNat 64 (16 * k)) from rfl,
    viewMem_block _ _ _ (by rw [show (t.gpr .r9).toNat = nb t from rfl, h.nb_eq]; omega)
      (by rw [show (t.gpr .r9).toNat = nb t from rfl, h.nb_eq]; omega),
    h.r8, h.rbx, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (16 * k)), ← BitVec.add_assoc,
    BitVec.add_comm (op s₀), BitVec.sub_add_cancel]

end

/-! ## The loop out of place -/

section
variable {M : CtxMode} {s₀ t : State} (h : Start M s₀ t)
include h

/-- The view's memory is `s₀`'s but on the output and at `scratch + 816`. -/
theorem Start.frameV : Frame [oR s₀, pR s₀] s₀.mem (view t).mem := by
  refine (h.frame.sub fun r hr => ?_).trans ((view_frame' t).sub fun r hr => ?_)
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨pR s₀, by simp, Start.slotR⟩
  · simp only [List.mem_singleton] at hr; subst r
    refine ⟨oR s₀, by simp, ?_⟩
    simp only [Stitch.dR, Stitch.oR, h.dp_eq, h.nb_eq]
    exact fun _ h => h

theorem Start.blockAt_s₀ {a : Addr} (hd : Region.Disjoint ⟨a, 16⟩ (oR s₀))
    (hp : Region.Disjoint ⟨a, 16⟩ (pR s₀)) : blockAt (view t).mem a = blockAt s₀.mem a :=
  blockAt_frame h.frameV (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hp)

theorem Start.blk_view (k : Nat) (hk : k < nb s₀) :
    blk (view t) k = blockAt s₀.mem (sp s₀ + BitVec.ofNat 64 (16 * k)) := by
  have hw := h.pre.wrap_o
  rw [show blk (view t) k = blockAt (viewMem t.mem ⟨t.gpr .r8, 16 * (t.gpr .r9).toNat⟩ (t.gpr .rbx))
      (t.gpr .r8 + BitVec.ofNat 64 (16 * k)) from rfl,
    viewMem_block _ _ _ (by rw [show (t.gpr .r9).toNat = nb t from rfl, h.nb_eq]; omega)
      (by rw [show (t.gpr .r9).toNat = nb t from rfl, h.nb_eq]; omega),
    h.r8, h.rbx, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (16 * k)), ← BitVec.add_assoc,
    BitVec.add_comm (op s₀), BitVec.sub_add_cancel]
  exact blockAt_frame h.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact (h.pre.s_p.sub_left (Offset.sub_base (sp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))).sub_right
      Start.slotR)

/-- What the in-place proof concludes of the view, once `rbx` is restored,
is `EPostTo` of `s₀`. -/
theorem epostTo_of_view {w x : State} (hw : EPost (view t) w)
    (hs : w.mem.readW (pp (view t) + 816) 64 = (view t).mem.readW (pp (view t) + 816) 64)
    (hx : x.gpr .rbx = w.mem.readW (w.gpr .r11 + BitVec.ofNat 64 816) 64)
    (hg : ∀ r, r ≠ .rbx → x.gpr r = w.gpr r) (hm : x.mem = w.mem) (hrd : x.rd = w.rd) (hwr : x.wr = w.wr) :
    EPostTo s₀ x := by
  have hp := h.pre
  have hv := spre_view h.spre
  have hkp : kp (view t) = kp s₀ := h.kp_eq
  have hn : nr (view t) = nr s₀ := h.nr_eq
  have hc : cp (view t) = cp s₀ := h.cp_eq
  have hy : yp (view t) = yp s₀ := h.yp_eq
  have hd : dp (view t) = op s₀ := h.dp_eq
  have hb : nb (view t) = nb s₀ := h.nb_eq
  have hpp : pp (view t) = pp s₀ := h.pp_eq
  -- What the view reads of the key context, the counter and `Y` is `s₀`'s.
  have hsch : sch (view t) = sch s₀ := by
    rw [← sch_frame hv (m := s₀.mem) (fun x hx => (h.frameV x fun r hr => hx r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl
      · left; simp only [Stitch.dR, Stitch.oR, hd, hb]
      · right; simp only [Stitch.pR, hpp])).symm), hkp, hn]
  have hcb : cb (view t) = cb s₀ := by
    rw [Stitch.cb, hc]
    exact h.blockAt_s₀ hp.o_c.symm hp.p_c.symm
  have hy₀ : y₀ (view t) = y₀ s₀ := by
    rw [Stitch.y₀, hy]
    exact h.blockAt_s₀ hp.o_y.symm hp.p_y.symm
  have hhk : hk (view t) = hk s₀ := by
    rw [Stitch.hk, hkp]
    have hk240 : Region.Sub ⟨kp s₀ + BitVec.ofNat 64 240, 16⟩ ⟨kp s₀, M.len⟩ :=
      Offset.sub_base (kp s₀) (d := 240) (n := 16) (k := M.len) (by have := M.ge; omega)
    exact h.blockAt_s₀ (hp.k_o.sub_left hk240) (hp.k_p.sub_left hk240)
  have hci : ciph (view t) = ciph s₀ := by rw [Stitch.ciph, hsch, hn]
  have hsrc : blocksAt (view t).mem (dp (view t)) (nb (view t)) = blocksAt s₀.mem (sp s₀) (nb s₀) := by
    rw [hb]
    refine List.map_congr_left fun k hk' => ?_
    have hk'' := List.mem_range.mp hk'
    exact h.blk_view k hk''
  have hr11 : w.gpr .r11 = pp s₀ :=
    (hw.gpr _ (by decide) (by decide) (by decide) (by decide)).trans hpp
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, hrd.trans (hw.rd.trans h.rd), hwr.trans (hw.wr.trans h.wr)⟩
  · rw [hm, ← hd, ← hb, hw.data, hci, hcb, hsrc, hb]
  · rw [hm, ← hc, hw.ctr, hb, hcb]
  · rw [hm, ← hy, hw.y, hhk, hy₀, hd, hb]
  · refine (h.frameV.sub fun r hr => ?_).trans (hw.frame.sub fun r hr => ?_) |>.trans (hm ▸ Frame.refl _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨oR s₀, by simp, fun _ h => h⟩
      · exact ⟨pR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨cR s₀, by simp, by simp only [Stitch.cR, hc]; exact fun _ h => h⟩
      · exact ⟨yR s₀, by simp, by simp only [Stitch.yR, hy]; exact fun _ h => h⟩
      · exact ⟨oR s₀, by simp, by simp only [Stitch.dR, Stitch.oR, hd, hb]; exact fun _ h => h⟩
      · exact ⟨pR s₀, by simp, by simp only [Stitch.pR, hpp]; exact fun _ h => h⟩
  · by_cases hbx : r = .rbx
    · subst hbx
      have hs' : w.mem.readW (pp (view t) + BitVec.ofNat 64 816) 64 =
          (view t).mem.readW (pp (view t) + BitVec.ofNat 64 816) 64 := hs
      rw [hx, hr11, ← hpp, hs', hpp]
      have e : (view t).mem.readW (pp s₀ + BitVec.ofNat 64 816) 64 =
          t.mem.readW (pp s₀ + BitVec.ofNat 64 816) 64 :=
        (view_frame t).readW (r := ⟨pp s₀ + BitVec.ofNat 64 816, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          simp only [Stitch.dR, h.dp_eq, h.nb_eq]
          exact hp.o_p.symm.sub_left Start.slotR) (by decide) |>.symm
      rw [e, h.mem]
      exact Mem.readW_writeW_self64 _ _ _
    · rw [hg r hbx, hw.gpr r h1 h2 h4 h5]
      exact h.gpr r hbx h3

end

/-- The out-of-place loop after the setup `su` (`setup`, `setupR`), for a
key context of kind `M`, of any number of blocks from 16 on. -/
theorem encToWith_ok (M : CtxMode) {su : List Instr}
    (hsu : ∀ t, SPreM M t → WP isa (.block su) t fun u => ∃ P : Nat → Block, Ready t P u ∧
      ∀ k < 8, x * φ (P k) = φ (hk t) ^ (8 - k)) :
    StitchToOkM M (encToWith su) 1 := by
  intro s₀ hp _
  rw [encToWith]
  refine WP.seq (WP.mono (toEntry_ok s₀ (in_sub hp.p_in (off := 816) (by decide)))
    fun s₁ ⟨m₁, b₁, r8₁, g₁, rd₁, wr₁⟩ => ?_)
  have st₁ : Start M s₀ s₁ := ⟨hp, b₁, r8₁, g₁, m₁, rd₁, wr₁⟩
  let Q : State → Prop := fun w => EPost (view s₁) w ∧
    w.mem.readW (pp (view s₁) + 816) 64 = (view s₁).mem.readW (pp (view s₁) + 816) 64
  let R : State → Prop := fun u => ∃ P : Nat → Block, Ready s₁ P u ∧ ∀ k < 8, x * φ (P k) = φ (hk s₁) ^ (8 - k)
  have branch : ∀ n, ∀ u t, R u → RaxStep u t → nr s₁ = n → WP isa (encRest n true) t Q := by
    intro n u t ⟨P, hR, hP⟩ ht hn
    have hR' := hR.rax ht
    have e := encRestI_ok (s₀ := view s₁) (s := t) (ix := true) (spre_view st₁.spre) st₁.srcOk
      (st₁.readyC hR') (st₁.src hR') (by rw [st₁.hk_view]; exact hP)
    have hnr : nr (view s₁) = n := hn
    rw [hnr] at e
    exact e
  refine WP.seq (WP.mono (dispatch_ok st₁.spre (hsu s₁ st₁.spreM) (fun s ⟨P, hR, _⟩ => ready_rounds hR)
    (branch 10) (branch 12) (branch 14)) fun w ⟨hw, hs⟩ => ?_)
  have hr11 : w.gpr .r11 = pp s₀ :=
    (hw.gpr _ (by decide) (by decide) (by decide) (by decide)).trans st₁.pp_eq
  refine WP.mono (toExit_ok w (by
    rw [hw.rd, hw.wr, view_rd, view_wr, st₁.rd, st₁.wr, hr11]
    exact in_rdwr (in_sub hp.p_in (off := 816) (by decide))))
    fun x ⟨hx, hg, hm, hrd, hwr⟩ => epostTo_of_view st₁ hw hs hx hg hm hrd hwr

/-- Out of place, the setup computing the powers, for any key context. -/
theorem stitchTo_ok (M : CtxMode) : StitchToOkM M encTo 1 :=
  encToWith_ok M fun _ hp => setup_ok hp.base

/-- Out of place with a prepared key context. -/
theorem stitchToR_okN (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) :
    StitchToOkM (CtxMode.preparedN np hn) encToR 1 :=
  encToWith_ok (CtxMode.preparedN np hn) fun _ hp => setupR_ok hp.toPrepared hn.1

theorem stitchToR_ok : StitchToOkM CtxMode.prepared encToR 1 := stitchToR_okN 24

end VG.Proof.Gcm.X86_64.StitchAvx8
