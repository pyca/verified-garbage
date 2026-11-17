module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Mont.Words32
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
import VerifiedGarbage.Proof.Mont.Halve32
import Init.Prelude
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGaps
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.TwosMath
public import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairScan
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words
import VerifiedGarbage.Proof.Mont.X86.ExponentWord

/-! ### `RsaKeyGen.X86.HalfPassWord`, which this module and modules that import it used -/

section

/-! # One exponent word is halved or retained under the secret mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem select_word (old shifted : BitVec 32) (choice : Bool) :
    old ^^^ ((shifted ^^^ old) &&& cmask choice) = if choice then shifted else old := by
  cases choice
  · rw [show cmask false = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
    rfl
  · rw [show cmask true = BitVec.allOnes 32 from rfl, BitVec.and_allOnes, BitVec.xor_comm shifted old,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rfl

theorem step_ok {s : State} {base : Addr} {size src out index : Nat} (scratch : Scr s base size)
    (pointer : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * index))
    (srcFit : src + 4 * index + 8 ≤ size) (outFit : out + 4 * index + 4 ≤ size)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (.block (step src out)) s fun t =>
      Outside base (out + 4 * index) 4 s.mem t.mem ∧
      w32 t.mem base (out + 4 * index) =
        (if choice then w32 s.mem base (src + 4 * index) / 2 +
          2 ^ 31 * (w32 s.mem base (src + 4 * index + 4) % 2) else w32 s.mem base (src + 4 * index)) ∧
      Keeps [.eax, .ebx, .edx] s t := by
  unfold step
  refine wp_movS (readSrc_at' scratch pointer (by omega_using [srcFit])) fun a A _ =>
    wp_logicS (.inl rfl) rfl fun b B => wp_ror (by decide) fun c C => ?_
  have Kc : Keeps [.eax, .ebx, .edx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have pc : c.gpr .ebp = c.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kc.1 .ebp (by decide), Kc.1 .edi (by decide)]; exact pointer
  refine wp_movS (readSrc_at' (scratch.of_keeps Kc (by decide)) pc (by omega_using [srcFit])) fun d D _ =>
    wp_shr (by decide) fun e E _ => wp_addS rfl fun f F _ => ?_
  have Kf : Keeps [.eax, .ebx, .edx] s f := ((Kc.widen D.keeps).widen E.keeps).widen F.keeps
  have pf : f.gpr .ebp = f.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kf.1 .ebp (by decide), Kf.1 .edi (by decide)]; exact pointer
  refine wp_movS (readSrc_at' (scratch.of_keeps Kf (by decide)) pf (by omega_using [srcFit])) fun g G _ =>
    wp_xor fun h H => wp_and fun i I => wp_xor fun j J => ?_
  have Kj : Keeps [.eax, .ebx, .edx] s j := (((Kf.widen G.keeps).widen H.keeps).widen I.keeps).widen J.keeps
  have pj : j.gpr .ebp = j.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kj.1 .ebp (by decide), Kj.1 .edi (by decide)]; exact pointer
  have Sj := scratch.of_keeps Kj (by decide)
  refine wp_storeS (Sj.ea_at' pj (by omega_using [outFit])) (Sj.write outFit) fun t T => WP.block_nil ?_
  have M : j.mem = s.mem := J.mem.trans (I.mem.trans (H.mem.trans (G.mem.trans
    (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem))))))))
  have old : g.gpr .ebx = s.mem.readW (off base (src + 4 * index)) 32 := by
    rw [G.gpr, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  have half : f.gpr .edx = (s.mem.readW (off base (src + 4 * index)) 32 >>> 1) +
      (s.mem.readW (off base (src + 4 * index + 4)) 32 &&& 1).rotateRight 1 := by
    rw [F.gpr, E.gpr, D.gpr, E.other .eax (by decide), D.other .eax (by decide), C.gpr, B.gpr, A.gpr,
      C.mem, B.mem, A.mem]
    rw [show src + 4 + 4 * index = src + 4 * index + 4 by omega_using []]
    rfl
  have selected : j.gpr .ebx = if choice then f.gpr .edx else g.gpr .ebx := by
    rw [J.gpr, I.other .ebx (by decide), H.other .ebx (by decide), I.gpr, H.gpr,
      G.other .edx (by decide), H.other .ecx (by decide),
      G.other .ecx (by decide), Kf.1 .ecx (by decide), mask, select_word]
  refine ⟨?_, ?_, Kj.widen (T.keeps [])⟩
  · rw [T.mem, M]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega_using [outFit, this])
  · rw [T.mem, w32_write_self, selected, old, half]
    cases choice
    · rfl
    · exact VG.Proof.Mont.X86.Dynamic.shifted_word _ _

end VG.Proof.RsaKeyGen.X86.HalfPass

end

end

/-! ### `RsaKeyGen.X86.ExponentMarker`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowBit`, which this module and modules that import it used -/

section

/-! # Native subtraction and masking isolate the paired word's lowest set bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/NegPair.lean`, which only this module imported.
section

/-! # Native subtraction through the borrow forms the negation of a 64-bit pair -/

section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.Proof.Mont.X86

theorem neg_pair (lo hi : BitVec 32) :
    (0#32 - hi - (BitVec.ofBool (decide (0 < lo.toNat))).setWidth 32) ++ (0#32 - lo) = -(hi ++ lo) := by
  let borrow := decide (0 < lo.toNat)
  let carry := decide (0 < hi.toNat + borrow.toNat)
  have L := Mod64.sub_rel (0#32) lo
  have H := sbb_rel (0#32) hi borrow
  simp only [BitVec.toNat_zero, Nat.zero_add] at L H
  change (0#32 - lo).toNat + lo.toNat = 2 ^ 32 * borrow.toNat at L
  change (0#32 - hi - (BitVec.ofBool borrow).setWidth 32).toNat + hi.toNat + borrow.toNat =
    2 ^ 32 * carry.toNat at H
  have paired : ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat +
      (hi ++ lo).toNat = 2 ^ 64 * carry.toNat := by
    rw [Gcd64.append_pair, Gcd64.append_pair]
    unfold Mod64.pair
    omega
  have outputBound := ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).isLt
  have inputBound := (hi ++ lo).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg]
  change ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat = _
  cases C : carry <;> rw [C] at paired <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at paired <;> omega

end VG.Proof.RsaKeyGen.X86.LowBit
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowBit

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .edx ++ t.gpr .eax = (s.gpr .esi ++ s.gpr .ebx) &&& -(s.gpr .esi ++ s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cfB => wp_movS rfl fun c C cfC => ?_
  refine wp_sbbS rfl (cfC.trans cfB) fun d D _ => wp_and fun e E => wp_and fun t T => WP.block_nil ?_
  have low : t.gpr .eax = (0#32 - s.gpr .ebx) &&& s.gpr .ebx := by
    rw [T.other .eax (by decide), E.gpr, D.other .eax (by decide), C.other .eax (by decide),
      B.gpr, A.gpr, A.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
    rfl
  have high : t.gpr .edx = (0#32 - s.gpr .esi - (BitVec.ofBool (decide (0 < (s.gpr .ebx).toNat))).setWidth 32)
      &&& s.gpr .esi := by
    rw [T.gpr, E.other .edx (by decide), D.gpr, C.gpr, C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide), A.gpr, A.other .ebx (by decide),
      E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide)]
    rfl
  refine ⟨?_, ?_, (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [low, high, ← BitVec.and_append, neg_pair, BitVec.and_comm]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.LowBit

end

end

/-! ### `RsaKeyGen.X86.LowPairTwos`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowPairFirst`, which only this module used -/

section

/-! # The paired scan retains exactly the first nonzero source word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG

theorem first_keep (m : Mem) (base : Addr) (src start count : Nat) (before : BitVec 32 × BitVec 32)
    (nonzero : ¬(before.1 = 0#32 ∧ before.2 = 0#32)) : first m base src before start count = before := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    unfold first select
    rw [ite_eq_right nonzero]
    exact ih (start + 1)

theorem first_hit (m : Mem) (base : Addr) (src start count index : Nat)
    (lo : start ≤ index) (hi : index < start + count)
    (below : ∀ j, start ≤ j → j < index → pairAt m base (src + 8 * j) = (0#32, 0#32))
    (hit : pairAt m base (src + 8 * index) ≠ (0#32, 0#32)) :
    first m base src (0#32, 0#32) start count = pairAt m base (src + 8 * index) := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change first m base src (pairAt m base (src + 8 * start)) (start + 1) count = _
    by_cases same : start = index
    · subst start
      exact first_keep m base src (index + 1) count _ (fun ⟨a, b⟩ => hit (Prod.ext a b))
    · rw [below start (Nat.le_refl _) (by omega_using [lo, same])]
      exact ih (start + 1) (by omega_using [lo, same]) (by omega_using [hi]) (fun j hj lt => below j (by omega_using [hj]) lt)

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! # The native pair scan finds the word containing the exponent's lowest set bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/LowPairWord.lean`, which only this module imported.
section

/-! # Native halves read by the masked scan form the original 64-bit word -/

section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.Proof.Mont

theorem pairAt_word (m : Mem) (base : Addr) (src : Nat) :
    (pairAt m base src).2 ++ (pairAt m base src).1 = word m base src := by
  rw [word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  rfl

theorem pairAt_zero_iff (m : Mem) (base : Addr) (src : Nat) :
    pairAt m base src = (0#32, 0#32) ↔ word m base src = 0#64 := by
  constructor
  · intro h
    rw [← pairAt_word, h]
    rfl
  · intro h
    have value := congrArg BitVec.toNat h
    rw [word_eq_w32] at value
    change w32 m base src + 2 ^ 32 * w32 m base (src + 4) = 0 at value
    have low : w32 m base src = 0 := by omega
    have high : w32 m base (src + 4) = 0 := by omega
    exact Prod.ext (BitVec.eq_of_toNat_eq low) (BitVec.eq_of_toNat_eq high)

end VG.Proof.RsaKeyGen.X86.LowPair
end

end

-- Formerly `VerifiedGarbage/Proof/Mont/Digits64.lean`, which only this module imported.
section

/-! # A native paired word is a base-2⁶⁴ digit of its integer -/

section
namespace VG.Proof.Mont
open VG

theorem word_digit64 (m : Mem) (base : Addr) (src n index : Nat) (bound : index < n) :
    (word m base (src + 8 * index)).toNat = wordsVal m base src n / 2 ^ (64 * index) % 2 ^ 64 := by
  have bridge : ∀ k, wordsVal m base src k = VG.Proof.Bignum.wv m base src k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [wordsVal_succ_top, VG.Proof.Bignum.wv, ih]
  rw [bridge]
  exact VG.Proof.Bignum.word_of_wv m base src n bound

end VG.Proof.Mont
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

/-- The first nonzero pair of `count` pairs whose value is `N > 0` is the
64-bit word holding `N`'s lowest set bit. -/
theorem first_twos {m : Mem} {base : Addr} {src count N : Nat}
    (value : val32 m base src (2 * count) = N) (positive : 0 < N) :
    ((first m base src (0#32, 0#32) 0 count).2 ++ (first m base src (0#32, 0#32) 0 count).1).toNat =
      N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 := by
  obtain ⟨factor, odd⟩ := VG.Proof.Rsa.splitTwos_spec positive
  rw [Nat.mul_comm] at factor
  let a := (Spec.Rsa.splitTwos N).1
  obtain ⟨zero, bit, lower⟩ := VG.Proof.RsaKeyGen.lowWord_bits factor odd
  have bound : a < 64 * count := by
    have small : N < 2 ^ (64 * count) := by
      rw [← value, ← wordsVal_eq_val32]
      exact wordsVal_lt _ _ _ _
    by_cases h : a < 64 * count
    · exact h
    · have pow := Nat.pow_le_pow_right (n := 2) (by decide) (show 64 * count ≤ a by omega_using [h])
      have mul := Nat.le_mul_of_pos_left (2 ^ a) (show 0 < (Spec.Rsa.splitTwos N).2 by omega_using [odd])
      rw [← factor] at mul
      omega
  have digit {j : Nat} (index : j < count) :
      (word m base (src + 8 * j)).toNat = N / 2 ^ (64 * j) % 2 ^ 64 := by
    rw [word_digit64 _ _ _ _ _ index, wordsVal_eq_val32, value]
  have below (j : Nat) (_ : 0 ≤ j) (hj : j < a / 64) :
      pairAt m base (src + 8 * j) = (0#32, 0#32) := by
    apply (pairAt_zero_iff _ _ _).mpr
    apply BitVec.eq_of_toNat_eq
    rw [digit (by omega_using [bound, hj]), zero j hj]
    rfl
  have hit : pairAt m base (src + 8 * (a / 64)) ≠ (0#32, 0#32) := by
    intro h
    have empty := congrArg BitVec.toNat ((pairAt_zero_iff _ _ _).mp h)
    rw [digit (by omega_using [bound])] at empty
    have notZero : N / 2 ^ (64 * (a / 64)) % 2 ^ 64 ≠ 0 := by
      intro h
      rw [h, Nat.zero_testBit] at bit
      contradiction
    exact notZero empty
  rw [first_hit m base src 0 count (a / 64) (by omega_using []) (by omega_using [bound]) below hit, pairAt_word, digit (by omega_using [bound])]

theorem scan_twos {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (scan src count) s fun t =>
      (t.gpr .esi ++ t.gpr .ebx).toNat = N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.mono (scan_ok scratch fit) fun t ⟨V, M, K⟩ => ?_
  have pair := congrArg (fun p : BitVec 32 × BitVec 32 => p.2 ++ p.1) V
  dsimp only at pair
  exact ⟨by rw [pair]; exact first_twos value positive, M, K⟩

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! # The native alignment marker is exactly 2^(v2(N) mod 64) -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentMarker
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentMarker

/-- `LowBit` on the 64-bit word holding `N`'s lowest set bit, in `esi:ebx`. -/
theorem lowBit_marker {a : State} {N : Nat} (positive : 0 < N)
    (selectedWord : (a.gpr .esi ++ a.gpr .ebx).toNat = N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.LowBit.code) a fun t =>
      t.gpr .edx ++ t.gpr .eax = BitVec.twoPow 64 ((Spec.Rsa.splitTwos N).1 % 64) ∧
      t.mem = a.mem ∧ Keeps [.eax, .edx] a t := by
  refine WP.mono (LowBit.code_ok a) fun t ⟨marker, Mt, Kt⟩ => ?_
  obtain ⟨factor, odd⟩ := VG.Proof.Rsa.splitTwos_spec positive
  rw [Nat.mul_comm] at factor
  obtain ⟨_, bit, below⟩ := VG.Proof.RsaKeyGen.lowWord_bits factor odd
  have setBit : (a.gpr .esi ++ a.gpr .ebx).getLsbD ((Spec.Rsa.splitTwos N).1 % 64) = true := by
    change (a.gpr .esi ++ a.gpr .ebx).toNat.testBit _ = true
    rw [selectedWord]
    exact bit
  have clearBit (j : Nat) (lt : j < (Spec.Rsa.splitTwos N).1 % 64) :
      (a.gpr .esi ++ a.gpr .ebx).getLsbD j = false := by
    change (a.gpr .esi ++ a.gpr .ebx).toNat.testBit j = false
    rw [selectedWord]
    exact below j lt
  exact ⟨marker.trans (VG.Proof.RsaKeyGen.and_neg_eq_twoPow (Nat.mod_lt _ (by decide)) setBit clearBit), Mt, Kt⟩

theorem code_ok {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (code src count) s fun t =>
      t.gpr .edx ++ t.gpr .eax = BitVec.twoPow 64 ((Spec.Rsa.splitTwos N).1 % 64) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.seq (WP.mono (LowPair.scan_twos scratch fit value positive) fun a ⟨selectedWord, M, K⟩ => ?_)
  refine WP.mono (lowBit_marker positive selectedWord) fun t ⟨marker, Mt, Kt⟩ => ?_
  exact ⟨marker, Mt.trans M, K.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentMarker

end

end

/-! ### `RsaKeyGen.X86.Exponent`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.HalfPassLoop`, which only this module used -/

section

/-! # A single masked pass halves or retains the complete native exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem code_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * n ≤ size)
    (sep : src = out ∨ src + 4 * (n + 1) ≤ out ∨ out + 4 * n ≤ src)
    (top : w32 s.mem base (src + 4 * n) = 0)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (code n src out) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if choice then val32 s.mem base src n / 2 else val32 s.mem base src n) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  let P (j : Nat) (t : State) : Prop :=
    Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside base out (4 * j) s.mem t.mem ∧
    ∀ i < j, w32 t.mem base (out + 4 * i) =
      if choice then w32 s.mem base (src + 4 * i) / 2 +
        2 ^ 31 * (w32 s.mem base (src + 4 * i + 4) % 2) else w32 s.mem base (src + 4 * i)
  refine wordLoop_ok P positive (by have := scratch.size_lt; omega_using [srcFit, this])
    (fun j t u ⟨K, O, V⟩ ⟨M, rd, wr, regs⟩ =>
      ⟨⟨fun r hr => (regs r (by simp_all) (by simp_all)).trans (K.1 r hr), rd.trans K.2.1, wr.trans K.2.2⟩,
        M ▸ O, M ▸ V⟩)
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_
  · intro j hj t ⟨K, O, V⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine WP.mono (step_ok (choice := choice) St pointer (by omega_using [srcFit, hj]) (by omega_using [outFit, hj]) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Ku⟩ => ?_
    have sameLo : w32 t.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      O.w32 (by rcases sep with h | h | h <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
    have sameHi : w32 t.mem base (src + 4 * j + 4) = w32 s.mem base (src + 4 * j + 4) :=
      O.w32 (by rcases sep with h | h | h <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
    refine ⟨⟨K.widen Ku, (O.mono (by omega_using []) (by omega_using [])).trans (Ou.mono (by omega_using []) (by omega_using [])), ?_⟩,
      Ku.1 .ebp (by decide), Ku.1 .edi (by decide)⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega_using [before]) (by have := scratch.nowrap; omega_using [outFit, hj, hi, this])]
      exact V i before
    · rw [value, sameLo, sameHi]
  · intro t ⟨K, O, V⟩
    refine ⟨O, ?_, K⟩
    cases choice
    · exact val32_congr_at s.mem t.mem base n src out V
    · apply val32_halve_at s.mem t.mem base n src out
      intro i hi
      rw [V i hi, show src + 4 * i + 4 = src + 4 * (i + 1) by omega_using []]
      by_cases last : i + 1 = n
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

end VG.Proof.RsaKeyGen.X86.HalfPass

end

end

/-! # Complete native exponent and alignment-marker preparation -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentClear.lean`, which only this module imported.
section

/-! # Zero top sentinels supply the incoming bits for fixed masked halving -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem clearTops_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (.block (clearTops n src out)) s fun t =>
      w32 t.mem base (src + 4 * n) = 0 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      t.gpr .ecx = cmask true ∧
      Outs base [(src + 4 * n, 4), (out + 4 * n, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold clearTops
  refine wp_movS rfl fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun b B => ?_
  have Kb : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (by omega)) fun c C => wp_movS rfl fun t T _ => WP.block_nil ?_
  have Mb : b.mem = s.mem.writeW (off base (src + 4 * n)) (0#32) := by
    rw [B.mem, A.mem, A.gpr]
    rfl
  have Mc : c.mem = b.mem.writeW (off base (out + 4 * n)) (0#32) := by
    rw [C.mem, (B.keeps []).1 .eax (by decide), A.gpr]
    rfl
  have Os : Outside base (src + 4 * n) 4 s.mem b.mem := by
    rw [Mb]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have Oo : Outside base (out + 4 * n) 4 b.mem c.mem := by
    rw [Mc]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  refine ⟨?_, ?_, T.gpr, ?_, ((Kb.mono (by decide : ∀ r : Reg, r ∈ [.eax] → r ∈ [.eax, .ecx])).widen (C.keeps [])).widen T.keeps⟩
  · rw [T.mem, Oo.w32 (by omega) (by have := scratch.nowrap; omega), Mb, w32_write_self]
    rfl
  · rw [T.mem, Mc, w32_write_self]
    rfl
  · rw [T.mem]
    exact (Outs.of_outside Os (List.mem_cons_self ..)).trans
      (Outs.of_outside Oo (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFirst.lean`, which only this module imported.
section

/-! # The first native pass copies c/2 into the exponent and retains its zero sentinel -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def firstRanges (n src out : Nat) : List (Nat × Nat) :=
  [(src + 4 * n, 4), (out + 4 * n, 4), (out, 4 * n)]

theorem firstPass_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (firstPass n src out) s fun t =>
      val32 t.mem base out n = val32 s.mem base src n / 2 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      Outs base (firstRanges n src out) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (clearTops_ok scratch srcFit outFit sep) fun a ⟨srcTop, outTop, mask, Oa, Ka⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps Ka (by decide)) positive srcFit (by omega)
    (Or.inr (Or.inl sep)) srcTop mask) fun t ⟨Ot, V, Kt⟩ => ?_
  have before : val32 a.mem base src n = val32 s.mem base src n :=
    Oa.val32 (fun r mem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> left <;> omega) (by have := scratch.nowrap; omega)
  refine ⟨by rw [before] at V; exact V, ?_, ?_, (Ka.mono (by decide)).widen Kt⟩
  · rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by have := scratch.nowrap; omega)]
    exact outTop
  · exact (Oa.mono (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl <;> simp)).trans
      (Outs.of_outside Ot (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShift.lean`, which only this module imported.
section

/-! # An alignment pass halves exactly when sigma exceeds its public index -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem halfIf_ok {s : State} {base : Addr} {size n marker out j k : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : out + 4 * (n + 1) ≤ size) (markerFit : marker + 8 ≤ size)
    (top : w32 s.mem base (out + 4 * n) = 0) (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3)
    (value : word s.mem base marker = BitVec.twoPow 64 k) :
    WP isa (halfIf n marker out j) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (SigMask.code_sig scratch markerFit index choice value) fun a ⟨mask, M, K⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps K (by decide)) positive fit (by omega) (Or.inl rfl)
    (by rw [M]; exact top) mask) fun t ⟨O, V, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, by simpa only [decide_eq_true_eq] using V, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftContext.lean`, which only this module imported.
section

/-! # Alignment marker and top sentinel remain available across all three passes -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

structure Context (base : Addr) (size n marker out k : Nat) (s : State) : Prop where
  scratch : Scr s base size
  positive : 0 < n
  fit : out + 4 * (n + 1) ≤ size
  markerFit : marker + 8 ≤ size
  apart : marker + 8 ≤ out
  index : k < 64
  value : word s.mem base marker = BitVec.twoPow 64 k
  top : w32 s.mem base (out + 4 * n) = 0

theorem halfIf_context {s : State} {base : Addr} {size n marker out j k : Nat}
    (C : Context base size n marker out k s) (choice : 1 ≤ j ∧ j ≤ 3) :
    WP isa (halfIf n marker out j) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (halfIf_ok C.scratch C.positive C.fit C.markerFit C.top C.index choice C.value)
    fun t ⟨O, V, K⟩ => ?_
  refine ⟨⟨C.scratch.of_keeps K (by decide), C.positive, C.fit, C.markerFit, C.apart, C.index, ?_, ?_⟩, O, V, K⟩
  · rw [O.word (Or.inl C.apart) (by have := C.scratch.nowrap; have := C.markerFit; omega)]
    exact C.value
  · rw [O.w32 (Or.inr (Nat.le_refl _)) (by have := C.scratch.nowrap; have := C.fit; omega)]
    exact C.top

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftPasses.lean`, which only this module imported.
section

/-! # The three masked native passes produce the reviewed exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem passes_ok {s : State} {base : Addr} {size n marker out k : Nat}
    (C : Context base size n marker out k s) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n =
        (let x := val32 s.mem base out n
         let x1 := if 1 < VG.Proof.RsaKeyGen.sigOf k then x / 2 else x
         let x2 := if 2 < VG.Proof.RsaKeyGen.sigOf k then x1 / 2 else x1
         if 3 < VG.Proof.RsaKeyGen.sigOf k then x2 / 2 else x2) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (halfIf_context C (j := 1) (by decide)) fun a ⟨A, Oa, Va, Ka⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_context A (j := 2) (by decide)) fun b ⟨B, Ob, Vb, Kb⟩ => ?_)
  refine WP.mono (halfIf_context B (j := 3) (by decide)) fun t ⟨T, Ot, Vt, Kt⟩ => ?_
  exact ⟨T, (Oa.trans Ob).trans Ot, by rw [Vt, Vb, Va], (Ka.trans Kb).trans Kt⟩

theorem passes_exponent {s : State} {base : Addr} {size n marker out c : Nat}
    (C : Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) s)
    (odd : c % 2 = 1) (value : val32 s.mem base out n = c / 2) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) t ∧
      Outside base out (4 * n) s.mem t.mem ∧ val32 t.mem base out n = Proof.MillerRabin.Round.exponent c ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (passes_ok C) fun t ⟨T, O, V, K⟩ => ?_
  rw [value, VG.Proof.RsaKeyGen.sigOf_mod] at V
  exact ⟨T, O, V.trans (VG.Proof.RsaKeyGen.mrE_halves odd), K⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFinish.lean`, which only this module imported.
section

/-! # Store the complete paired alignment marker after the prepared exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem finish_ok {s : State} {base : Addr} {size n out : Nat} (scratch : Scr s base size)
    (markerFit : markerOffset + 8 ≤ size) (outFit : out + 4 * n + 8 ≤ size) :
    WP isa (.block (finish n out)) s fun t =>
      word t.mem base (out + 4 * n) = word s.mem base markerOffset ∧
      Outside base (out + 4 * n) 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) outFit) fun t ⟨M, O, Kt⟩ => ?_
  have pair : b.gpr .edx ++ b.gpr .eax = word s.mem base markerOffset := by
    rw [B.gpr, B.other .eax (by decide), A.gpr, A.mem,
      VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [VG.Proof.Mont.word, M, Mem.readW_writeW_self64, pair]
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def ranges (w src out : Nat) : List (Nat × Nat) := [(markerOffset, 8), (src + 8 * w, 4), (out, 8 * w + 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w minusOne src out c : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (minusFit : minusOne + 8 * w ≤ size) (srcFit : src + 8 * w + 4 ≤ size)
    (outFit : out + 8 * w + 8 ≤ size) (lo : markerOffset + 8 ≤ src) (sep : src + 8 * w + 4 ≤ out)
    (candidate : val32 s.mem base src (2 * w) = c)
    (minusValue : val32 s.mem base minusOne (2 * w) = c - 1) (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (code w minusOne src out) s fun t =>
      val32 t.mem base out (2 * w) = Proof.MillerRabin.Round.exponent c ∧
      word t.mem base (out + 8 * w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs base (ranges w src out) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.seq (WP.mono (ExponentMarker.code_ok scratch minusFit minusValue (by omega_using [large]))
    fun a ⟨marker, Ma, Ka⟩ => ?_)
  have Sa := scratch.of_keeps Ka (by decide)
  have markerFit : markerOffset + 8 ≤ size := by omega_using [srcFit, lo]
  refine WP.seq (WP.mono (Header.storePair_ok Sa markerFit) fun b ⟨Mb, Ob, Kb⟩ => ?_)
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  have Sb := scratch.of_keeps Ksb (by unfold clob; decide)
  have candidateB : val32 b.mem base src (2 * w) = c := by
    rw [Ob.val32 (Or.inr lo) (by have := scratch.nowrap; omega_using [srcFit, this]), Ma]
    exact candidate
  have markerB : word b.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [VG.Proof.Mont.word, Mb, Mem.readW_writeW_self64, marker]
  refine WP.seq (WP.mono (firstPass_ok Sb (by omega_using [positive]) (by omega_using [srcFit]) (by omega_using [outFit]) (by omega_using [sep]))
    fun d ⟨valueD, topD, Od, Kd⟩ => ?_)
  have Ksd : Keeps clob s d := Ksb.widen Kd
  have Sd := scratch.of_keeps Ksd (by unfold clob; decide)
  have markerD : word d.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [Od.word (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> left <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, lo, this])]
    exact markerB
  have C : ExponentShift.Context base size (2 * w) markerOffset out
      ((Spec.Rsa.splitTwos (c - 1)).1 % 64) d :=
    ⟨Sd, by omega_using [positive], by omega_using [outFit], markerFit, by omega_using [lo, sep], Nat.mod_lt _ (by decide), markerD, topD⟩
  have valueD' : val32 d.mem base out (2 * w) = c / 2 := by rw [valueD, candidateB]
  refine WP.seq (WP.mono (ExponentShift.passes_exponent C odd valueD') fun e ⟨Ce, Oe, Ve, Ke⟩ => ?_)
  refine WP.mono (finish_ok Ce.scratch markerFit (by omega_using [outFit])) fun t ⟨markerT, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (Ksd.widen Ke).widen Kt⟩
  · rw [Ot.val32 (Or.inl (by omega_using [])) (by have := scratch.nowrap; omega_using [outFit, this])]
    exact Ve
  · have : out + 4 * (2 * w) = out + 8 * w := by omega_using []
    rw [this] at markerT
    exact markerT.trans Ce.value
  · have Fsb : Outs base (ranges w src out) s.mem b.mem := by
      rw [← Ma]
      exact Outs.of_outside Ob (List.mem_cons_self ..)
    have Fd : Outs base (ranges w src out) b.mem d.mem := Od.cover (by
      intro r mem
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact ⟨(src + 8 * w, 4), by simp [ranges], by omega_using [], by omega_using []⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega_using [], by omega_using []⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega_using [], by omega_using []⟩)
    have Fe : Outs base (ranges w src out) d.mem e.mem :=
      Outs.of_outside (Oe.mono (by omega_using []) (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have Ft : Outs base (ranges w src out) e.mem t.mem :=
      Outs.of_outside (Ot.mono (by omega_using []) (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    exact ((Fsb.trans Fd).trans Fe).trans Ft

end VG.Proof.RsaKeyGen.X86.Exponent

end

end


/-! # Preparing the exponent retains the prepared Montgomery context and constants -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def preparedRanges (g : Geometry) : List (Nat × Nat) := ranges g.w (g.array 0) (g.array 27)

theorem prepared_preserve {g : Geometry} (v : g.Valid) {s t : Mem} (O : Outs g.W (preparedRanges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 5 ∨ j = 9 ∨ j = 10) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply O.val32
  · intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl | rfl <;> rcases mem with rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_using []
  · have bound := v.maxWidth
    rcases index with rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [bound]

/-- `Ready` kept by writes to the exponent's ranges. -/
theorem ready_keep {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (O : Outs g.W (preparedRanges g) s.mem t.mem) (K : Keeps clob s t) :
    Ready g c capacity p t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  have fits : ∀ r ∈ preparedRanges g, r.1 + r.2 ≤ g.L := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith
  have metadata : ∀ r ∈ preparedRanges g, (128 ≤ r.1 ∧ r.1 + r.2 ≤ 224) ∨ 256 ≤ r.1 := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · left; decide
    · right; have := v.arrayHeader 0; omega
    · right; exact v.arrayHeader 27
  have F := WorkspaceFrame.of_outs S.scratch.nowrap O
  refine ⟨Prepared.keepGaps v S.context K (by unfold clob; decide) O metadata,
    S.modulus.keep v F (fun r mem => by have := metadata r mem; omega_using [this]) ?_,
    S.caller.keepOuts K (by unfold clob; decide) O fits,
    S.scratch.of_keeps K (by unfold clob; decide)⟩
  intro r mem
  simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
  have top := v.arrayHeader 0
  have before := g.arrayBefore (i := 0) (j := 27) (by decide)
  rcases mem with rfl | rfl | rfl
  · right; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [top]
  · left; unfold Geometry.words; omega_using []
  · left; exact before

theorem ready_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1)
    (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.Exponent.code g.w (g.array 5) (g.array 0) (g.array 27)) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c ∧
      word t.mem g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps clob s t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have apart := Prepared.paddedBefore g (i := 0) (j := 27) (by decide)
  have head := v.headerFit
  refine WP.mono (code_ok S.scratch (by have := v.minWidth; omega_using [this])
    (by have := v.arrayFit (j := 5) (by decide); unfold Geometry.words at this; omega_using [this])
    (by omega_using [srcFit]) (by omega_using [outFit]) (by have := v.arrayHeader 0; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [this])
    (by omega_using [apart]) S.modulus.candidate minusOne odd large) fun t ⟨E, marker, O, K⟩ => ?_
  exact ⟨ready_keep v S O K, E, marker, O, K⟩

end VG.Proof.RsaKeyGen.X86.Exponent
