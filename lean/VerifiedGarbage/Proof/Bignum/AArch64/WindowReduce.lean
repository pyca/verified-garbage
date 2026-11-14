module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowLazy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout

/-! ### `Bignum.AArch64.WindowLazyBound`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64

/-- A reduced product below R + m has a single carry bit above R. -/
theorem top_bound {R L H U m : Nat} (hm : m < R)
    (h : L + R*(H + 2^64*U) < R+m) : U = 0 ∧ H ≤ 1 := by
  have h2 : H + 2^64*U < 2 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left R (show 2 ≤ H+2^64*U by omega_using [hn])
    omega_using [hm, h, hh]
  have hu : U = 0 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left (2^64) (show 1 ≤ U by omega_using [hn])
    omega_using [h2, hn]
  exact ⟨hu, by omega_using [h2]⟩

/-- Expose the high carry as a Boolean without inspecting any secret in control
flow. This is a proof witness for the branch-free masked subtraction. -/
theorem top_bit {s : State} {B : Addr} {e w m : Nat}
    (hm : m < 2^(64*w)) (ht : wv s.mem B e (w+2) < 2^(64*w)+m) :
    ∃ bit : Bool, word s.mem B (e+8*w) = BitVec.ofNat 64 bit.toNat ∧
      wv s.mem B e (w+2) = wv s.mem B e w + 2^(64*w)*bit.toNat := by
  have hh := top_bound hm (by rwa [wv_top2] at ht)
  rcases hh with ⟨hu,hh⟩
  have hw : (word s.mem B (e+8*w)).toNat = 0 ∨ (word s.mem B (e+8*w)).toNat = 1 := by omega_using [hh]
  rcases hw with hw | hw
  · refine ⟨false, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simpa using hw
    · rw [wv_top2, hw, hu]
      simp
  · refine ⟨true, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simpa using hw
    · rw [wv_top2, hw, hu]
      simp

end VG.Proof.Bignum.AArch64.WindowLazy

end

end

/-! ### `Bignum.AArch64.WindowLazyFinish`, which only this module used -/

section

/-! ### `Bignum.AArch64.WindowLazyLoop`, which only this module used -/

section

/-! ### `Bignum.AArch64.WindowLazyTile`, which only this module used -/

section

/-! ### `Bignum.AArch64.WindowLazyWord`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The pointers stay at the tile's start while its four words are processed. -/
structure TileInv (s₀ : State) (B : Addr) (Z eA eN eT j k : Nat) (bit : Bool) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8*j)
  x17 : t.gpr .x17 = off B (eN + 8*j)
  x5 : t.gpr .x5 = off B (eT + 8*j)
  mask : t.gpr .x15 = if bit then -1 else 0
  out : Outside B eT (8*(j+k)) s₀.mem t.mem
  val : wv t.mem B eT (j+k) + bit.toNat * wv s₀.mem B eN (j+k) =
    wv s₀.mem B eA (j+k) + 2 ^ (64*(j+k)) * (!t.c).toNat

theorem word_ok {s₀ : State} {B : Addr} {Z w eA eN eT j k : Nat}
    (hA : eA+8*w ≤ Z) (hN : eN+8*w ≤ Z) (hT : eT+8*w ≤ Z)
    (sA : eT+8*w ≤ eA ∨ eA+8*w ≤ eT) (sN : eT+8*w ≤ eN ∨ eN+8*w ≤ eT)
    (hk : k < 4) (hj : j+k < w) {bit : Bool} {t : State} (hI : TileInv s₀ B Z eA eN eT j k bit t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowLazy.word k)) t fun t' =>
      TileInv s₀ B Z eA eN eT j (k+1) bit t' := by
  have hn := hI.scr.nowrap
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun u =>
    u.mem = t.mem.writeW (off B (eT+8*(j+k)))
      (word t.mem B (eA+8*(j+k)) + ~~~(word t.mem B (eN+8*(j+k)) &&& (if bit then -1 else 0)) + BitVec.ofNat 64 t.c.toNat) ∧
    u.c = decide (2 ^ 64 ≤ (word t.mem B (eA+8*(j+k))).toNat +
      (~~~(word t.mem B (eN+8*(j+k)) &&& (if bit then -1 else 0))).toNat + t.c.toNat)) ?_ rfl rfl rfl)
    fun u ⟨⟨hm, hc⟩, ku⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.WindowLazy.word
    have enc : (8*k) % 8 = 0 ∧ 8*k < 32768 := by omega_arith
    have eAEq : eA+8*j+8*k = eA+8*(j+k) := by omega_arith
    have eNEq : eN+8*j+8*k = eN+8*(j+k) := by omega_arith
    have eTEq : eT+8*j+8*k = eT+8*(j+k) := by omega_arith
    brun [hI.x16, hI.x17, hI.x5, hI.mask, enc,
      hI.scr.ld (show eA+8*j+8*k+8 ≤ Z by omega_arith),
      hI.scr.ld (show eN+8*j+8*k+8 ≤ Z by omega_arith),
      hI.scr.st (show eT+8*j+8*k+8 ≤ Z by omega_arith)]
    all_goals simp only [eAEq, eNEq, eTEq, and_self]
  have hx : word t.mem B (eA+8*(j+k)) = word s₀.mem B (eA+8*(j+k)) :=
    hI.out.word (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eN+8*(j+k)) = word s₀.mem B (eN+8*(j+k)) :=
    hI.out.word (by omega_arith) (by omega_arith)
  refine ⟨hI.scr.congr ku.wr, (hI.keep.trans ku).mono (by decide),
    (ku.gpr .x16 (by decide)).trans hI.x16, (ku.gpr .x17 (by decide)).trans hI.x17,
    (ku.gpr .x5 (by decide)).trans hI.x5,
    (ku.gpr .x15 (by decide)).trans hI.mask, ?_, ?_⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [show j+(k+1) = (j+k)+1 by omega_arith, hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hc]
    have hs := sbcs_toNat (word t.mem B (eA+8*(j+k))) (word t.mem B (eN+8*(j+k)) &&& (if bit then -1 else 0)) t.c
    rw [hx, hy] at hs
    have hv := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy]
    cases bit <;>
      simp only [Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, ite_false, ite_true,
        show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
        Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hs hv ⊢ <;> grind

end VG.Proof.Bignum.AArch64.WindowLazy

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.WindowLazy

structure Inv (s₀ : State) (B : Addr) (Z eA eN eT j : Nat) (bit : Bool) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8*j)
  x17 : t.gpr .x17 = off B (eN + 8*j)
  x5 : t.gpr .x5 = off B (eT + 8*j)
  mask : t.gpr .x15 = if bit then -1 else 0
  out : Outside B eT (8*j) s₀.mem t.mem
  val : wv t.mem B eT j + bit.toNat * wv s₀.mem B eN j =
    wv s₀.mem B eA j + 2 ^ (64*j) * (!t.c).toNat

theorem words_ok {s₀ : State} {B : Addr} {Z w eA eN eT j : Nat}
    (hA : eA+8*w ≤ Z) (hN : eN+8*w ≤ Z) (hT : eT+8*w ≤ Z)
    (sA : eT+8*w ≤ eA ∨ eA+8*w ≤ eT) (sN : eT+8*w ≤ eN ∨ eN+8*w ≤ eT)
    (hj : j+4 ≤ w) {bit : Bool} {t : State} (hI : TileInv s₀ B Z eA eN eT j 0 bit t) :
    WP isa (.block words) t fun t' => TileInv s₀ B Z eA eN eT j 4 bit t' ∧ Keep [.x3, .x4] t t' := by
  have each (k : Nat) (hk : k ≤ 4) {u : State} (hu : TileInv s₀ B Z eA eN eT j 0 bit u) :
      WP isa (.block ((List.range k).flatMap WindowLazy.word)) u fun v => TileInv s₀ B Z eA eN eT j k bit v := by
    induction k with
    | zero => exact WP.block_nil hu
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      exact WP.mono (ih (by omega_using [hk])) fun v hv => word_ok hA hN hT sA sN (by omega_using [hk]) (by omega_using [hj, hk]) hv
  exact WP.keep [.x3, .x4] (each 4 (by omega_using []) hI) rfl rfl rfl

theorem tile_ok {s₀ : State} {B : Addr} {Z n eA eN eT j : Nat}
    (hA : eA+8*(4*n) ≤ Z) (hN : eN+8*(4*n) ≤ Z) (hT : eT+8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT)
    (hj : j < n) {bit : Bool} {t : State} (hI : Inv s₀ B Z eA eN eT (4*j) bit t) :
    WP isa (.block ((words ++ ([.addImm .x .x16 .x16 32,
      .addImm .x .x17 .x17 32, .addImm .x .x5 .x5 32] : List Instr)) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      Inv s₀ B Z eA eN eT (4*(j+1)) bit u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff, WP.block_append_iff]
  have hi : TileInv s₀ B Z eA eN eT (4*j) 0 bit t :=
    ⟨hI.scr, hI.keep, hI.x16, hI.x17, hI.x5, hI.mask, hI.out, hI.val⟩
  refine WP.mono (words_ok hA hN hT sA sN (by omega_using [hj]) hi) fun u ⟨hu, ku⟩ => ?_
  refine WP.mono (WP.keep [.x16, .x17, .x5] (Q := fun v =>
    v.gpr .x16 = off B (eA+8*(4*(j+1))) ∧
    v.gpr .x17 = off B (eN+8*(4*(j+1))) ∧
    v.gpr .x5 = off B (eT+8*(4*(j+1))) ∧ v.mem = u.mem ∧ v.c = u.c)
    (by
      brun [hu.x16, hu.x17, hu.x5,
        show eA+8*(4*j)+32 = eA+8*(4*(j+1)) by omega_using [],
        show eN+8*(4*j)+32 = eN+8*(4*(j+1)) by omega_using [],
        show eT+8*(4*j)+32 = eT+8*(4*(j+1)) by omega_using []]) rfl rfl rfl) fun v ⟨⟨h16, h17, h13, hm, hc⟩, kv⟩ => ?_
  refine WP.mono (dec_ok v .x14) fun z ⟨⟨h14, hzm, hzc⟩, kz⟩ => ⟨?_, ?_⟩
  · refine ⟨hu.scr.congr (kz.wr.trans kv.wr), (hu.keep.trans (kv.trans kz)).mono (by decide),
      (kz.gpr .x16 (by decide)).trans h16, (kz.gpr .x17 (by decide)).trans h17,
      (kz.gpr .x5 (by decide)).trans h13,
      ((kv.trans kz).gpr .x15 (by decide)).trans hu.mask, ?_, ?_⟩
    · rw [hzm, hm, show 4*(j+1) = 4*j+4 by omega_using []]; exact hu.out
    · rw [hzm, hm, hzc, hc, show 4*(j+1) = 4*j+4 by omega_using []]; exact hu.val
  · rw [h14, kv.gpr .x14 (by decide)]
    rw [ku.gpr .x14 (by decide)]

end VG.Proof.Bignum.AArch64.WindowLazy

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The masked subtraction traverses each limb exactly once, independently of
its value. The mask is fixed throughout the loop. -/
theorem loop_ok {s : State} {B : Addr} {Z n eA eN eT : Nat} {bit : Bool}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eN)
    (h5 : s.gpr .x5 = off B eT) (h14 : s.gpr .x14 = BitVec.ofNat 64 n)
    (h15 : s.gpr .x15 = if bit then -1 else 0) (hc : s.c = true)
    (hn : 0 < n) (hn' : n < 2 ^ 64)
    (hA : eA + 8*(4*n) ≤ Z) (hN : eN + 8*(4*n) ≤ Z) (hT : eT + 8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT) :
    WP isa (countLoop .x14 (VG.Impl.Bignum.AArch64.WindowLazy.words ++
      ([.addImm .x .x16 .x16 32, .addImm .x .x17 .x17 32, .addImm .x .x5 .x5 32] : List Instr))) s fun t =>
      wv t.mem B eT (4*n) + bit.toNat * wv s.mem B eN (4*n) =
        wv s.mem B eA (4*n) + 2 ^ (64*(4*n)) * (!t.c).toNat ∧
      Outside B eT (8*(4*n)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x14, .x16, .x17] s t := by
  have h0 : Inv s B Z eA eN eT 0 bit s :=
    ⟨hs, Keep.refl _ _, by simpa using h16, by simpa using h17,
      by simpa using h5, h15, Outside.refl _ _ _ _, by simp [wv, hc]⟩
  exact WP.mono (wp_countdown hn' hn (fun j => Inv s B Z eA eN eT (4*j) bit)
    (fun j hj t hI _ => tile_ok hA hN hT sA sN hj hI) h0 h14)
    fun _ hI => ⟨hI.val, hI.out, hI.keep⟩

end VG.Proof.Bignum.AArch64.WindowLazy

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Final subtraction for a loose Montgomery residue. Its only mask is the
word above the radix; the result is below the radix and congruent modulo m. -/
theorem finish_ok {s : State} {B : Addr} {Z n eA eN eT : Nat} {bit : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h10 : s.gpr .x10 = off B eN)
    (h5 : s.gpr .x5 = off B eT) (h12 : s.gpr .x12 = BitVec.ofNat 64 (4*n))
    (h7 : s.gpr .x7 = 0) (hn : 0 < n) (hn' : 4*n < 2 ^ 31)
    (hA : eA + 8*(4*n+1) ≤ Z) (hN : eN + 8*(4*n) ≤ Z) (hT : eT + 8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n+1) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT)
    (hbit : word s.mem B (eA+8*(4*n)) = BitVec.ofNat 64 bit.toNat)
    (hlt : wv s.mem B eA (4*n) + 2 ^ (64*(4*n)) * bit.toNat <
      2 ^ (64*(4*n)) + wv s.mem B eN (4*n)) :
    WP isa VG.Impl.Bignum.AArch64.WindowLazy.code s fun t =>
      wv t.mem B eT (4*n) % wv s.mem B eN (4*n) =
        (wv s.mem B eA (4*n) + 2 ^ (64*(4*n)) * bit.toNat) % wv s.mem B eN (4*n) ∧
      Outside B eT (8*(4*n)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x14, .x15, .x16, .x17] s t := by
  have hsz := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.WindowLazy.code
  refine WP.seq (WP.mono (WP.keep [.x3, .x14, .x15, .x16, .x17] (Q := fun u =>
    u.gpr .x16 = off B eA ∧ u.gpr .x17 = off B eN ∧
    u.gpr .x14 = BitVec.ofNat 64 n ∧ u.gpr .x15 = (if bit then -1 else 0) ∧
    u.c = true ∧ u.mem = s.mem) ?_ rfl rfl rfl) fun u ⟨⟨h16,h17,h14,h15,hc,hm⟩,ku⟩ => ?_)
  · brun [h8, h10, h12, h7, BlockedRedc.shl3_ofNat (show 4*n < 2^64 by omega_using [hn']),
      Square.shr2_ofNat (show 4*n < 2^64 by omega_using [hn']),
      hs.ld (show eA+8*(4*n)+8 ≤ Z by omega_using [hA])]
    constructor
    · congr 1; omega_using []
    · change 0 - word s.mem B (eA+8*(4*n)) = _
      rw [hbit]
      cases bit <;> rfl
  · have hl := loop_ok (hs.congr ku.wr) h16 h17 ((ku.gpr .x5 (by decide)).trans h5)
      h14 h15 hc hn (by omega_using [hn']) (by omega_using [hA]) hN hT (by omega_using [sA]) sN
    refine WP.mono hl fun t ⟨hv,ho,kt⟩ => ?_
    rw [hm] at hv ho
    refine ⟨lazy_sub (wv_lt _ _ _ _) (Bool.toNat_le _) (Bool.toNat_le _) hlt hv,
      ho, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowLazy

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowArithmetic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Reduction with a loose result, for the full radix-squared product range.
Only the window's final multiplication requires a canonical residue. -/
theorem lazy_ok {s : State} {B : Addr} {Z w o : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2^31) (hmod : w % 8 = 0)
    (h8 : s.gpr .x8 = off B (slot w aAcc+16)) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (ho : o < 8) (_ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (hoN : o ≠ aN)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2^64 = 0) :
    WP isa (VG.Impl.Bignum.AArch64.WindowArithmetic.reduce o true) s fun t =>
      wv t.mem B (slot w o) w * 2^(64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w aAcc+16) (2*w) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc,aTmp,o] s.mem t.mem ∧ Keep WindowRaw.regs s t := by
  have hn := hs.nowrap
  have hsep : slot w aN+8*(w+2) ≤ slot w aAcc+16 := by unfold slot aN aAcc; omega_using []
  have hnz := slot_le (w := w) (show aN < 8 by decide)
  have htz := slot_le (w := w) (show aTmp < 8 by decide)
  have hoz := slot_le (w := w) ho
  have hso := slot_sep (w := w) ho2
  have hson := slot_sep (w := w) hoN
  unfold VG.Impl.Bignum.AArch64.WindowArithmetic.reduce
  simp only [ite_true]
  refine WP.seq (WP.mono (BlockedRedc.redc_layout_ok hs h0 hH hZ h8 h12 h7 hw
    (by omega_using [hw']) hmod) fun r ⟨hrValue,hrOut,hr8,hr10,hr12,hr7,kr⟩ => ?_)
  obtain ⟨q,hq,heq⟩ := hrValue hinv
  have hNR : wv r.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    hrOut.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hnz])
  have hHR := (Square.scratch_arrays hrOut).hdr hH
  have hlt : wv r.mem B (slot w aTmp) (w+2) < 2^(64*w)+wv s.mem B (slot w aN) w := by
    apply redc_lt_add hq _ heq
    simpa only [show 64*(2*w) = 64*w+64*w by omega_using [], Nat.pow_add] using
      wv_lt s.mem B (slot w aAcc+16) (2*w)
  obtain ⟨bit,hbit,hval⟩ := WindowLazy.top_bit (wv_lt s.mem B (slot w aN) w) hlt
  refine WP.seq (WP.mono (Square.finishBases_ok (hs.congr kr.wr)
    ((kr.gpr .x0 (by decide)).trans h0) hHR hZ ho) fun c ⟨⟨hc5,hc6,hcm⟩,kc⟩ => ?_)
  have kw := kr.trans kc
  have hew : 4*(w/4) = w := by omega_using [hmod]
  have hp := WindowLazy.finish_ok (bit := bit) (hs.congr kw.wr)
    ((kc.gpr .x8 (by decide)).trans hr8) ((kc.gpr .x10 (by decide)).trans hr10) hc5
    (by simpa only [hew] using (kc.gpr .x12 (by decide)).trans hr12)
    ((kc.gpr .x7 (by decide)).trans hr7) (by omega_using [hw] : 0 < w/4) (by omega_using [hw'])
    (by omega_using [hZ, htz]) (by omega_using [hZ, hnz]) (by omega_using [hZ, hoz]) (by omega_using [hso]) (by omega_using [hson])
    (by simpa only [hew,hcm] using hbit) (by simpa only [hew,hcm,hNR,← hval] using hlt)
  simp only [hew,hcm,← hval,hNR] at hp
  refine WP.mono hp fun t ⟨hv,ho',kt⟩ => ⟨?_,?_,(kw.trans kt).mono (by decide)⟩
  · rw [Nat.mul_mod, hv, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · have hFrame := (Square.scratch_arrays hrOut).mono (js' := [aAcc,aTmp,o]) (by simp)
    have ho'' : Outside B (slot w o) (8*w) r.mem t.mem := by simpa only [hcm] using ho'
    exact hFrame.trans (Arrays.of_outside (j := o) (by simp) ho'' (Nat.le_refl _) (by omega_using []))

end VG.Proof.Bignum.AArch64.WindowArithmetic
