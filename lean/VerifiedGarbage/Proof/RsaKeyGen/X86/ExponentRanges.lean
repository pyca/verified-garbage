module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Rsa.X86.InvU
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar

/-! ### `RsaKeyGen.X86.Gcd64Preserve`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.Gcd64Check`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.Gcd64Result`, which this module and modules that import it used -/

section

/-! # The native GCD's low and high words encode one exactly when the return bit is set -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Gcd64

theorem equals_one (low high : BitVec 32) :
    ((low - 1) ||| high).toNat = 0 ↔ Mod64.pair low high = 1 := by
  have zero (x : BitVec 32) : x = 0#32 ↔ x.toNat = 0 :=
    ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
  rw [← zero, BitVec.or_eq_zero_iff, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  constructor
  · rintro ⟨L, H⟩
    rw [L, H]
    rfl
  · intro H
    unfold Mod64.pair at H
    have highZero : high.toNat = 0 := by omega_using [H]
    refine ⟨?_, BitVec.eq_of_toNat_eq highZero⟩
    apply BitVec.eq_of_toNat_eq
    change low.toNat = 1
    omega_using [H]

theorem result_ok {s : State} {base : Addr} {size : Nat}
    (scratch : Scr s base size) (fit : 184 ≤ size) :
    WP isa (.block result) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (val32 s.mem base 176 2 = 1)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold result
  refine wp_movS (readSrc_sc scratch (by omega_using [fit])) fun a A _ => wp_subS rfl fun b B _ => ?_
  have Kb : Keeps [.eax] s b := A.keeps.trans B.keeps
  have read := readSrc_sc (scratch.of_keeps Kb (by decide)) (d := 180) (by omega_using [fit])
  rw [B.mem, A.mem] at read
  refine wp_orS read fun c C => wp_movS rfl fun d D _ => wp_subS rfl fun e E cfE =>
    wp_adcS rfl cfE fun f F _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have tested : d.gpr .eax = (s.mem.readW (off base 176) 32 - 1) ||| s.mem.readW (off base 180) 32 := by
    rw [D.other .eax (by decide), C.gpr, B.gpr, A.gpr]
  refine ⟨?_, ?_, (((((Kb.mono (by decide)).widen C.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen T.keeps⟩
  · rw [T.gpr, F.gpr, E.other .ecx (by decide), D.gpr]
    change 0#32 + 0#32 + _ = _
    rw [BitVec.zero_add, BitVec.zero_add, Near.carry_bit, tested]
    change Near.bit (decide ((((s.mem.readW (off base 176) 32 - 1) ||| s.mem.readW (off base 180) 32).toNat) < 1)) = _
    have eq : val32 s.mem base 176 2 = Mod64.pair (s.mem.readW (off base 176) 32) (s.mem.readW (off base 180) 32) := by
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      rfl
    rw [eq]
    apply congrArg (fun b : Bool => BitVec.ofNat 32 b.toNat)
    apply decide_eq_decide.mpr
    rw [← equals_one]
    omega_using []
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! ### `RsaKeyGen.X86.Gcd64`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.Gcd64Body`, which this module and modules that import it used -/

section

/-! # A pair of verified native binary steps advances the fixed GCD schedule -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Gcd64Step.lean`, which only this module imported.
section

/-! # Reuse the verified native inverse's u/v step as a 64-bit binary GCD step -/

section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem bankStep_ok {s : State} {base : Addr} {size count a b : Nat}
    (W : Ws s base size 2 count) (space : 15 ≤ count) (bank : (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0)) :
    WP isa (bankStep a b) s fun t =>
      Ws t base size 2 count ∧ Keep base 2 [b, b + 1, aT1, aT2, aT3] [sOdd, sB, sC] s.mem t.mem ∧
      (num t.mem base 2 b, num t.mem base 2 (b + 1)) =
        VG.Proof.RsaKeyGen.gcdStep (num s.mem base 2 a) (num s.mem base 2 (a + 1)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  refine WP.mono (invU_ok W space bank) fun t ⟨Wt, F, _, _, V, U, K⟩ => ?_
  refine ⟨Wt, F, ?_, K⟩
  rw [U, V]
  by_cases odd : num s.mem base 2 a % 2 = 1 <;>
    by_cases less : num s.mem base 2 a < num s.mem base 2 (a + 1) <;>
    simp [VG.Proof.RsaKeyGen.gcdStep, odd, less]

end VG.Proof.RsaKeyGen.X86.Gcd64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Gcd64

def arrays : List Nat := [0, 1, 4, 5, aT1, aT2, aT3]
def slots : List Nat := [sOdd, sB, sC]

structure LoopState (s₀ : State) (base : Addr) (size count i : Nat) (s : State) : Prop where
  workspace : Ws s base size 2 count
  frame : Keep base 2 arrays slots s₀.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 (64 - i)
  value : (num s.mem base 2 0, num s.mem base 2 1) =
    VG.Proof.RsaKeyGen.gcdIter (2 * i) (num s₀.mem base 2 0) (num s₀.mem base 2 1)

theorem body_ok {s₀ s : State} {base : Addr} {size count i : Nat} (space : 15 ≤ count)
    (S : LoopState s₀ base size count i s) (index : i < 64) :
    WP isa body s fun t => LoopState s₀ base size count (i + 1) t ∧ t.zf = some (decide (i + 1 = 64)) := by
  unfold body
  refine WP.seq (WP.mono (bankStep_ok S.workspace space (Or.inl ⟨rfl, rfl⟩))
    fun a ⟨Wa, Fa, Va, Ka⟩ => ?_)
  refine WP.seq (WP.mono (bankStep_ok Wa space (Or.inr ⟨rfl, rfl⟩))
    fun b ⟨Wb, Fb, Vb, Kb⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok b) fun t ⟨counter, Z, M, K⟩ => ?_
  have beforeCount : b.gpr .esi = s.gpr .esi := (Kb.1 .esi (by decide)).trans (Ka.1 .esi (by decide))
  have A₀ := congrArg Prod.fst S.value
  have A₁ := congrArg Prod.snd S.value
  dsimp only [Prod.fst, Prod.snd] at A₀ A₁
  rw [A₀, A₁, ← VG.Proof.RsaKeyGen.gcdIter_succ'] at Va
  have V₀ := congrArg Prod.fst Va
  have V₁ := congrArg Prod.snd Va
  dsimp only [Prod.fst, Prod.snd] at V₀ V₁
  rw [V₀, V₁, ← VG.Proof.RsaKeyGen.gcdIter_succ'] at Vb
  refine ⟨⟨Wb.rest K (by decide) (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [M]
    exact (S.frame.trans (Fa.mono (by decide) (by decide))).trans (Fb.mono (by decide) (by decide))
  · exact S.rest.trans (((Ka.mono (by decide)).trans (Kb.mono (by decide))).widen K)
  · rw [counter, beforeCount, S.counter]
    change BitVec.ofNat 32 (64 - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [index])]
    congr 1
  · rw [M, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_using []]
    exact Vb
  · rw [Z, beforeCount, S.counter]
    change some (BitVec.ofNat 32 (64 - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [index]), ofNat_beq_zero (by omega_using [])]
    simp only [show 64 - i - 1 = 0 ↔ i + 1 = 64 by omega_using [index]]

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! # A complete native 64-bit GCD from any odd second operand -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Gcd64Loop.lean`, which only this module imported.
section

/-! # Run exactly 128 binary GCD steps on the two native-word banks -/

section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem code_iter {s : State} {base : Addr} {size count : Nat}
    (W : Ws s base size 2 count) (space : 15 ≤ count) :
    WP isa code s (LoopState s base size count 64) := by
  unfold code
  refine WP.seq (wp_movS rfl fun a A _ => WP.block_nil ?_)
  let Inv := fun q t => ∃ i, i + q = 64 ∧ 0 < q ∧ LoopState s base size count i t
  refine WP.loop (M := isa) Inv ?_ 64 a ?_
  · rintro q t ⟨i, counter, positive, T⟩
    refine WP.mono (body_ok space T (by omega)) fun u ⟨U, Z⟩ => ?_
    by_cases done : i + 1 = 64
    · left
      refine ⟨?_, done ▸ U⟩
      change u.zf.map Bool.not = some false
      rw [Z, decide_eq_true done]
      rfl
    · right
      refine ⟨?_, q - 1, by omega, i + 1, by omega, by omega, U⟩
      change u.zf.map Bool.not = some true
      rw [Z, decide_eq_false done]
      rfl
  · refine ⟨0, by decide, by decide, W.rest A.keeps (by decide) (by decide), ?_, A.keeps.mono (by decide), A.gpr, ?_⟩
    · rw [A.mem]
      exact Keep.refl _ _ _ _ _
    · rw [A.mem]
      rfl

end VG.Proof.RsaKeyGen.X86.Gcd64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem code_ok {s : State} {base : Addr} {size count : Nat}
    (W : Ws s base size 2 count) (space : 15 ≤ count) (odd : num s.mem base 2 1 % 2 = 1) :
    WP isa code s fun t => Ws t base size 2 count ∧ Keep base 2 arrays slots s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      num t.mem base 2 1 = Nat.gcd (num s.mem base 2 0) (num s.mem base 2 1) := by
  have aBound : num s.mem base 2 0 < 2 ^ 64 := val32_lt ..
  have bBound : num s.mem base 2 1 < 2 ^ 64 := val32_lt ..
  have bPositive : 0 < num s.mem base 2 1 := by omega_using [odd]
  have product : num s.mem base 2 0 * num s.mem base 2 1 < 2 ^ 128 := by
    have first := Nat.mul_lt_mul_of_pos_right aBound bPositive
    have second := Nat.mul_lt_mul_of_pos_left bBound (Nat.two_pow_pos 64)
    have H := Nat.lt_trans first second
    rw [show 2 ^ 64 * 2 ^ 64 = (2 : Nat) ^ 128 by rw [← Nat.pow_add]] at H
    exact H
  refine WP.mono (code_iter W space) fun t T => ?_
  have value := T.value
  rw [VG.Proof.RsaKeyGen.gcdIter_eq 128 _ _ odd product] at value
  exact ⟨T.workspace, T.frame, T.rest, congrArg Prod.snd value⟩

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! ### `RsaKeyGen.X86.Gcd64Setup`, which this module and modules that import it used -/

section

/-! # Establish the native GCD workspace from a paired remainder and exponent -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Gcd64Input.lean`, which only this module imported.
section

/-! # Store complete register pairs into the native GCD input banks -/

section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Gcd64

theorem remainderInput_ok {s : State} {base : Addr} {size : Nat}
    (scratch : Scr s base size) (fit : 168 ≤ size) :
    WP isa (.block remainderInput) s fun t =>
      val32 t.mem base 160 2 = Mod64.pair (s.gpr .ecx) (s.gpr .ebx) ∧
      Outside base 160 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold remainderInput
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) fit) fun t ⟨M, O, Kt⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [M, val32_write_pair, B.other .eax (by decide), A.gpr, B.gpr, A.other .ebx (by decide)]
  · rw [B.mem, A.mem] at O
    exact O

theorem exponentInput_ok {s : State} {base : Addr} {size offset : Nat}
    (scratch : Scr s base size) (fit : 184 ≤ size) (sourceFit : offset + 8 ≤ size) :
    WP isa (.block (exponentInput offset)) s fun t =>
      val32 t.mem base 176 2 = Mod64.exponentValue s.mem base offset ∧
      Outside base 176 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold exponentInput
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  refine wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) fit) fun t ⟨M, O, Kt⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [M, val32_write_pair, B.other .eax (by decide), A.gpr, B.gpr, A.mem]
    rfl
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Gcd64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem setup_ok {s : State} {base : Addr} {size offset : Nat}
    (scratch : Scr s base size) (space : 400 ≤ size) (fit : offset + 8 ≤ size)
    (apart : offset + 8 ≤ 160 ∨ 168 ≤ offset) :
    WP isa (.block (setup offset)) s fun t =>
      Ws t base size 2 15 ∧ num t.mem base 2 0 = Mod64.pair (s.gpr .ecx) (s.gpr .ebx) ∧
      num t.mem base 2 1 = Mod64.exponentValue s.mem base offset ∧
      Outside base 160 24 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold setup
  refine WP.block_append (WP.mono (remainderInput_ok scratch (by omega_using [space])) fun a ⟨R, Oa, Ka⟩ => ?_)
  refine WP.mono (exponentInput_ok (scratch.of_keeps Ka (by decide)) (by omega_using [space]) fit)
    fun t ⟨E, Ot, Kt⟩ => ?_
  have K := Ka.trans Kt
  have exponent : Mod64.exponentValue a.mem base offset = Mod64.exponentValue s.mem base offset := by
    change w32 a.mem base offset + 2 ^ 32 * w32 a.mem base (offset + 4) = _
    rw [Oa.w32 (d := offset) (by omega_using [apart]) (by have := scratch.nowrap; omega_using [fit, this]),
      Oa.w32 (d := offset + 4) (by omega_using [apart]) (by have := scratch.nowrap; omega_using [fit, this])]
    rfl
  refine ⟨⟨scratch.of_keeps K (by decide), space, by decide, by decide⟩, ?_, E.trans exponent,
    (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), K⟩
  change val32 t.mem base 160 2 = _
  rw [Ot.val32 (by decide) (by decide)]
  exact R

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! # Complete native 64-bit coprimality check, including precise scratch writes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

def checkRanges : List (Nat × Nat) := [(160, 24)] ++ ranges 2 arrays slots

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! # The native gcd's working space lies below the candidate's arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem ranges_below {r : Nat × Nat} (mem : r ∈ checkRanges) : r.1 + r.2 ≤ 400 := by
  simp only [checkRanges, ranges, arrays, slots, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! # Exponent filtering preserves the candidate header and its saved minus-one array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def ranges (w : Nat) : List (Nat × Nat) := Gcd64.checkRanges ++ [(slot w 0, 8 * w)]

def protectedHeader (d bytes : Nat) : Prop := d + bytes ≤ 100 ∨ 112 ≤ d ∧ d + bytes ≤ 160

theorem gcd_ranges_class {r : Nat × Nat} (mem : r ∈ Gcd64.checkRanges) :
    r.1 + r.2 ≤ 112 ∧ 100 ≤ r.1 ∨ 160 ≤ r.1 := by
  simp only [Gcd64.checkRanges, VG.Proof.Rsa.X86.Keys.ranges, Gcd64.arrays, Gcd64.slots,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  repeat' first
    | (rcases mem with mem | mem)
    | (rcases mem with rfl)
  all_goals decide

theorem ranges_apart {w d bytes : Nat} (safe : protectedHeader d bytes) {r : Nat × Nat}
    (mem : r ∈ ranges w) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rcases List.mem_append.mp mem with mem | mem
  · have C := gcd_ranges_class mem
    unfold protectedHeader at safe
    omega_using [safe, C]
  · obtain rfl := List.mem_singleton.mp mem
    have lo : 256 ≤ slot w 0 := by change 256 ≤ 256 + 0 * stride w; omega_using []
    unfold protectedHeader at safe
    exact Or.inl (by omega)

theorem saved_apart {w : Nat} (width : 4 ≤ w) {r : Nat × Nat} (mem : r ∈ ranges w) :
    r.1 + r.2 ≤ slot w 5 := by
  rcases List.mem_append.mp mem with mem | mem
  · have hi := Gcd64.ranges_below mem
    have lo : 400 ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega_using [width]
    omega_using [hi, lo]
  · obtain rfl := List.mem_singleton.mp mem
    unfold slot stride VG.Impl.Bignum.hdrBytes
    omega_using []

end VG.Proof.RsaKeyGen.X86.ExponentFilter
