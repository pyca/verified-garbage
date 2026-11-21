module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Init.Data.Nat.Gcd
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import Mathlib.Data.Nat.Prime.Defs
import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Array
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.MillerRabin.X86.SelectLoop
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Rsa.X86.InvU
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
import VerifiedGarbage.TCB.X86.Isa

/-! ### `RsaKeyGen.X86.ExponentRanges`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.NearScalar`, which this module and modules that import it used -/

section

/-! # Scalar flags used by the RSA separation comparison -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near

def bit (b : Bool) : BitVec 32 := BitVec.ofNat 32 b.toNat

theorem bit_toNat (b : Bool) : (bit b).toNat = b.toNat := by cases b <;> rfl

theorem carry_bit (b : Bool) : (BitVec.ofBool b).setWidth 32 = bit b := by cases b <;> rfl

theorem bit_and (a b : Bool) : bit a &&& bit b = bit (a && b) := by cases a <;> cases b <;> rfl

theorem nonzero_bit (low : BitVec 32) :
    1#32 - 0#32 - (BitVec.ofBool (decide (low.toNat < 1))).setWidth 32 = bit (decide (low.toNat ≠ 0)) := by
  by_cases zero : low.toNat = 0
  · rw [zero, decide_eq_true (by decide : (0 : Nat) < 1), decide_eq_false (by decide : ¬ (0 : Nat) ≠ 0)]
    rfl
  · rw [decide_eq_false (by omega_using [zero] : ¬ low.toNat < 1), decide_eq_true zero]
    rfl

theorem nibble_sum (nibble low : BitVec 32) (bound : nibble.toNat < 16) :
    (nibble + bit (decide (low.toNat ≠ 0))).toNat = nibble.toNat + (decide (low.toNat ≠ 0)).toNat := by
  rw [BitVec.toNat_add, bit_toNat]
  have delta : (decide (low.toNat ≠ 0)).toNat ≤ 1 := by cases decide (low.toNat ≠ 0) <;> decide
  omega_using [bound, delta]

end VG.Proof.RsaKeyGen.X86.Near

end

end

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
  unfold Impl.RsaKeyGen.X86.Gcd64.code
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

end

end

/-! ### `RsaKeyGen.X86.CandidateBranch`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.CandidateDrawn`, which the modules that import this one used -/

section

/-! # Register and flag operations retain the drawn candidate and input snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86

theorem Input.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (I : Input E eBytes pBytes entropy s) (M : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (syms : t.syms = s.syms) : Input E eBytes pBytes entropy t := by
  have F : WorkFrame E s.mem t.mem := by rw [M]; exact Frame.refl _ _
  refine I.keep v K base sp F ?_ ?_ (by rw [syms])
  · intro i index; rw [M]; exact I.header i index
  · rw [M]; exact I.usedPointer

theorem Drawn.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s) (M : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (syms : t.syms = s.syms) : Drawn E eBytes pBytes entropy t := by
  have F : WorkFrame E s.mem t.mem := by rw [M]; exact Frame.refl _ _
  refine ⟨D.input.keep v K base sp F ?_ ?_ (by rw [syms]), ?_, ?_, ?_⟩
  · intro i index; rw [M]; exact D.input.header i index
  · rw [M]; exact D.input.usedPointer
  · rw [M]; exact D.candidate
  · rw [M]; exact D.used
  · rw [M]; exact D.zeros

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Candidate branch flags are exact Boolean status tests -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem cmp_bool {s : State} {bit : Bool} (flag : s.gpr .eax = BitVec.ofNat 32 bit.toNat) :
    WP isa (.block [.alu .cmp .eax (.imm 0)]) s fun t =>
      Fupd s t ∧ isa.eval .e t = some (!bit) ∧ isa.eval .ne t = some bit := by
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨T, ?_, ?_⟩
  · change t.zf = _
    rw [Z, flag]
    cases bit <;> decide
  · change t.zf.map Bool.not = _
    rw [Z, flag]
    cases bit <;> decide

theorem cmp_src_cf {s : State} {src : Src} {value : BitVec 32} (read : readSrc s src = some value) :
    WP isa (.block [.alu .cmp .eax src]) s fun t =>
      Fupd s t ∧ t.cf = some (decide ((s.gpr .eax).toNat < value.toNat)) := by
  refine cons (s' := arithFlags s (s.gpr .eax - value)
    (decide ((s.gpr .eax).toNat < value.toNat)) (subOverflow (s.gpr .eax) value (s.gpr .eax - value)))
    (by simp only [exec, execAlu, read, Option.bind_some]) (WP.block_nil ?_)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.ExponentRt.General`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.ExponentRt.Copy`, which this module and modules that import it used -/

section

/-! # Saving the candidate minus one into array 5, and restoring it, at a run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

/-- `copyCount`: `esi = 2 w` words, and the mask `ecx` of a copy. -/
theorem copyCount_ok {s : State} {base : Addr} {size w : Nat} {is : List Instr} {Q : State → Prop}
    (S : Scr s base size) (header : 8 ≤ size) (hw : w ≤ 64)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (k : ∀ u, Keeps [.esi, .ecx] s u → u.mem = s.mem → (u.gpr .esi).toNat = 2 * w →
      u.gpr .ecx = BitVec.allOnes 32 → WP isa (.block is) u Q) :
    WP isa (.block (copyCount ++ is)) s Q := by
  simp only [copyCount, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc S (by omega_using [header])) fun a A _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun b B => wp_movS rfl fun u U _ => ?_
  obtain K : Keeps [.esi, .ecx] s u := ((A.keeps.trans B.keeps).mono (by decide)).trans (U.keeps.mono (by decide))
  refine k u K (by rw [U.mem, B.mem, A.mem]) ?_ U.gpr
  rw [U.other .esi (by decide), B.gpr, A.gpr, len, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hw]), Nat.shiftRight_eq_div_pow]
  omega_using []

/-- `copyLoop` over `N` words from `y` to `x`. -/
theorem copyLoop_ok {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (dstFit : x + 4 * N ≤ L) (srcFit : y + 4 * N ≤ L)
    (apart : x + 4 * N ≤ y ∨ y + 4 * N ≤ x)
    (dst : PtrAt s W .ebx x) (src : PtrAt s W .ebp y) (count : (s.gpr .esi).toNat = N)
    (mask : s.gpr .ecx = BitVec.allOnes 32) :
    WP isa copyLoop s fun t =>
      Outside W x (4 * N) s.mem t.mem ∧ val32 t.mem W x N = val32 s.mem W y N ∧
      Keeps [.eax, .ebx, .ebp, .esi] s t :=
  VG.Proof.MillerRabin.X86.selectLoop_ok hw positive dstFit srcFit apart dst src count true
    (by rw [mask]; rfl)

theorem saveSetup_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (hw : w ≤ 64)
    (header : 8 ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block saveSetup) s
      fun d => Keeps [.ebx, .edx, .esi, .ecx, .ebp] s d ∧ d.mem = s.mem ∧
        d.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 256 ∧ d.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
        (d.gpr .esi).toNat = 2 * w ∧ d.gpr .ecx = BitVec.allOnes 32 := by
  simp only [saveSetup, List.cons_append]
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  obtain Kb : Keeps [.ebp] s b := (A.keeps.trans B.keeps)
  obtain Sb := S.of_keeps Kb (by decide)
  obtain edib : b.gpr .edi = s.gpr .edi := Kb.1 .edi (by decide)
  refine savedPtr_ok Sb header (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebx => ?_
  obtain Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc header hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  refine ⟨(Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kd.mono (by decide))),
    by rw [Md, Mc, B.mem, A.mem], ?_, ?_, esi, ecx⟩
  · rw [Kd.1 .ebp (by decide), Kc.1 .ebp (by decide), B.gpr, A.gpr]; rfl
  · rw [Kd.1 .ebx (by decide), ebx, edib]

theorem restoreSetup_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (hw : w ≤ 64)
    (header : 8 ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block restoreSetup) s
      fun d => Keeps [.ebx, .edx, .esi, .ecx, .ebp] s d ∧ d.mem = s.mem ∧
        d.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 256 ∧ d.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
        (d.gpr .esi).toNat = 2 * w ∧ d.gpr .ecx = BitVec.allOnes 32 := by
  simp only [restoreSetup, List.cons_append]
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  obtain Kb : Keeps [.ebx] s b := (A.keeps.trans B.keeps)
  obtain Sb := S.of_keeps Kb (by decide)
  obtain edib : b.gpr .edi = s.gpr .edi := Kb.1 .edi (by decide)
  refine savedPtr_ok Sb header (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebp => ?_
  obtain Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc header hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  refine ⟨(Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kd.mono (by decide))),
    by rw [Md, Mc, B.mem, A.mem], ?_, ?_, esi, ecx⟩
  · rw [Kd.1 .ebx (by decide), Kc.1 .ebx (by decide), B.gpr, A.gpr]; rfl
  · rw [Kd.1 .ebp (by decide), ebp, edib]

theorem save_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : val32 s.mem base (slot w 0) (2 * w) % 2 = 1) :
    WP isa save s fun t =>
      val32 t.mem base (slot w 5) (2 * w) + 1 = val32 s.mem base (slot w 0) (2 * w) ∧
      Outside base (slot w 5) (8 * w) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain lo := slot5_ge w
  have nowrap := S.nowrap
  rw [slot0_eq] at odd ⊢
  obtain hws : Ws s base size := ⟨S.wr, S.nowrap⟩
  unfold save saveSetup
  simp only [List.cons_append]
  refine WP.seq (wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_)
  obtain Kb : Keeps [.ebp] s b := (A.keeps.trans B.keeps)
  obtain Sb := S.of_keeps Kb (by decide)
  obtain ebp : b.gpr .ebp = b.gpr .edi + BitVec.ofNat 32 256 := by
    rw [B.gpr, A.gpr, Kb.1 .edi (by decide)]; rfl
  refine savedPtr_ok Sb (by omega_using [width, space]) (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebx => ?_
  obtain Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc (by omega_using [width, space]) hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  obtain Kbd : Keeps [.ebx, .edx, .esi, .ecx] b d := (Kc.mono (by decide)).trans (Kd.mono (by decide))
  obtain Sd := Sb.of_keeps Kbd (by decide)
  obtain edi : d.gpr .edi = b.gpr .edi := Kbd.1 .edi (by decide)
  obtain Md' : d.mem = s.mem := by rw [Md, Mc, B.mem, A.mem]
  obtain K6 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.mono (by decide)).trans (Kbd.mono (by decide))
  refine WP.seq (WP.mono (copyLoop_ok (hws.of_keeps K6) (x := slot w 5) (y := 256) (N := 2 * w) (by omega_using [width]) (by omega_using [space]) (by omega_using [space, lo])
    (by omega_using [lo]) (ptrAt_edi Sd (by rw [Kd.1 .ebx (by decide), ebx, edi]))
    (ptrAt_edi Sd (by rw [Kbd.1 .ebp (by decide), ebp, edi])) esi ecx) fun e ⟨Oe, Ve, Ke⟩ => ?_)
  obtain Se := Sd.of_keeps Ke (by decide)
  obtain Le : e.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) :=
    (BitVec.eq_of_toNat_eq (Oe.w32 (d := 4) (Or.inl (by omega_using [lo])) (by omega_using []))).trans (by rw [Md']; exact len)
  refine WP.seq (WP.mono (savedPtr_block_ok Se (by omega_using [width, space]) Le (by decide) (by decide) (by decide))
    fun f ⟨Kf, Mf, ebxf⟩ => ?_)
  unfold decrementAt
  obtain Sf := Se.of_keeps Kf (by decide)
  obtain Pf : PtrAt f base .ebx (slot w 5) := ptrAt_edi Sf (by rw [ebxf, Kf.1 .edi (by decide)])
  obtain hwf : Ws f base size := hws.of_keeps ((K6.trans (Ke.mono (by decide))).trans (Kf.mono (by decide)))
  refine wp_movS (readSrc_ptr hwf Pf (d := 0) (by omega_using [width, space])) fun g G _ => wp_subS rfl fun h H _ => ?_
  obtain Kh : Keeps [.eax] f h := G.keeps.trans H.keeps
  obtain Ph : PtrAt h base .ebx (slot w 5) := by rw [PtrAt, Kh.1 .ebx (by decide)]; exact Pf
  refine wp_storeS (ea_ptr (hwf.of_keeps Kh) Ph (d := 0) (by omega_using [width, space]))
    (ws_write (hwf.of_keeps Kh) (y := slot w 5 + 0) (n := 4) (by omega_using [width, space])) fun t T => WP.block_nil ?_
  obtain copied : val32 f.mem base (slot w 5) (2 * w) = val32 s.mem base 256 (2 * w) := by
    rw [Mf, Ve, Md']
  obtain lowPos : 0 < w32 f.mem base (slot w 5) := by
    have := VG.Proof.RsaKeyGen.X86.LowWord.odd_low (m := f.mem) (base := base) (out := slot w 5) (n := 2 * w)
      (by omega_using [width]) (by rw [copied]; exact odd)
    exact this
  obtain Ot : Outside base (slot w 5) 4 f.mem t.mem := by
    rw [T.mem, H.mem, G.mem, Nat.add_zero]
    exact writeW32_outside _ _ _ (by omega_using [space, nowrap])
  obtain low : w32 t.mem base (slot w 5) + 1 = w32 f.mem base (slot w 5) := by
    simp only [T.mem, Nat.add_zero, w32_write_self, H.gpr, G.gpr]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact lowPos)]
    change w32 f.mem base (slot w 5) - 1 + 1 = _
    omega_using [lowPos]
  refine ⟨?_, ?_, ?_⟩
  · rw [← copied, show 2 * w = (2 * w - 1) + 1 by omega_using [width], val32, val32,
      Ot.val32 (Or.inr (by omega_using [])) (by omega_using [space, nowrap])]
    omega_using [low]
  · rw [show f.mem = e.mem from Mf] at Ot
    rw [← Md', show 8 * w = 4 * (2 * w) by omega_using []]
    exact Oe.trans (Ot.mono (by omega_using []) (by omega_using [width]))
  · exact ((K6.trans (Ke.mono (by decide))).trans (Kf.mono (by decide))).trans
      ((Kh.mono (by decide)).widen (T.keeps []))

theorem restore_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (even : val32 s.mem base (slot w 5) (2 * w) % 2 = 0) :
    WP isa restore s fun t =>
      val32 t.mem base (slot w 0) (2 * w) = val32 s.mem base (slot w 5) (2 * w) + 1 ∧
      Outside base (slot w 0) (8 * w) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain lo := slot5_ge w
  have nowrap := S.nowrap
  rw [slot0_eq]
  obtain hws : Ws s base size := ⟨S.wr, S.nowrap⟩
  unfold restore restoreSetup
  simp only [List.cons_append]
  refine WP.seq (wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_)
  obtain Kb : Keeps [.ebx] s b := (A.keeps.trans B.keeps)
  obtain Sb := S.of_keeps Kb (by decide)
  obtain ebx : b.gpr .ebx = b.gpr .edi + BitVec.ofNat 32 256 := by
    rw [B.gpr, A.gpr, Kb.1 .edi (by decide)]; rfl
  refine savedPtr_ok Sb (by omega_using [width, space]) (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebp => ?_
  obtain Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc (by omega_using [width, space]) hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  obtain Kbd : Keeps [.ebp, .edx, .esi, .ecx] b d := (Kc.mono (by decide)).trans (Kd.mono (by decide))
  obtain Sd := Sb.of_keeps Kbd (by decide)
  obtain edi : d.gpr .edi = b.gpr .edi := Kbd.1 .edi (by decide)
  obtain Md' : d.mem = s.mem := by rw [Md, Mc, B.mem, A.mem]
  obtain K6 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.mono (by decide)).trans (Kbd.mono (by decide))
  refine WP.seq (WP.mono (copyLoop_ok (hws.of_keeps K6) (x := 256) (y := slot w 5) (N := 2 * w) (by omega_using [width]) (by omega_using [space, lo]) (by omega_using [space])
    (by omega_using [lo]) (ptrAt_edi Sd (by rw [Kbd.1 .ebx (by decide), ebx, edi]))
    (ptrAt_edi Sd (by rw [Kd.1 .ebp (by decide), ebp, edi])) esi ecx) fun e ⟨Oe, Ve, Ke⟩ => ?_)
  obtain Se := Sd.of_keeps Ke (by decide)
  obtain copied : val32 e.mem base 256 (2 * w) = val32 s.mem base (slot w 5) (2 * w) := by rw [Ve, Md']
  obtain bound : w32 e.mem base 256 + 1 < 2 ^ 32 :=
    VG.Proof.RsaKeyGen.X86.LowWord.even_low (n := 2 * w) (by omega_using [width]) (by rw [copied]; exact even)
  refine WP.mono (VG.Proof.RsaKeyGen.X86.LowWord.increment_ok Se (n := 2 * w) (by omega_using [width]) (by omega_using [space, lo]) bound)
    fun t ⟨V, Ot, Kt⟩ => ?_
  refine ⟨by rw [V, copied], ?_, ?_⟩
  · rw [← Md', show 8 * w = 4 * (2 * w) by omega_using []]
    exact Oe.trans (Ot.mono (by omega_using []) (by omega_using [width]))
  · exact (K6.trans (Ke.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.RsaKeyGen.X86.ExponentRt

end

end

/-! # An arbitrary odd public exponent: one remainder and a fixed native gcd, at a run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt
open VG.Proof.RsaKeyGen.X86 (Gcd64.checkRanges)

/-- Setting up and running the gcd keep the length in the header. -/
theorem gcd_keep_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (width : 4 ≤ w) (space : slot w 5 + 8 * w ≤ size)
    (odd : Mod64.exponentValue s.mem base 128 % 2 = 1) :
    WP isa (.seq (.block (VG.Impl.RsaKeyGen.X86.Gcd64.setup 128)) VG.Impl.RsaKeyGen.X86.Gcd64.code) s fun t =>
      Scr t base size ∧ t.mem.readW (off base 4) 32 = s.mem.readW (off base 4) 32 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have lo' := slot5_eq w
  refine WP.seq (WP.mono (Gcd64.setup_ok scratch (by omega_using [width, space, lo']) (by omega_using [space, lo']) (by decide)) fun a ⟨Wa, R, E, Oa, Ka⟩ => ?_)
  refine WP.mono (Gcd64.code_ok Wa (by decide) (by rw [E]; exact odd)) fun b ⟨Wb, F, Kb, V⟩ => ?_
  have Ftotal : Outs base Gcd64.checkRanges s.mem b.mem :=
    (Outs.of_outside Oa (List.mem_append_left _ (List.mem_singleton_self _))).trans
      (Outs.mono F (fun _ mem => List.mem_append_right _ mem))
  have h := Ftotal.val32 (d := 4) (k := 1)
    (fun r mem => Or.inl (by have := ExponentFilter.gcd_ranges_class mem; omega_using [this])) (by have := scratch.nowrap; omega_using [])
  simp only [val32, w32, Nat.mul_zero, Nat.add_zero] at h
  exact ⟨Wb.workspace, BitVec.eq_of_toNat_eq h, (Ka.mono (by decide)).trans (Kb.mono (by decide))⟩

theorem preserving_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64) (space : slot w 5 + 8 * w ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : Mod64.exponentValue s.mem base 128 % 2 = 1)
    (even : val32 s.mem base (slot w 5) (2 * w) % 2 = 0) :
    WP isa (.seq (.block (VG.Impl.RsaKeyGen.X86.Gcd64.setup 128)) (.seq VG.Impl.RsaKeyGen.X86.Gcd64.code
      (.seq restore (.block VG.Impl.RsaKeyGen.X86.Gcd64.result)))) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (Mod64.pair (s.gpr .ecx) (s.gpr .ebx))
        (Mod64.exponentValue s.mem base 128) = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = val32 s.mem base (slot w 5) (2 * w) + 1 ∧
      Outs base (Gcd64.checkRanges ++ [(slot w 0, 8 * w)]) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have lo := slot5_ge w
  have lo' := slot5_eq w
  have space' : 400 ≤ size := by omega_using [width, space, lo']
  refine WP.seq (WP.mono (Gcd64.setup_ok scratch space' (by omega_using [space']) (by decide)) fun a ⟨Wa, R, E, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Gcd64.code_ok Wa (by decide) (by rw [E]; exact odd)) fun b ⟨Wb, F, Kb, V⟩ => ?_)
  have Ftotal : Outs base Gcd64.checkRanges s.mem b.mem :=
    (Outs.of_outside Oa (List.mem_append_left _ (List.mem_singleton_self _))).trans
      (Outs.mono F (fun _ mem => List.mem_append_right _ mem))
  have savedValue : val32 b.mem base (slot w 5) (2 * w) = val32 s.mem base (slot w 5) (2 * w) :=
    Ftotal.val32 (fun r mem => Or.inr (by have := Gcd64.ranges_below mem; omega_using [width, lo', this]))
      (by have := scratch.nowrap; omega_using [hw, lo'])
  have lenB : b.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
    have h := Ftotal.val32 (d := 4) (k := 1)
      (fun r mem => Or.inl (by have := ExponentFilter.gcd_ranges_class mem; omega_using [this])) (by omega_using [])
    simp only [val32, w32, Nat.mul_zero, Nat.add_zero] at h
    exact (BitVec.eq_of_toNat_eq h).trans len
  refine WP.seq (WP.mono (restore_ok Wb.workspace width hw space lenB (by rw [savedValue]; exact even))
    fun c ⟨restored, Oc, Kc⟩ => ?_)
  rw [slot0_eq] at restored Oc
  refine WP.mono (Gcd64.result_ok (Wb.workspace.of_keeps Kc (by decide)) (by omega_using [space']))
    fun t ⟨test, M, Kt⟩ => ?_
  have bank : num c.mem base 2 1 = num b.mem base 2 1 :=
    Oc.val32 (Or.inl (by change 176 + 4 * 2 ≤ 256; omega_using [])) (by change 176 + 4 * 2 ≤ 2 ^ 64; decide)
  change t.gpr .eax = BitVec.ofNat 32 (decide (num c.mem base 2 1 = 1)).toNat at test
  rw [bank, V, R, E] at test
  refine ⟨test, ?_, ?_, ?_⟩
  · rw [M, slot0_eq, restored, savedValue]
  · rw [M, slot0_eq]
    exact (Ftotal.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Oc (List.mem_append_right _ (List.mem_singleton_self _)))
  · have K1 : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s b := ((Ka.mono (by decide)).trans Kb).mono (by decide)
    exact (K1.trans (Kc.mono (by decide))).widen Kt

theorem general_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1)
    (large : 1 < candidate) (cOdd : candidate % 2 = 1)
    (eValue : Mod64.exponentValue s.mem base 128 = exponent) (eOdd : exponent % 2 = 1)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa general s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = candidate ∧
      Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      WorkspaceFrame ⟨base, size, w⟩ (ExponentFilter.ranges w) s.mem t.mem := by
  have sizeBound : 400 ≤ size := by have := slot5_eq w; omega_using [width, space, this]
  unfold general
  refine WP.seq (WP.mono (framed_ok S width hw space len saved eValue (by omega_using [eOdd]) fit separate)
    fun a ⟨Sa, remainder, savedA, eA, Fa, Ka⟩ => ?_)
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega_using [fit]) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  have lenA : a.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
    rw [← len]
    exact Fa.readW (r := ⟨base, size⟩) (Offset.contains_base _ (by omega_using [sizeBound]) (by have := S.nowrap; omega_using []))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far) (by decide)
  refine WP.mono (preserving_ok Sa width hw space lenA (by rw [eA]; exact eOdd) (by rw [savedA]; omega_using [cOdd]))
    fun t ⟨result, restored, O, K⟩ => ?_
  have Wa : WorkspaceFrame ⟨base, size, w⟩ [] s.mem a.mem :=
    VG.Proof.RsaKeyGen.X86.workspace_of_frame Fa S.nowrap
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far)
  have Wb : WorkspaceFrame ⟨base, size, w⟩ (ExponentFilter.ranges w) a.mem t.mem := WorkspaceFrame.of_outs S.nowrap O
  refine ⟨?_, ?_, ?_, (Ka.mono (by decide)).trans (K.mono (by decide)),
    (Wa.mono (by intro r mem; nomatch mem)).trans Wb⟩
  · rw [remainder, eA] at result
    have gcdEq : Nat.gcd ((candidate - 1) % exponent) exponent = Nat.gcd (candidate - 1) exponent :=
      (Nat.gcd_rec exponent (candidate - 1)).symm.trans (Nat.gcd_comm _ _)
    simpa only [gcdEq] using result
  · rw [restored, savedA]; omega_using [large]
  · have Fb : Frame [⟨base, size⟩] a.mem t.mem := workspaceGlobalFrame
      (g := ⟨base, size, 0⟩) O (by
        intro r mem
        change r.1 + r.2 ≤ size
        rcases List.mem_append.mp mem with mem | mem
        · exact Nat.le_trans (Gcd64.ranges_below mem) sizeBound
        · obtain rfl := List.mem_singleton.mp mem; have := slot5_ge w; simp only [slot0_eq]; omega_using [space, this])
    exact (Fa.mono (fun _ mem => List.mem_cons_of_mem _ mem)).trans
      (Fb.mono (fun _ mem => by obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self))

end VG.Proof.RsaKeyGen.X86.ExponentRt

end

end

/-! ### `RsaKeyGen.X86.ExponentRt.Fast`, which this module and modules that import it used -/

section

/-! # The 65537 filter over the saved candidate minus one at a run-time width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/FermatExponent.lean`, which only this module imported.
section

/-! # Coprimality for RSA's usual public exponent

65537 is prime, so a candidate minus one is coprime to it exactly when
its whole-word trial reduction is nonzero. This permits the normal exponent
to reuse the native trial kernel; other exponents need the general check.
-/

section
namespace VG.Proof.RsaKeyGen

theorem prime65537 : Nat.Prime 65537 := by
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

theorem coprime65537 (c : Nat) : Nat.gcd c 65537 = 1 ↔ c % 65537 ≠ 0 := by
  change Nat.Coprime c 65537 ↔ _
  rw [Nat.coprime_comm, prime65537.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]

end VG.Proof.RsaKeyGen
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FermatExponent.lean`, which only this module imported.
section

/-! # The usual RSA exponent needs one whole-word reduction and no general gcd -/

section
namespace VG.Proof.RsaKeyGen.X86.FermatExponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.FermatExponent

theorem xor_one {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .eax (s.gpr .eax ^^^ 1) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .xor .eax (.imm 1) :: is)) s Q :=
  cons (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _))

theorem code_ok (s : State) (p : BitVec 32) (w endOffset : Nat)
    (positive : 0 < w) (lengthBound : 4 * (2 * w) < 2 ^ 32) (fit : p.toNat + 4 * (2 * w) ≤ 2 ^ 32)
    (candidateRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * i)) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = p + BitVec.ofNat 32 (4 * (2 * w)))
    (ptr : s.gpr .edi = p) :
    WP isa (code endOffset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  unfold Impl.RsaKeyGen.X86.FermatExponent.code init
  refine WP.seq (wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_movS rfl fun c C _ => WP.block_nil ?_)
  obtain K : Keeps [.ebx, .esi, .ebp] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  obtain M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  obtain prime : c.gpr .ebx = 65537#32 := by rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]; rfl
  obtain inv : c.gpr .esi = 65535#32 := by rw [C.other .esi (by decide), B.gpr]; rfl
  obtain sp : c.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  refine WP.seq (WP.mono (Trial.divisor_ok c p w endOffset positive lengthBound fit
    (by intro i index; rw [K.2.1, K.2.2]; exact candidateRead i index)
    (by rw [K.2.1, K.2.2, sp]; exact endRead)
    (by rw [M, sp]; exact endValue) ((K.1 .edi (by decide)).trans ptr) C.gpr
    (by rw [prime]; decide) (by rw [prime]; decide) (by rw [prime]; decide)
    (by rw [prime, inv]; decide +kernel)) fun d ⟨V, Md, Kd⟩ => ?_)
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s d := (K.mono (by decide)).widen Kd
  refine xor_one fun t T => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (Md.trans M), Kall.widen T.keeps⟩
  rw [T.gpr, V, M, prime]
  change BitVec.ofNat 32 (decide (val32 s.mem (p.setWidth 64) 0 (2 * w) % 65537 = 0)).toNat ^^^ 1 = _
  obtain coprime := VG.Proof.RsaKeyGen.coprime65537 (val32 s.mem (p.setWidth 64) 0 (2 * w))
  by_cases divides : val32 s.mem (p.setWidth 64) 0 (2 * w) % 65537 = 0
  · rw [decide_eq_true divides, decide_eq_false (by omega : ¬ Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)]
    rfl
  · rw [decide_eq_false divides, decide_eq_true (coprime.mpr divides)]
    rfl

end VG.Proof.RsaKeyGen.X86.FermatExponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

theorem val32_off (m : Mem) (base : Addr) (start d n : Nat) :
    val32 m (off base start) d n = val32 m base (start + d) n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [val32, ih, w32, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [Nat.add_assoc]

theorem fastArgs_ok {p : BitVec 32} {w : Nat} {s : State} {base : Addr} {size : Nat}
    (C : VG.Proof.RsaKeyGen.X86.Sieve.StackContext p s) (S : Scr s base size) (header : 8 ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block fastArgs) s fun t =>
      t.gpr .edi = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
      t.mem.readW (off (p.setWidth 64) 4) 32 = s.gpr .edi + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w) ∧
      t.mem.readW (off (p.setWidth 64) 0) 32 = s.gpr .edi ∧
      Outside (p.setWidth 64) 0 8 s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .edi] s t := by
  unfold fastArgs
  refine savedPtr_ok S header len (by decide) (by decide) (by decide) fun a Ka Ma eaxA => ?_
  obtain Sa := S.of_keeps Ka (by decide)
  refine wp_movS (readSrc_sc Sa (by omega_using [header])) fun b B _ => ?_
  obtain Kb : Keeps [.eax, .ecx, .edx] s b := (Ka.mono (by decide)).trans (B.keeps.mono (by decide))
  obtain Cb := C.keep Kb (by decide)
  refine wp_storeS (Cb.address 0 (by decide)) (ws_write Cb.ws (by decide)) fun c D => ?_
  obtain Cc := Cb.keep (D.keeps []) (by decide)
  refine wp_movS rfl fun d E _ => wp_addS rfl fun e F _ => ?_
  obtain K : Keeps [.eax, .ecx, .edx, .edi] s e :=
    (((Kb.mono (by decide)).trans ((D.keeps []).mono (by decide))).trans (E.keeps.mono (by decide))).trans
      (F.keeps.mono (by decide))
  obtain Ce := C.keep K (by decide)
  refine wp_storeS (Ce.address 4 (by decide)) (ws_write Ce.ws (by decide)) fun t T => WP.block_nil ?_
  obtain ediS : b.gpr .edi = s.gpr .edi := Kb.1 .edi (by decide)
  obtain eaxD : d.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w 5) := by
    rw [E.other .eax (by decide), D.gpr, B.other .eax (by decide), eaxA]
  obtain value : e.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w) := by
    rw [F.gpr, eaxD, F.other .ecx (by decide) |>.symm.trans (F.other .ecx (by decide)), E.other .ecx (by decide),
      D.gpr, B.gpr, Ma, len]
  obtain memE : e.mem = c.mem := F.mem.trans E.mem
  obtain Oc : Outside (p.setWidth 64) 0 4 s.mem c.mem := by
    rw [D.mem, B.mem, Ma]
    exact writeW32_outside _ _ _ (by decide)
  obtain Ot : Outside (p.setWidth 64) 4 4 c.mem t.mem := by
    rw [T.mem, memE]
    exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, ?_, ?_, (Oc.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)),
    K.widen (T.keeps [])⟩
  · rw [T.gpr, F.other .edi (by decide), E.gpr, D.gpr, B.other .eax (by decide), eaxA]
  · rw [T.mem, Mem.readW_writeW_self32, value]
  · rw [BitVec.eq_of_toNat_eq (Ot.w32 (d := 0) (by decide) (by decide)), D.mem, Mem.readW_writeW_self32, ediS]

theorem fast_ok {s : State} {base : Addr} {size w candidate : Nat}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa fast s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) 65537 = 1)).toNat ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let p := s.gpr .edi + BitVec.ofNat 32 (slot w 5)
  obtain slotBound : slot w 5 + 8 * w ≤ 2 ^ 32 := Nat.le_trans space (by have := S.nowrap; omega_using [this])
  obtain pbase : p.setWidth 64 = off base (slot w 5) := S.ea (d := slot w 5) (by omega_using [width, space])
  obtain pnat : p.toNat = base.toNat + slot w 5 := by
    change (s.gpr .edi + BitVec.ofNat 32 (slot w 5)).toNat = base.toNat + slot w 5
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
    rw [Nat.mod_eq_of_lt (a := slot w 5) (by omega_using [width, slotBound]),
      Nat.mod_eq_of_lt (by have := S.nowrap; omega_using [width, space, this])]
  obtain far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega_using [fit]) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  obtain sourceFar : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint (below (s.gpr .esp) 20) := by
    apply Region.Disjoint.sub_left far
    intro x hx
    rw [pbase] at hx
    exact Offset.sub_base base space x hx
  obtain sourceRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * i)) 4 := by
    intro i index
    rw [pbase]
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add] using S.read (d := slot w 5 + 4 * i) (n := 4) (by omega_using [space, index])
  unfold fast
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega_using [fit]) (NoSp.of_all (by rfl)) ?_
  let initial := allocFrame 20 s
  obtain C : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (s.gpr .esp - 20#32) initial :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by omega_using [fit])
  obtain Si : Scr initial base size := VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S (by omega_using [fit])
    (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  refine WP.seq (WP.mono (fastArgs_ok (w := w) C Si (by omega_using [width, space]) (by rw [allocFrame_mem]; exact len))
    fun a ⟨ptrA, endA, savedA, Oa, Ka⟩ => ?_)
  obtain ptr : a.gpr .edi = p := by rw [ptrA, allocFrame_gpr _ _ (by decide)]
  obtain Ca := C.keep Ka (by decide)
  obtain frameA : Frame [below (s.gpr .esp) 20] s.mem a.mem := by
    simpa only [allocFrame_mem, below, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame (Oa.mono (o' := 0) (n' := 20) (by decide) (by decide)) (by decide)
  obtain value : val32 a.mem (p.setWidth 64) 0 (2 * w) = val32 s.mem (p.setWidth 64) 0 (2 * w) := by
    apply val32_congr
    intro i index
    exact congrArg BitVec.toNat (frameA.readW (r := ⟨p.setWidth 64, 8 * w⟩)
      (Offset.contains_base _ (by omega_using [index]) (by omega_using [widthBound, index]))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact sourceFar) (by decide))
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.FermatExponent.code_ok a p w 4 (by omega_using [width]) (by omega_using [widthBound])
    (by rw [pnat]; have := S.nowrap; omega_using [space, this])
    (by
      intro i index
      rw [Ka.2.1, Ka.2.2]
      obtain ⟨r, mem, contains⟩ := sourceRead i index
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp mem with mem | mem
      · exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem))
    (Ca.access 4 (by decide)) (by
      change a.mem.readW (a.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4)) 32 = _
      rw [Ca.address 4 (by decide), endA, allocFrame_gpr _ _ (by decide)]
      rw [show 4 * (2 * w) = 8 * w by omega_using []]) ptr) fun b ⟨result, Mb, Kb⟩ => ?_)
  obtain Cb := Ca.keep Kb (by decide)
  refine wp_movS (v := initial.gpr .edi) (by
    change readSrc b (.mem (VG.Impl.RsaKeyGen.X86.Sieve.slot 0)) = some (initial.gpr .edi)
    rw [Cb.read 0 (by decide), Mb, savedA]) fun t T _ => WP.block_nil ?_
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] initial t :=
    ((Ka.mono (by decide)).trans Kb).widen T.keeps
  have restored : t.gpr .edi = initial.gpr .edi := T.gpr
  obtain Kbody : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] initial t := by
    refine ⟨?_, Kall.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact restored
    · exact Kall.1 r (by cases r <;> simp_all)
  intro m _ fl
  refine ⟨?_, ?_, VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps Kbody (by decide)⟩
  · show (freed 20 t).gpr .eax = _
    rw [freed_gpr _ _ (by decide), T.other .eax (by decide), result, value, pbase,
      val32_off, Nat.add_zero, saved]
  · show Frame _ s.mem m
    rw [T.mem, Mb] at fl
    exact frameA.trans fl

end VG.Proof.RsaKeyGen.X86.ExponentRt

end

end

/-! ### `RsaKeyGen.X86.ExponentFilterContext`, which this module and modules that import it used -/

section

/-! # Public geometry and preserved candidate data across exponent classification -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.MillerRabin.X86

structure Input (base : Addr) (size w candidate exponent : Nat) (s : State) : Prop where
  scratch : Scr s base size
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 + 8 * w ≤ size
  original : val32 s.mem base (slot w 0) (2 * w) = candidate
  saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1
  large : 1 < candidate
  odd : candidate % 2 = 1
  exponentEq : Mod64.exponentValue s.mem base 128 = exponent
  fit : 40 ≤ (s.gpr .esp).toNat
  separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat

theorem Input.header {base : Addr} {size w candidate exponent : Nat} {s : State}
    (S : Input base size w candidate exponent s) : 136 ≤ size := by
  have := S.space
  simp only [slot, VG.Impl.Bignum.X86.PublicContext.stride, VG.Impl.Bignum.hdrBytes] at this
  omega_using [this]

theorem Input.keepReadonly {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s) (M : t.mem = s.mem) (K : Keeps [.eax] s t) :
    Input base size w candidate exponent t := by
  refine ⟨S.scratch.of_keeps K (by decide), S.width, S.widthBound, S.space, ?_, ?_, S.large, S.odd, ?_, ?_, ?_⟩
  · rw [M]; exact S.original
  · rw [M]; exact S.saved
  · rw [M]; exact S.exponentEq
  · rw [K.1 .esp (by decide)]; exact S.fit
  · rw [K.1 .esp (by decide)]; exact S.separate

structure Output (base : Addr) (size w candidate exponent : Nat) (s t : State) : Prop where
  result : t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat
  original : val32 t.mem base (slot w 0) (2 * w) = candidate
  frame : Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  workspace : WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem

theorem Output.prepend {base : Addr} {size w candidate exponent : Nat} {s a t : State}
    (H : Output base size w candidate exponent a t) (M : a.mem = s.mem) (K : Keeps [.eax] s a) :
    Output base size w candidate exponent s t := by
  refine ⟨H.result, H.original, ?_, (K.mono (by decide)).trans H.keeps, ?_⟩
  · have F := H.frame
    rw [K.1 .esp (by decide), M] at F
    exact F
  · rw [← M]; exact H.workspace

theorem Input.readonlyOutput {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s)
    (result : t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) exponent = 1)).toNat)
    (M : t.mem = s.mem) (K : Keeps [.eax] s t) : Output base size w candidate exponent s t := by
  refine ⟨result, ?_, ?_, K.mono (by decide), ?_⟩
  · rw [M]; exact S.original
  · rw [M]; exact Frame.refl _ _
  · rw [M]; exact WorkspaceFrame.refl _ _ _

theorem Input.stackFrameValue {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s) (F : Frame [below (s.gpr .esp) 20] s.mem t.mem) :
    val32 t.mem base (slot w 0) (2 * w) = candidate := by
  rw [← S.original]
  apply val32_congr
  intro i index
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    FilterStack.allocated_apart (by have := S.fit; omega_using [this]) S.scratch.nowrap
      (by have := S.separate; rcases this with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  have sourceFit : slot w 0 + 8 * w ≤ size := by
    have := S.space
    simp only [slot, VG.Impl.Bignum.X86.PublicContext.stride, VG.Impl.Bignum.hdrBytes] at this ⊢
    omega_using [this]
  exact congrArg BitVec.toNat (F.readW (r := ⟨base, size⟩)
    (Offset.contains_base _ (by omega_using [index, sourceFit]) (by have := S.scratch.nowrap; omega_using [index, sourceFit, this]))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far) (by decide))

theorem Input.stackWorkspaceFrame {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (S : Input base size w candidate exponent s) (F : Frame [below (s.gpr .esp) 20] s.mem t.mem) :
    WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem := by
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    FilterStack.allocated_apart (by have := S.fit; omega_using [this]) S.scratch.nowrap
      (by have := S.separate; rcases this with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))
  have W : WorkspaceFrame ⟨base, size, w⟩ [] s.mem t.mem :=
    workspace_of_frame F S.scratch.nowrap (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact far)
  exact W.mono (by intro r mem; nomatch mem)

theorem Output.savedValue {base : Addr} {size w candidate exponent : Nat} {s t : State}
    (O : Output base size w candidate exponent s t) (width : 4 ≤ w) (space : slot w 5 + 8 * w ≤ size) :
    val32 t.mem base (slot w 5) (2 * w) = val32 s.mem base (slot w 5) (2 * w) :=
  O.workspace.val32 (by change slot w 5 + 4 * (2 * w) ≤ size; omega_using [space]) (fun _ mem => Or.inr (saved_apart width mem))

end VG.Proof.RsaKeyGen.X86.ExponentFilter

end

end

/-! ### `RsaKeyGen.X86.ExponentClass`, which this module and modules that import it used -/

section

/-! # Branches on the public exponent inspect its complete native 64-bit value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentFilter

theorem exponent_word (m : Mem) (base : Addr) (offset : Nat) :
    Mod64.exponentValue m base offset = (word m base offset).toNat := by
  rw [word_eq_w32]
  rfl

theorem pair_parity (low high : BitVec 32) : Mod64.pair low high % 2 = low.toNat % 2 := by
  unfold Mod64.pair
  omega_using []

theorem pair_equal (low high : BitVec 32) {value : Nat} (bound : value < 2 ^ 32) :
    (low ^^^ BitVec.ofNat 32 value ||| high == 0#32) = decide (Mod64.pair low high = value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  change (low.toNat = value ∧ high.toNat = 0) ↔ low.toNat + 2 ^ 32 * high.toNat = value
  have := low.isLt
  omega_using [bound]

theorem parity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (fit : 136 ≤ size) :
    WP isa (.block parity) s fun t =>
      t.zf = some (decide (Mod64.exponentValue s.mem base 128 % 2 = 0)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold parity
  refine wp_movS (readSrc_sc S (d := 128) (by omega_using [fit])) fun a A _ => wp_andi fun b B =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans (T.keeps _)⟩
  rw [Z, B.gpr, A.gpr]
  change some ((s.mem.readW (off base 128) 32 &&& 1#32) - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_and]
  change (s.mem.readW (off base 128) 32).toNat &&& 1 = 0 ↔ Mod64.exponentValue s.mem base 128 % 2 = 0
  rw [Nat.and_one_is_mod]
  change (s.mem.readW (off base 128) 32).toNat % 2 = 0 ↔ Mod64.exponentValue s.mem base 128 % 2 = 0
  unfold Mod64.exponentValue
  rw [pair_parity]

theorem equal_ok {s : State} {base : Addr} {size value : Nat} (S : Scr s base size)
    (fit : 136 ≤ size) (bound : value < 2 ^ 32) :
    WP isa (.block (equal value)) s fun t =>
      t.zf = some (decide (Mod64.exponentValue s.mem base 128 = value)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold equal
  refine wp_movS (readSrc_sc S (d := 128) (by omega_using [fit])) fun a A _ =>
    wp_logicS (Or.inr rfl) rfl fun b B => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  refine wp_orS (readSrc_sc (S.of_keeps K (by decide)) (d := 132) (by omega_using [fit])) fun d D =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (D.mem.trans (B.mem.trans A.mem)), (K.trans D.keeps).trans (T.keeps _)⟩
  rw [Z, D.gpr, B.gpr, A.gpr, B.mem, A.mem]
  simp only [show AluOp.xor ≠ AluOp.and by decide, ite_false]
  change some (((s.mem.readW (off base 128) 32 ^^^ BitVec.ofNat 32 value) ||| s.mem.readW (off base 132) 32) - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  change some ((s.mem.readW (off base 128) 32 ^^^ BitVec.ofNat 32 value) ||| s.mem.readW (off base 132) 32 == 0#32) = _
  rw [pair_equal _ _ bound]
  rfl

end VG.Proof.RsaKeyGen.X86.ExponentFilter

end

end

/-! # The exponent stage at a run-time width: save, import and coprimality, with the candidate kept -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/EvenExponent.lean`, which only this module imported.
section

/-! # An even exponent cannot be coprime to an odd candidate minus one -/

section
namespace VG.Proof.RsaKeyGen

theorem even_exponent_rejected {c e : Nat} (odd : c % 2 = 1) (large : 1 < c) (even : e % 2 = 0) :
    Nat.gcd (c - 1) e ≠ 1 := by
  have dc : 2 ∣ c - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have de : 2 ∣ e := Nat.dvd_of_mod_eq_zero even
  have both := Nat.dvd_gcd dc de
  intro one
  rw [one] at both
  exact (by decide : ¬ 2 ∣ 1) both

end VG.Proof.RsaKeyGen
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentRt/Filter.lean`, which only this module imported.
section

/-! # The exponent filter at a run-time width returns the exact coprimality bit -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.ExponentRt VG.Impl.RsaKeyGen.X86.ExponentFilter
open VG.Proof.RsaKeyGen.X86.ExponentFilter (Input Output)

theorem nontrivial_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Input base size w candidate exponent s) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : exponent % 2 = 1) :
    WP isa (.seq (.block (equal 65537)) (.ite .e fast general)) s
      (Output base size w candidate exponent s) := by
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentFilter.equal_ok S.scratch S.header (by decide : 65537 < 2 ^ 32))
    fun a ⟨Z, M, K⟩ => ?_)
  have A := S.keepReadonly M K
  have lenA : a.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by rw [M]; exact len
  rw [S.exponentEq] at Z
  by_cases common : exponent = 65537
  · refine WP.ite true (by change a.zf = _; rw [Z, decide_eq_true common]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine WP.mono (fast_ok A.scratch A.width A.widthBound A.space lenA A.saved A.fit A.separate)
      fun t ⟨result, F, Kt⟩ => ?_
    apply Output.prepend (s := s) (a := a) _ M K
    refine ⟨?_, A.stackFrameValue F, F.mono (fun _ mem => List.mem_cons_of_mem _ mem), Kt, A.stackWorkspaceFrame F⟩
    simpa only [common] using result
  · refine WP.ite false (by change a.zf = _; rw [Z, decide_eq_false common]) (fun impossible => nomatch impossible) (fun _ => ?_)
    refine WP.mono (general_ok A.scratch A.width A.widthBound A.space lenA A.saved A.large A.odd A.exponentEq odd
      A.fit A.separate) fun t ⟨result, original, F, Kt, W⟩ => ?_
    exact (show Output base size w candidate exponent a t from ⟨result, original, F, Kt, W⟩).prepend M K

theorem odd_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Input base size w candidate exponent s) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : exponent % 2 = 1) :
    WP isa (.seq (.block (equal 1)) (.ite .e (.block [.mov .eax (.imm 1)])
      (.seq (.block (equal 65537)) (.ite .e fast general)))) s
      (Output base size w candidate exponent s) := by
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentFilter.equal_ok S.scratch S.header (by decide : 1 < 2 ^ 32))
    fun a ⟨Z, M, K⟩ => ?_)
  have A := S.keepReadonly M K
  rw [S.exponentEq] at Z
  by_cases one : exponent = 1
  · refine WP.ite true (by change a.zf = _; rw [Z, decide_eq_true one]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    apply Output.prepend (s := s) (a := a) _ M K
    apply A.readonlyOutput _ T.mem T.keeps
    rw [T.gpr]
    simp only [one, Nat.gcd_one_right, decide_true, Bool.toNat_true]
    rfl
  · refine WP.ite false (by change a.zf = _; rw [Z, decide_eq_false one]) (fun impossible => nomatch impossible) (fun _ => ?_)
    exact WP.mono (nontrivial_ok A (by rw [M]; exact len) odd) fun _ H => H.prepend M K

theorem filter_ok {s : State} {base : Addr} {size w candidate exponent : Nat}
    (S : Input base size w candidate exponent s) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa filter s (Output base size w candidate exponent s) := by
  unfold filter
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.ExponentFilter.parity_ok S.scratch S.header) fun a ⟨Z, M, K⟩ => ?_)
  have A := S.keepReadonly M K
  rw [S.exponentEq] at Z
  by_cases even : exponent % 2 = 0
  · refine WP.ite true (by change a.zf = _; rw [Z, decide_eq_true even]) (fun _ => ?_) (fun impossible => nomatch impossible)
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    apply Output.prepend (s := s) (a := a) _ M K
    apply A.readonlyOutput _ T.mem T.keeps
    rw [T.gpr]
    simp only [decide_eq_false (VG.Proof.RsaKeyGen.even_exponent_rejected S.odd S.large even), Bool.toNat_false]
    rfl
  · refine WP.ite false (by change a.zf = _; rw [Z, decide_eq_false even]) (fun impossible => nomatch impossible) (fun _ => ?_)
    exact WP.mono (odd_ok A (by rw [M]; exact len) (by omega)) fun _ H => H.prepend M K

end VG.Proof.RsaKeyGen.X86.ExponentRt
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentImport.lean`, which only this module imported.
section

/-! # Full-width exponent import agrees with the reviewed arbitrary-byte input -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentImport
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem code_ok {s : State} {base : Addr} {size len : Nat} {source : BitVec 32}
    (S : Scr s base size) (header : 256 ≤ size)
    (pointer : s.mem.readW (off base 12) 32 = source) (length : w32 s.mem base 16 = len)
    (positive : 0 < len) (bound : len ≤ 8) (sourceFit : source.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (source.setWidth 64) len)
    (separate : (⟨source.setWidth 64, len⟩ : Region).Disjoint ⟨off base 128, 8⟩) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentImport.code s fun t =>
      word t.mem base 128 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (source.setWidth 64) len)) ∧
      Outside base 128 8 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentImport.code
  refine WP.seq (wp_movS (readSrc_sc S (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 16) (by omega)) fun b B _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b :=
    (A.keeps.mono (by decide)).widen B.keeps
  have mem : b.mem = s.mem := B.mem.trans A.mem
  have ptr : b.gpr .esi = source := by rw [B.other .esi (by decide), A.gpr, pointer]
  have count : b.gpr .ecx = BitVec.ofNat 32 len := by
    rw [B.gpr, A.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← length, Nat.mod_eq_of_lt (s.mem.readW (off base 16) 32).isLt]
  refine WP.mono (VG.Proof.Bignum.X86.loadBE_ok (S.of_keeps K (by decide)) (by decide) (by omega)
    positive bound (by rw [ptr]; exact sourceFit) count
    (by rw [ptr, K.2.1, K.2.2]; exact readable) (by rw [ptr]; exact separate))
    fun t ⟨value, O, Kt⟩ => ?_
  rw [mem, ptr] at value
  rw [mem] at O
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at value
  change (word t.mem base 128).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (source.setWidth 64) len) at value
  exact ⟨by apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← value, Nat.mod_eq_of_lt (word t.mem base 128).isLt], O, K.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentImport
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def ranges (w : Nat) : List (Nat × Nat) := [(slot w 5, 8 * w), (128, 8)] ++ ExponentFilter.ranges w

theorem prepare_ok {s : State} {base : Addr} {size w candidate len : Nat} {e : BitVec 32}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size)
    (candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate)
    (large : 1 < candidate) (odd : candidate % 2 = 1)
    (pointer : s.mem.readW (off base 12) 32 = e) (length : w32 s.mem base 16 = len)
    (ePositive : 0 < len) (eBound : len ≤ 8) (eFit : e.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (e.setWidth 64) len)
    (separateE : (⟨e.setWidth 64, len⟩ : Region).Disjoint ⟨base, size⟩)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat)
    (outLen : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code) s fun t =>
      ExponentFilter.Input base size w candidate
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)) t ∧
      WorkspaceFrame ⟨base, size, w⟩ [(slot w 5, 8 * w), (128, 8)] s.mem t.mem ∧
      Frame [⟨base, size⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      t.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
  have gap : slot w 0 + 8 * w ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega_using []
  have savedLo : 400 ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega_using [width]
  have sourceLo : 256 ≤ slot w 0 := by change 256 ≤ 256 + 0 * stride w; omega_using []
  have header : 256 ≤ size := by omega_using [space, savedLo]
  have exponentBound : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len) < 2 ^ 64 := by
    calc _ < 256 ^ len := by
           simpa only [VG.Proof.Bignum.bytesAt_length] using VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)
         _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) eBound
         _ = 2 ^ 64 := by decide
  refine WP.seq (WP.mono (save_ok S width widthBound space outLen
    (by rw [candidateEq]; exact odd)) fun a ⟨saved, Oa, Ka⟩ => ?_)
  rw [candidateEq] at saved
  have savedA : val32 a.mem base (slot w 5) (2 * w) = candidate - 1 := by omega_using [saved]
  have originalA : val32 a.mem base (slot w 0) (2 * w) = candidate :=
    (Oa.val32 (Or.inl (by omega_using [gap])) (by have := S.nowrap; omega_using [space, gap, this])).trans candidateEq
  have Sa := S.of_keeps Ka (by decide)
  have Fa := VG.Proof.Bignum.outside_frame Oa (by have := S.nowrap; omega_using [space, this])
  have eUnchanged : Spec.Rsa.bytesAt a.mem (e.setWidth 64) len = Spec.Rsa.bytesAt s.mem (e.setWidth 64) len :=
    VG.Proof.RsaKeyGen.frame_bytesAt Fa
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact separateE.sub_right (Offset.sub_base base space))
      (by omega_using [eBound])
  refine WP.mono (ExponentImport.code_ok Sa header
    (by rw [BitVec.eq_of_toNat_eq (Oa.w32 (d := 12) (by omega_using [width, gap]) (by decide))]; exact pointer)
    (by rw [Oa.w32 (d := 16) (by omega_using [width, gap]) (by decide)]; exact length)
    ePositive eBound eFit (by rw [Ka.2.1, Ka.2.2]; exact readable)
    (separateE.sub_right (Offset.sub_base base (by omega_using [header])))) fun b ⟨value, Ob, Kb⟩ => ?_
  rw [eUnchanged] at value
  have originalB := (Ob.val32 (d := slot w 0) (k := 2 * w) (Or.inr (by omega_using [sourceLo])) (by have := S.nowrap; omega_using [space, gap, this])).trans originalA
  have savedB := (Ob.val32 (d := slot w 5) (k := 2 * w) (Or.inr (by omega_using [savedLo])) (by have := S.nowrap; omega_using [space, this])).trans savedA
  have exponentEq : Mod64.exponentValue b.mem base 128 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len) := by
    rw [ExponentFilter.exponent_word, value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt exponentBound]
  have Ksb : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (Ka.mono (by decide)).trans Kb
  have I : ExponentFilter.Input base size w candidate (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)) b :=
    ⟨Sa.of_keeps Kb (by decide), width, widthBound, space, originalB, savedB, large, odd, exponentEq,
      by rw [Ksb.1 .esp (by decide)]; exact fit, by rw [Ksb.1 .esp (by decide)]; exact separateStack⟩
  have Wa : WorkspaceFrame ⟨base, size, w⟩ [(slot w 5, 8 * w)] s.mem a.mem :=
    WorkspaceFrame.of_outs S.nowrap (Outs.of_outside Oa (List.mem_singleton_self _))
  have Wb : WorkspaceFrame ⟨base, size, w⟩ [(128, 8)] a.mem b.mem :=
    WorkspaceFrame.of_outs S.nowrap (Outs.of_outside Ob (List.mem_singleton_self _))
  have W : WorkspaceFrame ⟨base, size, w⟩ [(slot w 5, 8 * w), (128, 8)] s.mem b.mem :=
    (Wa.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans
      (Wb.mono (fun _ mem => List.mem_cons_of_mem _ mem))
  have Fsave : Frame [⟨base, size⟩] s.mem a.mem := workspaceGlobalFrame (g := ⟨base, size, w⟩)
    (Outs.of_outside Oa (List.mem_singleton_self _)) (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change slot w 5 + 8 * w ≤ size; exact space)
  have Fimport : Frame [⟨base, size⟩] a.mem b.mem := workspaceGlobalFrame (g := ⟨base, size, w⟩)
    (Outs.of_outside Ob (List.mem_singleton_self _)) (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 128 + 8 ≤ size; omega_using [header])
  have lenB : b.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
    rw [BitVec.eq_of_toNat_eq (Ob.w32 (d := 4) (by omega_using []) (by omega_using [])),
      BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (by have := slot5_eq w; omega_using [width, gap]) (by omega_using [])), outLen]
  exact ⟨I, W, Fsave.trans Fimport, Ksb, lenB⟩

theorem code_ok {s : State} {base : Addr} {size w candidate len : Nat} {e : BitVec 32}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size)
    (candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate)
    (large : 1 < candidate) (odd : candidate % 2 = 1)
    (pointer : s.mem.readW (off base 12) 32 = e) (length : w32 s.mem base 16 = len)
    (ePositive : 0 < len) (eBound : len ≤ 8) (eFit : e.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (e.setWidth 64) len)
    (separateE : (⟨e.setWidth 64, len⟩ : Region).Disjoint ⟨base, size⟩)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat)
    (outLen : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentRt.code s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)) = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = candidate ∧
      val32 t.mem base (slot w 5) (2 * w) = candidate - 1 ∧
      WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem ∧
      Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentRt.code
  apply WP.assoc
  refine WP.seq (WP.mono (prepare_ok S width widthBound space candidateEq large odd pointer length
    ePositive eBound eFit readable separateE fit separateStack outLen) fun b ⟨I, Wb, Fb, Kb, lenB⟩ => ?_)
  refine WP.mono (filter_ok I lenB) fun t T => ?_
  have W : WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem :=
    (Wb.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (T.workspace.mono (fun _ mem => List.mem_append_right _ mem))
  refine ⟨T.result, T.original, (T.savedValue width space).trans I.saved, W, ?_, Kb.trans T.keeps⟩
  have Ft := T.frame
  rw [Kb.1 .esp (by decide)] at Ft
  exact (Fb.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans Ft

end VG.Proof.RsaKeyGen.X86.ExponentRt
