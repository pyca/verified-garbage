module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Doubles
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Square
import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
/-! # Complete fast prepared R² setup has a candidate-independent trace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/PreparedR2TimingSquares.lean`, which only this module imported.
section

/-! # Prepared R² squarings leak no candidate or intermediate residue -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

def SquareInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ val32 s.mem g.W (g.array 6) g.words < c

def SquarePair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ SquareInput g capacity p s ∧ SquareInput g capacity p t

theorem square_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (SquarePair g capacity p) (VG.Impl.MillerRabin.X86.mulY name mont 6)
      (SquarePair g capacity p) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  have input {a : State} (I : SquareInput g capacity p a) : MulInput g capacity 6 p a := by
    obtain ⟨c, A, odd, lt⟩ := I
    exact ⟨A.context, ⟨c, A.modulus, odd, lt⟩, A.caller⟩
  have post {a : State} (I : SquareInput g capacity p a) :
      WP isa (VG.Impl.MillerRabin.X86.mulY name mont 6) a (SquareInput g capacity p) := by
    obtain ⟨c, A, odd, lt⟩ := I
    refine WP.mono (FastR2.square_ok verified noSp stack v A.context length A.modulus A.caller odd lt)
      fun b ⟨Cb, Mb, caller, bound, _, _, K, _⟩ => ?_
    exact ⟨c, ⟨Cb, Mb, caller, A.scratch.of_keeps K (by decide)⟩, odd, bound⟩
  obtain ⟨trace, pair⟩ := mulY_relCT (p := p) verified noSp stack v length
    (by unfold Proof.Rsa.Mont.Operand; decide) _ _ _ _ _ _ ⟨H, input S, input T⟩ E G
  exact ⟨trace, pair, wp_result (post S) E, wp_result (post T) G⟩

theorem squares_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity)
    (n : Nat) :
    RelCT isa (SquarePair g capacity p)
      (VG.Impl.Rsa.X86.Keys.seqs (List.replicate (n + 1) (VG.Impl.MillerRabin.X86.mulY name mont 6)))
      (SquarePair g capacity p) := by
  induction n with
  | zero => exact square_pair verified noSp stack v length
  | succ n ih => exact RelCT.seq (square_pair verified noSp stack v length) ih

end VG.Proof.RsaKeyGen.X86.PreparedR2
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FastR2RoundTiming.lean`, which only this module imported.
section

/-! # Short R² preparation preserves the caller's public stack and workspace base -/

section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.RsaKeyGen.X86.FastR2

theorem seedAt_round_trace (n e out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (seedAt n e out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold seedAt setConstW
  refine RelCT.seq (erased_relCT (σ := roundTaint [.edi]) _ (zerosW 0 1)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (zerosW 0 1))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)) ?_
  apply blockFlatMap_relCT
  intro j
  split
  · exact RelCT.block_nil (fun _ _ h => h)
  · exact erased_relCT _ (.block [.mov .eax (.imm 1), .store (sc 0) .eax])
      (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem seed_round_trace (n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (seed n out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  seedAt_round_trace n _ out

theorem doublesAt_round_trace (M : VG.Impl.Mont.Mod) (e acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (doublesAt M e acc out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  refine RelCT.seq (seedAt_round_trace _ _ _) ?_
  exact erased_relCT (τ := roundTaint [.edi]) (σ := roundTaint [.edi])
    (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (M.n + 64 * M.n - e)))]) (doubleLoop M acc out))
    (.seq (.block [.mov .esi (.imm 1)]) (doubleLoop { n := 1, mo := 0, tmp := 0, minv := 0 } 0 0))
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (.seq (.block [.mov .esi (.imm 1)])
      (doubleLoop { n := 1, mo := 0, tmp := 0, minv := 0 } 0 0))))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem doubles_round_trace (M : VG.Impl.Mont.Mod) (acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (doubles M acc out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  doublesAt_round_trace M _ acc out

end VG.Proof.RsaKeyGen.X86.FastR2
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext

/-- A candidate of at least `e + 1` bits (`FastR2.codeAt`). -/
def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) (e : Nat := 64 * g.w - 1) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ 2 ^ e ≤ c

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) (e : Nat := 64 * g.w - 1) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s e ∧ Input g capacity p t e

theorem doublesAt_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => InputPair g capacity p s t e)
      (VG.Impl.RsaKeyGen.X86.FastR2.doublesAt (modulus g.w) e (g.array 2) (g.array 6))
      (SquarePair g capacity p) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, A⟩ := FastR2.doublesAt_round_trace (modulus g.w) e (g.array 2) (g.array 6)
    _ _ _ _ _ _ H.2.2 E G
  have post {a : State} (I : Input g capacity p a e) :
      WP isa (VG.Impl.RsaKeyGen.X86.FastR2.doublesAt (modulus g.w) e (g.array 2) (g.array 6)) a
        (SquareInput g capacity p) := by
    obtain ⟨c, C, odd, top⟩ := I
    refine WP.mono (doublesAt_ready v C bound odd positive eLt top) fun b ⟨B, value, _, _⟩ => ?_
    exact ⟨c, B, odd, by rw [value]; exact Nat.mod_lt _ (by have := Nat.one_le_two_pow (n := e); omega)⟩
  have U := wp_result (post S) E
  have Z := wp_result (post T) G
  obtain ⟨cu, Cu, ou, lu⟩ := U
  obtain ⟨cz, Cz, oz, lz⟩ := Z
  exact ⟨trace, ⟨Cu.context, Cz.context, A⟩, ⟨cu, Cu, ou, lu⟩, ⟨cz, Cz, oz, lz⟩⟩

theorem code_traceAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    RelCT isa (fun s t => InputPair g capacity p s t e) (VG.Impl.RsaKeyGen.X86.PreparedR2.codeAt e g.w name mont)
      (Pair g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.PreparedR2.codeAt VG.Impl.RsaKeyGen.X86.FastR2.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq]
  refine RelCT.seq (RelCT.seq (doublesAt_pair v bound positive eLt) (squares_pair verified noSp stack v length 5)) ?_
  exact (copy_relCT v 4 6 (by decide) (by decide)).mono (fun _ _ H => H.1) (fun _ _ H => H)

theorem code_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont)
      (Pair g [.edi]) :=
  code_traceAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

end VG.Proof.RsaKeyGen.X86.PreparedR2
