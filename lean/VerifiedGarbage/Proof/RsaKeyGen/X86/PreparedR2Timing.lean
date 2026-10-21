module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2TimingSquares
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2RoundTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Doubles
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext

/-! # Complete fast prepared R² setup has a candidate-independent trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ 2 ^ (64 * g.w - 1) ≤ c

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s ∧ Input g capacity p t

theorem doubles_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (bound : g.w ≤ 64) :
    RelCT isa (InputPair g capacity p)
      (VG.Impl.RsaKeyGen.X86.FastR2.doubles (modulus g.w) (g.array 2) (g.array 6))
      (SquarePair g capacity p) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, A⟩ := FastR2.doubles_round_trace (modulus g.w) (g.array 2) (g.array 6)
    _ _ _ _ _ _ H.2.2 E G
  have post {a : State} (I : Input g capacity p a) :
      WP isa (VG.Impl.RsaKeyGen.X86.FastR2.doubles (modulus g.w) (g.array 2) (g.array 6)) a
        (SquareInput g capacity p) := by
    obtain ⟨c, C, odd, top⟩ := I
    refine WP.mono (doubles_ready v C bound odd top) fun b ⟨B, value, _, _⟩ => ?_
    exact ⟨c, B, odd, by rw [value]; exact Nat.mod_lt _ (by omega)⟩
  have U := wp_result (post S) E
  have Z := wp_result (post T) G
  obtain ⟨cu, Cu, ou, lu⟩ := U
  obtain ⟨cz, Cz, oz, lz⟩ := Z
  exact ⟨trace, ⟨Cu.context, Cz.context, A⟩, ⟨cu, Cu, ou, lu⟩, ⟨cz, Cz, oz, lz⟩⟩

theorem code_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont)
      (Pair g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.PreparedR2.code VG.Impl.RsaKeyGen.X86.FastR2.code
  rw [Prepared.slot_eq, Prepared.slot_eq]
  refine RelCT.seq (RelCT.seq (doubles_pair v bound) (squares_pair verified noSp stack v length 5)) ?_
  exact (copy_relCT v 4 6 (by decide) (by decide)).mono (fun _ _ H => H.1) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.PreparedR2
