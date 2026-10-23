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
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
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
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (bound : g.w ≤ 64) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont)
      (Pair g [.edi]) :=
  code_traceAt verified noSp stack v length bound (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega)

end VG.Proof.RsaKeyGen.X86.PreparedR2
