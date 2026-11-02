module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquares
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquareStep

/-! # The square loop branches only on its public countdown -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem squareLoop_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ SquareInput g capacity p q s ∧ SquareInput g capacity p q t)
      (squareLoop name code) (Pair g [.edi]) := by
  unfold squareLoop
  refine (private_count_loop (F := fun q (_ : Unit) s => SquareInput g capacity p q s) ?_ q positive).mono
    (fun _ _ H => ⟨H.1, ⟨(), H.2.1⟩, ⟨(), H.2.2⟩⟩) (fun _ _ H => H.1)
  intro n positive
  refine private_control ?_ (fun _ s I => I.step verified noSp stack v length positive)
    (fun _ _ I => I.context) positive
  exact (squareStep_trace verified noSp stack v length).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.mulInput, H.2.2.choose_spec.mulInput⟩) (fun _ _ H => H)

end VG.Proof.MillerRabin.X86
