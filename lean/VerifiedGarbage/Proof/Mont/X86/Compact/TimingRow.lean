module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingSetup
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingCarry
import VerifiedGarbage.Proof.Mont.X86.Compact.RowPointer
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Either complete paired-word multiplication row is constant time -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mulRow_relCT {g : Geometry} (v : g.Valid) (modulus : Bool) (w : Nat)
    (low : g.S ≤ w) (high : w + 4 * g.N + 8 ≤ g.S + 8 * g.N + 28) :
    RelCT isa (fun s t => Pair g [.ebp, .edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S ∧
        PtrAt s g.W .ebp w ∧ PtrAt t g.W .ebp w)
      (Compact.mulRow (rowSource modulus)) (Pair g [.ebp, .edi]) := by
  unfold Compact.mulRow
  refine RelCT.seq (setup_relCT v modulus w) (RelCT.seq
    (pairLoop_relCT v (sourceNumber g modulus) w (source_fit v modulus) low (by omega)) ?_)
  exact (carryUp_relCT v (w + 4 * g.N) (by omega) (by omega)).mono
    (fun _ _ H => ⟨pair_regs H.1 (by decide), H.2⟩) (fun _ _ H => H)

theorem mulRow_positioned_relCT {g : Geometry} (v : g.Valid) (modulus : Bool) (w : Nat)
    (low : g.S ≤ w) (high : w + 4 * g.N + 8 ≤ g.S + 8 * g.N + 28) :
    RelCT isa (WindowPair g w) (Compact.mulRow (rowSource modulus)) (WindowPair g w) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, P⟩ := mulRow_relCT v modulus w low high _ _ _ _ _ _ H E G
  obtain ⟨Du, Bu, _, _⟩ := VG.Proof.Dsa.X86.wp_result
    (mulRow_pointer v H.1.1 modulus w low high H.2.1 H.2.2.2.1) E
  obtain ⟨Dz, Bz, _, _⟩ := VG.Proof.Dsa.X86.wp_result
    (mulRow_pointer v H.1.2.1 modulus w low high H.2.2.1 H.2.2.2.2) G
  exact ⟨trace, P, Du, Dz, Bu, Bz⟩

end VG.Proof.Mont.X86.Compact
