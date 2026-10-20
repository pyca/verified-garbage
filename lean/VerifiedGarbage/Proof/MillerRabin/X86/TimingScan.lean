module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSelect
import VerifiedGarbage.Proof.MillerRabin.X86.Mask
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # All sixteen powers are scanned independently of the secret digit -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem maskIndex_pair_relCT {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (Pair g [.edi]) (.block (maskIndex j)) fun s t =>
      Pair g [.edi] s t ∧ masked g s ∧ masked g t := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := maskIndex_relCT j _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, _, _, Cu⟩ := wp_result (maskIndex_ok v H.1 j digit) E
  obtain ⟨Mz, _, _, Cz⟩ := wp_result (maskIndex_ok v H.2.1 j digit) G
  refine ⟨trace, ⟨Cu, Cz, A⟩, ?_, ?_⟩
  · refine ⟨decide ((s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j), ?_⟩
    simpa using Mu
  · refine ⟨decide ((t.mem.readW (off g.W sValue) 32 >>> 28).toNat = j), ?_⟩
    simpa using Mz

theorem scanFrom_relCT {g : Geometry} (v : g.Valid) (n : Nat) :
    ∀ j, j + n ≤ 16 → RelCT isa (Pair g [.edi]) (scanFrom j n) (Pair g [.edi]) := by
  induction n with
  | zero => intro j _; exact RelCT.block_nil (fun _ _ H => H)
  | succ n ih =>
    intro j bound
    exact RelCT.seq (maskIndex_pair_relCT v j (by omega))
      (RelCT.seq (selectEntry_relCT v j (by omega)) (ih (j + 1) (by omega)))

theorem scan_relCT {g : Geometry} (v : g.Valid) : RelCT isa (Pair g [.edi]) scan (Pair g [.edi]) :=
  RelCT.seq (copy_relCT v aX aTable (by decide) (by decide)) (scanFrom_relCT v 15 1 (by decide))

end VG.Proof.MillerRabin.X86
