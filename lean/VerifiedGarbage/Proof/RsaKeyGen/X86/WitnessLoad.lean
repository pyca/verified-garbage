module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessSample
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData

/-! # Entropy import and interval sampling retain all reusable candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) (width : input.count = g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * g.w) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessLoad.code g.w) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.code
  rw [Prepared.slot_eq, Prepared.slot_eq]
  have dstAddr : input.dst.setWidth 64 = off g.W (g.array 6) := by
    rw [← destination]
    have fit : g.array 6 < g.L := by
      have fit := v.arrayFit (j := 6) (by decide)
      have := v.minWidth
      unfold Geometry.words at fit
      omega
    exact S.ready.scratch.ea fit
  have region : input.destRegion = ⟨off g.W (g.array 6), 4 * g.words⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr, width]
  have load := Import.load_ok C source destination
  rw [width] at load
  change WP isa (VG.Impl.RsaKeyGen.X86.Import.load g.words (g.array 6)) s _ at load
  change WP isa (.seq (VG.Impl.RsaKeyGen.X86.Import.load g.words (g.array 6)) _) s _
  refine WP.seq (WP.mono load fun a ⟨value, F, K⟩ => ?_)
  have Va : val32 a.mem g.W (g.array 6) g.words =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (8 * g.w)) := by
    rw [dstAddr, show 4 * g.words = 8 * g.w by unfold Geometry.words; omega] at value
    rw [← VG.Proof.Bignum.read_eq_val32, show 4 * g.words = 8 * g.w by unfold Geometry.words; omega]
    exact value
  rw [region] at F
  have Oa := frame_outside F (by have := S.ready.scratch.nowrap; have := v.arrayFit (j := 6) (by decide); omega)
  have A := WitnessMont.data_outside v S Oa K (by decide) (by decide)
  refine WP.mono (WitnessSample.code_ok A.ready.scratch (by have := v.minWidth; omega)
    (by have := v.arrayFit (j := 6) (by decide); unfold Geometry.words at this; omega)
    (by have := v.arrayFit (j := 0) (by decide); unfold Geometry.words at this; omega)
    (Or.inr (by have := g.arrayBefore (i := 0) (j := 6) (by decide); unfold Geometry.words at this; omega))
    A.ready.modulus.candidate Va odd shape) fun t ⟨Vt, mask, Ot, Kt⟩ => ?_
  have Ot' : Outside g.W (g.array 6) (4 * g.words) a.mem t.mem := by
    rw [show 4 * g.words = 8 * g.w by unfold Geometry.words; omega]
    exact Ot
  exact ⟨WitnessMont.data_outside v A Ot' Kt (by unfold WitnessSample.clob; decide)
    (by unfold WitnessSample.clob; decide), Vt, mask, Oa.trans Ot',
    (K.mono (by unfold clob; decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessLoad
