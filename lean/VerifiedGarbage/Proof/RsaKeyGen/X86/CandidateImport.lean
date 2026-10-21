module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateImport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBits
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # The complete native construction agrees with the candidate specification -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateImport
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem code_ok {s : State} {base : Addr} {size w out : Nat} {g : Import.Geometry}
    (scratch : Scr s base size) (positive : 0 < w) (fit : out + 8 * w ≤ size)
    (context : Import.Context g s) (width : g.count = 2 * w)
    (source : s.gpr .esi = g.src) (destination : s.gpr .edi + BitVec.ofNat 32 out = g.dst) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateImport.code w out) s fun t =>
      val32 t.mem base out (2 * w) = Spec.RsaKeyGen.candidate (64 * w)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.src.setWidth 64) (8 * w))) ∧
      Frame [⟨off base out, 8 * w⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have dstAddr : g.dst.setWidth 64 = off base out := by
    rw [← destination]
    exact scratch.ea (by omega)
  have region : g.destRegion = ⟨off base out, 8 * w⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr, width, show 4 * (2 * w) = 8 * w by omega]
  have load := Import.load_ok context source destination
  rw [width] at load
  refine WP.seq (WP.mono load fun a ⟨value, F, K⟩ => ?_)
  have input : val32 a.mem base out (2 * w) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (g.src.setWidth 64) (8 * w)) := by
    rw [dstAddr, show 4 * (2 * w) = 8 * w by omega] at value
    rw [← VG.Proof.Bignum.read_eq_val32, show 4 * (2 * w) = 8 * w by omega]
    exact value
  refine WP.mono (CandidateBits.code_ok (scratch.of_keeps K (by decide)) positive fit)
    fun t ⟨result, O, Kt⟩ => ?_
  rw [input] at result
  rw [region] at F
  exact ⟨result, F.trans (VG.Proof.Bignum.outside_frame O (by have := scratch.nowrap; omega)), K.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.CandidateImport
