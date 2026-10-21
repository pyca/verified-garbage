module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClose
import VerifiedGarbage.Proof.RsaKeyGen.X86.Close
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # A supplied prime is imported at full width before the exact separation test -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateClose
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

theorem other_ok {s : State} {base : Addr} {size w candidate : Nat} {p : BitVec 32}
    (S : Scr s base size) (width : 4 ≤ w) (header : 24 ≤ size)
    (space : slot w 4 + 8 * w ≤ size)
    (candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate)
    (pointer : s.mem.readW (off base 20) 32 = p)
    (sourceFit : p.toNat + 8 * w ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (p.setWidth 64) (8 * w))
    (separate : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint ⟨base, size⟩) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateClose.other w) s fun t =>
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * w)
        (some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w)))) candidate) ∧
      Outs base [(slot w 4, 8 * w), (slot w 2, 8 * w), (slot w 3, 8 * w)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have s02 : slot w 0 + 8 * w ≤ slot w 2 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
  have s23 : slot w 2 + 8 * w ≤ slot w 3 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
  have s34 : slot w 3 + 8 * w ≤ slot w 4 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
  unfold VG.Impl.RsaKeyGen.X86.CandidateClose.other
  refine WP.seq (wp_movS (readSrc_sc S (d := 20) (by omega)) fun a A _ => WP.block_nil ?_)
  have Sa := S.of_keeps A.keeps (by decide)
  have context : Import.Context ⟨p, a.gpr .edi + BitVec.ofNat 32 (slot w 4), 2 * w⟩ a :=
    Import.context_workspace Sa (by omega) (by omega) (by omega)
      (by rw [A.keeps.2.1, A.keeps.2.2, show 4 * (2 * w) = 8 * w by omega]; exact readable)
      (by rw [show 4 * (2 * w) = 8 * w by omega]; exact separate)
  refine WP.seq (WP.mono (Import.load_ok context (by rw [A.gpr, pointer]) rfl) fun b ⟨value, F, Kb⟩ => ?_)
  have destAddress : (a.gpr .edi + BitVec.ofNat 32 (slot w 4)).setWidth 64 = off base (slot w 4) := Sa.ea (d := slot w 4) (by omega)
  change (b.mem.read ((a.gpr .edi + BitVec.ofNat 32 (slot w 4)).setWidth 64) (4 * (2 * w))).toNat = _ at value
  rw [destAddress, show 4 * (2 * w) = 8 * w by omega, A.mem] at value
  have pval : val32 b.mem base (slot w 4) (2 * w) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (p.setWidth 64) (8 * w)) := by
    rw [← VG.Proof.Bignum.read_eq_val32, show 4 * (2 * w) = 8 * w by omega]
    exact value
  change Frame [⟨(a.gpr .edi + BitVec.ofNat 32 (slot w 4)).setWidth 64, 4 * (2 * w)⟩] a.mem b.mem at F
  rw [destAddress, show 4 * (2 * w) = 8 * w by omega, A.mem] at F
  have O := VG.Proof.RsaKeyGen.frame_outside F (by have := S.nowrap; omega)
  have candidateB : val32 b.mem base (slot w 0) (2 * w) = candidate :=
    (O.val32 (Or.inl (by omega)) (by have := S.nowrap; omega)).trans candidateEq
  refine WP.mono (Close.code_ok (Sa.of_keeps Kb (by decide)) (by omega)
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))) fun t ⟨result, Ot, Kt⟩ => ?_
  rw [candidateB, pval, show 32 * (2 * w) = 64 * w by omega] at result
  rw [show 4 * (2 * w) = 8 * w by omega] at Ot
  refine ⟨result, ?_, ((A.keeps.mono (by decide)).trans (Kb.mono (by decide))).trans Kt⟩
  exact (Outs.of_outside O (List.mem_cons_self)).trans
    (Ot.mono (fun _ mem => List.mem_cons_of_mem _ mem))

end VG.Proof.RsaKeyGen.X86.CandidateClose
