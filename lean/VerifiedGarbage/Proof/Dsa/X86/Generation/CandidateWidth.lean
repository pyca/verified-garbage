module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Bignum.CopyOctets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth

/-! The native leading-byte test is exactly the specification's modulus-width guard. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86

theorem candidate_width {s : State} {base : Addr} {bytes len p : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (positive : 0 < len)
    (bound : p < 2 ^ (8 * len))
    (encoded : Spec.Rsa.bytesAt s.mem (off base Layout.p) len = Spec.Dsa.encodeBE len p) :
    WP isa (.block candidateWidth) s fun t =>
      t.cf = some (decide (p < 2 ^ (8 * len - 1))) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  have first := congrArg (fun bs : List Byte => bs.getD 0 0) encoded
  rw [VG.Proof.Bignum.bytesAt_getD _ _ positive, BitVec.add_zero] at first
  have comparison := VG.Proof.Dsa.Generation.candidate_firstByte positive (by
    rw [VG.Proof.Bignum.pow256_eq]; exact bound)
  rw [← first] at comparison
  unfold candidateWidth
  refine wp_loadByte (scr.ea (d := Layout.p) (by unfold Layout.p; omega))
    (scr.read (d := Layout.p) (n := 1) (by unfold Layout.p; omega)) fun a A =>
    wp_cmpi fun t T carry _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans (T.keeps _)⟩
  rw [carry, A.gpr, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := (s.mem (off base Layout.p)).isLt; omega)]
  change some (decide ((s.mem (off base Layout.p)).toNat < 128)) = _
  simp only [comparison]

end VG.Proof.Dsa.X86.Generation
