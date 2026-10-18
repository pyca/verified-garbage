module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Framework.Omega

/-! # Copy a complete digest using the shared byte loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem copyDigest_ok {s : State} {rp op : Addr} {bs : List Byte}
    (hlen : bs.length = 20 ∨ bs.length = 32)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hbits : s.gpr .rdx = BitVec.ofNat 64 (8 * bs.length))
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off rp i ≠ off op j) :
    WP isa Impl.Ffdh.X86_64.ParameterCandidate.witnessCut s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rax, .rdx, .r8, .r9, .r10, .r11, .rcx] s t := by
  refine WP.mono (Ffdh.X86_64.ParameterCandidate.witnessCut_ok
    (by omega) (by omega) (by omega) hrp hop hn hbits hrd hwr hbytes hsep)
    fun t ⟨hb, _, hf, hk⟩ => ?_
  refine ⟨?_, hf, hk⟩
  rw [show (8 * bs.length - 1) % 8 = 7 by omega] at hb
  rw [hb]
  cases bs with
  | nil => simp at hlen
  | cons b bs =>
    change (b &&& BitVec.allOnes 8) :: bs = b :: bs
    rw [BitVec.and_allOnes]

end VG.Proof.Dsa.X86_64.Generation
