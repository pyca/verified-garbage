module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! # Shape a seed digest into DSA's subgroup-prime candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Dsa.Generation
open VG.Proof.Ffdh.ParameterCandidate

theorem qShape_ok {s : State} {rp op : Addr} {seed : List Byte} {n : Nat}
    (hn : n = 160 ∨ n = 256)
    (hlen : 8 * (Spec.Dsa.seedHash n seed).length = n)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hl : s.gpr .rcx = BitVec.ofNat 64 (Spec.Dsa.seedHash n seed).length)
    (hbits : s.gpr .rdx = BitVec.ofNat 64 n)
    (hrd : ∀ i < (Spec.Dsa.seedHash n seed).length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < (Spec.Dsa.seedHash n seed).length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < (Spec.Dsa.seedHash n seed).length,
      s.mem (off rp i) = (Spec.Dsa.seedHash n seed).getD i 0)
    (hsep : ∀ i < (Spec.Dsa.seedHash n seed).length,
      ∀ j < (Spec.Dsa.seedHash n seed).length, off rp i ≠ off op j) :
    WP isa Impl.Ffdh.X86_64.ParameterCandidate.shape s fun t =>
      Spec.Rsa.bytesAt t.mem op (Spec.Dsa.seedHash n seed).length =
        Spec.Dsa.encodeBE (Spec.Dsa.seedHash n seed).length (Spec.Dsa.qCandidate n seed) ∧
      (∀ a, (∀ i < (Spec.Dsa.seedHash n seed).length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rax, .rdx, .r8, .r9, .r10, .r11, .rcx] s t := by
  refine WP.mono (VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
    (by omega) (by omega) (by omega) hrp hop hl hbits hrd hwr hbytes hsep)
    fun t ⟨hout, hvalue, hframe, hk⟩ => ?_
  have he : (n - 1) % 8 = 7 := by omega
  rw [he] at hout
  refine ⟨?_, hframe, hk⟩
  rw [hout, ← qCandidate_octets (by omega) seed hlen]
  have hne : Spec.Dsa.seedHash n seed ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil, Nat.mul_zero] at hlen
    omega
  have hsize : (shapedOctets (Spec.Dsa.seedHash n seed) 7).length = (Spec.Dsa.seedHash n seed).length :=
    (lastOne_length (by simp [topCut])).trans (topCut_length hne 7)
  rw [← hsize, encodeBE_decodeBE]

end VG.Proof.Dsa.X86_64.Generation
