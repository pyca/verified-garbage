module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstantsCT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! RSA's exponent preparation has a public trace for every DSA candidate. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

def ExponentBefore (p : PrimeParams) (s : State) : Prop :=
  PrimeGood p s ∧ wv s.mem p.B (slot p.w aN) p.w = p.N

def exponentRegs (p : PrimeParams) : Reg → BitVec 64
  | .x0 => p.B
  | .x12 => BitVec.ofNat 64 p.w
  | _ => BitVec.ofNat 64 (8 * (p.w + 2))

theorem lowWord_registers {p : PrimeParams} {s : State} (h : ExponentBefore p s) :
    WP isa (seqs lowWord) s fun t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = exponentRegs p r :=
  WP.mono (lowWord_ok h.1 h.2 p.odd (by have := p.n3; omega)) fun t ⟨_, _, _, _, h11, h12, hk⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hk.gpr .x0 (by decide)).trans h.1.x0
    · exact h12
    · exact h11

theorem primeExponent_ct : RelCT isa (Two ExponentBefore) (seqs expSetup) (fun _ _ => True) := by
  rw [expSetup_eq]
  apply RelCT.seqs_append (by simp [lowWord]) (by simp)
  refine RelCT.seq (R := Two fun (p : PrimeParams) t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = exponentRegs p r) ?_ (two_taint [.x0, .x12, .x11]
    (fun _ _ _ hs ht r hr => (hs r hr).trans (ht r hr).symm) (by taint_decide))
  have e : seqs lowWord = Code.seq _ _ := rfl
  rw [e]
  exact ws_ct PrimeParams.B PrimeParams.Z PrimeParams.w (fun _ _ h => h.1) (by taint_decide)
    (fun _ _ h => lowWord_registers h)

end VG.Proof.Dsa.AArch64.Generation
