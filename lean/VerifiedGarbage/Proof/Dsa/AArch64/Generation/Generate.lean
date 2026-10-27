module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Generate
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputPlan
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishOutput
import VerifiedGarbage.Proof.Dsa.Generation.ByteResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeParameters

/-! # The native search and output implement the reviewed byte-level generator -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.AArch64

theorem generate_ok (H : GenerationHashes) (M : Mont) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (h16 : W 16 = 0) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (seedLength : p.seeds.bytes.length % p.geo.qLen = 0)
    (hLength : p.hs.bytes.length % p.geo.pLen = 0) :
    WP isa (Impl.Dsa.AArch64.Generation.generate H.sha1 H.sha256 M.mm T.run p.geo.pLen p.geo.qLen) s fun t =>
      let result := Spec.Dsa.generateParametersBytes p.geo.pLen p.geo.qLen p.seeds.bytes p.hs.bytes p.rand.bytes
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        result.getD (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame (p.changed ++ [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩]) s.mem t.mem ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have specification : Spec.Dsa.generateParametersBytes p.geo.pLen p.geo.qLen p.seeds.bytes p.hs.bytes p.rand.bytes =
      (p.remaining 0 0).map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen) := by
    rw [VG.Proof.Dsa.Generation.generateParametersBytes_attempt p.geo.lengths _ _ _ seedLength hLength]
    simp only [GenerationContext.remaining, List.drop_zero]
  unfold Impl.Dsa.AArch64.Generation.generate
  refine WP.seq (WP.mono (nativeParameters_ok H M T h (randUsed := 0) h16 (Nat.zero_le _))
    fun u ⟨Wu, mu, result, fu, ru, wu⟩ => ?_)
  refine WP.mono (finishOutput_ok mu o (by rw [wu]; exact hw) (p.remaining 0 0) result)
    fun t ⟨status, bytes, ft, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, kt.rd.trans ru, kt.wr.trans wu⟩
  · rw [specification]
    cases he : p.remaining 0 0 <;> simpa [he, Spec.Dsa.signStatus] using status
  · rw [specification]
    exact bytes
  · exact (fu.mono (by intro r hr; exact List.mem_append_left _ hr)).trans (ft.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_append_left _ (by simp [GenerationContext.changed])
      · exact List.mem_append_right _ (by simp)))
  · exact kt.sp.trans (mu.layout.sp.trans h.layout.sp.symm)

end VG.Proof.Dsa.AArch64.Generation
