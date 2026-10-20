module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness

/-! # The complete native uniform-range test preserves the original draw -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

def testRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aXm, 8 * (w + 2)), (slot w aTmp, 8 * w), (8 * kU, 8)]

theorem testWitness_ok {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) (hd : MrDims B Z w) (hodd : N % 2 = 1)
    (hk1 : 1 ≤ bs.length) (hk31 : bs.length < 2 ^ 31) (hkw : (bs.length + 7) / 8 ≤ w) :
    WP isa Impl.Dsa.X86_64.Generation.testWitness s fun t =>
      SampleState B p Z w N mi bs t ∧ wv t.mem B (slot w aXm) w = Spec.Rsa.os2ip bs ∧
      word t.mem B (8 * kU) = mask (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      t.zf = some (!decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      Frm B (testRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hXm := slot_le (w := w) (show aXm < 8 by decide)
  have hTmp := slot_le (w := w) (show aTmp < 8 by decide)
  have hz := hd.z
  have hhdr : 256 ≤ Z := by simp only [slot, hdrBytes] at hz; omega
  unfold Impl.Dsa.X86_64.Generation.testWitness
  simp only [seqs]
  refine WP.seq (WP.mono (loadWitness_ok h.ready hd (by decide) (by decide) h.ptr h.len h.source hk1 hk31 hkw)
    fun u ⟨hu, hxu, hfu, ku⟩ => ?_)
  have hsu := h.of_frm hd hu hfu ku (by rng_disj) (by rng_disj)
    (by simp only [List.mem_singleton, forall_eq]; omega)
  refine WP.seq (WP.mono (witnessRange_ok hu hd hodd hxu) fun v ⟨hax, _, hv, hxv, hfv, kv⟩ => ?_)
  have hsv := hsu.of_frm hd hv hfv kv
    (by simp only [Impl.Ffdh.X86_64.Domain.sF]; rng_disj)
    (by simp only [Impl.Ffdh.X86_64.Domain.sF]; rng_disj)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · omega
      · change 248 ≤ Z; omega)
  have hax' : v.gpr .rax = BitVec.ofNat 64 (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)).toNat := by
    by_cases hp : 2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1 <;>
      simpa [VG.Proof.Ffdh.X86_64.bit, hp] using hax
  refine WP.mono (saveUniform_ok hv hd hax') fun t ⟨ht, hut, hzt, hft, kt⟩ => ?_
  have hst := hsv.of_frm hd ht hft kt (by rng_disj) (by rng_disj)
    (by simp only [List.mem_singleton, forall_eq]; change 248 ≤ Z; omega)
  refine ⟨hst, ?_, hut, hzt, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [hft.wv_eq (by rng_disj) (by have := h.ready.good.scr.nowrap; omega)]
    exact hxv
  · exact ((hfu.mono (by simp [testRanges])).trans
      (hfv.mono (by simp [testRanges, Impl.Ffdh.X86_64.Domain.sF, kU]))).trans
        (hft.mono (by simp [testRanges]))

end VG.Proof.Dsa.X86_64.Generation
