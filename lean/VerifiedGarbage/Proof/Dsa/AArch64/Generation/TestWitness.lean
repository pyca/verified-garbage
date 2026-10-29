module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleState
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Sample

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadWitness
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.WitnessRange
import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep: its symbolic execution names RegUpd lemmas by path, which shake does not see
/-! Classify the complete truncated draw while preserving its original bytes. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/WitnessRange.lean`, which only this module imported.
section

/-! The uniform flag agrees with the shared RSA sampler, without changing the draw. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.Ffdh.AArch64.ParameterCandidate VG.Proof.MlKem.AArch64

theorem testRange_ok {s : State} {B : Addr} {Z w X N : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w aX) w = X)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) :
    WP isa Impl.Dsa.AArch64.Generation.testRange s fun t =>
      t.gpr .x9 = mask (decide (2 ≤ X ∧ X < N - 1)) ∧
      t.mem = s.mem.writeW (off B (8 * kU)) (mask (decide (2 ≤ X ∧ X < N - 1))) ∧
      Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.testRange
  refine WP.seq (WP.mono (drawRange_ok h hx) fun u ⟨hu9, hum, ku⟩ => ?_)
  have hu9' : u.gpr .x9 = mask (decide (2 ≤ X ∧ X < N - 1)) := by
    simpa only [hn, or1_lt_iff hodd, Bool.decide_and] using hu9
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = u.mem.writeW (off B (8 * kU)) (mask (decide (2 ≤ X ∧ X < N - 1))))
      (by
        brun [(ku.gpr .x0 (by decide)).trans h.x0, hu9', hdr_enc (show kU < 32 by decide),
          (h.scr.congr ku.wr).st (d := 8 * kU) (by have := h.h256; simp only [kU]; omega)])
      rfl rfl rfl) fun t ⟨htm, kt⟩ => ?_
  exact ⟨(kt.gpr .x9 (by decide)).trans hu9', by rw [htm, hum], (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

def testRanges (w : Nat) : List (Nat × Nat) := [(slot w aX, 8 * (w + 2)), (8 * kU, 8)]

theorem testWitness_ok {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hodd : N % 2 = 1) (h1 : 1 ≤ bs.length) (hw : bs.length ≤ 8 * w) :
    WP isa Impl.Dsa.AArch64.Generation.testWitness s fun t =>
      SampleState B p Z w N bs t ∧ wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧
      word t.mem B (8 * kU) = mask (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      t.gpr .x9 = mask (decide (2 ≤ Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs < N - 1)) ∧
      Frm B (testRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := h.ready.ws.scr.nowrap
  have hZ := h.ready.ws.hZ
  have h256 := h.ready.ws.h256
  have hX := h.ready.ws.sl (show aX < 16 by decide)
  unfold Impl.Dsa.AArch64.Generation.testWitness
  refine WP.seq (WP.mono (loadWitness_ok h.ready hEZ h.ptr h.len h.source h1 hw)
    fun u ⟨hu, hxu, fu, ku⟩ => ?_)
  have hsu := h.of_frm hu fu ku
    (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [slot, hdrBytes, aX, kOut, sFn]; omega_arith)
    (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [slot, hdrBytes, aX, kUsedP, sFn]; omega_arith)
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact hX)
  refine WP.mono (testRange_ok hu.ws hxu hu.modulus hodd) fun t ⟨ht9, htm, kt⟩ => ?_
  have ft : Frm B [(8 * kU, 8)] u.mem t.mem := by
    rw [htm]; exact Frm.of_outside (writeW_outside _ B _ (by decide)) (by simp)
  have ht : ModulusReady t B Z w N := hu.of_frm hEZ ft
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact KMut.hdr (.inl (by decide))) kt (by decide)
    (by
      intro a ha r hr; rw [List.mem_singleton.mp hr]
      right; simp only [slot, hdrBytes, kU]; omega_arith)
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; decide)
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; simp only [slot, hdrBytes, aE, kU]; omega_arith)
  have hst := hsu.of_frm ht ft kt
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; decide)
    (by intro r hr; rw [List.mem_singleton.mp hr]; right; decide)
    (by intro r hr; rw [List.mem_singleton.mp hr]; simp only [kU]; omega)
  refine ⟨hst, ?_, ?_, ht9, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by intro r hr; rw [List.mem_singleton.mp hr]; right; simp only [slot, hdrBytes, aX, kU]; omega_arith)
      (by omega)]
    exact hxu
  · rw [htm, word_writeW_self]
  · exact (fu.mono (by simp [testRanges])).trans (ft.mono (by simp [testRanges]))

end VG.Proof.Dsa.AArch64.Generation
