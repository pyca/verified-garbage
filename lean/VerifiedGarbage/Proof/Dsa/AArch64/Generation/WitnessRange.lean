module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.WitnessRange
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The uniform flag agrees with the shared RSA sampler, without changing the draw. -/
@[expose] public section
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
