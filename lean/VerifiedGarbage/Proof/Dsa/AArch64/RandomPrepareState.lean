module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepare
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Initialize the persistent sampler state from the public q buffer. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_prepare_ready {C : RandomContext} {used draws : Nat} {s : State}
    (hs : Scr s C.B Random.frameBytes) (hsp : s.sp = C.B)
    (hR : word s.mem C.B Random.oRand = C.R)
    (hRL : word s.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length)
    (hU : word s.mem C.B Random.oUsed = BitVec.ofNat 64 used)
    (hD : word s.mem C.B Random.oDraws = BitVec.ofNat 64 draws)
    (hQ : word s.mem C.B Random.oQ = C.Q)
    (hQL : word s.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length)
    (hRand : Src s C.B Random.frameBytes C.R C.rand)
    (hQS : Src s C.B Random.frameBytes C.Q C.qBytes)
    (hFrame : Frm C.B randomWriteRanges C.initialMem s.mem)
    (hUsed : used ≤ C.rand.length) (hq : 1 < Spec.Dsa.decodeBE C.qBytes) :
    WP isa Random.prepare s fun t => t.gpr .x0 = 1 ∧ RandomReady C used draws t := by
  have hfit := VG.Proof.Dsa.significant_fits C.qBytes
  refine WP.mono (random_prepare_valid hs hsp hQ hQL hQS
    (by have := C.positive; omega) (by have := C.qlen; omega))
    fun t ⟨hta, htm, hkt⟩ => ?_
  have hf : Outside C.B 168 64 s.mem t.mem := by
    rw [htm]; exact random_prepare_outside _ _ _ _
  have hfs := InScr.of_outside hf (show 168 + 64 ≤ Random.frameBytes by decide)
  have hw (d : Nat) (hd : d + 8 ≤ 168) : word t.mem C.B d = word s.mem C.B d :=
    hf.word (Or.inl hd) (by omega)
  refine ⟨?_, hs.congr hkt.wr, hkt.sp.trans hsp,
    (hw _ (by decide)).trans hR, (hw _ (by decide)).trans hRL,
    (hw _ (by decide)).trans hU, ?_, (hw _ (by decide)).trans hQL, ?_, ?_,
    (hw _ (by decide)).trans hD, hRand.congrK hfs hkt, hQS.congrK hfs hkt, hUsed,
    hFrame.trans (Frm.of_outside (hf.mono (by decide) (by decide))
      (show (160, 72) ∈ randomWriteRanges by decide)), ?_⟩
  · rw [hta, ite_eq_left hq]; rfl
  · rw [htm, random_prepare_width, VG.Proof.Dsa.random_drawBytes_scan]
  · rw [htm, random_prepare_mask]
  · rw [htm, random_prepare_pointer]
  · intro i hi
    rw [htm]
    exact random_prepare_zero _ _ _ _ i (by have := C.qlen; omega)

end VG.Proof.Dsa.AArch64
