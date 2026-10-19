module

public import VerifiedGarbage.Proof.MlKem.X86_64.DjFusedCT16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the decapsulation with
16-bit polynomials that hashes `z ‖ c` in the fragments (`kemDecapsJ16`);
any other, the one with polynomials of `u32`s (`kemDecaps`). As
`EkSel16.lean`, whose `ek16_ctl` and `ek16_sp` give its control flow and
stack pointer.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem decapsSel_verified {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F16 : DjF16.DjHWf K)
    (T16 : DjF16.DjTWf K) (W : Decaps.DcWf K.L) {wc wd : List Nat} (C : KemCalls K.L wc wd) {k : Contract isa}
    (hk : (decapsK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemDecaps K.L v.callee) = true) :
    Verified X86_64.target (kemDecapsSel K v.callee) k := by
  unfold kemDecapsSel
  split
  · rename_i p b hs hb
    obtain ⟨n, c⟩ := p
    exact Verified.of_correct
      (kemDecapsJ16_correct hK v F16 hs hb (hctl16 n c b (v.s16 n c hs) (v.batchH16 b hb)))
      (kemDecapsJ16_ct hK v F16 T16 hs hb) hk
  · exact Verified.of_correct (kemDecaps_correct v W C hctl) (kemDecaps_ct v W C) hk

/-- No instruction of `kemDecapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem decapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemDecapsJ16 K v.callee (n, c) b).all p = true)
    (h : (kemDecaps K.L v.callee).all p = true) : (kemDecapsSel K v.callee).all p = true := by
  unfold kemDecapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64
