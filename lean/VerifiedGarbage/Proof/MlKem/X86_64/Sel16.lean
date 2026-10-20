module

import VerifiedGarbage.Proof.MlKem.X86_64.KgTop16
public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop16
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop16

/-!
# ML-KEM on x86-64: the top-level functions of each implementation

An implementation `v` with a 16-bit sampler (`Callee4.s16`) runs the
top-level functions with 16-bit polynomials (`kemKeyGenSel`, …); the
baseline, those with polynomials of `u32`s. Each is `Verified` by the proof
of the one it runs, against any contract the K-PKE functions' parameter
set's implies.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem keyGenSel_verified {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W16 : KeyGen16.Kg16Wf K)
    (W : KeyGen.KgWf K.L) {k : Contract isa} (hk : (keyGenK K.L).Implies k)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemKeyGen16 K v.callee (n, c)) = true)
    (hctl : ctlOk (kemKeyGen K.L v.callee) = true) :
    Verified X86_64.target (kemKeyGenSel K v.callee) k := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (n, c) =>
    exact Verified.of_correct (kemKeyGen16_correct hK v W16 hs (hctl16 n c (v.s16 n c hs)))
      (kemKeyGen16_ct hK v W16 hs) hk
  | none => exact Verified.of_correct (kemKeyGen_correct v W hctl) (kemKeyGen_ct v W) hk

theorem encapsHSel_verified {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (W16 : Encaps16.Ec16Wf K)
    (W : Encaps.EcWf K.L) {wc wd : List Nat} (C : KemCalls K.L wc wd) {k : Contract isa}
    (hk : (encapsK K.L).Implies k)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemEncapsH16 K v.callee (n, c)) = true)
    (hctl : ctlOk (kemEncapsH K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsHSel K v.callee) k := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (n, c) =>
    exact Verified.of_correct (kemEncapsH16_correct hK v W16 hs (hctl16 n c (v.s16 n c hs)))
      (kemEncapsH16_ct hK v W16 hs) hk
  | none => exact Verified.of_correct (kemEncapsH_correct v W C hctl) (kemEncapsH_ct v W C) hk

/-- No instruction of the top-level function `kemKeyGenSel K c` writes the
stack pointer, if neither of the functions it may run does. -/
theorem keyGenSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c, S16Ok c → (kemKeyGen16 K v.callee (n, c)).all p = true)
    (h : (kemKeyGen K.L v.callee).all p = true) : (kemKeyGenSel K v.callee).all p = true := by
  unfold kemKeyGenSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

theorem encapsHSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c, S16Ok c → (kemEncapsH16 K v.callee (n, c)).all p = true)
    (h : (kemEncapsH K.L v.callee).all p = true) : (kemEncapsHSel K v.callee).all p = true := by
  unfold kemEncapsHSel
  match hs : v.callee.s16 with
  | some (n, c) => exact h16 n c (v.s16 n c hs)
  | none => exact h

end VG.Proof.MlKem.X86_64
