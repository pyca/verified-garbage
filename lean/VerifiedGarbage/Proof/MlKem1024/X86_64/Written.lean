module

public import VerifiedGarbage.Proof.MlKem1024.X86_64.Top
import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkSel16
import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl

/-!
# ML-KEM-1024 on x86-64: what the top-level functions write of `scratch`

An implementation with 16-bit polynomials (`Callee4.s16`, and for
encapsulation hashing the key `Callee4.batchH16` too) writes only the first
`scr16` bytes of `scratch` (`Artifact.written`), whose callers wipe only
those; the baseline writes all of it.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64

/-- What key generation, encapsulation with `H(ek)` given and decapsulation
with the implementation `v` write of `scratch`. -/
def written (v : Sample4Impl) : List (String × Nat) :=
  if v.callee.s16.isSome then [("scratch", scr16)] else []

/-- What encapsulation hashing the key with the implementation `v` writes of `scratch`. -/
def writtenEnc (v : Sample4Impl) : List (String × Nat) :=
  if v.callee.s16.isSome && v.callee.batchH16.isSome then [("scratch", scr16)] else []

theorem keyGen1024_written (v : Sample4Impl) (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.MlKem1024.keyGenContract X86_64.abi 32).pre s) (he : Exec isa (keyGen1024 v.callee) s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.MlKem1024.keyGenSig (written v) s s' := by
  unfold written
  match hm : v.callee.s16 with
  | none => simp [Sig.writtenWithin]
  | some (m, c) =>
    have hS := v.s16 m c hm
    simp [Sig.writtenWithin, X86_64.abi, VG.X86_64.argRegs, Abi.withConsts, Spec.MlKem1024.keyGenSig, Sig.words,
      Param.words, ArgWord.bits, Sig.arrays]
    intro i h1 h2
    exact keyGenSel_keep (K := kem1024w) (n := scr16) (by decide) kpke1024 v kg16Wf1024 hm
      (by s16_ctl v c hS kpke1024) (SpSafe.of_all (by s16_sp v c hS kpke1024))
      (xdLe_spec (by s16_xd v c hS kpke1024)) (keyGenImp1024.pre s hs) he h1
      (by simp only [Elem.size] at h2; exact h2)

theorem encapsH1024_written (v : Sample4Impl) (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.MlKem1024.encapsHContract X86_64.abi 32).pre s) (he : Exec isa (encapsH1024 v.callee) s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.MlKem1024.encapsHSig (written v) s s' := by
  unfold written
  match hm : v.callee.s16 with
  | none => simp [Sig.writtenWithin]
  | some (m, c) =>
    have hS := v.s16 m c hm
    simp [Sig.writtenWithin, X86_64.abi, VG.X86_64.argRegs, Abi.withConsts, Spec.MlKem1024.encapsHSig,
      Spec.MlKem.encapsHSigOf, Sig.words, Param.words, ArgWord.bits, Sig.arrays]
    intro i h1 h2
    exact encapsHSel_keep (K := kem1024w) (n := scr16) (by decide) kpke1024 v ec16Wf1024 hm
      (by s16_ctl v c hS kpke1024) (SpSafe.of_all (by s16_sp v c hS kpke1024))
      (xdLe_spec (by s16_xd v c hS kpke1024)) (encapsHImp1024.pre s hs) he h1
      (by simp only [Elem.size] at h2; exact h2)

theorem encaps1024_written (v : Sample4Impl) (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.MlKem1024.encapsContract X86_64.abi 32).pre s) (he : Exec isa (encaps1024 v.callee) s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.MlKem1024.encapsSig (writtenEnc v) s s' := by
  unfold writtenEnc
  match hm : v.callee.s16, hb : v.callee.batchH16 with
  | none, _ => simp [Sig.writtenWithin]
  | some _, none => simp [Sig.writtenWithin]
  | some (m, c), some b =>
    have hS := v.s16 m c hm
    have hB := v.batchH16 b hb
    simp [Sig.writtenWithin, X86_64.abi, VG.X86_64.argRegs, Abi.withConsts, Spec.MlKem1024.encapsSig, Sig.words,
      Param.words, ArgWord.bits, Sig.arrays]
    intro i h1 h2
    exact encapsSel_keep (K := kem1024w) (n := scr16) (by decide) kpke1024 v ek16HWf1024 ekt16Wf1024 hm hb
      (by ek16_ctl v c b hS hB kpke1024) (SpSafe.of_all (by ek16_sp v c b hS hB kpke1024))
      (xdLe_spec (by ek16_xd v c b hS hB kpke1024)) (encapsImp1024.pre s hs) he h1
      (by simp only [Elem.size] at h2; exact h2)

theorem decaps1024_written (v : Sample4Impl) (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.MlKem1024.decapsContract X86_64.abi 32).pre s) (he : Exec isa (decaps1024 v.callee) s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.MlKem1024.decapsSig (written v) s s' := by
  unfold written
  match hm : v.callee.s16 with
  | none => simp [Sig.writtenWithin]
  | some (m, c) =>
    have hS := v.s16 m c hm
    simp [Sig.writtenWithin, X86_64.abi, VG.X86_64.argRegs, Abi.withConsts, Spec.MlKem1024.decapsSig, Sig.words,
      Param.words, ArgWord.bits, Sig.arrays]
    intro i h1 h2
    exact decapsSel_keep (K := kem1024w) (n := scr16) (by decide) kpke1024 v dc16Wf1024 hm
      (by s16_ctl v c hS kpke1024) (SpSafe.of_all (by s16_sp v c hS kpke1024))
      (xdLe_spec (by s16_xd v c hS kpke1024)) (decapsImp1024.pre s hs) he h1
      (by simp only [Elem.size] at h2; exact h2)

end VG.Proof.MlKem1024.X86_64
