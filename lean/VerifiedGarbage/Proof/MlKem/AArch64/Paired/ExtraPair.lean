module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStep

/-! # Complete the paired matrix sampler within the shared five-block bound -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.Sha3

 theorem advance_ok {A B : Spec.Sha3.State} {p a b c : Addr} {s : State} {n : Nat}
    (h : Progress A B n p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa Impl.MlKem.AArch64.Paired.extraStep s (Advanced A B (n+1) p a b c s) := by
  have run := extraStep_ok h.context h.ptr hs h.pair (accepted_length A n) (accepted_length B n)
    h.left h.right h.saveLeft h.saveRight
  have ea : sampleAfter (accepted A n) (byteOf (Spec.Sha3.keccakF (iterF n A))) 56=accepted A (n+1) :=
    accepted_next A n
  have eb : sampleAfter (accepted B n) (byteOf (Spec.Sha3.keccakF (iterF n B))) 56=accepted B (n+1) :=
    accepted_next B n
  rw [ea,eb] at run
  refine WP.mono run fun t ht => ?_
  exact ⟨ht.keep.mono (by decide),ht.frameFine,
    ⟨ht.context,ht.pointer,ht.pair,ht.left,ht.right,ht.saveLeft,ht.saveRight⟩,ht.flagBoth⟩

theorem extraPair_ok {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : Progress A B 3 p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa Impl.MlKem.AArch64.Paired.extraPair s (ResumePost A B p a b s) :=
  resume_ok (fun _ ht hs=>advance_ok ht hs) h hs

end VG.Proof.MlKem.AArch64.Paired
