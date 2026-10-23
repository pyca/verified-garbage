module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result

/-! # Both calls read the original packed domain -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.KeyRandom

theorem callKey {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKeyWide.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

theorem checkResult_eq {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    CheckCall.callResult s₀ t = checked s₀ := by
  unfold CheckCall.callResult
  rw [callKey A h]
  rfl

theorem callResult_eq {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {k : Nat}
    (hn : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length k) :
    callResult s₀ t = Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) := by
  have hqn := rQBytes_length A
  have hnon : Spec.Rsa.bytesAt t.mem (off (rLow s₀) 112) (X86.arg s₀ 6).toNat =
      Spec.Dsa.encodeBE (rInput s₀).qLen k := by
    rw [show off (rLow s₀) 112 = off (rBase s₀) oNonce from (rBase_off s₀ oNonce).symm, ← hqn, hn, hqn]; rfl
  unfold callResult
  rw [callKey A h, hnon]; rfl

end VG.Proof.Dsa.X86.KeyRandom
