module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyInvariant
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
import VerifiedGarbage.Proof.Dsa.X86.Comb.InvokeInputs
import VerifiedGarbage.Proof.Dsa.X86.Comb.GenerationStack
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InlineInvoke
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult

/-! The internal prevalidated body is called only with the checked retained context. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

def deriveInvoke : DeriveInvoke keyInvariant where
  code := invoke deriveKey
  correct := by
    intro s₀ t A R C checked context
    obtain ⟨reads,writes⟩ := call_covers A R
    have low : 112≤(t.gpr .esp).toNat := by have := esp_toNat A R; have := rLow_toNat A; have := A.stackLow; omega
    let v := (allocated 4 t).withRegions (callRd s₀) (callWr s₀)
    have args (i : Nat) (hi : i<9) : arg v i=callVal s₀ (t.gpr .esp) i := by
      rw [allocated_arg R (by omega)]
      exact C i hi
    have valid := derive_allocated_valid A R C checked
    have contextV := derive_allocated_context A R C context
    have result : Spec.Dsa.deriveKeyBytes (arg v 4).toNat (arg v 6).toNat
        (Spec.Rsa.bytesAt v.mem (argumentPointer v 2) (arg v 3).toNat)
        (Spec.Rsa.bytesAt v.mem (argumentPointer v 5) (arg v 6).toNat)=callResult s₀ t := by
      simp only [argumentPointer,args 2 (by decide),args 3 (by decide),args 4 (by decide),
        args 5 (by decide),args 6 (by decide),callVal]
      rw [esp_ptr R (d := VG.Impl.Dsa.X86.KeyRandom.oNonce) (by decide)]
      rfl
    let Q := fun mem (ax : BitVec 32) => ax.toNat=Spec.Dsa.signStatus (callResult s₀ t) ∧
      Spec.Rsa.bytesAt mem (argumentPointer s₀ 0) (arg s₀ 1).toNat=
        (callResult s₀ t).getD (List.replicate (arg s₀ 1).toNat 0)
    have body : WP isa deriveKey v fun u => abiPreserved v u ∧ Q u.mem (u.gpr .eax) := by
      refine WP.mono (derivingOperation_spec (allocated_derivingABI A R C) valid contextV)
        fun u ⟨V,B,ABI,_⟩ => ?_
      rw [result] at V B
      simp only [argumentPointer,args 0 (by decide),args 1 (by decide),callVal] at B
      exact ⟨ABI,V,B⟩
    refine WP.mono (inlineInvoke_ok (Q := Q) derive_noSp derive_depth low reads writes body)
      fun u ⟨rd,wr,K,F,V,B⟩ => ?_
    rw [invocation_below A R] at F
    have Frame : VG.Frame (callWrites s₀) t.mem u.mem := F
    refine ⟨R.returned rd wr (K .esp (by simp [calleeSaved])) (deriveFrame_outer Frame),Frame,K,?_,B⟩
    apply BitVec.eq_of_toNat_eq
    rw [V,BitVec.toNat_ofNat]
    unfold Spec.Dsa.signStatus
    split <;> rfl

end VG.Proof.Dsa.X86.Comb
