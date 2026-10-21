module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyInvariant
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckInvoke
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
import VerifiedGarbage.Proof.Dsa.X86.Comb.GenerationStack
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InlineInvoke
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult

/-! Invoke the checking body internally and retain its canonical table. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

def checkInvoke : CheckInvoke keyInvariant where
  code := invoke checkParameters
  correct := by
    intro s₀ t A R C
    obtain ⟨reads,writes⟩ := CheckCall.call_covers A R
    have low : 24≤(t.gpr .esp).toNat := by have := CheckCall.esp_toNat A R; omega
    let v := (allocated 4 t).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)
    have args (i : Nat) (hi : i<6) : arg v i=CheckCall.callVal s₀ (t.gpr .esp) i := by
      rw [allocated_arg R (by omega)]
      exact C i hi
    have body : WP isa checkParameters v fun u => abiPreserved v u ∧
        (u.gpr .eax).toNat=(if CheckCall.callResult s₀ t then 1 else 0) ∧
        (CheckCall.callResult s₀ t=true → keyInvariant s₀ u.mem) := by
      refine WP.mono (checkingOperation_spec (allocated_checkingABI A R C)) fun u ⟨V,ABI,_,_,_,I⟩ => ?_
      have V' := V
      simp only [args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),
        argumentPointer,CheckCall.callVal] at V'
      refine ⟨ABI,V',?_⟩
      intro ok
      have Inv : checkContext v u.mem := I (by
        simp only [argumentPointer,args 0 (by decide),args 1 (by decide),args 2 (by decide),
          args 3 (by decide),CheckCall.callVal]
        exact ok)
      refine ⟨A,?_⟩
      unfold checkContext parameterContext at Inv
      simp only [argumentPointer,args 0 (by decide),args 1 (by decide),args 2 (by decide),
        args 3 (by decide),args 4 (by decide),CheckCall.callVal] at Inv
      change parameterContext (argumentPointer s₀ 9) (arg s₀ 5).toNat (arg s₀ 6).toNat
        (Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (arg s₀ 4).toNat) u.mem at Inv
      rw [callKey A R] at Inv
      exact Inv
    refine WP.mono (inlineInvoke_ok (Q := fun mem ax => ax.toNat=(if CheckCall.callResult s₀ t then 1 else 0) ∧
      (CheckCall.callResult s₀ t=true → keyInvariant s₀ mem)) check_noSp check_depth low reads writes body) fun u ⟨rd,wr,K,F,V,I⟩ => ?_
    rw [invocation_below A R] at F
    have Frame : VG.Frame (CheckCall.callWrites s₀) t.mem u.mem := F
    refine ⟨R.returned rd wr (K .esp (by simp [calleeSaved])) (checkFrame_outer Frame),Frame,K,?_,I⟩
    apply BitVec.eq_of_toNat_eq
    rw [V]
    cases CheckCall.callResult s₀ t <;> rfl

end VG.Proof.Dsa.X86.Comb
