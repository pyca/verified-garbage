module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
public import VerifiedGarbage.Impl.Mont.X86.Compact
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryCore
import VerifiedGarbage.Proof.Mont.X86.Compact.MemoryContract
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory

/-! # Callable prepared Montgomery multiplication meets the reviewed contract -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.Mont hiding Keeps
open VG.Impl.Mont.X86

def Result (s : State) (m : Mem) : Prop :=
  let W := wsOf s
  let w := wOf s.mem W
  let M := numAt s.mem W w aM
  numAt m W w (arg s 2).toNat < M ∧
    numAt m W w (arg s 2).toNat * 2 ^ (64 * w) % M =
      numAt s.mem W w (arg s 3).toNat * numAt s.mem W w (arg s 4).toNat % M ∧
    Proof.Rsa.Mont.Keeps W (arg s 1).toNat w (arg s 2).toNat s.mem m

theorem correct (s : State) (h : (mulContract abi 16).pre s) :
    ∃ tr t, Exec isa Compact.body s tr t ∧ abiPreserved s t ∧ (mulContract abi 16).post s t := by
  have A := entry_of h
  have result : WP isa Compact.body s fun t => abiPreserved s t ∧ Result s t.mem := by
    refine frame_ok A.stackFit A.savedFar A.returnFar ?_
    refine WP.mono A.core ?_
    rintro t ⟨O, low, congruence, K⟩
    have fit : arrAt (wOf s.mem (wsOf s)) 8 ≤ lenOf s := by
      simpa only [lenOf, Nat.mul_comm] using A.layout.2.2.1
    have lay := layout_bounds fit A.left A.right
    have outFit := array_fit fit A.output.1
    refine ⟨?_, ?_, K⟩
    · intro x hx
      exact O x fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> right
        · have := lay.scr; omega
        · omega
    · change _ ∧ _ ∧ _
      refine ⟨?_, ?_, A.keeps O⟩
      · rw [numAt_val32, numAt_val32]; exact low
      · rw [numAt_val32, numAt_val32, numAt_val32, numAt_val32,
          show 64 * wOf s.mem (wsOf s) = 32 * (2 * wOf s.mem (wsOf s)) by omega]
        exact congruence
  obtain ⟨tr, t, E, preserved, R⟩ := result
  refine ⟨tr, t, E, preserved, ?_⟩
  sig_post [mulContract, sig, abi, argSlots, argVal, argBytes]
  exact R

end VG.Proof.Mont.X86.Compact
