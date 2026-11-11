module
-- separate module: correctness through the frame, apart from the timing proofs

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Post
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: correct

The frame around the body (`WP.frameAlloc`), which writes no `esp`
(`noSp_body`), and the contract's postcondition from `final_post`
(`correct`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (body code publicArgs primesArgs status copyPrimes maskArgs maskLoop primes
  stackAt statusOffset)

theorem noSp_blocks {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .esp) = true) :
    ∀ i ∈ is, Taint.clobbers i .esp = false := fun i hi => by
  simpa using List.all_eq_true.mp h i hi

theorem noSp_body {pcName prName : String} {pc : Prog isa} (pns : NoSp pc) (prns : NoSp primes) :
    NoSp (body pcName pc prName primes) := by
  intro i hi
  simp only [body, instrs, List.mem_append] at hi
  rcases hi with h | h | h | h | h | h | h | h | h
  · exact noSp_blocks (by decide) i h
  · exact pns i h
  · exact noSp_blocks (by decide) i h
  · exact prns i h
  · exact noSp_blocks (by decide) i h
  · exact noSp_blocks (is := instrs copyPrimes) (by decide) i h
  · exact noSp_blocks (by decide) i h
  · exact noSp_blocks (is := instrs maskLoop) (by decide) i h
  · exact noSp_blocks (by decide) i h

theorem correct {pcName prName : String} {pc : Prog isa}
    (pv : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)) (pst : stackUse pc ≤ 96) (pns : NoSp pc)
    (prst : stackUse primes ≤ 96) (prns : NoSp primes) (s : State)
    (h : (Spec.Rsa.privatePrecomputeContract abi stackBytes).pre s) :
    ∃ trace t, Exec isa (code pcName pc prName primes) s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.privatePrecomputeContract abi stackBytes).post s t := by
  have A := ppABI_of h
  have l := A.stackLow
  simp only [stackBytes] at l
  suffices W : WP isa (code pcName pc prName primes) s
      (fun t => abiPreserved s t ∧ (Spec.Rsa.privatePrecomputeContract abi stackBytes).post s t) by
    obtain ⟨trace, t, E, P⟩ := W
    exact ⟨trace, t, E, P⟩
  refine WP.frameAlloc (by decide) (by decide) (by decide)
    (by simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega)
    (noSp_body pns prns) (WP.mono (body_ok pv pst pns prst prns A) fun v ⟨Bv, Kv, Ev, X, m, Pm, Hm⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he
      rw [freed_esp, Bv.sp, BitVec.sub_add_cancel]
    · have hk : r ∉ [Reg.eax, .ecx, .edx] := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp_all
      rw [freed_gpr _ _ he, Kv.1 r hk, allocFrame_gpr _ _ he]
  · rw [freed_mem]
    refine Bv.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact A.retPre
    · exact A.retWs
    · rw [esp_bot A]
      exact Offset.disjoint_base _ (by simp [stackBytes]) (by decide)
  · have F := final_post A Pm Hm
    sig_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right, Ev]
    exact F

end VG.Proof.Bignum.X86.PrivPre
