module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.Ctr
public import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Sm4.X86.CtrLit
public import VerifiedGarbage.Impl.Sm4.X86.Ctr
meta import VerifiedGarbage.Proof.Sm4.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.Ctr
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Sm4.X86.CtrLit
meta import VerifiedGarbage.Impl.Sm4.X86.Ctr

/-! # SM4-CTR on x86 meets its correctness and constant-time contracts -/

@[expose] public section

namespace VG.Proof.Sm4.X86.Ctr

open VG VG.X86 VG.Impl.Sm4.X86 VG.Proof.Sm4.X86.Fb
open VG.Proof.Sm4.X86 (dirCoreSpec)

/-- The data XORed with the encrypted counters, and the next counter. -/
def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (arg s 3).toNat

theorem ctr_wp_x86 {s₀ : State} (hp : (fbX86 ctrPost).pre s₀) :
    WP isa ctr s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 ctrPost).post s₀ s' :=
  WP.mono (Modes.X86.ctr_wp (dirCoreSpec .encrypt) rfl (Fb.seqPre_of .encrypt rfl hp) (Fb.keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem ctr_ct : ConstantTime isa (fbX86 ctrPost).pre (fbX86 ctrPost).pub ctr :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

theorem wide_implies_ctr :
    (wideContract ctrPost).Implies (Proof.Sm4.ctrScratchContract X86.abi 184 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Proof.Sm4.ctrPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctrPost] at h
    sig_split h
    sig_reduce [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Proof.Sm4.ctrPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctrPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Proof.Sm4.ctrPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctrPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Proof.Sm4.ctrPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctrPost]
  · sig_implies_sat [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Spec.Sm4.ctrSig, Proof.Sm4.ctrPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctrPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ctr_verified : Verified X86.target ctr (Proof.Sm4.ctrScratchContract X86.abi 184 20) :=
  fb_verified (fun _ hs => ctr_wp_x86 hs) ctr_ct (fun _ _ _ _ _ _ h => h) wide_implies_ctr

/-- CTR with its working space on the stack, wiped before returning. -/
theorem ctr_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 ctr)
      (Spec.Sm4.ctrContract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Sm4.ctrPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) ctr_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ctrPost_local _) (Proof.Sm4.ctrPostOut_local _) (frameSat_pre _)

end VG.Proof.Sm4.X86.Ctr
