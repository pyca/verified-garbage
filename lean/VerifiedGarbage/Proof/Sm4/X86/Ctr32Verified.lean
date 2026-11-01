module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.Ctr32
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
public import VerifiedGarbage.Impl.Sm4.X86.Ctr32
meta import VerifiedGarbage.Proof.Sm4.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.Ctr32
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Proof.Modes.Ctr32
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
meta import VerifiedGarbage.Impl.Sm4.X86.Ctr32
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4's counter mode with `inc₃₂` on x86 meets its contracts

`ctr32_wp_x86`: the modes' counter mode with `inc₃₂`
(`Proof.Modes.X86.ctr32_wp`) over SM4's core in the encryption direction,
as `vg_sm4_ctr`'s (`CtrVerified.lean`), with the data and the counter block
as GCM's blocks (`Spec.Gcm.blocksAt`, `blockAt`). The rest is CTR's: the
working space as a fifth argument (`fbX86`), the taint analysis with the
calls' summaries, and `ctr32_framed`, with the working space on the stack,
zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.Ctr32

open VG VG.X86 VG.Impl.Sm4.X86 VG.Proof.Sm4.X86.Fb
open VG.Proof.Sm4.X86 (dirCoreSpec)

/-- The data XORed with the encrypted counter blocks, and `inc₃₂ⁿ` of the
counter block, as GCM's blocks. -/
def ctr32Post (s s' : State) : Prop :=
  Spec.Gcm.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)))
        (Spec.Gcm.blockAt s.mem ((arg s 1).setWidth 64)) (Spec.Gcm.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) ∧
    Spec.Gcm.blockAt s'.mem ((arg s 1).setWidth 64) =
      Nat.repeat Spec.Gcm.inc32 (arg s 3).toNat (Spec.Gcm.blockAt s.mem ((arg s 1).setWidth 64))

theorem ctr32_wp_x86 {s₀ : State} (hp : (fbX86 ctr32Post).pre s₀) :
    WP isa ctr32 s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 ctr32Post).post s₀ s' :=
  WP.mono (Modes.X86.ctr32_wp (dirCoreSpec .encrypt) rfl (Fb.seqPre_of .encrypt rfl hp) (Fb.keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      refine ⟨h1, ?_, h3⟩
      rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
      exact h2

theorem ctr32_ct : ConstantTime isa (fbX86 ctr32Post).pre (fbX86 ctr32Post).pub ctr32 :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

theorem wide_implies_ctr32 :
    (wideContract ctr32Post).Implies (Proof.Sm4.ctr32ScratchContract X86.abi 184 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post] at h
    sig_split h
    sig_reduce [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
  · sig_implies_pub [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
  · sig_implies_sat [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ctr32_verified : Verified X86.target ctr32 (Proof.Sm4.ctr32ScratchContract X86.abi 184 20) :=
  fb_verified (fun _ hs => ctr32_wp_x86 hs) ctr32_ct (fun _ _ _ _ _ _ h => h) wide_implies_ctr32

/-- `vg_sm4_ctr32` with its working space on the stack, wiped before
returning. -/
theorem ctr32_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 ctr32)
      (Proof.Sm4.ctr32Contract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Sm4.ctr32Post X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) ctr32_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ctr32Post_local _) (Proof.Sm4.ctr32PostOut_local _) (frameSat_pre _)

end VG.Proof.Sm4.X86.Ctr32
