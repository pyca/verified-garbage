module

public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.Sm4.X86.AesNiWideModes
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Impl.Sm4.X86.AesNiWideCtr32
import VerifiedGarbage.Proof.Modes.X86.Wide
import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiWideModes
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Proof.Sm4.Contract
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiWideCtr32
meta import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Modes.Ctr32
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `Sm4Ctr32` on x86 (32-bit): the AES S-box

`Impl.Sm4.X86.AesNiWide.ctr32Framed`, the modes' counter mode with `inc₃₂`
(`Proof.Modes.X86.ctr32Levels_wp`) over SM4's core for four blocks, in its
frame, as the internal function `vg_sm4_ctr32_aesni`: `ctr32_wp_x86`,
constant time by the taint analysis of its code (`X86.sseTaint`), and its
contract with the stack that SM4-GCM's functions leave the code they call
(`Proof.Sm4Gcm.X86.ctrK`): the frame of 752 bytes, and 764 below it, of
which the code uses four.
-/

@[expose] public section

namespace VG.Proof.Variants.Sm4Ctr32.X86.AesNi

open VG VG.X86 VG.Impl.Sm4.X86.AesNiWide VG.Proof.Sm4.X86.AesNiWide.Modes
open VG.Proof.Sm4.X86.AesNiWide (coreSpec)

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
  WP.mono (Proof.Modes.X86.ctr32Levels_wp (coreSpec .encrypt) rfl (levels_fit _) (seqPre_of .encrypt rfl hp)
    (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, core_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_enc] at h2 h3
      refine ⟨h1, ?_, h3⟩
      rw [Proof.Modes.gcmBlocks_eq, Proof.Modes.gcmBlocks_eq]
      exact h2

theorem ctr32_ct : ConstantTime isa (fbX86 ctr32Post).pre (fbX86 ctr32Post).pub ctr32 :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem wide_implies_ctr32 :
    (wideContract ctr32Post).Implies (Proof.Sm4.ctr32ScratchContract X86.abi 91 764) := by
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
      | omega_arith
      | with_reducible (refine below4_of_764 (by assumption) ?_; assumption)
      | (simp only [Nat.mul_comm] at *
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›
           | with_reducible (refine below4_of_764 (by assumption) ?_; assumption))
  · sig_implies_post [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
  · sig_implies_pub [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
  · sig_implies_sat [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig, Proof.Sm4.ctr32Post, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ctr32Post]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_ctr32 (post : Proof.Sm4.ctr32Sig.Post X86.abi.ptrBits) :
    ∃ s, (Proof.Sm4.ctr32Sig.contract X86.abi (post := post) (writeArgs := true) (stack := 1516)).pre s := by
  implies_sat [Proof.Sm4.ctr32Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem ctr32_verified : Verified X86.target ctr32 (Proof.Sm4.ctr32ScratchContract X86.abi 91 764) :=
  fb_verified (fun _ hs => ctr32_wp_x86 hs) ctr32_ct (fun _ _ _ _ _ _ h => h) wide_implies_ctr32

/-- `ctr32` with its working space on the stack, wiped before returning. -/
theorem ctr32_framed : Verified X86.target ctr32Framed (Proof.Sm4.ctr32Contract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64)
    (n := 91) (post := Proof.Sm4.ctr32Post X86.abi.ptrBits) (wa := true) (stack := 764)
    (bytes := 752) ctr32_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ctr32Post_local _) (Proof.Sm4.ctr32PostOut_local _) (frameSat_ctr32 _)

def variant : Proof.Sm4Gcm.X86.CtrImpl where
  fn := ⟨"vg_sm4_ctr32_aesni", ctr32Framed⟩
  ok := ctr32_framed.1
  ct := ctr32_framed.2.1
  nosp := NoSp.of_all (by unfold ctr32Framed; lit_decide)
  stack := by unfold ctr32Framed; lit_decide
  spSafe := Code.all_of_spTest (by unfold ctr32Framed; lit_decide)
  scrub := by unfold ctr32Framed; lit_decide
  suffix := "_aesni"
  features := ["aes", "ssse3"]

end VG.Proof.Variants.Sm4Ctr32.X86.AesNi
