module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
meta import VerifiedGarbage.Proof.Camellia.X86.FbVerified
public import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Proof.Camellia.X86.CtrLit
public import Mathlib.Data.List.Induction
meta import VerifiedGarbage.Proof.Camellia.X86.CtrLit
import VerifiedGarbage.Proof.Modes.X86.Ctr
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.X86.Copy
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Camellia.X86.Fl
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Modes.CtrStep
import VerifiedGarbage.Proof.Modes.X86.Counter
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.Camellia.CtrCipher
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.X86.Copy
meta import VerifiedGarbage.Proof.Camellia.X86.Crypt8
meta import VerifiedGarbage.Proof.Camellia.X86.Fl
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Modes.Steps
meta import VerifiedGarbage.Proof.Modes.X86.Counter
meta import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Spec.Ctr.Contract

@[expose] public section

namespace VG.Proof.Camellia.X86.Ctr

open VG VG.X86 VG.Impl.Camellia.X86 VG.Proof.Camellia.X86.Fb
open VG.Proof.Camellia.X86 (dirCoreSpec dirCore_ka)

def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (arg s 4).toNat
theorem ctr_wp_x86 {s₀ : State} (hp : (fbX86 ctrPost).pre s₀) :
    WP isa ctr s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 ctrPost).post s₀ s' :=
  WP.mono (Modes.X86.ctr_wp (dirCoreSpec .encrypt) rfl (Fb.seqPre_of rfl hp) (Fb.keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem ctr_ct : ConstantTime isa (fbX86 ctrPost).pre (fbX86 ctrPost).pub ctr :=
  let ⟨_, h⟩ := (by taint_decide_sum [fbPairSum] :
    ∃ h, (VG.X86.taint.check fbTaint ctr h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem wide_implies_ctr :
    (wideContract ctrPost).Implies (Proof.Camellia.ctrScratchContract X86.abi 341) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPost, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPost, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPost, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPost, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
  · sig_implies_sat [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Spec.Camellia.ctrPost, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_ctr (post : Spec.Camellia.ctrSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.ctrSig.contract X86.abi (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 2756)).pre s := by
  implies_sat [Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem ctr_verified : Verified X86.target ctr (Proof.Camellia.ctrScratchContract X86.abi 341) :=
  fb_verified (fun _ hs => ctr_wp_x86 hs) ctr_ct (fun _ _ _ _ _ _ h => h) wide_implies_ctr

/-- `ctr` with its working space on the stack. -/
theorem ctr_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 ctr)
      (Spec.Camellia.ctrContract X86.abi 2756) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := Spec.Camellia.ctrPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2756) ctr_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.ctrPre_local _)
    (Proof.Camellia.ctrPost_local _) (Proof.Camellia.ctrPostOut_local _) (frameSat_ctr _)

end VG.Proof.Camellia.X86.Ctr
