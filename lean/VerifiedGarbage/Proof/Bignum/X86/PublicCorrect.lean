module
public import VerifiedGarbage.Proof.Bignum.X86.PublicABI
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Bignum.X86.PublicInstalled
import VerifiedGarbage.Proof.Bignum.X86.PublicOperation
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicResources
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.EntrySave

/-! # Functional correctness and cdecl preservation of checked public RSA -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86 PublicContext

theorem publicOperation_ok {s : State} (A : PublicABI s) :
    WP isa PublicFn.code s fun t =>
      Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 3).toNat (t.gpr .eax)
        (Spec.Rsa.publicOpChecked
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 3).toNat)) ∧
      abiPreserved s t := by
  have low : 16 ≤ (arg s 9).toNat * 8 := by have := A.used; omega
  have high : (arg s 9).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega
  unfold PublicFn.code
  refine WP.seq (WP.mono (publicInstalled_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  refine WP.seq (WP.mono (publicBody_ok I) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have Saved := publicFrame_saved F I.outApart low high S
  have Whole : Frame [⟨argumentPointer s 8, (arg s 9).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 3).toNat⟩] s.mem v.mem :=
    by
    have Start := outside_frame O (by omega)
    simp only [BitVec.add_zero] at Start
    exact (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (publicFrame_full F low)
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.retScratch
    · rw [← A.outLength]; exact A.retOut
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, publicRestored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide)]
  have N := scratch_bytes O (by have := A.lengths.2; omega) A.nScratch
  have E := scratch_bytes O (by have := (arg s 5).isLt; omega) A.eScratch
  have X := scratch_bytes (p := argumentPointer s 6) (len := (arg s 3).toNat) O (by have := A.lengths.2; omega)
    (by rw [← A.inLength]; exact A.inScratch)
  change Spec.Rsa.written v.mem (argumentPointer s 0) (arg s 3).toNat (v.gpr .eax)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt u.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt u.mem (argumentPointer s 4) (arg s 5).toNat)
      (Spec.Rsa.bytesAt u.mem (argumentPointer s 6) (arg s 3).toNat)) at V
  rw [N, E, X] at V
  exact V

theorem publicCorrect (s : State) (h : (Spec.Rsa.publicCheckedContract abi 20).pre s) :
    ∃ trace t, Exec isa PublicFn.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicCheckedContract abi 20).post s t := by
  obtain ⟨trace, t, E, V, A⟩ := publicOperation_ok (publicABI_of h)
  refine ⟨trace, t, E, A, ?_⟩
  sig_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Bignum.X86
