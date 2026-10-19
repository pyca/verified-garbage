module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInstalled
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedOperation
public import VerifiedGarbage.Proof.Bignum.X86.PublicReturn

/-! # Functional correctness and cdecl preservation of precomputed public RSA -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86 PublicContext

theorem precomputedOperation_ok {s : State} (A : PrecomputedABI s) :
    WP isa PrecomputedFn.code s fun t =>
      (∀ nB : List Byte, nB.length = (arg s 1).toNat →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat) →
        Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 1).toNat (t.gpr .eax)
          (Spec.Rsa.publicOpChecked nB
            (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
            (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 1).toNat))) ∧ abiPreserved s t := by
  have low : 16 ≤ (arg s 9).toNat * 8 := by have := A.used; omega
  have high : (arg s 9).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega
  unfold PrecomputedFn.code
  refine WP.seq (WP.mono (precomputedInstalled_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  refine WP.seq (WP.mono (precomputedBody_ok I) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have Saved := publicFrame_saved F I.outApart low high S
  have Whole : Frame [⟨argumentPointer s 8, (arg s 9).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 1).toNat⟩] s.mem v.mem := by
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
    · exact A.retOut
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, publicRestored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  intro nB length key
  rw [R.mem, R.other .eax (by decide)]
  have W := scratch_words O high (n := (arg s 3).toNat)
    (by have := A.preBound; omega) (by simpa only [Nat.mul_comm] using A.preScratch)
  have EB := scratch_bytes O (by have := (arg s 5).isLt; omega) A.eScratch
  have XB := scratch_bytes (p := argumentPointer s 6) (len := (arg s 1).toNat) O (by have := A.lengths.2; omega)
    (by rw [← A.inLength]; exact A.inScratch)
  have keyU : Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt u.mem (byteAddr (arg s 2))
      (2 * Spec.Rsa.modulusWords (arg s 1).toNat)) := by
    change Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt u.mem (argumentPointer s 2)
      (Spec.Rsa.precomputedWords (arg s 1).toNat))
    rw [← A.preLength, W]
    exact key
  have Result := V nB length keyU
  change Spec.Rsa.written v.mem (argumentPointer s 0) (arg s 1).toNat (v.gpr .eax)
    (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt u.mem (argumentPointer s 4) (arg s 5).toNat)
      (Spec.Rsa.bytesAt u.mem (argumentPointer s 6) (arg s 1).toNat)) at Result
  rw [EB, XB] at Result
  exact Result

theorem precomputedCorrect (s : State) (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 20).pre s) :
    ∃ trace t, Exec isa PrecomputedFn.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputedCheckedContract abi 20).post s t := by
  obtain ⟨trace, t, E, V, A⟩ := precomputedOperation_ok (precomputedABI_of h)
  refine ⟨trace, t, E, A, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Bignum.X86
