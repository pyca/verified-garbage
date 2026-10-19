module
public import VerifiedGarbage.Proof.Bignum.X86.CrtPost
public import VerifiedGarbage.Proof.Bignum.X86.CrtABI

import VerifiedGarbage.Proof.Bignum.X86.CrtInstalled
import VerifiedGarbage.Proof.Bignum.X86.CrtBody
import VerifiedGarbage.Proof.Bignum.X86.CrtReturn
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
import VerifiedGarbage.Proof.Bignum.X86.CrtResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame

/-! # Functional correctness and cdecl preservation of private CRT RSA -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86

theorem operation_ok {s : State} (A : CrtABI s) :
    WP isa Crt.code s fun t =>
      Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 3).toNat (t.gpr .eax)
        (specResult s.mem (arg s)) ∧ abiPreserved s t := by
  have low : 48 ≤ (arg s 17).toNat * 8 := by have := A.used; omega
  have high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega
  unfold Crt.code
  refine WP.seq (WP.mono (installed_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  refine WP.seq (WP.mono (body_ok I) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have Saved := frame_saved F I.outApart low high S
  have Whole : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 3).toNat⟩] s.mem v.mem := by
    have Start := VG.Proof.Bignum.outside_frame O (by omega)
    simp only [BitVec.add_zero] at Start
    exact (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (frame_full F low)
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.retScratch
    · rw [← A.outLength]; exact A.retOut
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, restored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide)]
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega)
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  have Specs : specResult u.mem (arg s) = specResult s.mem (arg s) := by
    unfold specResult
    rw [B 2 (by decide), B 4 (by decide), B 6 (by decide), B 8 (by decide),
      B 10 (by decide), B 12 (by decide), B 14 (by decide)]
  rw [Specs] at V
  exact V

theorem correct (s : State) (h : (Spec.Rsa.privateCrtContract abi 20).pre s) :
    ∃ trace t, Exec isa Crt.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.privateCrtContract abi 20).post s t := by
  have A := crtABI_of h
  obtain ⟨trace, t, E, V, P⟩ := operation_ok A
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold specResult at V
  rw [A.inLength, A.dpLength, A.dqLength, A.qiLength] at V
  exact V

end VG.Proof.Bignum.X86.Crt
