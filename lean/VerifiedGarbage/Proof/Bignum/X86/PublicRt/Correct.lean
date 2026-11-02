module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Top
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.X86.PublicResources
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Functional correctness and cdecl preservation of public RSA at a run-time width

From the entry, which saves the callee-saved registers in the working
space, through `body_ok` to their restore, with the 96 bytes of stack
below `esp` that the calls use.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Spill VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicContext
open VG.Proof.Dsa.X86 (argumentPointer)

theorem frame_saved {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem} {g : Reg → BitVec 32}
    (F : Frame [⟨off base 16, bytes - 16⟩, ⟨out, len⟩, below sp 96] m m')
    (A : Region.Disjoint ⟨base, bytes⟩ ⟨out, len⟩) (low : 16 ≤ bytes) (high : bytes ≤ 2 ^ 64)
    (Z : Region.Disjoint (below sp 96) ⟨base, bytes⟩)
    (S : Saved m (off base) g PublicFn.savedRegisters) : Saved m' (off base) g PublicFn.savedRegisters := by
  intro p hp
  have B : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (F.readW (r := ⟨base, 16⟩) (Offset.contains_base _ B (by omega)) ?_ (by decide)).trans (S p hp)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.base_disjoint base (Nat.le_refl 16) (by omega)
  · exact A.sub_left (Region.sub_prefix (by omega))
  · exact (Z.sub_right (Region.sub_prefix (by omega))).symm

theorem frame_full {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame [⟨off base 16, bytes - 16⟩, ⟨out, len⟩, below sp 96] m m') (low : 16 ≤ bytes) :
    Frame [⟨base, bytes⟩, ⟨out, len⟩, below sp 96] m m' := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by omega)⟩
  · exact ⟨⟨out, len⟩, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The return address lies above the stack the calls use. -/
theorem ret_below {sp : BitVec 32} (h : 96 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (below sp 96) := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]
  exact Offset.base_disjoint_below _ (by decide)

theorem operation_ok {s : State} (A : TopABI s) :
    WP isa PublicRt.code s fun t =>
      Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 3).toNat (t.gpr .eax)
        (Spec.Rsa.publicOpChecked
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 3).toNat)) ∧
      abiPreserved s t := by
  have B := A.abi
  have low : 16 ≤ (arg s 9).toNat * 8 := by have := B.used; omega
  have high : (arg s 9).toNat * 8 ≤ 2 ^ 64 := by have := B.scratchBound; omega
  unfold PublicRt.code
  refine WP.seq (WP.mono (publicInstalled_ok B) fun u ⟨I, S, K, O⟩ => ?_)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have X : Room (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s) u :=
    ⟨(setWidth_toNat _).symm, rfl, by rw [espu]; exact A.room, by rw [espu]; exact B.stackBound⟩
  refine WP.seq (WP.mono (body_ok I X) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  rw [espu] at F
  have Saved := frame_saved F I.outApart low high A.room.apart S
  have Whole : Frame [⟨argumentPointer s 8, (arg s 9).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 3).toNat⟩, below (s.gpr .esp) 96] s.mem v.mem := by
    have Start := outside_frame O (by omega)
    simp only [BitVec.add_zero] at Start
    exact (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (frame_full F low)
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact B.retScratch
    · rw [← B.outLength]; exact B.retOut
    · exact ret_below A.room.low
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, publicRestored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide)]
  have N := scratch_bytes O (by have := B.lengths.2; omega) B.nScratch
  have E := scratch_bytes O (by have := (arg s 5).isLt; omega) B.eScratch
  have X := scratch_bytes (p := argumentPointer s 6) (len := (arg s 3).toNat) O (by have := B.lengths.2; omega)
    (by rw [← B.inLength]; exact B.inScratch)
  change Spec.Rsa.written v.mem (argumentPointer s 0) (arg s 3).toNat (v.gpr .eax)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt u.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt u.mem (argumentPointer s 4) (arg s 5).toNat)
      (Spec.Rsa.bytesAt u.mem (argumentPointer s 6) (arg s 3).toNat)) at V
  rw [N, E, X] at V
  exact V

theorem correct (s : State) (h : (Proof.Rsa.publicCheckedContract abi 96).pre s) :
    ∃ trace t, Exec isa PublicRt.code s trace t ∧ abiPreserved s t ∧
      (Proof.Rsa.publicCheckedContract abi 96).post s t := by
  obtain ⟨trace, t, E, V, A⟩ := operation_ok (topABI_of h)
  refine ⟨trace, t, E, A, ?_⟩
  sig_post [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Bignum.X86.PublicRt
