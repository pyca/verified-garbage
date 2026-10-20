module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Sized
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInstalled
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponentArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Correct
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordsFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedResources
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedABI
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Top
import VerifiedGarbage.Impl.Bignum.X86.PrecomputedRt
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPost
import VerifiedGarbage.Proof.Bignum.X86.PublicControls
import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn

/-! # Functional correctness and cdecl preservation of precomputed public RSA at a run-time width

The exponent saved (`valid_ok`) and checked (`body_ok`) around `sized`, from
the entry, which saves the callee-saved registers in the working space, to
their restore (`operation_ok`), with the 40 bytes of stack below `esp` that
the calls use (`TopABI`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicContext
open VG.Proof.Bignum.X86.PublicRt (Room frame_saved frame_full ret_below)
open VG.Proof.Dsa.X86 (argumentPointer)

theorem Post.compose {s u t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}
    (h : PrecomputedInputs base bytes len args s) (O : Outside base 16 (bytes - 16) s.mem u.mem)
    (P : Post base bytes len args sp u.mem t) : Post base bytes len args sp s.mem t := by
  have nw := h.scratch.nowrap
  have sz := h.space
  have size := size_eq (Spec.Rsa.modulusWords len)
  have Os : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  have W := scratch_words Os (by omega) (n := 2 * Spec.Rsa.modulusWords len) (by omega)
    (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega] using h.preApart)
  have E := scratch_bytes Os (by have := h.eBound; have := h.upper; omega) h.eApart
  have X := scratch_bytes Os (by have := h.upper; omega) h.inApart
  refine ⟨?_, ((outside_frame O (by omega)).mono (by simp)).trans P.2⟩
  intro nB length key
  have R := P.1 nB length (by rw [W]; exact key)
  rw [E, X] at R
  exact R

theorem valid_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) (X : Room base bytes args s)
    (exponent : e = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))
    (validE : Spec.Rsa.exponentValid e = true)
    (he : e < 2 ^ 33) (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (VG.Proof.Bignum.exponentHigh e)) :
    WP isa PrecomputedRt.valid s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have space := h.space
  have nw := h.scratch.nowrap
  unfold PrecomputedRt.valid
  refine WP.seq (WP.mono (saveExponent_ok h.scratch (by omega) he lo hi) fun v ⟨E, O, K⟩ => ?_)
  have O' : Outside base 0 bytes s.mem v.mem := O.mono (by omega) (by omega)
  have hv := h.keep K (by decide) (by decide) O'
  have EB := scratch_bytes O' (by have := h.eBound; have := h.upper; omega) h.eApart
  have sp : v.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.mono (sized_ok hv (X.keep K (by decide)) (by rw [E, EB, ← exponent])
    (by rw [EB, ← exponent]; exact validE)) fun t ⟨P, Kt⟩ => ?_
  rw [sp] at P
  exact ⟨Post.compose h (O.mono (by omega) (by omega)) P, (K.mono (by decide)).trans Kt⟩

theorem body_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputedInputs base bytes len args s) (X : Room base bytes args s) :
    WP isa PrecomputedRt.body s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PrecomputedRt.body
  refine WP.seq (WP.mono (precomputedExponentScan_ok h) fun u ⟨E, Lo, Hi, M, K⟩ => ?_)
  refine WP.seq (WP.mono (exponentFlag_ok _ E) fun v ⟨Z, Mv, Kv⟩ => ?_)
  have Ms : v.mem = s.mem := Mv.trans M
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
  have sp : v.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
  refine WP.ite (!Spec.Rsa.exponentValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))) Z ?_ ?_
  · intro bad
    have invalid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = false := by simpa using bad
    refine WP.mono (precomputedFailure_post hv (by
      intro nB _ _
      simp only [Ms, Spec.Rsa.publicOpChecked, invalid, Bool.false_eq_true, ite_false])) fun t ⟨P, T⟩ => ?_
    exact ⟨Post.of_old (by simpa only [Ms] using P), Ks.trans T⟩
  · intro good
    have valid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true := by simpa using good
    have bound : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat) < 2 ^ 33 := by
      have H := valid
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at H
      exact H.2
    refine WP.mono (valid_ok hv (X.keep Ks (by decide)) (by rw [Ms]) valid bound
      ((Kv.1 .ebx (by decide)).trans Lo) ((Kv.1 .edx (by decide)).trans Hi)) fun t ⟨R, T⟩ => ?_
    rw [Ms, sp] at R
    exact ⟨R, Ks.trans T⟩

/-- The contract's resources with 40 bytes of stack. -/
structure TopABI (s : State) : Prop where
  abi : PrecomputedABI s
  room : CallRoom (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8)
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩

theorem topABI_of {s : State} (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pre s) : TopABI s := by
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  sig_split h
  have low : 40 ≤ (s.gpr .esp).toNat := by with_reducible assumption
  have bs : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 40#64, 40⟩
      ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩ := by with_reducible assumption
  refine ⟨?_, ⟨low, ?_⟩, by with_reducible assumption⟩
  · constructor <;> first
      | with_reducible assumption
      | omega
      | exact bs.sub_left (VG.X86.Taint.below_sub (by decide) (by decide))
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth low]
    exact bs

theorem operation_ok {s : State} (A : TopABI s) :
    WP isa PrecomputedRt.code s fun t =>
      (∀ nB : List Byte, nB.length = (arg s 1).toNat →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat) →
        Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 1).toNat (t.gpr .eax)
          (Spec.Rsa.publicOpChecked nB
            (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
            (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 1).toNat))) ∧ abiPreserved s t := by
  have B := A.abi
  have low : 16 ≤ (arg s 9).toNat * 8 := by have := B.used; omega
  have high : (arg s 9).toNat * 8 ≤ 2 ^ 64 := by have := B.scratchBound; omega
  unfold PrecomputedRt.code
  refine WP.seq (WP.mono (precomputedInstalled_ok B) fun u ⟨I, S, K, O⟩ => ?_)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have X : Room (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s) u :=
    ⟨(PublicRt.setWidth_toNat _).symm, rfl, by rw [espu]; exact A.room, by rw [espu]; exact B.stackBound⟩
  refine WP.seq (WP.mono (body_ok I X) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  rw [espu] at F
  have Saved := frame_saved F I.outApart low high A.room.apart S
  have Whole : Frame [⟨argumentPointer s 8, (arg s 9).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 1).toNat⟩, below (s.gpr .esp) 40] s.mem v.mem := by
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
    · exact B.retOut
    · exact ret_below A.room.low
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, publicRestored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  intro nB length key
  rw [R.mem, R.other .eax (by decide)]
  have W := scratch_words O high (n := (arg s 3).toNat)
    (by have := B.preBound; omega) (by simpa only [Nat.mul_comm] using B.preScratch)
  have EB := scratch_bytes O (by have := (arg s 5).isLt; omega) B.eScratch
  have XB := scratch_bytes (p := argumentPointer s 6) (len := (arg s 1).toNat) O (by have := B.lengths.2; omega)
    (by rw [← B.inLength]; exact B.inScratch)
  have keyU : Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt u.mem (byteAddr (arg s 2))
      (2 * Spec.Rsa.modulusWords (arg s 1).toNat)) := by
    change Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt u.mem (argumentPointer s 2)
      (Spec.Rsa.precomputedWords (arg s 1).toNat))
    rw [← B.preLength, W]
    exact key
  have Result := V nB length keyU
  change Spec.Rsa.written v.mem (argumentPointer s 0) (arg s 1).toNat (v.gpr .eax)
    (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt u.mem (argumentPointer s 4) (arg s 5).toNat)
      (Spec.Rsa.bytesAt u.mem (argumentPointer s 6) (arg s 1).toNat)) at Result
  rw [EB, XB] at Result
  exact Result

theorem correct (s : State) (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pre s) :
    ∃ trace t, Exec isa PrecomputedRt.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputedCheckedContract abi 40).post s t := by
  obtain ⟨trace, t, E, V, A⟩ := operation_ok (topABI_of h)
  refine ⟨trace, t, E, A, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Bignum.X86.PrecomputedRt
