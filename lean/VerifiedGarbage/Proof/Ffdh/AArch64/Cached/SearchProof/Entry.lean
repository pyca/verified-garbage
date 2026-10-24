module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory

import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key-generation controller's entry (AArch64)

The stack arguments are loaded, the caller's `x19` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving
`x30`, the controller is at the tape's start (`key_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .x19), (5, s.gpr .x0), (6, s.gpr .x2), (7, s.gpr .x5), (8, s.gpr .x6),
    (9, stackArg s 0), (10, stackArg s 1), (11, 0), (12, stackArg s 2), (13, stackArg s 3),
    (15, s.gpr .x4)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) (j : Nat) (hj : j < 7) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .x19 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := input_args h 2 (by decide)
  have ha3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 24) 8 := input_args h 3 (by decide)
  have ha4 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 := input_args h 4 (by decide)
  refine WP.keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] ?_ (by decide) (by decide) (by decide +kernel)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide), hd, ha0,
    ha1, ha2, ha3, ha4, hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 96 (by decide), hs 104 (by decide), hs 120 (by decide)]
  simp only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rfl

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
