module

public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.CallFacts
public import VerifiedGarbage.Impl.Ffdh.AArch64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The attempt's arguments (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search

/-- The attempt's stack arguments: `rand_len` (`p_len`), `scratch` and
`scratch_len`. -/
def callValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.xp ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.yp ∧
  t.gpr .x3 = BitVec.ofNat 64 p.len ∧ t.gpr .x4 = p.dp ∧ t.gpr .x5 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .x6 = BitVec.ofNat 64 p.len ∧ t.gpr .x7 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11]

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block arguments) (allocated 32 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController s.mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 32 s) u := by
  have a := h.access
  have hw : ∀ d, d + 8 ≤ 32 → InRegions (⟨callSp p, 32⟩ :: s.wr) (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 32⟩, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  have hw0 : InRegions (⟨callSp p, 32⟩ :: s.wr) (callSp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ ⟨callSp p, 32⟩ :: s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := h.header (j := 5) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := h.header (j := 6) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := h.header (j := 7) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := h.header (j := 12) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := h.header (j := 13) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold arguments writeController callValues KeyArgs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, allocated, h.sp, h.x19, exec_addSp (show 0 < 4096 by decide),
    hl 16 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hl 72 (by decide), hl 96 (by decide), hl 104 (by decide), hw0, hw 8 (by decide), hw 16 (by decide),
    hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]
  simp only [off, Nat.mul_zero, BitVec.add_zero]

end VG.Proof.Ffdh.AArch64.KeyGeneration
