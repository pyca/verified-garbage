module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.CallFacts
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # One attempt of the key-generation controller (PPC64LE)

In its frame of 128 bytes, the controller passes `vg_ffdh_generate_key` the
next `p_len` octets of the tape, its stack arguments at offset 96 of the
frame. The attempt keeps the controller's state, and leaves its status, and
the key pair or zeros, in `x` and `y`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gkContract)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- The attempt's stack arguments: `rand_len` (`p_len`), `scratch` and
`scratch_len`, at offset 96 of its frame. -/
def callValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(12, BitVec.ofNat 64 p.len), (13, p.B), (14, BitVec.ofNat 64 (p.Z / 8))]

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .r3 = p.xp ∧ t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = p.yp ∧
  t.gpr .r6 = BitVec.ofNat 64 p.len ∧ t.gpr .r7 = p.dp ∧ t.gpr .r8 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .r9 = BitVec.ofNat 64 p.len ∧ t.gpr .r10 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem callSp_eq' (p : KeyPublic) : p.sp - 48 - BitVec.ofNat 64 128 = callSp p := rfl

/-- The frame's push writes its back chain below the stack pointer. -/
theorem alloc_frame {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    Frame (KeyInput.callChanges original) s.mem (allocated 128 s).mem := by
  have hi := h.input
  refine Frame.write (Frame.refl _ _) (r := below original.sp stackUse) (by simp [KeyInput.callChanges]) _ ?_
  rw [h.sp, callSp_eq', callSp_eq, ← hi.sp_eq]
  exact Offset.contains_below p.sp (a := 176) (b := 176) (by decide) (by decide) (by decide)

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block arguments) (allocated 128 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController (allocated 128 s).mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 128 s) u := by
  have a := h.access
  have hc := h.input.control_frame (alloc_frame h)
  have e0 : s.sp - BitVec.ofNat 64 128 = callSp p := by rw [h.sp]
  have hw : ∀ e, e + 8 ≤ 96 → InRegions (allocated 128 s).wr (callSp p + 32 + BitVec.ofNat 64 e) 8 := by
    intro e he
    refine ⟨frameR 128 s, List.mem_cons_self .., ?_⟩
    simp only [frameR, e0]
    exact Offset.contains_base _ he (by omega)
  have hl : ∀ d, d + 8 ≤ 128 →
      InRegions ((allocated 128 s).rd ++ (allocated 128 s).wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv (j : Nat) (hj : j < 16) {v : BitVec 64} (he : (j, v) ∈ p.headers used keys scalars) :
      (allocated 128 s).mem.readW (p.control + BitVec.ofNat 64 (8 * j)) 64 = v :=
    (hc j hj).trans (h.header he)
  have hv2 := hv 2 (by decide) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := hv 5 (by decide) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := hv 6 (by decide) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := hv 7 (by decide) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := hv 8 (by decide) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := hv 9 (by decide) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := hv 12 (by decide) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := hv 13 (by decide) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  have ea : ∀ t : State, exec (.addSp .r11 96) t = some (t.write .r11 (t.sp + BitVec.ofNat 64 96)) := by
    intro t; simp [exec]
  have hwo : ∀ e, e + 8 ≤ 96 → InRegions (allocated 128 s).wr (Mont.off (callSp p) (32 + e)) 8 := by
    intro e he
    have := hw e he
    rwa [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 e = BitVec.ofNat 64 (32 + e) by
      rw [BitVec.ofNat_add]; rfl] at this
  have hw96 := hwo 64 (by decide)
  have hw104 := hwo 72 (by decide)
  have hw112 := hwo 80 (by decide)
  have hw96' : InRegions (allocated 128 s).wr (callSp p + 96#64) 8 := hw96
  simp only [Nat.reduceAdd] at hw96 hw104 hw112
  refine WP.keep argRegsW ?_ (by decide)
  unfold arguments writeController callValues KeyArgs
  simp only [List.foldl_cons, List.foldl_nil]
  have r31 : (allocated 128 s).gpr .r31 = p.control := h.r31
  have sp' : (allocated 128 s).sp = callSp p := e0
  prun [ldf, r31, sp', ea, hl 16 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    hl 64 (by decide), hl 72 (by decide), hl 96 (by decide), hl 104 (by decide), hw96, hw96', hw104, hw112, hv2, hv5, hv6, hv7, hv8,
    hv9, hv12, hv13]

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
