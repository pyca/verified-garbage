module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicInput
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Geometry and input preservation across the public RSA stack push -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem public_push_argAddr {s : State} (fit : 56 ≤ s.sp.toNat) :
    off (State.addr (pcPushed s).sp) 56 = State.addr s.sp := by
  have spNat : (pcPushed s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' fit
  change State.addr (pcPushed s).sp + BitVec.ofNat 64 56 = State.addr s.sp
  rw [← addr_add (a := (pcPushed s).sp) (k := 56) (by rw [spNat]; have := s.sp.isLt; omega)]
  change State.addr (s.sp - BitVec.ofNat 32 56 + BitVec.ofNat 32 56) = _
  rw [BitVec.sub_add_cancel]

theorem public_push_argOffset {s : State} (fit : 56 ≤ s.sp.toNat) (d : Nat) :
    off (State.addr (pcPushed s).sp) (56 + d) = off (State.addr s.sp) d := by
  change State.addr (pcPushed s).sp + BitVec.ofNat 64 (56 + d) = _
  rw [← Offset.add_add]
  rw [show State.addr (pcPushed s).sp + BitVec.ofNat 64 56 = State.addr s.sp from public_push_argAddr fit]

theorem public_push_arguments {s : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicFnInput base dst np ep xp len k eLen nb eb xb s) :
    InRegions ((pcPushed s).rd ++ (pcPushed s).wr) (off (State.addr (pcPushed s).sp) 56) 24 ∧
      WorkspaceEq (State.addr s.sp) 24 s.mem (pcPushed s).mem := by
  have frame := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) h.stackFit
  refine ⟨?_, WorkspaceEq.of_frame (by decide) frame ?_⟩
  · rw [public_push_argAddr h.stackFit]
    exact InRegions_append_cons.mpr (Or.inr h.argRead)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.stackArgs.symm

theorem public_push_separate {s : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicFnInput base dst np ep xp len k eLen nb eb xb s) :
    (⟨State.addr (pcPushed s).sp, 80⟩ : Region).Disjoint ⟨State.addr base, 8 * len⟩ := by
  intro a ha hb
  have lo : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint ⟨State.addr base, 8 * len⟩ := h.stackWorkspace
  by_cases low : (a - State.addr (pcPushed s).sp).toNat < 56
  · exact lo a low hb
  · apply h.argsWorkspace a ?_ hb
    rw [← public_push_argAddr h.stackFit]
    change (a - (State.addr (pcPushed s).sp + BitVec.ofNat 64 56)).toNat + 1 ≤ 24
    have inside := (Offset.lt_iff a (State.addr (pcPushed s).sp) (d := 56) (n := 24) (by decide)).mpr
      ⟨by omega, by change (a - State.addr (pcPushed s).sp).toNat + 1 ≤ 80 at ha; omega⟩
    omega

end VG.Proof.Bignum.Arm
