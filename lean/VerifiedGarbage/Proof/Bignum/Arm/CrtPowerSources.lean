module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! # Read-only ciphertext and exponent buffers for one CRT factor -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtPowerStack.lean`, which only this module imported.
section

/-! # The immutable input and factor-exponent arguments in the CRT call frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtPowerStack (base xp ep : BitVec 32) (len k eLen slot : Nat) (s : State) : Prop where
  nowrap : s.sp.toNat + 112 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 56) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 12) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) slot) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) (slot + 4)) 4
  separate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr base, 8 * len⟩
  slotFit : slot + 8 ≤ 112
  input : s.mem.readW (off (State.addr s.sp) 56) 32 = xp
  inputCount : s.mem.readW (off (State.addr s.sp) 12) 32 = BitVec.ofNat 32 k
  exponent : s.mem.readW (off (State.addr s.sp) slot) 32 = ep
  exponentCount : s.mem.readW (off (State.addr s.sp) (slot + 4)) 32 = BitVec.ofNat 32 eLen

theorem CrtPowerStack.after_workspace {s t : State} {base xp ep : BitVec 32} {len k eLen slot : Nat} {rs : List Reg}
    (h : CrtPowerStack base xp ep len k eLen slot s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtPowerStack base xp ep len k eLen slot t := by
  have eq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  have fit := h.slotFit
  refine ⟨by rw [rest.sp]; exact h.nowrap,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.readable,
    by rw [rest.sp]; exact h.separate, fit, ?_, ?_, ?_, ?_⟩
  · rw [rest.sp, eq.word (d := 56) (bits := 32) (by decide)]; exact h.input
  · rw [rest.sp, eq.word (d := 12) (bits := 32) (by decide)]; exact h.inputCount
  · rw [rest.sp, eq.word (d := slot) (bits := 32) (by omega)]; exact h.exponent
  · rw [rest.sp, eq.word (d := slot + 4) (bits := 32) (by omega)]; exact h.exponentCount

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure CrtPowerSources (base xp ep : BitVec 32) (len w k eLen slot : Nat) (xb eb : List Byte) (s : State) : Prop where
  stack : CrtPowerStack base xp ep len k eLen slot s
  input : PublicBytes xp k xb s
  exponent : PublicBytes ep eLen eb s
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputPositive : 0 < k
  inputFits : k ≤ 8 * w
  exponentPositive : 0 < eLen
  exponentFits : eLen < 2 ^ 32

theorem CrtPowerSources.after_workspace {s t : State} {base xp ep : BitVec 32}
    {len w k eLen slot : Nat} {xb eb : List Byte} {rs : List Reg}
    (h : CrtPowerSources base xp ep len w k eLen slot xb eb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtPowerSources base xp ep len w k eLen slot xb eb t :=
  ⟨h.stack.after_workspace frame rest,
    h.input.after_frame frame rest (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.inputSeparate),
    h.exponent.after_frame frame rest (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate),
    h.inputSeparate, h.exponentSeparate, h.inputPositive, h.inputFits, h.exponentPositive, h.exponentFits⟩

end VG.Proof.Bignum.Arm
