module
public import VerifiedGarbage.Proof.Bignum.Arm.PublicData
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Arm.PublicStack

import VerifiedGarbage.Proof.Bignum.Arm.PublicStackFrame
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Offset

/-! # Public buffers and packed precomputation for the callable RSA body -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PdBodyInput (base dst pp ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  buffers : PublicData base dst ep xp len k eLen eb xb s
  stack : PublicStack base dst pp ep xp len k eLen s
  ptr : s.gpr .r0 = base
  sourceFit : pp.toNat + 16 * Spec.Rsa.modulusWords k ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr pp) (16 * Spec.Rsa.modulusWords k)
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr pp, 16 * Spec.Rsa.modulusWords k⟩
  stackPre : Region.Disjoint ⟨State.addr pp, 16 * Spec.Rsa.modulusWords k⟩ ⟨State.addr s.sp, 56⟩
  modulus : (s.mem.read (State.addr pp) (8 * Spec.Rsa.modulusWords k)).toNat = N
  r2 : (s.mem.read (off (State.addr pp) (8 * Spec.Rsa.modulusWords k)) (8 * Spec.Rsa.modulusWords k)).toNat = R

theorem PdBodyInput.after_checks {s t : State} {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {rs : List Reg} (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = base) : PdBodyInput base dst pp ep xp len k eLen N R eb xb t := by
  have eq : WorkspaceEq (State.addr pp) (16 * Spec.Rsa.modulusWords k) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := h.sourceFit; omega) frame (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.separate.symm
      · exact h.stackPre.sub_right (Offset.sub_base _ (by decide)))
  refine ⟨h.buffers.after_frame frame rest ?_ ?_, h.stack.after_checks frame rest, ptr,
    h.sourceFit, by rw [rest.rd, rest.wr]; exact h.read, h.separate,
    by rw [rest.sp]; exact h.stackPre, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.buffers.exponentSeparate
    · exact h.buffers.stackExponent.sub_right (Offset.sub_base _ (by decide))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.buffers.inputSeparate
    · exact h.buffers.stackInput.sub_right (Offset.sub_base _ (by decide))
  · have read := eq.read (d := 0) (8 * Spec.Rsa.modulusWords k) (by omega)
    simp only [BitVec.add_zero] at read
    rw [read]; exact h.modulus
  · rw [eq.read (d := 8 * Spec.Rsa.modulusWords k) (8 * Spec.Rsa.modulusWords k) (by omega)]
    exact h.r2

theorem PdBodyInput.after_workspace {s t : State} {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {rs : List Reg} (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = base) : PdBodyInput base dst pp ep xp len k eLen N R eb xb t :=
  h.after_checks (frame.mono (by simp)) rest ptr

theorem PdBodyInput.of_mem {s t : State} {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {rs : List Reg} (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s)
    (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = base) : PdBodyInput base dst pp ep xp len k eLen N R eb xb t :=
  h.after_workspace (by rw [mem]; exact Frame.refl _ _) rest ptr
end VG.Proof.Bignum.Arm
