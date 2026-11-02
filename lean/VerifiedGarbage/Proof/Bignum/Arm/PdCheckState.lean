module
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! # Stable workspace and stack geometry for public precomputation checks -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

structure PdCheckState (base : BitVec 32) (len w N R : Nat) (s : State) : Prop where
  ready : LayoutFrameReady base len w s
  stackFit : s.sp.toNat + 52 ≤ 2 ^ 32
  write : InRegions s.wr (off (State.addr s.sp) 48) 4
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr s.sp) 48, 4⟩
  modulus : numAt s.mem (State.addr base) w 0 = N
  r2 : numAt s.mem (State.addr base) w 4 = R

theorem PdCheckState.read {base : BitVec 32} {len w N R : Nat} {s : State}
    (h : PdCheckState base len w N R s) : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4 := by
  obtain ⟨r, hr, sub⟩ := h.write
  exact ⟨r, List.mem_append_right _ hr, sub⟩

theorem PdCheckState.after {base : BitVec 32} {len w N R : Nat} {s t : State} {rs : List Reg}
    (h : PdCheckState base len w N R s) (ready : LayoutFrameReady base len w t) (rest : Rest rs s t)
    (n : numAt t.mem (State.addr base) w 0 = N) (r2 : numAt t.mem (State.addr base) w 4 = R) :
    PdCheckState base len w N R t :=
  ⟨ready, by rw [rest.sp]; exact h.stackFit, by rw [rest.wr, rest.sp]; exact h.write,
    by rw [rest.sp]; exact h.separate, n, r2⟩

theorem PdCheckState.after_array {base : BitVec 32} {len w N R o : Nat} {s t : State} {rs : List Reg}
    (h : PdCheckState base len w N R s) (ready : LayoutFrameReady base len w t) (rest : Rest rs s t)
    (keeps : Keeps (State.addr base) len w o s.mem t.mem) (n0 : 0 ≠ o) (n4 : 4 ≠ o) :
    PdCheckState base len w N R t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  exact h.after ready rest
    ((keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) n0).trans h.modulus)
    ((keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) n4).trans h.r2)

theorem PdCheckState.after_flag {base : BitVec 32} {len w N R : Nat} {s t : State} {rs : List Reg}
    (h : PdCheckState base len w N R s) (ready : LayoutFrameReady base len w t) (rest : Rest rs s t)
    (eq : WorkspaceEq (State.addr base) (8 * len) s.mem t.mem) : PdCheckState base len w N R t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  exact h.after ready rest ((eq.number fits (by decide : 0 < 8)).trans h.modulus)
    ((eq.number fits (by decide : 4 < 8)).trans h.r2)

theorem PdCheckState.keep_flag {base : BitVec 32} {len w N R : Nat} {s t : State} {rs : List Reg}
    (h : PdCheckState base len w N R s) (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest rs s t) :
    t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
  have eq := WorkspaceEq.of_frame (by decide : 4 < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate.symm)
  have word := eq.word (d := 0) (bits := 32) (by decide)
  simpa only [rest.sp, off, BitVec.add_zero] using word

end VG.Proof.Bignum.Arm
