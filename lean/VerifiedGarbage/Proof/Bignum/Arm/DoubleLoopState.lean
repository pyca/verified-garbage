module
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Bignum.Arm.Shift
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.TCB.Arm.Isa

/-! # Workspace and stack invariants shared by repeated modular doublings -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

structure DoubleLoopReady (base : BitVec 32) (len w c : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  inverse : ((word s.mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  operand : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0
  two : w32 s.mem (State.addr base) (arrAt w 7) = 2
  counter : s.mem.readW (off (State.addr base) 208) 32 = BitVec.ofNat 32 c
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem DoubleLoopReady.after_double {s t : State} {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s)
    (bound : numAt t.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0)
    (keeps : Keeps (State.addr base) len w 4 s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) :
    DoubleLoopReady base len w c t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  have oldM := keeps_array_num keeps fits (show Operand 0 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  have oldLow := keeps_array_word (d := 0) (bits := 64) keeps fits (show Operand 0 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) (by omega)
  have oldTwo := keeps_array_word (d := 0) (bits := 32) keeps fits (show Operand 7 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) (by omega)
  simp only [Nat.add_zero] at oldLow oldTwo
  refine ⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((t.mem.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (t.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [oldLow, keeps_header_readW keeps size (d := 56) (bits := 64) (by decide)]
    exact h.inverse
  · rw [oldM]; exact bound
  · change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [oldTwo]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

end VG.Proof.Bignum.Arm
