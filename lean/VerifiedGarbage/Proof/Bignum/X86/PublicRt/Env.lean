module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Call
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages

/-! # What the exponentiation of public RSA at a run-time width keeps

`Env`: the inputs, the room for calls below `esp`, the modulus `M` (number
0) and `-M⁻¹ mod 2³²` (at 152). Every stage after the setup changes memory
only in the exponent's words and masks (128 to 139), the numbers from 1 on
and the callee's range, and the stack below `esp` (`Chg`), so it keeps
`Env` (`Env.keep`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The regions the exponentiation changes. -/
def Chg (base : Addr) (len bytes : Nat) (sp : BitVec 32) : List Region :=
  [⟨off base 128, 12⟩, ⟨off base (numAt len 1), bytes - numAt len 1⟩, below sp 40]

structure Env (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (M : Nat) (s : State) : Prop where
  pi : RtIn base bytes len args s
  room : CallRoom (s.gpr .esp) base bytes
  mod : val32 s.mem base numOff (nw len) = M
  inv : (M * w32 s.mem base invOff + 1) % 2 ^ 32 = 0
  top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32

/-- A range of the working space keeps its bytes when memory changes only elsewhere. -/
theorem frame_read {base : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame (Chg base len bytes sp) m m') (R : CallRoom sp base bytes) (hn : base.toNat + bytes ≤ 2 ^ 32)
    (h1 : numAt len 1 ≤ bytes) {d k : Nat} (hdk : d + k ≤ bytes) (hsep : d + k ≤ 128 ∨ (140 ≤ d ∧ d + k ≤ numAt len 1)) :
    m'.read (off base d) k = m.read (off base d) k := by
  have h256 : 256 ≤ numAt len 1 := by simp [numAt, numOff]
  refine F.read (r := ⟨off base d, k⟩) (Region.contains_self _ _) (fun r hr => ?_) (by omega)
  simp only [Chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base (by omega) (by omega) (by omega)
  · exact Offset.disjoint base (by omega) (by omega) (by omega)
  · refine (R.apart.sub_right ?_).symm
    have := Offset.sub base (d := d) (n := k) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem Env.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat} {s t : State}
    (E : Env base bytes len args M s) {regs : List Reg} (K : Keeps regs s t) (di : .edi ∉ regs)
    (sp : .esp ∉ regs) (F : Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem) : Env base bytes len args M t := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have f0 := (h.fits (j := 0) (by decide)).1
  have e01 : numAt len 1 = numAt len 0 + wb len := numAt_succ len 0
  have n0 : numAt len 0 = numOff := by simp [numAt]
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  have h256 : numOff = 256 := rfl
  refine ⟨?_, by rw [esp]; exact E.room, ?_, ?_, by rw [esp]; exact E.top⟩
  · refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space, fun i hi => ?_, h.outLen, h.inLen,
      h.outFit, h.inFit, by rw [K.2.2]; exact h.outWrite, by rw [K.2.1, K.2.2]; exact h.inRead, h.outApart,
      h.inApart⟩
    have A := h.stack i hi
    refine ⟨A.stack.keep K sp, ?_⟩
    rw [← A.value]
    unfold VG.Proof.Dsa.X86.stackValue
    rw [show VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i by
      simp only [VG.Proof.Dsa.X86.stackAddress, esp]]
    refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    have ap := A.stack.apart
    simp only [Chg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ap.sub_right ?_
      have := Offset.sub base (d := 128) (n := 12) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · refine ap.sub_right ?_
      have := Offset.sub base (d := numAt len 1) (n := bytes - numAt len 1) (e := 0) (k := bytes) (Nat.zero_le _)
        (by omega)
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · -- The argument is above `esp`, the 40 bytes below it.
      have low := E.room.low
      have top := E.top
      have ea : (VG.Proof.Dsa.X86.stackAddress s i).toNat = (s.gpr .esp).toNat + (4 + 4 * i) := by
        simp only [VG.Proof.Dsa.X86.stackAddress, addr, setWidth_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have eb : ((s.gpr .esp - BitVec.ofNat 32 40).setWidth 64).toNat = (s.gpr .esp).toNat - 40 := by
        rw [setWidth_toNat, sub_toNat (by omega)]
      exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 40) (.inl (by dsimp only; rw [eb, ea]; omega))
        (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; omega)).symm
  · rw [← E.mod, ← read_eq_val32, ← read_eq_val32,
      frame_read F E.room nw' (by rw [e01]; omega) (by rw [← wb_eq]; omega) (.inr ⟨by simp [numOff], by rw [← wb_eq]; omega⟩)]
  · rw [show w32 t.mem base invOff = w32 s.mem base invOff by
      unfold w32
      simp only [Mem.readW]
      rw [frame_read F E.room nw' (by rw [e01]; omega) (by simp only [invOff, n0, numOff] at f0 ⊢; omega)
        (.inr ⟨by decide, by rw [e01, n0]; simp only [invOff, numOff]; omega⟩)]]
    exact E.inv

end VG.Proof.Bignum.X86.PublicRt
