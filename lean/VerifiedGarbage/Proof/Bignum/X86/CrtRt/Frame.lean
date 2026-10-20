module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee

/-! # What a stage of private CRT at a run-time width changes

`frameR base sp ws`: ranges `ws` of the working space and the 40 bytes below
`sp`, where the calls write their arguments and return addresses. A number
apart from the ranges keeps its value (`frameR_val32`), and so do the inputs
(`In.keepF`): the arguments lie above `sp`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (stackAddress stackValue)

/-- The regions a stage may change. -/
def frameR (base : Addr) (sp : BitVec 32) (ws : List (Nat × Nat)) : List Region :=
  below sp 40 :: ws.map fun p => ⟨off base p.1, p.2⟩

section
variable {base : Addr} {sp : BitVec 32} {ws ws' : List (Nat × Nat)} {m m' : Mem}

theorem frameR_mono (F : Frame (frameR base sp ws) m m') (h : ∀ p ∈ ws, p ∈ ws' := by decide) :
    Frame (frameR base sp ws') m m' :=
  F.mono fun r hr => by
    simp only [frameR, List.mem_cons, List.mem_map] at hr ⊢
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨p, h p hp, rfl⟩

theorem frameR_of_outside {o n : Nat} (O : Outside base o n m m') (fit : o + n ≤ 2 ^ 64) (h : (o, n) ∈ ws) :
    Frame (frameR base sp ws) m m' :=
  (outside_frame O fit).mono fun r hr => by
    rw [List.mem_singleton.mp hr]
    simp only [frameR, List.mem_cons, List.mem_map]
    exact .inr ⟨_, h, rfl⟩

theorem frameR_of_mul {o n sc k : Nat} (F : Frame [⟨off base o, n⟩, ⟨off base sc, k⟩, below sp 40] m m')
    (ho : (o, n) ∈ ws) (hs : (sc, k) ∈ ws) : Frame (frameR base sp ws) m m' :=
  F.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [frameR, List.mem_cons, List.mem_map]
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, ho, rfl⟩
    · exact .inr ⟨_, hs, rfl⟩
    · exact .inl rfl

/-- A number apart from the ranges keeps its value. -/
theorem frameR_val32 {bytes : Nat} (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes)
    (nw : base.toNat + bytes ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 * k ≤ bytes)
    (hws : ∀ p ∈ ws, d + 4 * k ≤ p.1 ∨ p.1 + p.2 ≤ d) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    val32 m' base d k = val32 m base d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) (fun r hr => ?_) (by omega))
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · refine (R.apart.sub_right ?_).symm
    have := Offset.sub base (d := d) (n := 4 * k) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · have := hws p hp
    have := hfit p hp
    exact Offset.disjoint base (by omega) (by omega) (by omega)

end

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}

/-- The inputs hold after a stage that changes registers but `edi` and `esp`, and memory in its ranges. -/
theorem In.keepF (h : In base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {ws : List (Nat × Nat)}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    In base bytes len args t := by
  have hc := h.crt
  have nw := hc.scratch.nowrap
  have low := hc.room.low
  have top := hc.top
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  refine ⟨⟨hc.scratch.of_keeps K di sp, hc.lower, hc.upper, hc.space, fun i hi => ⟨(hc.stack i hi).stack.keep K sp, ?_⟩,
    hc.outLen, hc.nLen, hc.inLen, hc.pShort, hc.qShort, hc.dpLen, hc.dqLen, hc.qiLen, hc.outFit,
    by rw [K.2.2]; exact hc.outWrite, hc.outApart, hc.positive, hc.bounded, hc.fits,
    fun i hi => by rw [K.2.1, K.2.2]; exact hc.readable i hi, hc.apart, by rw [esp]; exact hc.room,
    by rw [esp]; exact hc.top⟩, h.need, h.hbase, h.hbytes⟩
  have A := hc.stack i hi
  rw [← A.value]
  unfold stackValue
  rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, esp]]
  refine F.readW (r := ⟨stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · have ea : (stackAddress s i).toNat = (s.gpr .esp).toNat + (4 + 4 * i) := by
      simp only [stackAddress, addr, PublicRt.setWidth_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have eb : ((s.gpr .esp - BitVec.ofNat 32 40).setWidth 64).toNat = (s.gpr .esp).toNat - 40 := by
      rw [PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega)]
    exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 40) (.inl (by dsimp only; rw [eb, ea]; omega))
      (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; omega)).symm
  · refine A.stack.apart.sub_right ?_
    have := hfit p hp
    have := Offset.sub base (d := p.1) (n := p.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

end

end VG.Proof.Bignum.X86.CrtRt
