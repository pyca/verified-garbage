module

public import VerifiedGarbage.Proof.Ffdh.Arm.InitStores

/-! Small independent blocks keep controller symbolic execution bounded. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm
open VG.Proof.Mont (off)

def pairStore (m : Mem) (B : Addr) (d : Nat) (lo hi : BitVec 32) : Mem :=
  (m.writeW (off B d) lo).writeW (off B (d + 4)) hi

theorem budget_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.budget s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r1 = s.gpr .r1 ∧ t.wr = s.wr ∧
      t.mem = pairStore s.mem (State.addr base) 0
        ((s.gpr .r1 * s.gpr .r1) <<< 6) ((s.gpr .r1 * s.gpr .r1) >>> 26) := by
  have w0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [off, BitVec.add_zero] using h.write (off := 0) (by decide)
  have w4 := h.write (off := 4) (by decide)
  have a4 : State.addr (base + BitVec.ofNat 32 4) = off (State.addr base) 4 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  unfold Generation.budget pairStore
  ffrun [ptr, w0, w4, a4, off, BitVec.add_zero]

theorem width_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.width s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r2 = 0 ∧ t.gpr .r3 = (s.gpr .r1 + 7) >>> 3 ∧ t.wr = s.wr ∧
      t.mem = pairStore s.mem (State.addr base) 8 ((s.gpr .r1 + 7) >>> 3) 0 := by
  have w8 := h.write (off := 8) (by decide)
  have w12 := h.write (off := 12) (by decide)
  have a8 : State.addr (base + BitVec.ofNat 32 8) = off (State.addr base) 8 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  have a12 : State.addr (base + BitVec.ofNat 32 12) = off (State.addr base) 12 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  unfold Generation.width pairStore
  ffrun [ptr, w8, w12, a8, a12, off]

theorem entropy_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) (zero : s.gpr .r2 = 0) :
    WP isa Generation.entropy s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r2 = 0 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.wr = s.wr ∧
      t.mem = pairStore s.mem (State.addr base) 16 (s.gpr .r3 + (s.gpr .r3 <<< 15)) 0 := by
  have w16 := h.write (off := 16) (by decide)
  have w20 := h.write (off := 20) (by decide)
  have a16 : State.addr (base + BitVec.ofNat 32 16) = off (State.addr base) 16 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  have a20 : State.addr (base + BitVec.ofNat 32 20) = off (State.addr base) 20 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  unfold Generation.entropy pairStore
  ffrun [ptr, zero, w16, w20, a16, a20, off]

theorem request_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) (zero : s.gpr .r2 = 0) :
    WP isa Generation.request s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = pairStore s.mem (State.addr base) 24 (s.gpr .r3 <<< 9) 0 := by
  have w24 := h.write (off := 24) (by decide)
  have w28 := h.write (off := 28) (by decide)
  have a24 : State.addr (base + BitVec.ofNat 32 24) = off (State.addr base) 24 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  have a28 : State.addr (base + BitVec.ofNat 32 28) = off (State.addr base) 28 :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  unfold Generation.request pairStore
  ffrun [ptr, zero, w24, w28, a24, a28, off]

theorem parameterInitializeState_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa Generation.initializeState s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = controlMem s.mem (State.addr base) (parameterInitValues (s.gpr .r1)) := by
  rw [Generation.initializeState, WP.seq_iff]
  refine WP.mono (budget_ok s h ptr) ?_
  rintro u ⟨ptrU, bitsU, wrU, memU⟩
  rw [WP.seq_iff]
  refine WP.mono (width_ok u (h.congr wrU) ptrU) ?_
  rintro v ⟨ptrV, zeroV, widthV, wrV, memV⟩
  rw [WP.seq_iff]
  refine WP.mono (entropy_ok v (h.congr (wrV.trans wrU)) ptrV zeroV) ?_
  rintro z ⟨ptrZ, zeroZ, widthZ, wrZ, memZ⟩
  refine WP.mono (request_ok z (h.congr (wrZ.trans (wrV.trans wrU))) ptrZ zeroZ) ?_
  rintro t ⟨result, memT⟩
  refine ⟨result, ?_⟩
  rw [memT, memZ, memV, memU, widthZ, widthV, bitsU]
  rfl

end VG.Proof.Ffdh.Arm
