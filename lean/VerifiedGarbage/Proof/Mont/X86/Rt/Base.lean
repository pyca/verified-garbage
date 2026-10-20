module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # Pointers into a working space (32-bit x86)

The run-time width multiplication (`Impl/Mont/X86/MulRt.lean`) reaches its
working space, `L` bytes at `W` below `2³²` (`Ws`), through registers that
hold `W` plus an offset (`PtrAt`): its loads and stores through them are the
bytes `off W y` (`ea_ptr`), which `w32`, `val32` and `Outside` read and
frame.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- The working space: writable, and below `2³²`. -/
structure Ws (s : State) (W : Addr) (L : Nat) : Prop where
  wr : (⟨W, L⟩ : Region) ∈ s.wr
  nowrap : W.toNat + L ≤ 2 ^ 32

/-- `r` holds `W + x` (modulo `2³²`: a pointer may end just past the top of
the address space). -/
abbrev PtrAt (s : State) (W : Addr) (r : Reg) (x : Nat) : Prop := (s.gpr r).toNat = (W.toNat + x) % 2 ^ 32

theorem Ws.of_wr {s s' : State} {W : Addr} {L : Nat} (h : Ws s W L) (hw : s'.wr = s.wr) : Ws s' W L :=
  ⟨hw ▸ h.wr, h.nowrap⟩

theorem Ws.of_keeps {s s' : State} {W : Addr} {L : Nat} {rs : List Reg} (h : Ws s W L) (K : Keeps rs s s') :
    Ws s' W L := h.of_wr K.2.2

/-- `[r + d]`, for `r = W + x`. -/
theorem ea_ptr {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {r : Reg} {x d : Nat} (hp : PtrAt s W r x)
    (hd : x + d < L) : s.ea (at_ r d) = off W (x + d) := by
  have := hw.nowrap
  rw [at_, ea_mk, addr_eq (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hW : W.toNat < 2 ^ 64 := W.isLt
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega), hp]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem ws_read {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {y n : Nat} (hy : y + n ≤ L) :
    InRegions (s.rd ++ s.wr) (off W y) n :=
  ⟨_, List.mem_append_right _ hw.wr, Scr.contains hw.nowrap hy⟩

theorem ws_write {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {y n : Nat} (hy : y + n ≤ L) :
    InRegions s.wr (off W y) n := ⟨_, hw.wr, Scr.contains hw.nowrap hy⟩

/-- A load through `r = W + x`. -/
theorem readSrc_ptr {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {r : Reg} {x d : Nat} (hp : PtrAt s W r x)
    (hd : x + d + 4 ≤ L) : readSrc s (.mem (at_ r d)) = some (s.mem.readW (off W (x + d)) 32) := by
  show s.load32 (s.ea (at_ r d)) = _
  rw [ea_ptr hw hp (by omega), State.load32, ite_eq_left_iff.mpr fun h => absurd (ws_read hw hd) h]

/-- A pointer moved up by a register or an immediate. -/
theorem ptr_add {s : State} {W : Addr} {r : Reg} {x : Nat} (hp : PtrAt s W r x) (v : BitVec 32) :
    (s.gpr r + v).toNat = (W.toNat + (x + v.toNat)) % 2 ^ 32 := by
  rw [BitVec.toNat_add, hp]; omega

/-- A pointer moved down. -/
theorem ptr_sub {s : State} {W : Addr} {r : Reg} {x : Nat} (hp : PtrAt s W r x) (v : BitVec 32)
    (h : v.toNat ≤ x) : (s.gpr r - v).toNat = (W.toNat + (x - v.toNat)) % 2 ^ 32 := by
  have := v.isLt
  rw [BitVec.toNat_sub, hp]; omega

end VG.Proof.Mont.X86.Rt
