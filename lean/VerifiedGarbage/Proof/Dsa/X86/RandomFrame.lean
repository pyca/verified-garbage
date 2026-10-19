module
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Dsa.X86.Random

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The randomized signer's frame (x86)

`esp` holds the frame's base `B` (`RF`), whose `frameBytes` bytes are
writable; above them lie the return address and the caller's thirteen
arguments, writable (the contract's `writeArgs`), all below `2³²`. Slots and arguments are 32-bit words
at offsets from `B` (`w32`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The offset of the caller's argument `j` from the frame's base. -/
def argOff (j : Nat) : Nat := frameBytes + 4 + 4 * j

/-- The frame and the arguments above it. -/
structure RF (s : State) (B : Addr) : Prop where
  esp : (s.gpr .esp).setWidth 64 = B
  wr : (⟨B, frameBytes⟩ : Region) ∈ s.wr
  args : (⟨off B (argOff 0), 52⟩ : Region) ∈ s.wr
  nowrap : B.toNat + argOff 13 ≤ 2 ^ 32

theorem RF.esp_toNat {s : State} {B : Addr} (h : RF s B) : (s.gpr .esp).toNat = B.toNat := by
  rw [← h.esp, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

/-- `[esp + d]`. -/
theorem RF.ea {s : State} {B : Addr} (h : RF s B) {d : Nat} (hd : d < argOff 13) :
    s.ea (sp d) = off B d := by
  change addr (s.gpr .esp) d = _
  rw [addr_eq (by have := h.nowrap; have := h.esp_toNat; omega), h.esp]

theorem RF.read {s : State} {B : Addr} (h : RF s B) {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions (s.rd ++ s.wr) (off B d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base B hd (by have := h.nowrap; unfold argOff at this; omega)⟩

theorem RF.write {s : State} {B : Addr} (h : RF s B) {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions s.wr (off B d) n :=
  ⟨_, h.wr, Offset.contains_base B hd (by have := h.nowrap; unfold argOff at this; omega)⟩

theorem RF.readArg {s : State} {B : Addr} (h : RF s B) {j : Nat} (hj : j < 13) :
    InRegions (s.rd ++ s.wr) (off B (argOff j)) 4 := by
  refine ⟨_, List.mem_append_right _ h.args, ?_⟩
  have e : off B (argOff j) = off (off B (argOff 0)) (4 * j) := by
    rw [off, off, off, BitVec.add_assoc, ← BitVec.ofNat_add, show argOff 0 + 4 * j = argOff j by
      unfold argOff; omega]
  rw [e]
  exact Offset.contains_base _ (by omega) (by omega)

/-- A slot's word. -/
theorem RF.readSlot {s : State} {B : Addr} (h : RF s B) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    readSrc s (.mem (sp d)) = some (s.mem.readW (off B d) 32) := by
  show s.load32 (s.ea (sp d)) = _
  rw [h.ea (by unfold argOff; omega), State.load32, ite_eq_left_iff.mpr fun e => absurd (h.read hd) e]

/-- The caller's argument `j`. -/
theorem RF.readArgSrc {s : State} {B : Addr} (h : RF s B) {j : Nat} (hj : j < 13) :
    readSrc s (.mem (arg j)) = some (s.mem.readW (off B (argOff j)) 32) := by
  show s.load32 (s.ea (sp (argOff j))) = _
  rw [h.ea (by unfold argOff; omega), State.load32, ite_eq_left_iff.mpr fun e => absurd (h.readArg hj) e]

theorem RF.of_keeps {rs : List Reg} {s s' : State} {B : Addr} (h : RF s B) (hk : Keeps rs s s')
    (hsp : .esp ∉ rs := by decide) : RF s' B :=
  ⟨by rw [hk.1 _ hsp]; exact h.esp, hk.2.2 ▸ h.wr, hk.2.2 ▸ h.args, h.nowrap⟩

/-- A store to a slot leaves the arguments, which lie above the frame. -/
theorem RF.arg_store {s : State} {B : Addr} (h : RF s B) {d j : Nat} (hd : d + 4 ≤ frameBytes)
    (v : BitVec 32) (hj : j < 13) :
    (s.mem.writeW (off B d) v).readW (off B (argOff j)) 32 = s.mem.readW (off B (argOff j)) 32 := by
  apply BitVec.eq_of_toNat_eq
  have := (writeW32_outside s.mem B (d := d) v (by have := h.nowrap; unfold argOff at this; omega)).w32
    (d := argOff j) (.inr (by unfold argOff; omega)) (by have := h.nowrap; unfold argOff at this ⊢; omega)
  simpa only [w32] using this

theorem RF.of_mupd {s t : State} {B : Addr} {m : Mem} (h : RF s B) (hu : Mupd s t m) : RF t B :=
  h.of_keeps (hu.keeps []) (by decide)

/-- The 32-bit word at offset `d` of `B`. -/
abbrev slot (m : Mem) (B : Addr) (d : Nat) : BitVec 32 := m.readW (off B d) 32

theorem slot_write_self (m : Mem) (B : Addr) (d : Nat) (v : BitVec 32) :
    slot (m.writeW (off B d) v) B d = v := Mem.readW_writeW_self32 _ _ _

theorem slot_write_ne (m : Mem) (B : Addr) {o d : Nat} {w : Nat} (v : BitVec w)
    (hsep : d + 4 ≤ o ∨ o + w / 8 ≤ d) (hd : d + 4 ≤ 2 ^ 64) (ho : o + w / 8 ≤ 2 ^ 64) :
    slot (m.writeW (off B o) v) B d = slot m B d :=
  Mem.readW_writeW_sep (Offset.sep B hsep hd ho) (by decide)

/-- `mov [esp + d], r`, a slot of the frame. -/
theorem wp_slot {s : State} {B : Addr} (hf : RF s B) {d : Nat} (hd : d + 4 ≤ frameBytes) {r : Reg}
    {v : BitVec 32} (hv : s.gpr r = v) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RF t B → t.mem = s.mem.writeW (off B d) v → t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr →
      t.zf = s.zf → t.cf = s.cf → WP isa (.block is) t Q) :
    WP isa (.block (.store (sp d) r :: is)) s Q :=
  wp_storeS (hf.ea (by unfold argOff frameBytes at *; omega)) (hf.write hd) fun t u =>
    k t (hf.of_mupd u) (by rw [u.mem, hv]) u.gpr u.rd u.wr u.zf u.cf

end VG.Proof.Dsa.X86
