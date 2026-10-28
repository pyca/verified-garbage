module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Arena
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The stage's frame and working space, from its arguments

The frame is at `frameBase s`, the stack pointer less 272, and the stage's
288 bytes of stack hold it and the 16 bytes below it. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

/-- The frame's base. -/
abbrev frameBase (s : State) : Addr := s.sp - BitVec.ofNat 64 272

/-- The working space's region. -/
abbrev wsRegion (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩

/-- The h tape's region. -/
abbrev tapeRegion (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩

/-- The hash workspace the frame's layout names. -/
abbrev hashBase (s : State) : Addr := off (s.gpr .x0) VG.Impl.Dsa.Generation.Layout.hash

theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ 272) :
    Region.Sub ⟨off (frameBase s) d, n⟩ (below s.sp stack) := by
  have e : off (frameBase s) d = s.sp - BitVec.ofNat 64 (272 - d) := by
    simp only [off, frameBase]
    rw [Offset.sub_ofNat_eq s.sp (show 272 - d ≤ 272 by omega), Nat.sub_sub_self (by omega)]
  rw [e]
  exact Offset.sub_below s.sp (by unfold stack; omega) (by unfold stack; omega)

theorem frame_sub0 (s : State) {n : Nat} (h : n ≤ 272) :
    Region.Sub ⟨frameBase s, n⟩ (below s.sp stack) := by
  simpa only [off, BitVec.add_zero] using frame_sub s (d := 0) (n := n) (by omega)

theorem retR_sub (s : State) : Region.Sub (below (frameBase s) 16) (below s.sp stack) := by
  have e : frameBase s - BitVec.ofNat 64 16 = s.sp - BitVec.ofNat 64 288 := by
    simp only [frameBase, BitVec.sub_sub]; rfl
  change Region.Sub ⟨_, 16⟩ ⟨_, 288⟩
  rw [e]
  simpa only [off, BitVec.add_zero] using Offset.sub_base (s.sp - BitVec.ofNat 64 288) (d := 0) (n := 16) (k := 288) (by decide)

variable {pLen : Nat} {s : State}

theorem StageABI.base_toNat (A : StageABI pLen s) : (frameBase s).toNat = s.sp.toNat - 272 := by
  have hl := A.stackLower
  have hb := s.sp.isLt
  unfold stack at hl
  simp only [frameBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem StageABI.used_sub (A : StageABI pLen s) : Region.Sub ⟨s.gpr .x0, usedBytes pLen⟩ (wsRegion s) := by
  have := A.size
  simpa only [off, BitVec.add_zero] using Offset.sub_base (s.gpr .x0) (d := 0) (n := usedBytes pLen) (by omega)

theorem StageABI.part_sub (A : StageABI pLen s) {d n : Nat} (h : d + n ≤ usedBytes pLen) :
    Region.Sub ⟨off (s.gpr .x0) d, n⟩ (wsRegion s) := fun x hx =>
  A.used_sub x (Offset.sub_base (s.gpr .x0) h x hx)

/-- The stage's working space and frame. -/
def arena (hb : Supported pLen) (A : StageABI pLen s) : Arena where
  B := s.gpr .x0
  F := frameBase s
  pLen := pLen
  width := hb
  arenaBound := by have := A.wsBound; have := A.size; omega
  frameArena := (A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega))).sub_right A.used_sub

theorem StageABI.geo (hb : Supported pLen) (A : StageABI pLen s) : VG.Proof.RsaOaep.AArch64.Geo (frameBase s) (hashBase s) where
  F16 := by rw [A.base_toNat]; have := A.stackLower; unfold stack at this; omega
  Fw := by rw [A.base_toNat]; have := s.sp.isLt; unfold frameBytes; omega
  Sw := by
    have ha := (arena hb A).arenaBound
    have hs := (arena hb A).small (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
    simp only [arena] at ha hs
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : VG.Impl.Dsa.Generation.Layout.hash < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt this]
    have := Nat.mod_le ((s.gpr .x0).toNat + VG.Impl.Dsa.Generation.Layout.hash) (2 ^ 64)
    omega
  dFS := (arena hb A).frame_part ((arena hb A).small (by decide) (by decide))
  dRS := (A.stackWs.sub_left (retR_sub s)).sub_right
    (A.part_sub ((arena hb A).small (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))
  dRF := (Offset.base_disjoint_below (frameBase s) (n := 16) (k := frameBytes) (by decide)).symm

end VG.Proof.Dsa.AArch64.Generator
