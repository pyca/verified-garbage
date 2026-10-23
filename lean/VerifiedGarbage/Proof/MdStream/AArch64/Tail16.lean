module

public import VerifiedGarbage.Impl.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The one-shot digest's last 16 bytes, built in registers

What `Impl.MdStream.AArch64.OneShot.tail16` stores: the `r` bytes at `x27`
(`0 < r < 16`, in `x11`), then `0x80`, then zeros, as one 16-byte store at
`x12` (`tail16_run`), from a 16-byte load of the bytes that end with them.
-/

@[expose] public section

namespace VG.Proof.MdStream.AArch64.OneShot

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.MdStream.AArch64.OneShot

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_ldrq0 {t : VReg} {n : Reg} {a : Addr} (ha : s.gpr n = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : WP isa (.block is) (s.setV t (s.mem.read a 16)) Q) :
    WP isa (.block (.ldrq t n 0 :: is)) s Q :=
  WP.cons (by simp [exec, addr, ha, State.load, hin]) k

theorem wp_strq0 {t : VReg} {n : Reg} {a : Addr} (ha : s.gpr n = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', Mupd s s' (s.mem.write a 16 (s.v t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strq t n 0 :: is)) s Q :=
  WP.cons (s' := { s with mem := s.mem.write a 16 (s.v t) })
    (by simp [exec, addr, ha, State.store, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_vop {op : VOp} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x))
    (k : WP isa (.block is) (s.setV d x) Q) : WP isa (.block (.vop op :: is)) s Q :=
  WP.cons (by rw [Tbl.exec_vop', h]; rfl) k

end

theorem itp {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a :=
  by simp [h]

theorem itn {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp [h]

/-- The bytes of `idx16`: `16 + e`. -/
theorem idx16_byte : ∀ e < 16, vbyte idx16 e = BitVec.ofNat 8 (16 + e) := by decide

/-- `0x80` in the low doubleword of a zero vector: byte 0 is `0x80`, the others zeros. -/
theorem mark_byte : ∀ e < 16,
    vbyte (setLane 0 64 0 (BitVec.ofNat 64 0x80)) e = if e = 0 then 0x80 else 0 := by decide

/-- The table registers' byte `idx < 32`: `v0`'s, then `v1`'s. -/
theorem tableByte_v0 (v : VReg → BitVec 128) {idx : Nat} (h : idx < 32) :
    tableByte v .v0 idx = if idx < 16 then vbyte (v .v0) idx else vbyte (v .v1) (idx - 16) := by
  by_cases h16 : idx < 16
  · simp [tableByte, h16, Nat.div_eq_of_lt h16, Nat.mod_eq_of_lt h16, Nat.repeat]
  · have hq : idx / 16 = 1 := by omega
    simp [tableByte, h16, hq, Nat.repeat, VReg.succ, show idx % 16 = idx - 16 by omega]

/-- The 16 bytes ending `r` bytes past `p`, then byte `i + 16 - r`: byte `i` past `p`. -/
theorem src_add (p : Addr) {r i : Nat} (hr : r ≤ 16) (hi : i < 16) :
    p + BitVec.ofNat 64 r - BitVec.ofNat 64 16 + BitVec.ofNat 64 (i + 16 - r) = p + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  have := p.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sub_byte {e r : Nat} (he : e < 16) (hr : r < 16) :
    (BitVec.ofNat 8 (16 + e) - (BitVec.ofNat 64 r).setWidth 8).toNat = e + 16 - r := by
  simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `tail16`: the `r` bytes at `x27`, `0x80` and zeros, stored at `x12` with one 16-byte store. -/
theorem tail16_run {t : State} {r : Nat} (hr0 : 0 < r) (hr : r < 16) (h11 : t.gpr .x11 = BitVec.ofNat 64 r)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .x27 + BitVec.ofNat 64 r - BitVec.ofNat 64 16) 16)
    (hout : InRegions t.wr (t.gpr .x12) 16) :
    WP isa (.block tail16) t fun t' =>
      (∀ g, g ≠ .x13 → g ≠ .x9 → g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      t'.sp = t.sp ∧
      ∃ V : BitVec 128, t'.mem = t.mem.write (t.gpr .x12) 16 V ∧ ∀ i < 16, vbyte V i =
        if i < r then t.mem (t.gpr .x27 + BitVec.ofNat 64 i) else if i = r then 0x80 else 0 := by
  unfold tail16
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_add fun t₁ u₁ => wp_subImm (by decide) fun t₂ u₂ => wp_movz fun t₃ u₃ => ?_
  have g₃ : ∀ g, g ≠ .x13 → g ≠ .x9 → t₃.gpr g = t.gpr g := fun g h13 h9 => by
    rw [u₃.other _ h9, u₂.other _ h13, u₁.other _ h13]
  have a₃ : t₃.gpr .x13 = t.gpr .x27 + BitVec.ofNat 64 r - BitVec.ofNat 64 16 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, h11]
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : t₃.sp = t.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  generalize hL : t.mem.read (t.gpr .x27 + BitVec.ofNat 64 r - BitVec.ofNat 64 16) 16 = L
  refine wp_ldrq0 a₃ (by rw [rd₃, wr₃]; exact hin) ?_
  rw [m₃, hL]
  refine wp_vop rfl (wp_vop (d := .v1) (x := setLane 0 64 0 (t₃.gpr .x9))
    (by simp [VOp.eval, v_setV_self, gpr_setV]) (WP.block_nil ?_))
  generalize hA : ((t₃.setV .v0 L).setV .v1 0).setV .v1 (setLane 0 64 0 (t₃.gpr .x9)) = tA
  refine WP.mono (Tbl.const128_ok tA .v2 idx16) fun tB ⟨b2, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  have v0B : tB.v .v0 = L := by
    rw [bv _ (by decide), ← hA]; simp [v_setV_of_ne, v_setV_self]
  have v1B : tB.v .v1 = setLane 0 64 0 (BitVec.ofNat 64 0x80) := by
    rw [bv _ (by decide), ← hA, v_setV_self, u₃.gpr]; rfl
  have gB : ∀ g, g ≠ .x6 → g ≠ .x7 → tB.gpr g = t₃.gpr g := fun g h6 h7 => by
    rw [bg g h6 h7, ← hA, gpr_setV, gpr_setV, gpr_setV]
  have x11B : tB.gpr .x11 = BitVec.ofNat 64 r := by
    rw [gB _ (by decide) (by decide), g₃ _ (by decide) (by decide), h11]
  have x12B : tB.gpr .x12 = t.gpr .x12 := by rw [gB _ (by decide) (by decide), g₃ _ (by decide) (by decide)]
  have mB : tB.mem = t.mem := by rw [bm, ← hA, mem_setV, mem_setV, mem_setV, m₃]
  refine wp_vop rfl (wp_vop rfl (wp_vop (d := .v4) (x := ofVBytes fun i =>
      let idx := (vbyte (VArr.map2 .b16 (fun _ x y => x - y) idx16
        (ofVBytes fun _ => (tB.gpr .x11).setWidth 8)) i).toNat
      if idx < 16 * 2 then tableByte (((tB.setV .v3 (ofVBytes fun _ => (tB.gpr .x11).setWidth 8)).setV .v2
        (VArr.map2 .b16 (fun _ x y => x - y) idx16 (ofVBytes fun _ => (tB.gpr .x11).setWidth 8)))).v .v0 idx
      else if false then 0 else 0)
    (by simp [VOp.eval, v_setV_self, v_setV_of_ne, b2]) (wp_strq0 (a := t.gpr .x12) (by simp [gpr_setV, x12B])
      (by simp only [wr_setV]; rw [bwr, ← hA]; simpa [wr_setV, wr₃] using hout) fun t₅ m₅ => WP.block_nil ?_)))
  refine ⟨fun g h13 h9 h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [m₅.gpr, gpr_setV]; rw [gB g h6 h7, g₃ g h13 h9]
  · simp only [m₅.rd, rd_setV]; rw [brd, ← hA, rd_setV, rd_setV, rd_setV, rd₃]
  · simp only [m₅.wr, wr_setV]; rw [bwr, ← hA, wr_setV, wr_setV, wr_setV, wr₃]
  · simp only [m₅.sp, sp_setV]; rw [bsp, ← hA, sp_setV, sp_setV, sp_setV, sp₃]
  have em := m₅.mem
  simp only [mem_setV, mB] at em
  refine ⟨_, em, fun e he => ?_⟩
  simp only [v_setV_self]
  rw [vbyte_ofVBytes _ he]
  simp only [VArr.map2, vbyte_ofVBytes _ he, x11B]
  rw [idx16_byte e he, sub_byte he hr, itp (show e + 16 - r < 16 * 2 by omega), tableByte_v0 _ (by omega)]
  have e0 : ((tB.setV .v3 (ofVBytes fun x => BitVec.setWidth 8 (BitVec.ofNat 64 r))).setV .v2
      (ofVBytes fun e => vbyte idx16 e - vbyte (ofVBytes fun x => BitVec.setWidth 8 (BitVec.ofNat 64 r)) e)).v
      .v0 = L := by simp [v_setV_of_ne, v0B]
  have e1 : ((tB.setV .v3 (ofVBytes fun x => BitVec.setWidth 8 (BitVec.ofNat 64 r))).setV .v2
      (ofVBytes fun e => vbyte idx16 e - vbyte (ofVBytes fun x => BitVec.setWidth 8 (BitVec.ofNat 64 r)) e)).v
      .v1 = setLane 0 64 0 (BitVec.ofNat 64 0x80) := by simp [v_setV_of_ne, v1B]
  rw [e0, e1]
  by_cases her : e < r
  · rw [itp (show e + 16 - r < 16 by omega), itp her, ← hL, vbyte,
      Mem.extractLsb'_read _ _ (show e + 16 - r < 16 by omega), src_add _ (by omega) he]
  · rw [itn (show ¬ e + 16 - r < 16 by omega), itn her, mark_byte _ (by omega)]
    by_cases h : e = r
    · rw [itp (show e + 16 - r - 16 = 0 by omega), itp h]
    · rw [itn (show ¬ e + 16 - r - 16 = 0 by omega), itn h]

end VG.Proof.MdStream.AArch64.OneShot
