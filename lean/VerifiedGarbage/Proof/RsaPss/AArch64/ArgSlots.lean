module

public import VerifiedGarbage.Impl.RsaPss.AArch64
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PSS on AArch64: stack arguments into slots of the frame

The prologues load stack arguments (`arg r j`) and store them to slots of
the frame through `x16` (`argSlot_ok`), some zero-extended from 32 bits
first (`argSlotW_ok`); a slot written is read back (`rd_self`), and writes
to other slots keep it (`rd_ws`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_movw)

variable {is : List Instr} {Q : State → Prop}

/-- `arg r j; str r, [x16, #d]`: the stack argument `j` to the slot `d` of
the frame at `F` (`x16`). -/
theorem argSlot_ok {u : State} {r : Reg} {j d : Nat} {F : Addr} {v : BitVec 64}
    (hj : (frameBytes + 8 * j) % 8 = 0 ∧ frameBytes + 8 * j < 32768)
    (hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8)
    (hv : u.mem.readW (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 64 = v)
    (h16 : u.gpr .x16 = F) (hr : r ≠ .x16) (hd : d % 8 = 0 ∧ d < 4096 * 8)
    (hw : InRegions u.wr (F + BitVec.ofNat 64 d) 8)
    (k : ∀ u', Keep [r] u u' → u'.gpr r = v → u'.mem = u.mem.writeW (F + BitVec.ofNat 64 d) v →
      WP isa (.block is) u' Q) :
    WP isa (.block (arg r j :: .str .x r .x16 d :: is)) u Q := by
  unfold arg
  refine wp_ldrSp hj hin fun u₁ o₁ e₁ => wp_strx hd (by rw [o₁.get .x16 (by simpa using hr.symm), h16])
    (by rw [o₁.wr]; exact hw) fun u₂ m₂ => k u₂ ((o₁.keep.trans m₂.keep).mono fun _ h => by simpa using h) (by rw [m₂.gpr, e₁, hv])
      (by rw [m₂.mem, o₁.mem, e₁, hv])

/-- `arg r j; mov wr, wr; str r, [x16, #d]`: the stack argument `j`,
zero-extended from 32 bits, to the slot `d`. -/
theorem argSlotW_ok {u : State} {r : Reg} {j d : Nat} {F : Addr} {v : BitVec 64}
    (hj : (frameBytes + 8 * j) % 8 = 0 ∧ frameBytes + 8 * j < 32768)
    (hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8)
    (hv : u.mem.readW (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 64 = v)
    (h16 : u.gpr .x16 = F) (hr : r ≠ .x16) (hd : d % 8 = 0 ∧ d < 4096 * 8)
    (hw : InRegions u.wr (F + BitVec.ofNat 64 d) 8)
    (k : ∀ u', Keep [r] u u' → u'.mem = u.mem.writeW (F + BitVec.ofNat 64 d) ((v.setWidth 32).setWidth 64) →
      WP isa (.block is) u' Q) :
    WP isa (.block (arg r j :: .addImm .w r r 0 :: .str .x r .x16 d :: is)) u Q := by
  unfold arg
  refine wp_ldrSp hj hin fun u₁ o₁ e₁ => wp_movw fun u₂ o₂ e₂ =>
    wp_strx hd (by rw [o₂.get .x16 (by simpa using hr.symm), o₁.get .x16 (by simpa using hr.symm), h16])
    (by rw [o₂.wr, o₁.wr]; exact hw) fun u₃ m₃ => k u₃ ((o₁.keep.trans (o₂.keep.trans m₃.keep)).mono fun _ h => by simpa using h)
      (by rw [m₃.mem, o₂.mem, o₁.mem, e₂, e₁, hv])

theorem rd_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.writeW a v).readW a 64 = v :=
  Mem.readW_writeW_self64 m a v

theorem rd_ws {m : Mem} {F : Addr} {d e : Nat} {v : BitVec 64} (h : e + 8 ≤ d ∨ d + 8 ≤ e) (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) :
    (m.writeW (F + BitVec.ofNat 64 e) v).readW (F + BitVec.ofNat 64 d) 64 = m.readW (F + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.RsaPss.AArch64
