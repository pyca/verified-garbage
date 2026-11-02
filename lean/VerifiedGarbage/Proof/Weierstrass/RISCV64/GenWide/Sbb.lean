module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Round
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: a difference with borrows

`n` steps of `sbbStep xb xo yb yo d` (`Impl/Weierstrass/RISCV64/GenWide.lean`)
from a state with `a3 = b` (`Ctx`): the words at `b + d` become those of
`X - Y - a5` for the words `X` at `xb + xo` and `Y` at `yb + yo`, with the
borrow out in `a5` (`sbbRow_ok`). Only those `n` words are written.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)
open VG.Proof.Weierstrass.RISCV64.P256Field (sbb_ok)

/-- The registers a step writes. -/
abbrev clobB : List Reg := [.t0, .t3, .a1, .a5, .a6, .a7]

/-- An operand of a row: its words at `X + xo + 8 j`, through `xb`. -/
structure OpOk (b X : Addr) (xb : Reg) (xo d n : Nat) (s0 : State) : Prop where
  hx : s0.gpr xb = X
  hxb : xb ∉ clobB
  hxo : ∀ j < n, xo + 8 * j < 2048
  al : ∀ j < n, (X + BitVec.ofNat 64 (xo + 8 * j)).toNat % 8 = 0
  inR : ∀ j < n, InRegions (s0.rd ++ s0.wr) (X + BitVec.ofNat 64 (xo + 8 * j)) 8
  dis : ∀ j < n, Region.Disjoint ⟨X + BitVec.ofNat 64 (xo + 8 * j), 8⟩ ⟨b + BitVec.ofNat 64 d, 8 * j⟩

/-- After `j` steps of a difference from `s0`. -/
structure SbbInv (b X Y : Addr) (xo yo d : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobB → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 d, 8 * j⟩] s0.mem s.mem
  cy : (s.gpr .a5).toNat ≤ 1
  val : colsV (fun i => dw s.mem b (d + 8 * i)) j + colsV (fun i => dw s0.mem Y (yo + 8 * i)) j +
      (s0.gpr .a5).toNat = colsV (fun i => dw s0.mem X (xo + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat

set_option linter.unusedSimpArgs false in
/-- Step `j` of a difference. -/
theorem sbbStep_ok {b X Y : Addr} {xb yb : Reg} {xo yo d n : Nat} {s0 : State} (hc : Ctx b s0)
    (hd : d + 8 * n ≤ 2048) (hd8 : d % 8 = 0)
    (hX : OpOk b X xb xo d n s0) (hY : OpOk b Y yb yo d n s0) {j : Nat} (hj : j < n) {s : State}
    (h : SbbInv b X Y xo yo d s0 j s) :
    WP isa (.block (sbbStep xb xo yb yo d j)) s (SbbInv b X Y xo yo d s0 (j + 1)) := by
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  have hxo := hX.hxo j hj
  have hyo := hY.hxo j hj
  unfold sbbStep
  refine wp_ld (by omega) (by rw [h.gpr _ hX.hxb, hX.hx]) (hX.al j hj)
    (by rw [h.rd, h.wr]; exact hX.inR j hj) fun s1 u1 => ?_
  refine wp_ld (by omega) (by rw [u1.other _ (fun e => hY.hxb (by rw [e]; decide)), h.gpr _ hY.hxb, hY.hx])
    (hY.al j hj) (by rw [u1.rd, u1.wr, h.rd, h.wr]; exact hY.inR j hj) fun s2 u2 => ?_
  show WP isa (.block ([.sltu .t3 .a7 .a6, .sub .t0 .a7 .a6, .sltu .a1 .t0 .a5, .sub .t0 .t0 .a5, .add .a5 .t3 .a1] ++
    [Instr.store .d .t0 .a3 (d + 8 * j)])) s2 _
  refine WP.block_append (WP.mono (sbb_ok (d := .t0) (x := .a7) (y := .a6) (c := .a5) (u := .t3) (v := .a1))
    fun s3 ⟨e3, k3⟩ => ?_)
  have hc3 : Ctx b s3 := ctx_of hcs (by rw [k3.1 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [k3.2.2.2.1, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have a5 : s2.gpr .a5 = s.gpr .a5 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain ⟨e3v, e3c⟩ := e3 (by rw [a5]; exact h.cy)
  have hX0 : dw s.mem X (xo + 8 * j) = dw s0.mem X (xo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hX.dis j hj
  have hY0 : dw s.mem Y (yo + 8 * j) = dw s0.mem Y (yo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hY.dis j hj
  have a7 : (s2.gpr .a7).toNat = dw s0.mem X (xo + 8 * j) := by
    rw [u2.other _ (by decide), u1.gpr, ← hX0]; rfl
  have a6 : (s2.gpr .a6).toNat = dw s0.mem Y (yo + 8 * j) := by
    rw [u2.gpr, u1.mem, ← hY0]; rfl
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (d + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, k3.2.1, u2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u4.rd, k3.2.2.1, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, k3.2.2.2.1, u2.wr, u1.wr, h.wr], by rw [u4.sp, k3.2.2.2.2, u2.sp, u1.sp, h.sp], ?_,
    by rw [u4.gpr]; exact e3c, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.gpr, k3.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), u2.other r hr.2.2.2.2.1,
      u1.other r hr.2.2.2.2.2, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s4.mem b (d + 8 * i)) j = colsV (fun i => dw s.mem b (d + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rw [a7, a6, a5] at e3v
    show colsV (fun i => dw s4.mem b (d + 8 * i)) j + (2 ^ 64) ^ j * dw s4.mem b (d + 8 * j) +
        (colsV (fun i => dw s0.mem Y (yo + 8 * i)) j + (2 ^ 64) ^ j * dw s0.mem Y (yo + 8 * j)) +
        (s0.gpr .a5).toNat =
      colsV (fun i => dw s0.mem X (xo + 8 * i)) j + (2 ^ 64) ^ j * dw s0.mem X (xo + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat
    rw [hcw, hm4, dw_write_self, u4.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s3.gpr .t0).toNat + E * dw s0.mem Y (yo + 8 * j) + E * (s.gpr .a5).toNat =
        E * dw s0.mem X (xo + 8 * j) + E * 2 ^ 64 * (s3.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e3v]
    omega

/-- The difference. -/
theorem sbbRow_ok {b X Y : Addr} {xb yb : Reg} {xo yo d n : Nat} {s0 : State} (hc : Ctx b s0)
    (hd : d + 8 * n ≤ 2048) (hd8 : d % 8 = 0)
    (hX : OpOk b X xb xo d n s0) (hY : OpOk b Y yb yo d n s0) (hc0 : (s0.gpr .a5).toNat ≤ 1) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap (sbbStep xb xo yb yo d))) s0 (SbbInv b X Y xo yo d s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, hc0, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (sbbRow_ok hc hd hd8 hX hY hc0 j (by omega)) fun s h =>
      sbbStep_ok hc hd hd8 hX hY (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide
