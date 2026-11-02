module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sbb
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: a sum with carries

`n` steps of `adcStep mk xb xo yb yo db d` (`Impl/Weierstrass/RISCV64/GenWide.lean`),
for `mk` nothing or the mask `a2` (`mkOf`): the words at `Dst + d` (`Dst` in
`db`) become those of `X + Y + a5`, for the words `X` at `xb + xo` and the
words at `yb + yo`, under the mask if `mk` takes it, with the carry out in `a5`
(`adcRow_ok`). Only those `n` words are written.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_write_self dw_write_other dw_frame al8 colsV)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok)

/-- Nothing, or the mask `a2` on `a7`. -/
def mkOf (msk : Bool) : List Instr := if msk then [.logic .and .a7 .a7 .a2] else []

/-- A word of the second operand, under the mask `M` or not. -/
def yw (msk : Bool) (M : BitVec 64) (y : Nat) : Nat := if msk then (BitVec.ofNat 64 y &&& M).toNat else y

theorem yw_lt (msk : Bool) (M : BitVec 64) (y : Nat) (hy : y < 2 ^ 64) : yw msk M y < 2 ^ 64 := by
  unfold yw; split
  · exact BitVec.isLt _
  · exact hy

/-- The destination of a row: `n` words at `Dst + d + 8 j`, through `db`. -/
structure DstOk (Dst : Addr) (db : Reg) (d n : Nat) (s0 : State) : Prop where
  hd : s0.gpr db = Dst
  hdb : db ∉ clobB
  al : Dst.toNat % 8 = 0
  d8 : d % 8 = 0
  hdo : d + 8 * n ≤ 2048
  nowrap : Dst.toNat + d + 8 * n ≤ 2 ^ 64
  w : ∀ j < n, InRegions s0.wr (Dst + BitVec.ofNat 64 (d + 8 * j)) 8

/-- After `j` steps of a sum from `s0`. -/
structure AdcInv (Dst X Y : Addr) (xo yo d : Nat) (msk : Bool) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobB → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨Dst + BitVec.ofNat 64 d, 8 * j⟩] s0.mem s.mem
  cy : (s.gpr .a5).toNat ≤ 1
  val : colsV (fun i => dw s.mem Dst (d + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem X (xo + 8 * i)) j + colsV (fun i => yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * i))) j +
      (s0.gpr .a5).toNat

/-- `mk`: `a7` under the mask or not, nothing else written. -/
theorem wp_mk {msk : Bool} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (s'.gpr .a7).toNat = yw msk (s.gpr .a2) (s.gpr .a7).toNat → (∀ r, r ≠ .a7 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (mkOf msk ++ is)) s Q := by
  cases msk
  · exact k s (by simp [yw]) (fun _ _ => rfl) rfl rfl rfl rfl
  · refine WP.cons exec_logic ?_
    refine k _ ?_ (fun r hr => ?_) rfl rfl rfl rfl
    · simp only [yw, ↓reduceIte, RegUpd.gpr_write, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [RegUpd.gpr_write, hr, ite_false]

set_option linter.unusedSimpArgs false in
/-- Step `j` of a sum. -/
theorem adcStep_ok {Dst X Y : Addr} {xb yb db : Reg} {xo yo d n : Nat} {msk : Bool} {s0 : State}
    (hD : DstOk Dst db d n s0) (hX : OpOk Dst X xb xo d n s0) (hY : OpOk Dst Y yb yo d n s0)
    {j : Nat} (hj : j < n) {s : State}
    (h : AdcInv Dst X Y xo yo d msk s0 j s) :
    WP isa (.block (adcStep (mkOf msk) xb xo yb yo db d j)) s (AdcInv Dst X Y xo yo d msk s0 (j + 1)) := by
  have hxo := hX.hxo j hj
  have hyo := hY.hxo j hj
  have hdo := hD.hdo
  have hnw := hD.nowrap
  unfold adcStep
  rw [List.append_assoc, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ld (by omega) (by rw [h.gpr _ hX.hxb, hX.hx]) (hX.al j hj)
    (by rw [h.rd, h.wr]; exact hX.inR j hj) fun s1 u1 => ?_
  refine wp_ld (by omega) (by rw [u1.other _ (fun e => hY.hxb (by rw [e]; decide)), h.gpr _ hY.hxb, hY.hx])
    (hY.al j hj) (by rw [u1.rd, u1.wr, h.rd, h.wr]; exact hY.inR j hj) fun s2 u2 => ?_
  refine wp_mk fun s3 e3 g3 m3 rd3 wr3 sp3 => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .t0) (x := .a6) (y := .a7) (c := .a5) (u := .t3))
    fun s4 ⟨e4, k4⟩ => ?_)
  have hk4 : db ∉ [Reg.t0, Reg.t3, Reg.a5] := fun e => hD.hdb (by
    revert e; simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (h | h | h) <;> simp [h])
  refine wp_sd (by omega) (by rw [k4.1 _ hk4, g3 _ (fun e => hD.hdb (by rw [e]; decide)),
      u2.other _ (fun e => hD.hdb (by rw [e]; decide)), u1.other _ (fun e => hD.hdb (by rw [e]; decide)),
      h.gpr _ hD.hdb, hD.hd]) (al8 hD.al (by have := hD.d8; omega))
    (by rw [k4.2.2.2.1, wr3, u2.wr, u1.wr, h.wr]; exact hD.w j hj) fun s5 u5 => WP.block_nil ?_
  have a5 : s3.gpr .a5 = s.gpr .a5 := by rw [g3 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have e4v := e4 (by rw [a5]; exact h.cy)
  have hX0 : dw s.mem X (xo + 8 * j) = dw s0.mem X (xo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hX.dis j hj
  have hY0 : dw s.mem Y (yo + 8 * j) = dw s0.mem Y (yo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hY.dis j hj
  have a6 : (s3.gpr .a6).toNat = dw s0.mem X (xo + 8 * j) := by
    rw [g3 _ (by decide), u2.other _ (by decide), u1.gpr, ← hX0]; rfl
  have a7 : (s3.gpr .a7).toNat = yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * j)) := by
    rw [e3, u2.other _ (by decide), u1.other _ (by decide), h.gpr _ (by decide), u2.gpr, u1.mem, ← hY0]; rfl
  have hm5 : s5.mem = s.mem.writeW (Dst + BitVec.ofNat 64 (d + 8 * j)) (s4.gpr .t0) := by
    rw [u5.mem, k4.2.1, m3, u2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u5.rd, k4.2.2.1, rd3, u2.rd, u1.rd, h.rd],
    by rw [u5.wr, k4.2.2.2.1, wr3, u2.wr, u1.wr, h.wr], by rw [u5.sp, k4.2.2.2.2, sp3, u2.sp, u1.sp, h.sp], ?_,
    by
      rw [u5.gpr]
      have := (s3.gpr .a6).isLt; have := (s3.gpr .a7).isLt; have := h.cy
      rw [← a5] at this
      omega, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.gpr, k4.1 r (by simp [hr.1, hr.2.1, hr.2.2.2.1]), g3 r hr.2.2.2.2.2, u2.other r hr.2.2.2.2.2,
      u1.other r hr.2.2.2.2.1, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub Dst (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains Dst (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s5.mem Dst (d + 8 * i)) j = colsV (fun i => dw s.mem Dst (d + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm5, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rw [a6, a7, a5] at e4v
    show colsV (fun i => dw s5.mem Dst (d + 8 * i)) j + (2 ^ 64) ^ j * dw s5.mem Dst (d + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s5.gpr .a5).toNat =
      colsV (fun i => dw s0.mem X (xo + 8 * i)) j + (2 ^ 64) ^ j * dw s0.mem X (xo + 8 * j) +
        (colsV (fun i => yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * i))) j +
          (2 ^ 64) ^ j * yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * j))) + (s0.gpr .a5).toNat
    rw [hcw, hm5, dw_write_self, u5.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s4.gpr .t0).toNat + E * 2 ^ 64 * (s4.gpr .a5).toNat =
        E * dw s0.mem X (xo + 8 * j) + E * yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * j)) + E * (s.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e4v]
    omega

/-- The sum. -/
theorem adcRow_ok {Dst X Y : Addr} {xb yb db : Reg} {xo yo d n : Nat} {msk : Bool} {s0 : State}
    (hD : DstOk Dst db d n s0) (hX : OpOk Dst X xb xo d n s0) (hY : OpOk Dst Y yb yo d n s0)
    (hc0 : (s0.gpr .a5).toNat ≤ 1) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap (adcStep (mkOf msk) xb xo yb yo db d))) s0
      (AdcInv Dst X Y xo yo d msk s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, hc0, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (adcRow_ok hD hX hY hc0 j (by omega)) fun s h =>
      adcStep_ok hD hX hY (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide
