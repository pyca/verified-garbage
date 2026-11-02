module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Words
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: a row of multiply-accumulate steps

`macRow k xb xo δ n` (`Impl/Weierstrass/RISCV64/GenWide.lean`) from a state
with `a3 = b` (`Ctx`): word `j < n` of `T` becomes word `j` of
`T[δ …] + x · a4 + a5`, for the words `x` at `X + xo + 8 δ …` (`X` in `xb`),
with the carry out in `a5` (`row_ok`). Only the first `n` words of `T` are
written.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- The registers a step writes. -/
abbrev clobS : List Reg := [.t0, .a1, .t3, .a5, .a6, .a7]

/-- After `j` steps of a row from `s0`. -/
structure RowInv (k : Nat) (b X : Addr) (xo δ : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * j⟩] s0.mem s.mem
  val : colsV (fun i => dw s.mem b (T k + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem b (T k + 8 * (i + δ)) + dw s0.mem X (xo + 8 * (i + δ)) * (s0.gpr .a4).toNat) j +
      (s0.gpr .a5).toNat

theorem RowInv.zero {k : Nat} {b X : Addr} {xo δ : Nat} (s0 : State) : RowInv k b X xo δ s0 0 s0 :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [colsV]⟩

theorem colsV_congr {f g : Nat → Nat} : ∀ {n}, (∀ i < n, f i = g i) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [colsV]; rw [colsV_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem ctx_of {b : Addr} {s0 s : State} (hc : Ctx b s0) (h3 : s.gpr .a3 = s0.gpr .a3) (hw : s.wr = s0.wr) :
    Ctx b s :=
  ⟨h3.trans hc.a3, hc.al, by rw [hw]; exact hc.wr⟩

/-- What a row needs of its operands. -/
structure RowOk (k : Nat) (b X : Addr) (xb : Reg) (xo δ n : Nat) (s0 : State) : Prop where
  ctx : Ctx b s0
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  hx : s0.gpr xb = X
  hxb : xb ∉ clobS
  hxo : ∀ i < n, xo + 8 * (i + δ) < 2048
  xal : ∀ i < n, (X + BitVec.ofNat 64 (xo + 8 * (i + δ))).toNat % 8 = 0
  xin : ∀ i < n, InRegions (s0.rd ++ s0.wr) (X + BitVec.ofNat 64 (xo + 8 * (i + δ))) 8
  xdis : ∀ i < n, ∀ j ≤ n,
    Region.Disjoint ⟨X + BitVec.ofNat 64 (xo + 8 * (i + δ)), 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * j⟩
  top : T k + 8 * (n + δ) ≤ 2048
  t8 : T k % 8 = 0

set_option linter.unusedSimpArgs false in
/-- Step `j` of a row. -/
theorem rowStep_ok {k : Nat} {b X : Addr} {xb : Reg} {xo δ n : Nat} {s0 : State} (hR : RowOk k b X xb xo δ n s0)
    {j : Nat} (hj : j < n) {s : State} (h : RowInv k b X xo δ s0 j s) :
    WP isa (.block (macStep xb (xo + 8 * (j + δ)) (T k + 8 * (j + δ)) (T k + 8 * j))) s
      (RowInv k b X xo δ s0 (j + 1)) := by
  have hc : Ctx b s := ctx_of hR.ctx (h.gpr _ (by decide)) h.wr
  have hT := hR.top
  have ht8 := hR.t8
  have hxo := hR.hxo j hj
  have hb := hR.nowrap
  unfold macStep
  -- The word `x`.
  refine wp_ld (by omega) (by rw [h.gpr _ hR.hxb, hR.hx]) (hR.xal j hj)
    (by rw [h.rd, h.wr]; exact hR.xin j hj) fun s1 u1 => ?_
  refine ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 => ?_
  show WP isa (.block ([.mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4, .add .t0 .t0 .a7, .sltu .t3 .t0 .a7,
    .add .a1 .a1 .t3, .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3] ++
    [Instr.store .d .t0 .a3 (T k + 8 * j)])) s2 _
  refine WP.block_append (WP.mono mac_ok fun s3 ⟨e3, k3⟩ => ?_)
  have hc3 : Ctx b s3 := ctx_of hc (by rw [k3.1 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [k3.2.2.2.1, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  -- Facts.
  have m3 : s3.mem = s.mem := by rw [k3.2.1, u2.mem, u1.mem]
  have g3 : ∀ r, r ∉ clobS → s3.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k3.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), u2.other r hr.2.2.2.2.2,
      u1.other r hr.2.2.2.2.1]
  have a6 : s2.gpr .a6 = s.mem.readW (X + BitVec.ofNat 64 (xo + 8 * (j + δ))) 64 := by
    rw [u2.other _ (by decide), u1.gpr]
  have a7 : s2.gpr .a7 = s.mem.readW (b + BitVec.ofNat 64 (T k + 8 * (j + δ))) 64 := by
    rw [u2.gpr, u1.mem]
  have a4 : s2.gpr .a4 = s.gpr .a4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have a5 : s2.gpr .a5 = s.gpr .a5 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, m3]
  -- The words read are those of `s0`.
  have hX0 : dw s.mem X (xo + 8 * (j + δ)) = dw s0.mem X (xo + 8 * (j + δ)) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hR.xdis j hj j (by omega)
  have hT0 : dw s.mem b (T k + 8 * (j + δ)) = dw s0.mem b (T k + 8 * (j + δ)) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  refine ⟨fun r hr => by rw [u4.gpr, g3 r hr, h.gpr r hr], by rw [u4.rd, k3.2.2.1, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, k3.2.2.2.1, u2.wr, u1.wr, h.wr], by rw [u4.sp, k3.2.2.2.2, u2.sp, u1.sp, h.sp], ?_, ?_⟩
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s4.mem b (T k + 8 * i)) j = colsV (fun i => dw s.mem b (T k + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have e3' : (s3.gpr .t0).toNat + 2 ^ 64 * (s3.gpr .a5).toNat =
        dw s0.mem X (xo + 8 * (j + δ)) * (s0.gpr .a4).toNat + dw s0.mem b (T k + 8 * (j + δ)) +
          (s.gpr .a5).toNat := by
      rw [e3, a6, a7, a4, a5, ← hX0, ← hT0, h.gpr _ (by decide)]; rfl
    show colsV (fun i => dw s4.mem b (T k + 8 * i)) j + (2 ^ 64) ^ j * dw s4.mem b (T k + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat =
      colsV (fun i => dw s0.mem b (T k + 8 * (i + δ)) + dw s0.mem X (xo + 8 * (i + δ)) * (s0.gpr .a4).toNat) j +
        (2 ^ 64) ^ j * (dw s0.mem b (T k + 8 * (j + δ)) + dw s0.mem X (xo + 8 * (j + δ)) * (s0.gpr .a4).toNat) +
        (s0.gpr .a5).toNat
    rw [hcw, hm4, dw_write_self, u4.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun i => dw s.mem b (T k + 8 * i)) j = C at *
    have key : E * (s3.gpr .t0).toNat + E * 2 ^ 64 * (s3.gpr .a5).toNat =
        E * (s.gpr .a5).toNat + E * (dw s0.mem b (T k + 8 * (j + δ)) +
          dw s0.mem X (xo + 8 * (j + δ)) * (s0.gpr .a4).toNat) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e3']; congr 1; omega
    omega

/-- The row. -/
theorem row_ok {k : Nat} {b X : Addr} {xb : Reg} {xo δ n : Nat} {s0 : State}
    (hR : RowOk k b X xb xo δ n s0) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap fun i =>
      macStep xb (xo + 8 * (i + δ)) (T k + 8 * (i + δ)) (T k + 8 * i))) s0 (RowInv k b X xo δ s0 j)
  | 0, _ => WP.block_nil (RowInv.zero s0)
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (row_ok hR j (by omega)) fun s h => rowStep_ok hR (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide
