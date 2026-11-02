module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sbb
import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Loop
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: the final subtraction

`csub k` (`Impl/Weierstrass/RISCV64/GenWide.lean`): for the `k + 1` words of
`T` below `2 m`, `[o]` becomes `T mod m` (`csub_ok`): `T - m` over `N`
(`sbbRow_ok`), the mask `T_k - borrow`, then each word of `T` or of the
difference by the mask (`selRow_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_and)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- A mask: all zeros or all ones. -/
def IsMask (m : BitVec 64) : Prop := m = 0 ∨ m = BitVec.allOnes 64

/-- `x ⊕ ((e ⊕ x) ∧ m)`: `e` under the mask all ones, `x` under zero. -/
theorem sel_mask {x e m : BitVec 64} (hm : IsMask m) :
    x ^^^ ((e ^^^ x) &&& m) = if m = BitVec.allOnes 64 then e else x := by
  rcases hm with rfl | rfl
  · have : (0 : BitVec 64) ≠ BitVec.allOnes 64 := by decide
    simp only [this, ↓reduceIte]
    ext i hi
    simp
  · simp only [BitVec.and_allOnes, ↓reduceIte]
    rw [BitVec.xor_comm e x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem wp_xor' {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- After `j` words of the selection from `s0`. -/
structure SelInv (k : Nat) (b O : Addr) (sel : Bool) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [.t0, .a6] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) = if sel then dw s0.mem b (T k + 8 * i) else dw s0.mem b (N k + 8 * i)

/-- What the selection needs. -/
structure SelOk (k : Nat) (b O : Addr) (sel : Bool) (s0 : State) : Prop where
  ctx : Ctx b s0
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  t2 : s0.gpr .t2 = O
  oal : O.toNat % 8 = 0
  onw : O.toNat + 8 * k ≤ 2 ^ 64
  ow : ∀ i < k, InRegions s0.wr (O + BitVec.ofNat 64 (8 * i)) 8
  tdis : ∀ i < k, Region.Disjoint ⟨b + BitVec.ofNat 64 (T k + 8 * i), 8⟩ ⟨O, 8 * k⟩
  ndis : ∀ i < k, Region.Disjoint ⟨b + BitVec.ofNat 64 (N k + 8 * i), 8⟩ ⟨O, 8 * k⟩
  mask : IsMask (s0.gpr .a7)
  sel : (s0.gpr .a7 = BitVec.allOnes 64) = (sel = true)
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem disj_mono {r : Region} {O : Addr} {n m : Nat} (h : Region.Disjoint r ⟨O, m⟩) (hn : n ≤ m) :
    Region.Disjoint r ⟨O, n⟩ := fun x h₁ h₂ => h x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega)

set_option linter.unusedSimpArgs false in
theorem selStep_ok {k : Nat} {b O : Addr} {sel : Bool} {s0 : State} (hS : SelOk k b O sel s0) {j : Nat}
    (hj : j < k) {s : State} (h : SelInv k b O sel s0 j s) :
    WP isa (.block (selStep k j)) s (SelInv k b O sel s0 (j + 1)) := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := hS.k7; omega) hS.k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by have := hS.k7; omega) hS.k30
  have hcs : Ctx b s := ctx_of hS.ctx (h.gpr _ (by decide)) h.wr
  have hb := hS.nowrap
  have hon := hS.onw
  unfold selStep
  refine ld_ok hcs (by omega) (by omega) fun s1 u1 => ?_
  refine ld_ok (ctx_of hcs (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 =>
    wp_xor' fun s3 u3 => wp_and fun s4 u4 => wp_xor' fun s5 u5 => ?_
  refine wp_sd (by omega) (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide), u1.other _ (by decide), h.gpr _ (by decide), hS.t2]) (al8 hS.oal (by omega))
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr]; exact hS.ow j hj) fun s6 u6 => WP.block_nil ?_
  have hT0 : dw s.mem b (T k + 8 * j) = dw s0.mem b (T k + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact disj_mono (hS.tdis j hj) (by omega)
  have hN0 : dw s.mem b (N k + 8 * j) = dw s0.mem b (N k + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact disj_mono (hS.ndis j hj) (by omega)
  have a7 : s4.gpr .a7 = s0.gpr .a7 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide),
      h.gpr _ (by decide)]
  have v5 : s5.gpr .t0 = s1.gpr .t0 ^^^ ((s2.gpr .a6 ^^^ s1.gpr .t0) &&& s0.gpr .a7) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide), a7.symm,
      u4.other .a7 (by decide), u3.other .a7 (by decide)]
  rw [sel_mask hS.mask] at v5
  have hm6 : s6.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s5.gpr .t0) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr],
    by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u6.gpr, u5.other r hr.1, u4.other r hr.2, u3.other r hr.2, u2.other r hr.2, u1.other r hr.1,
      h.gpr r (by simp [hr.1, hr.2])]
  · rw [hm6]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        rw [show O = O + BitVec.ofNat 64 0 by simp]; exact Offset.sub O (Nat.le_refl _) (by omega)⟩
    · rw [show (⟨O, 8 * (j + 1)⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 8 * (j + 1)⟩ by simp]
      exact Offset.contains O (by omega) (by omega) (by omega)
  · rw [hm6]
    by_cases hij : i = j
    · subst hij
      rw [dw_write_self, v5]
      cases sel
      · have : ¬ s0.gpr .a7 = BitVec.allOnes 64 := by rw [hS.sel]; decide
        simp only [this, ↓reduceIte, u1.gpr, ← hN0]; rfl
      · have : s0.gpr .a7 = BitVec.allOnes 64 := by rw [hS.sel]
        simp only [this, ↓reduceIte, u2.gpr, u1.mem, ← hT0]; rfl
    · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.val i (by omega)

theorem selRow_ok {k : Nat} {b O : Addr} {sel : Bool} {s0 : State} (hS : SelOk k b O sel s0) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap (selStep k))) s0 (SelInv k b O sel s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (selRow_ok hS j (by omega)) fun s h => selStep_ok hS (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide
