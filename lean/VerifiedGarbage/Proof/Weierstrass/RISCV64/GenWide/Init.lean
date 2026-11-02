module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Loop
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: the modulus's words and `T = 0`

`fillN k m` (`Impl/Weierstrass/RISCV64/GenWide.lean`) stores the `k` words of
`m` at `N` (`fillN_ok`), and `mulInit k m` the `k + 1` zero words of `T` and
`m'` into `t6` (`mulInit_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Impl.Words.RISCV64 (li64)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- `li64 d tmp v`. -/
theorem wp_li64 {is : List Instr} {s : State} {Q : State → Prop} {d tmp : Reg} (hdt : d ≠ tmp) (v : BitVec 64)
    (k : ∀ s', s'.gpr d = v → Keeps [d, tmp] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (li64 d tmp v ++ is)) s Q :=
  WP.block_append (WP.mono (ByteLoad.li64_ok hdt v) fun s' h => by
    subst h
    exact k _ (RegUpd.gpr_write_self _ _ _)
      (((Keeps.refl [d, tmp] s).write _ (by simp)).write _ (by simp)))

/-- A number's `n` words. -/
theorem colsV_wordOf (m : Nat) : ∀ n, colsV (fun j => (wordOf m j).toNat) n = m % (2 ^ 64) ^ n
  | 0 => by simp [colsV, Nat.mod_one]
  | n + 1 => by
    have e : ((2 : Nat) ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 := Nat.pow_succ ..
    rw [colsV_succ, colsV_wordOf m n, e, Nat.mod_mul]
    simp only [wordOf, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- After `j` words of `m`. -/
structure FillInv (k : Nat) (b : Addr) (m : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [.a6, .a7] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (N k), 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem b (N k + 8 * i) = (wordOf m i).toNat

theorem fill_ok {k : Nat} {b : Addr} {m : Nat} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap fun j =>
      li64 .a6 .a7 (wordOf m j) ++ [.store .d .a6 .a3 (N k + 8 * j)])) s0 (FillInv k b m s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨hNT, n8, ntop⟩ := N_facts k hk hk'
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (fill_ok hc hk hk' j (by omega)) fun s h => ?_)
    refine wp_li64 (by decide) _ fun s1 e1 k1 => ?_
    have hc1 : Ctx b s1 := ctx_of hc (by rw [k1.1 _ (by decide), h.gpr _ (by decide)]) (by rw [k1.2.2.2.1, h.wr])
    refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => WP.block_nil ?_
    have hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (N k + 8 * j)) (wordOf m j) := by
      rw [u2.mem, k1.2.1, e1]
    refine ⟨fun r hr => by rw [u2.gpr, k1.1 r hr, h.gpr r hr], by rw [u2.rd, k1.2.2.1, h.rd],
      by rw [u2.wr, k1.2.2.2.1, h.wr], by rw [u2.sp, k1.2.2.2.2, h.sp], ?_, fun i hi => ?_⟩
    · rw [hm2]
      refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by have := hc.al; omega)
    · rw [hm2]
      by_cases hij : i = j
      · subst hij; rw [dw_write_self]
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i (by omega)

/-- `m`'s words at `N`. -/
theorem fillN_ok {k : Nat} {b : Addr} {m : Nat} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30)
    (hm : m < 2 ^ (64 * k)) {is : List Instr} {Q : State → Prop}
    (h : ∀ s, (∀ r, r ∉ [.a6, .a7] → s.gpr r = s0.gpr r) → s.rd = s0.rd → s.wr = s0.wr → s.sp = s0.sp →
      Frame [⟨b + BitVec.ofNat 64 (N k), 8 * k⟩] s0.mem s.mem → nv k s.mem b = m →
      (∀ i < k, dw s.mem b (N k + 8 * i) = (wordOf m i).toNat) → WP isa (.block is) s Q) :
    WP isa (.block (fillN k m ++ is)) s0 Q := by
  refine WP.block_append (WP.mono (fill_ok hc hk hk' k (Nat.le_refl _)) fun s hs => ?_)
  refine h s hs.gpr hs.rd hs.wr hs.sp hs.frame ?_ hs.val
  rw [show nv k s.mem b = colsV (fun j => (wordOf m j).toNat) k from colsV_congr fun i hi => hs.val i hi,
    colsV_wordOf, Nat.mod_eq_of_lt (by rw [← Nat.pow_mul]; exact hm)]

/-- After `j` zero words of `T`. -/
structure ZeroInv (k : Nat) (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem b (T k + 8 * i) = 0

theorem zero_ok {k : Nat} {b : Addr} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30)
    (h7 : s0.gpr .a7 = 0) :
    ∀ j ≤ k + 1, WP isa (.block ((List.range j).map fun j => .store .d .a7 .a3 (T k + 8 * j))) s0
      (ZeroInv k b s0 j)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨t8, ttop⟩ := T_facts k hk hk'
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (zero_ok hc hk hk' h7 j (by omega)) fun s h => ?_)
    have hcs : Ctx b s := ctx_of hc (by rw [h.gpr]) h.wr
    refine sd_ok hcs (by omega) (by omega) fun s1 u1 => WP.block_nil ?_
    have hm1 : s1.mem = s.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * j)) (0 : BitVec 64) := by rw [u1.mem, h.gpr, h7]
    refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], ?_,
      fun i hi => ?_⟩
    · rw [hm1]
      refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by have := hc.al; omega)
    · rw [hm1]
      by_cases hij : i = j
      · subst hij; rw [dw_write_self]; rfl
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i (by omega)

/-- `T = 0` and `m'` in `t6`. -/
theorem mulInit_ok {k : Nat} {b : Addr} {m : Nat} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30) :
    WP isa (.block (mulInit k m)) s0 fun s =>
      (∀ r, r ∉ [.a7, .t6] → s.gpr r = s0.gpr r) ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧ s.sp = s0.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s.mem ∧ tv k s.mem b (k + 1) = 0 ∧
      s.gpr .t6 = BitVec.ofNat 64 (negInv m) := by
  obtain ⟨t8, ttop⟩ := T_facts k hk hk'
  unfold mulInit
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  refine WP.block_append (WP.mono (zero_ok hc1 hk hk' (by rw [u1.gpr]; rfl) (k + 1) (Nat.le_refl _))
    fun s2 h2 => ?_)
  refine WP.mono (ByteLoad.li64_ok (s := s2) (d := .t6) (tmp := .a7) (by decide) _) fun s3 h3 => ?_
  subst h3
  refine ⟨fun r hr => ?_, h2.rd.trans u1.rd, h2.wr.trans u1.wr, h2.sp.trans u1.sp, ?_, ?_,
    RegUpd.gpr_write_self _ _ _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ hr.2, RegUpd.gpr_write_of_ne _ _ hr.1, h2.gpr, u1.other r hr.1]
  · show Frame _ s0.mem s2.mem
    rw [← u1.mem]
    exact h2.frame.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
  · show colsV (fun i => dw s2.mem b (T k + 8 * i)) (k + 1) = 0
    rw [colsV_congr (g := fun _ => 0) fun i hi => h2.val i hi]
    clear h2; induction (k + 1) with
    | zero => rfl
    | succ n ih => simp [colsV, ih]

end VG.Proof.Weierstrass.RISCV64.GenWide
