module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
public import VerifiedGarbage.Proof.Ed25519.BaseTable
public import VerifiedGarbage.Proof.Ed25519.DblPoint
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyPoints
public import VerifiedGarbage.Proof.Ed25519.Group.Double
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Defs
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointAccumulate
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ed25519.RISCV64.WindowDigit
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointMul
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic

/-!
# Verification's windows on RISC-V

`[k]A - [S]B` by 4-bit windows (`Impl/Ed25519/RISCV64/VerifyWindow.lean`):
each window doubles the sum four times and adds the cached `[a]A` of `k`'s
digit `a` from the table at `TA`, then, in the low 64 windows, the cached
`-[b]B` of `S`'s digit `b` from the static (`windowStep_ok`); after the
`W` windows the sum represents `[k]A - [S]B` (`windows_ok`), which compared
with `-R` is the equation (`rhs_ok`, which is `RhsOk`). Before them: the
field programs of the doubling and the cached addition, the reads of a
cached point from a table entry or the static, and the table of `A`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

/-!
## The windows' field programs on RISC-V

As on AArch64 (`Proof/Ed25519/AArch64/WindowStep.lean`): the doubling's
program is `dblPoint` (`dblOps_eval`), the cached addition's is the
specification's `pointAdd` of the point and the one cached (`ring`), and
`cacheOps` is `cache` of the point saved in slots 17–20. Each keeps the
slots it does not write: the doubling and the addition slots 16 and up, and
the doubling the cached point in slots 4–7.
-/

section

open VG VG.Impl.Ed25519.RISCV64
open Fin.CommRing

theorem dblOps_eval (e : Env) : point (evalOps dblOps e) 0 1 2 3 = dblPoint (point e 0 1 2 3) := rfl

/-- Slots `ops` does not write keep their elements. -/
theorem evalOps_keep (ops : List FieldOp) (e : Env) (i : Slot)
    (h : ∀ op ∈ ops, match op with
      | .copy o _ | .const o _ | .mul o _ _ | .mulc o _ _ | .add o _ _ | .sub o _ _ => o ≠ i) :
    evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    simp only [evalOps, List.foldl_cons] at ih ⊢
    rw [ih _ fun op' h' => h op' (List.mem_cons_of_mem _ h')]
    have hop := h op List.mem_cons_self
    cases op <;> simp only [evalOp] at hop ⊢ <;> exact Function.update_of_ne (Ne.symm hop) _ _

theorem dblOps_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ 15 ≤ i.val) :
    evalOps dblOps e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [dblOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

def addCachedResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 * e 7
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddCached_formula (e : Env) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = addCachedResult e := rfl

theorem pointAddCached_eval (e : Env) (q : Spec.Ed25519.Point) (hq : point e 4 5 6 7 = cache q) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : e 7 = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  rw [pointAddCached_formula]
  simp only [addCachedResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, h7]
  congr 1 <;> ring

theorem pointAddCached_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val) :
    evalOps pointAddCachedOps e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [pointAddCachedOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

theorem cacheOps_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ i.val = 16 ∨ i.val = 21) :
    evalOps (savePointOps ++ cacheOps) e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [savePointOps, cacheOps, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

/-- The point saved in slots 17–20, then cached into slots 0–3. -/
theorem cacheOps_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 = cache (point e 0 1 2 3) ∧
      point (evalOps (savePointOps ++ cacheOps) e) 17 18 19 20 = point e 0 1 2 3 := by
  refine ⟨?_, rfl⟩
  simp only [evalOps, savePointOps, cacheOps, List.cons_append, List.nil_append, List.foldl_cons,
    List.foldl_nil, evalOp, point, cache]
  simp [hd]
  constructor <;> ring

end

/-!
## Points into slots 4–7 on RISC-V, from any table

`pointFromTableQ` with `s0` at `q` reads the 128 bytes there, a table entry
of the working space or of a static outside it, into slots 4–7
(`pointFromTableQ_ok`), as `pointFromTable` reads one into slots 0–3. An
entry at offset `o` of the working space is the point at `b + o`
(`tableAt_shift`).
-/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_congr)
open VG.Impl.Ed25519 (negBaseCached)

theorem wd_shift' (m : Mem) (b : Addr) (o d : Nat) : wd m (b + BitVec.ofNat 64 o) d = wd m b (o + d) := by
  unfold wd; rw [Offset.add_add]

theorem FS_shift (m : Mem) (b : Addr) (o d : Nat) : FS m (b + BitVec.ofNat 64 o) d = FS m b (o + d) := by
  unfold FS V limb
  simp only [wd_shift', Nat.add_assoc]

theorem tableAt_shift (m : Mem) (b : Addr) (o : Nat) : tableAt m (b + BitVec.ofNat 64 o) 0 = tableAt m b o := by
  simp only [tableAt, FS_shift, Nat.add_zero]

section
variable {b : Addr}

open VG.Proof.X448.RISCV64.R64 (dw ew dw_write_self dw_write_other) in
open VG.Proof.X25519.RISCV64.R64 (V_eq4 val4_congr) in
/-- After `j` doublewords of `pointFromTableQ` from `s0 = q`. -/
structure FromTableQInv (b q : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 192, 8 * j⟩] s0.mem s.mem
  outs : ∀ i < j, dw s.mem b (192 + 8 * i) = dw s0.mem q (8 * i)

open VG.Proof.X448.RISCV64.R64 (dw ew dw_write_self dw_write_other) in
open VG.Proof.X25519.RISCV64.R64 (V_eq4 val4_congr) in
theorem pointFromTableQ_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .s0 = q)
    (hq8 : q.toNat % 8 = 0)
    (hr : ∀ k, k + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 k) 8)
    (hd : (⟨q, 128⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 192, 128⟩) :
    WP isa (.block pointFromTableQ) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 192, 128⟩] s.mem t.mem ∧
      point (env t.mem b) 4 5 6 7 = tableAt s.mem q 0 ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem b i = env s.mem b i := by
  refine WP.mono (wp_range_flatMap (M := isa) (FromTableQInv b q s) (fun j t hj h => ?_) 16 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩) fun t h => ⟨h.rest.mono (by decide), h.frame, ?_,
      fun i hi => ?_⟩
  · have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
    have hq : t.gpr .s0 = q := by rw [h.rest.gpr _ (by decide), h14]
    -- The source's doubleword `j`, unchanged so far.
    have hsrc : t.mem.readW (q + BitVec.ofNat 64 (8 * j)) 64 = s.mem.readW (q + BitVec.ofNat 64 (8 * j)) 64 :=
      h.frame.readW (Region.contains_self _ _) (fun r hr' => by
        rw [List.mem_singleton.mp hr']
        exact (hd.sub_left (Offset.sub_base q (by omega))).sub_right (Region.sub_prefix (by omega))) (by decide)
    refine wp_ld (a := q + BitVec.ofNat 64 (8 * j)) (by omega) (by rw [hq]) (VG.Proof.X448.RISCV64.R64.al8 hq8 (by omega))
      (by rw [h.rest.rd, h.rest.wr]; exact hr _ (by omega)) fun t1 u1 => ?_
    have hc1 : Ctx8 b t1 := hct.of_rest (u1.rest (ws := [.a4]) (by decide)) (by decide)
    refine wp_sd (a := b + BitVec.ofNat 64 (192 + 8 * j)) (by omega) (by rw [hc1.a3])
      (VG.Proof.X448.RISCV64.R64.al8 hc1.al (by omega)) (hc1.inW (by omega)) fun t2 u2 => WP.block_nil ?_
    have hv : t1.gpr .a4 = s.mem.readW (q + BitVec.ofNat 64 (8 * j)) 64 := by rw [u1.gpr, hsrc]
    have hm2 : t2.mem = t.mem.writeW (b + BitVec.ofNat 64 (192 + 8 * j)) (t1.gpr .a4) := by rw [u2.mem, u1.mem]
    refine ⟨h.rest.trans ((u1.rest (ws := [.a4]) (by decide)).trans (u2.rest [.a4])), ?_, fun i hi => ?_⟩
    · rw [hm2]
      refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton.mp hr']; exact Region.sub_prefix (by omega)
      · exact Offset.contains b (by omega) (by omega) (by omega)
    · rw [hm2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega), h.outs i hi]
      · rw [dw_write_self, hv]; rfl
  · have e : ∀ j < 4, V t.mem b (192 + 32 * j) = V s.mem q (32 * j) := fun j hj => by
      rw [V_eq4, V_eq4]
      exact val4_congr fun i hi => by
        simp only [ew]
        rw [show 192 + 32 * j + 8 * i = 192 + 8 * (4 * j + i) by omega, h.outs _ (by omega),
          show 32 * j + 8 * i = 8 * (4 * j + i) by omega]
    simp only [tableAt, point, env, FS]
    rw [show offset 4 = 192 from rfl, show offset 5 = 224 from rfl, show offset 6 = 256 from rfl,
      show offset 7 = 288 from rfl, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  · have hs := slot_range i
    unfold env FS V
    refine congrArg _ (val32_congr (limb_frame h.frame fun r hr k hk => ?_))
    rw [List.mem_singleton.mp hr]
    rcases hi with hi | hi
    · exact Offset.disjoint _ (.inl (by simp only [offset]; omega)) (by omega) (by omega)
    · exact Offset.disjoint _ (.inr (by simp only [offset]; omega)) (by omega) (by omega)

/-! ## The static of `-[1]B … -[15]B` -/

private theorem lo_digit (v k' : Nat) :
    v / 2 ^ (64 * k') % 2 ^ 64 % 2 ^ 32 = v / 2 ^ (32 * (2 * k')) % 2 ^ 32 := by
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64), show 32 * (2 * k') = 64 * k' by omega]

private theorem hi_digit (v k' : Nat) :
    (v / 2 ^ (64 * k') % 2 ^ 64) >>> 32 % 2 ^ 32 = v / 2 ^ (32 * (2 * k' + 1)) % 2 ^ 32 := by
  rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mod_mul_right_div_self,
    Nat.mod_mod, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * k' + 32 = 32 * (2 * k' + 1) by omega]

/-- Limb `k` of coordinate `c` of the static's entry `j`. -/
theorem limb_static {m : Mem} {T : Addr}
    (hw : ∀ q < 240, m.readW (T + BitVec.ofNat 64 (8 * q)) 64 = bWord q) {j c k : Nat}
    (hj : j < 15) (hc : c < 4) (hk : k < 8) :
    limb m (T + BitVec.ofNat 64 (128 * j)) (32 * c) k =
      (pointCoord (negBaseCached j) c).val / 2 ^ (32 * k) % 2 ^ 32 := by
  unfold limb wd
  rw [Offset.add_add]
  obtain ⟨k', hk'⟩ : ∃ k', k = 2 * k' ∨ k = 2 * k' + 1 := ⟨k / 2, by omega⟩
  rcases hk' with rfl | rfl
  · have hq : 16 * j + 4 * c + k' < 240 := by omega
    rw [show 128 * j + (32 * c + 4 * (2 * k')) = 8 * (16 * j + 4 * c + k') by omega,
      Mem.readW_lo32 (hw _ hq), BitVec.toNat_setWidth, bWord, BitVec.toNat_ofNat,
      show (16 * j + 4 * c + k') / 16 = j by omega, show (16 * j + 4 * c + k') / 4 % 4 = c by omega,
      show (16 * j + 4 * c + k') % 4 = k' by omega, lo_digit]
  · have hq : 16 * j + 4 * c + k' < 240 := by omega
    rw [show 128 * j + (32 * c + 4 * (2 * k' + 1)) = 8 * (16 * j + 4 * c + k') + 4 by omega,
      ← Offset.add_add, Mem.readW_hi32 (hw _ hq), BitVec.extractLsb'_toNat, bWord, BitVec.toNat_ofNat,
      show (16 * j + 4 * c + k') / 16 = j by omega, show (16 * j + 4 * c + k') / 4 % 4 = c by omega,
      show (16 * j + 4 * c + k') % 4 = k' by omega, hi_digit]

/-- **The static's entry `j`** is `negBaseCached j`. -/
theorem tableAt_static {m : Mem} {T : Addr}
    (hw : ∀ q < 240, m.readW (T + BitVec.ofNat 64 (8 * q)) 64 = bWord q) {j : Nat} (hj : j < 15) :
    tableAt m (T + BitVec.ofNat 64 (128 * j)) 0 = negBaseCached j := by
  have hf : ∀ c < 4, FS m (T + BitVec.ofNat 64 (128 * j)) (32 * c) = pointCoord (negBaseCached j) c := by
    intro c hc
    unfold FS V
    rw [val32_congr (g := fun k => (pointCoord (negBaseCached j) c).val / 2 ^ (32 * k) % 2 ^ 32)
      fun k hk => limb_static hw hj hc hk, val32_digits,
      Nat.mod_eq_of_lt (Nat.lt_trans (pointCoord (negBaseCached j) c).isLt (by decide))]
    exact Fin.ext (Nat.mod_eq_of_lt (pointCoord (negBaseCached j) c).isLt)
  have e0 := hf 0 (by decide)
  have e1 := hf 1 (by decide)
  have e2 := hf 2 (by decide)
  have e3 := hf 3 (by decide)
  simp only [Nat.mul_zero, Nat.reduceMul] at e0 e1 e2 e3
  simp only [tableAt, Nat.zero_add, e0, e1, e2, e3, pointCoord]

end

end

/-!
## The table of `A` on RISC-V

`storeCached` writes the cache of the point of slots 0–3 to entry `s2` of
the table at `TA`, keeping the point and the cached one in slots 4–7
(`storeCached_ok`). `aTable` fills the table's 15 entries with the caches
of `[1]A … [15]A` for `A` in slots 0–3 (`aTable_ok`): `aMult A j` by the
specification's addition, which represents `(j + 1) • A` (`aMult_rep`).
-/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519 (Rep cache)
open VG.Proof.X25519 (val32_congr)

/-- `[n + 1] p` by the specification's addition. -/
def aMult (p : Spec.Ed25519.Point) : Nat → Spec.Ed25519.Point
  | 0 => p
  | n + 1 => Spec.Ed25519.pointAdd (aMult p n) p

theorem aMult_rep {p : Spec.Ed25519.Point} {a : Edwards.EPoint Proof.Ed25519.dZ} (h : Rep p a) :
    ∀ n, Rep (aMult p n) ((n + 1) • a)
  | 0 => by simp only [aMult, zero_add, one_smul]; exact h
  | n + 1 => by
    rw [aMult, succ_nsmul]
    exact Proof.Ed25519.pointAdd_rep (aMult_rep h n) h

section
variable {b : Addr}

theorem TA_eq : TA = 1632 := rfl

/-- The table's entry `n`. -/
abbrev entryR (b : Addr) (n : Nat) : Region := ⟨b + BitVec.ofNat 64 (TA + 128 * n), 128⟩

theorem entry_FA {n : Nat} (hn : n < 15) : (entryR b n).Disjoint (FA b) :=
  Offset.disjoint _ (.inr (by simp only [TA]; omega)) (by simp only [TA]; omega) (by omega)

theorem slot_entry (i : Slot) {n : Nat} (hn : n < 15) :
    (⟨b + BitVec.ofNat 64 (offset i), 32⟩ : Region).Disjoint (entryR b n) := by
  have := slot_range i
  exact Offset.disjoint _ (.inl (by simp only [TA]; omega)) (by omega) (by simp only [TA]; omega)

theorem storeCached_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {n : Nat}
    (hn : n < 15) (h16 : s.gpr .s2 = BitVec.ofNat 64 n) :
    WP isa storeCached s fun t => Rest (.a4 :: .s0 :: fclob) s t ∧ Frame [FA b, entryR b n] s.mem t.mem ∧
      tableAt t.mem b (TA + 128 * n) = cache (point (env s.mem b) 0 1 2 3) ∧
      point (env t.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 ∧
      point (env t.mem b) 4 5 6 7 = point (env s.mem b) 4 5 6 7 ∧ env t.mem b 16 = env s.mem b 16 := by
  unfold storeCached
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx hc.ws) fun s1 ⟨k1, e1⟩ => ?_)
  obtain ⟨c1, p1⟩ := cacheOps_eval (env s.mem b) hd
  rw [← e1] at c1 p1
  have q1 : ∀ i : Slot, 4 ≤ i.val ∧ i.val < 8 ∨ i.val = 16 ∨ i.val = 21 → env s1.mem b i = env s.mem b i :=
    fun i hi => by rw [e1]; exact cacheOps_keep _ i hi
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (tableAddr_ok hc1 (n := n) (by decide) (by omega) (by rw [k1.rest.gpr _ (by decide), h16]) fun t1 r1 m1 e14 => ?_)
  have hct1 : Ctx8 b t1 := hc1.of_rest r1 (by decide)
  refine WP.mono (pointToTable_ok hct1 e14 (by simp only [TA]; omega) (by simp only [TA]; omega))
    fun t2 ⟨r2, f2, tb2⟩ => ?_
  rw [m1] at f2 tb2
  have hct2 : Ctx8 b t2 := hct1.of_rest r2 (by decide)
  have k2 : ∀ i : Slot, env t2.mem b i = env s1.mem b i := fun i =>
    env_keep f2 i fun r hr => by rw [List.mem_singleton.mp hr]; exact slot_entry i hn
  refine WP.mono (fieldCode_ok restorePointOps hct2.ctx hct2.ws) fun t ⟨kt, et⟩ => ?_
  obtain ⟨rt0, -, rt16, rt4⟩ := env_restorePoint (env t2.mem b)
  rw [← et] at rt0 rt16 rt4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (k1.rest.mono (by decide)).trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      (kt.rest.mono (by decide))))
  · exact (k1.frame.mono (by simp)).trans ((f2.mono (by simp)).trans (kt.frame.mono (by simp)))
  · rw [tableAt_keep kt.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact entry_FA hn, tb2, c1]
  · rw [rt0]; simp only [point, k2]; exact p1
  · rw [rt4]; simp only [point, k2, q1 4 (by decide), q1 5 (by decide), q1 6 (by decide), q1 7 (by decide)]
  · rw [rt16, k2, q1 16 (by decide)]

/-- While filling the table of `A`: entries `j < n` written, the sum `aMult A (n - 1)` in slots 0–3
and the cached `A` in slots 4–7. -/
structure ATabInv (b : Addr) (s0 : State) (A : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  lt : n < 15
  ctx : Ctx8 b s
  rest : Rest (.a4 :: .s0 :: .s2 :: fclob) s0 s
  frame : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s0.mem s.mem
  s2 : s.gpr .s2 = BitVec.ofNat 64 n
  pt : point (env s.mem b) 0 1 2 3 = aMult A (n - 1)
  q : point (env s.mem b) 4 5 6 7 = cache A
  table : ∀ j < n, tableAt s.mem b (TA + 128 * j) = cache (aMult A j)
  d : env s.mem b 16 = Spec.Ed25519.d

theorem entry_sub {n : Nat} (hn : n < 15) :
    ∀ r ∈ [entryR b n], ∃ r' ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)], Region.Sub r r' :=
  fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨b + BitVec.ofNat 64 TA, 1920⟩, by simp,
      Offset.sub _ (by simp only [TA]; omega) (by simp only [TA]; omega)⟩

theorem entry_sub2 {n : Nat} (hn : n < 15) :
    ∀ r ∈ [FA b, entryR b n], ∃ r' ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)], Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨FA b, by simp, fun _ h => h⟩
    · exact entry_sub hn _ (List.mem_singleton_self _)

theorem entries_apart {j n : Nat} (hj : j < 15) (hn : n < 15) (h : j ≠ n) : (entryR b j).Disjoint (entryR b n) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Offset.disjoint _ (.inl (by omega)) (by simp only [TA]; omega) (by simp only [TA]; omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by simp only [TA]; omega) (by simp only [TA]; omega)

/-- **The table of `A`**: entries `j < 15` at `TA` are the caches of `aMult A j`. -/
theorem aTable_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa aTable s fun t => Rest (.a4 :: .s0 :: .s2 :: fclob) s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem t.mem ∧ Ctx8 b t ∧
      (∀ j < 15, tableAt t.mem b (TA + 128 * j) = cache (aMult (point (env s.mem b) 0 1 2 3) j)) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  set A := point (env s.mem b) 0 1 2 3 with hA
  unfold aTable aTableInit
  refine WP.seq (WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_))
  have hc1 : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.s2]) (by decide)) (by decide)
  refine WP.seq (WP.mono (storeCached_ok hc1 (by rw [u1.mem]; exact hd) (n := 0) (by decide) u1.gpr)
    fun s2 ⟨r2, f2, tb2, p2, _, d2⟩ => ?_)
  rw [u1.mem] at f2 tb2 p2 d2
  have hc2 : Ctx8 b s2 := hc1.of_rest r2 (by decide)
  refine tableAddr_ok hc2 (n := 0) (by decide) (by decide)
    (by rw [r2.gpr _ (by decide), u1.gpr]) fun t1 r3 m3 e3 => ?_
  have hct1 : Ctx8 b t1 := hc2.of_rest r3 (by decide)
  refine WP.append (pointFromTableQ_ok hct1 e3 (VG.Proof.X448.RISCV64.R64.al8 hct1.al (by rw [TA_eq]))
    (fun k hk => by rw [Offset.add_add]; exact hct1.inR (by rw [TA_eq]; omega))
    (Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by rw [TA_eq]; omega) (by omega)))
    fun t2 ⟨r4, f4, q4, k4⟩ => ?_
  refine wp_li (by decide) fun t3 u5 => WP.block_nil ?_
  rw [tableAt_shift, m3, tb2] at q4
  have hc3 : Ctx8 b t3 := (hct1.of_rest r4 (by decide)).of_rest (u5.rest (ws := [.s2]) (by decide)) (by decide)
  have m35 : t3.mem = t2.mem := u5.mem
  have hF3 : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem t3.mem := by
    rw [m35]
    refine ((f2.sub (entry_sub2 (n := 0) (by omega))).trans ?_)
    rw [← m3]
    exact f4.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨FA b, by simp, Offset.sub _ (by omega) (by omega)⟩
  have kq : ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t3.mem b i = env s2.mem b i := fun i hi => by
    rw [m35, k4 i hi, m3]
  have I0 : ATabInv b s A 1 t3 := by
    refine ⟨le_rfl, by decide, hc3, ?_, hF3, u5.gpr, ?_, ?_, fun j hj => ?_, ?_⟩
    · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
        ((r4.mono (by decide)).trans (u5.rest (by decide)))))
    · have e : point (env t3.mem b) 0 1 2 3 = point (env s2.mem b) 0 1 2 3 := by
        simp only [point, kq 0 (by decide), kq 1 (by decide), kq 2 (by decide), kq 3 (by decide)]
      rw [e, p2]; rfl
    · rw [m35]; simpa only [Nat.mul_zero, Nat.add_zero] using q4
    · obtain rfl : j = 0 := by omega
      rw [m35, tableAt_keep f4 fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by rw [TA_eq]; omega) (by omega), m3, tb2]
      rfl
    · rw [kq 16 (by decide), d2, hd]
  refine WP.loop (M := isa) (fun m t => ∃ n, m = 15 - n ∧ ATabInv b s A n t) ?_ 14 t3 ⟨1, rfl, I0⟩
  rintro m t ⟨n, rfl, h⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := h.lo; omega⟩
  have hlt := h.lt
  unfold aTableBody
  refine WP.seq (WP.mono (fieldCode_ok pointAddCachedOps h.ctx.ctx h.ctx.ws) fun v1 ⟨kv1, ev1⟩ => ?_)
  have hcv1 : Ctx8 b v1 := h.ctx.of_keep kv1
  have pv1 : point (env v1.mem b) 0 1 2 3 = aMult A (n' + 1) := by
    rw [ev1, pointAddCached_eval _ A h.q, h.pt]; rfl
  have kv : ∀ i : Slot, 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val → env v1.mem b i = env t.mem b i := fun i hi => by
    rw [ev1]; exact pointAddCached_keep _ i hi
  have qv1 : point (env v1.mem b) 4 5 6 7 = cache A := by
    simp only [point, kv 4 (by decide), kv 5 (by decide), kv 6 (by decide), kv 7 (by decide)]
    exact h.q
  have dv1 : env v1.mem b 16 = Spec.Ed25519.d := by rw [kv 16 (by decide)]; exact h.d
  refine WP.seq (WP.mono (storeCached_ok hcv1 dv1 (n := n' + 1) h.lt (by rw [kv1.rest.gpr _ (by decide), h.s2]))
    fun v2 ⟨r6, f6, tb6, p6, q6, d6⟩ => ?_)
  have hcv2 : Ctx8 b v2 := hcv1.of_rest r6 (by decide)
  refine wp_addi (by decide) fun v3 u7 => wp_subi (imm := 15) (by decide) fun v4 u8 => WP.block_nil ?_
  have e16 : v4.gpr .s2 = BitVec.ofNat 64 (n' + 1 + 1) := by
    rw [u8.other _ (by decide), u7.gpr, r6.gpr _ (by decide), kv1.rest.gpr _ (by decide), h.s2]
    exact (BitVec.ofNat_add (n' + 1) 1).symm
  have e7 : (v4.gpr .a4 != 0) = decide (n' + 1 + 1 ≠ 15) := by
    rw [u8.gpr, u7.gpr, r6.gpr _ (by decide), kv1.rest.gpr _ (by decide), h.s2,
      show BitVec.ofNat 64 (n' + 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n' + 1 + 1) from (BitVec.ofNat_add _ _).symm,
      ofNat_sub_ne_zero (by omega) (by omega)]
  have m4 : v4.mem = v2.mem := by rw [u8.mem, u7.mem]
  have hc4 : Ctx8 b v4 :=
    hcv2.of_rest ((u7.rest (ws := [.s2, .a4]) (by decide)).trans (u8.rest (ws := [.s2, .a4]) (by decide))) (by decide)
  have hR : Rest (.a4 :: .s0 :: .s2 :: fclob) s v4 :=
    h.rest.trans ((kv1.rest.mono (by decide)).trans ((r6.mono (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide)))))
  have hF : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem v4.mem := by
    rw [m4]
    exact h.frame.trans ((kv1.frame.mono (by simp)).trans (f6.sub (entry_sub2 h.lt)))
  have hT : ∀ j < n' + 1 + 1, tableAt v4.mem b (TA + 128 * j) = cache (aMult A j) := by
    intro j hj
    rw [m4]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [tableAt_keep f6 fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact entry_FA (by have := h.lt; omega)
          · exact entries_apart (by have := h.lt; omega) h.lt (by omega),
        tableAt_keep kv1.frame fun r hr => by
          rw [List.mem_singleton.mp hr]; exact entry_FA (by have := h.lt; omega)]
      exact h.table j hj
    · rw [tb6, pv1]
  have hP : point (env v4.mem b) 0 1 2 3 = aMult A (n' + 1) := by rw [m4, p6, pv1]
  have hQ : point (env v4.mem b) 4 5 6 7 = cache A := by rw [m4, q6, qv1]
  have hD : env v4.mem b 16 = Spec.Ed25519.d := by rw [m4, d6, dv1]
  rw [eval_nonzero, e7]
  by_cases hl : n' + 1 + 1 = 15
  · exact .inl ⟨by simp [hl], hR, hF, hc4, fun j hj => hT j (by omega), hD⟩
  · exact .inr ⟨by simp [hl], 15 - (n' + 1 + 1), by omega, n' + 1 + 1, rfl,
      ⟨by omega, by have := h.lt; omega, hc4, hR, hF, e16, hP, hQ, hT, hD⟩⟩
end

end

/-! ## The windows -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519 (Rep RepP cache dblPoint baseAff dZ negPoint)
open VG.Impl.Ed25519 (negBaseCached)
open VG.Spec.Ed25519 (decodeLE bytesAt)
open Edwards

/-! ## Arithmetic of the instructions -/

theorem evalOps_append (l₁ l₂ : List FieldOp) (e : Env) : evalOps (l₁ ++ l₂) e = evalOps l₂ (evalOps l₁ e) :=
  List.foldl_append

/-- `dblOpsXYZ` leaves `T` as it was and the double's `X`, `Y` and `Z`. -/
theorem dblOpsXYZ_eval (e : Env) : point (evalOps dblOpsXYZ e) 0 1 2 3 =
    { dblPoint (point e 0 1 2 3) with T := e 3 } := rfl

theorem dblOpsXYZ_keep (e : Env) (i : Slot) (hi : 4 ≤ i.val ∧ i.val < 8 ∨ 15 ≤ i.val) :
    evalOps dblOpsXYZ e i = e i :=
  evalOps_keep _ e i fun op hop => by
    simp only [dblOpsXYZ, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun h => by subst h; revert hi; decide

/-- A doubling reads only `X`, `Y` and `Z`. -/
theorem dblPoint_T (p : Spec.Ed25519.Point) (t : Spec.X25519.Fe) : dblPoint { p with T := t } = dblPoint p := rfl

/-- A doubling without `T` after one: the same `X`, `Y` and `Z` as two doublings. -/
theorem dblOpsXYZ_dblOpsXYZ (e : Env) : point (evalOps dblOpsXYZ (evalOps dblOpsXYZ e)) 0 1 2 3 =
    { dblPoint (dblPoint (point e 0 1 2 3)) with T := e 3 } := by
  rw [dblOpsXYZ_eval, dblOpsXYZ_eval, dblPoint_T]
  rfl

theorem dbl4_eval (e : Env) : point (evalOps (dblOpsXYZ ++ dblOpsXYZ ++ dblOpsXYZ ++ dblOps) e) 0 1 2 3 =
    dblPoint (dblPoint (dblPoint (dblPoint (point e 0 1 2 3)))) := by
  rw [evalOps_append, evalOps_append, evalOps_append, dblOps_eval, dblOpsXYZ_eval, dblPoint_T,
    dblOpsXYZ_dblOpsXYZ]
  rfl

theorem dbl4_keep (e : Env) : evalOps (dblOpsXYZ ++ dblOpsXYZ ++ dblOpsXYZ ++ dblOps) e 16 = e 16 := by
  rw [evalOps_append, evalOps_append, evalOps_append, dblOps_keep _ 16 (by decide),
    dblOpsXYZ_keep _ 16 (by decide), dblOpsXYZ_keep _ 16 (by decide), dblOpsXYZ_keep _ 16 (by decide)]

theorem rep_repP {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) : RepP p a := ⟨h.z, h.x, h.y⟩

/-- Four doublings: `16 • a`. -/
theorem dbl4_rep {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : RepP p a) :
    Rep (dblPoint (dblPoint (dblPoint (dblPoint p)))) ((16 : Nat) • a) := by
  have h1 := Proof.Ed25519.dblPoint_rep h
  rw [← two_nsmul] at h1
  have h2 := Proof.Ed25519.dblPoint_rep (rep_repP h1)
  rw [← two_nsmul, smul_smul] at h2
  have h3 := Proof.Ed25519.dblPoint_rep (rep_repP h2)
  rw [← two_nsmul, smul_smul] at h3
  have h4 := Proof.Ed25519.dblPoint_rep (rep_repP h3)
  rw [← two_nsmul, smul_smul] at h4
  exact h4

theorem sub1_fact : ∀ dg < 16, dg ≠ 0 → BitVec.ofNat 64 dg - BitVec.ofNat 64 1 = BitVec.ofNat 64 (dg - 1) := by
  decide

theorem sub1_shl_fact : ∀ dg < 16, dg ≠ 0 →
    (BitVec.ofNat 64 dg - BitVec.ofNat 64 1) <<< 7 = BitVec.ofNat 64 (128 * (dg - 1)) := by
  decide

theorem sltu_fact : ∀ c < 128,
    ((if BitVec.ofNat 64 c < BitVec.ofNat 64 64 then 1 else 0 : BitVec 64) != 0) = decide (c < 64) := by
  decide

theorem fa_sub {b : Addr} : ∀ r ∈ [FA b], Region.Sub r ⟨b, 8192⟩ := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)

private theorem wp_lla' {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {name : String}
    (k : ∀ s', Upd s s' d (s.syms name) → WP isa (.block is) s' Q) : WP isa (.block (.lla d name :: is)) s Q :=
  WP.cons exec_lla (k _ (Upd.write _ _ _))

section
variable {b pk sig ch T : Addr} {A : Spec.Ed25519.Point} {K S : Nat}

/-! ## What the windows read -/

/-- What the windows read and keep: the inputs, the static at `T` (in `s5`), the table of `A`,
and the scalars `K` and `S` of the inputs' bytes. -/
structure WCtx (b pk sig ch T : Addr) (A : Spec.Ed25519.Point) (K S : Nat) (s : State) : Prop where
  vc : VCtx b pk sig ch s
  bs : BStat b T s
  s5 : s.gpr .s5 = T
  tab : ∀ j < 15, tableAt s.mem b (TA + 128 * j) = cache (aMult A j)
  k : decodeLE (bytesAt s.mem ch 64) = K
  sc : decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32) = S

theorem WCtx.of {s t : State} {R : List Reg} (h : WCtx b pk sig ch T A K S s) (hr : Rest R s t)
    (hR : ∀ r ∈ [Reg.a3, .s9, .s10, .s11], r ∉ R) (h5 : Reg.s5 ∉ R) (hf : Frame [FA b] s.mem t.mem) :
    WCtx b pk sig ch T A K S t where
  vc := h.vc.of_rest hr hR
  bs := h.bs.of_frame hr.rd hf fa_sub
  s5 := by rw [hr.gpr _ h5, h.s5]
  tab j hj := by
    rw [tableAt_keep hf fun r hr => by rw [List.mem_singleton.mp hr]; exact entry_FA hj, h.tab j hj]
  k := by rw [bytesAt_ws hf fa_sub h.vc.chD (by decide), h.k]
  sc := by
    rw [bytesAt_ws hf fa_sub (h.vc.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
      (by decide), h.sc]

/-! ## The digits -/

/-- Nibble `i` of `n` bytes is digit `i` of their number. -/
theorem nibAt_eqN (m : Mem) (p : Addr) {n i : Nat} (hi : i < 2 * n) :
    nibAt m p i = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 16 ^ i % 16 := by
  rw [Proof.Ed25519.decodeLE_nibble, Proof.Ed25519.nibbleOf, nibAt]
  have hg : (Spec.Ed25519.bytesAt m p n).getD (i / 2) 0 = m (p + BitVec.ofNat 64 (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < n by omega]
  rw [hg]
  have := (m (p + BitVec.ofNat 64 (i / 2))).isLt
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), Nat.pow_zero, Nat.div_one]
  · rw [h, ite_eq_left rfl, Nat.pow_one]; omega

theorem digitK_ok {s : State} (h : WCtx b pk sig ch T A K S s) {c : Nat} (hc : c < 128)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 c) :
    WP isa (.block (nibble .s11 0)) s fun t => Rest [.a1, .a2, .t0] s t ∧ t.mem = s.mem ∧
      t.gpr .a2 = BitVec.ofNat 64 (K / 16 ^ c % 16) := by
  refine WP.mono (nibble_ok (p := .s11) (by decide) h.vc.s11 (o := 0) (by decide) hc h1 ?_)
    fun t ⟨r, m, e⟩ => ⟨r, m, ?_⟩
  · rw [Offset.add_add]
    exact in_base (List.mem_append_left _ h.vc.chR) (by omega) (by omega)
  · rw [e, show ch + BitVec.ofNat 64 0 = ch from BitVec.add_zero ch, nibAt_eqN s.mem ch (n := 64) (by omega), h.k]

theorem digitS_ok {s : State} (h : WCtx b pk sig ch T A K S s) {c : Nat} (hc : c < 64)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 c) :
    WP isa (.block (nibble .s10 32)) s fun t => Rest [.a1, .a2, .t0] s t ∧ t.mem = s.mem ∧
      t.gpr .a2 = BitVec.ofNat 64 (S / 16 ^ c % 16) := by
  refine WP.mono (nibble_ok (p := .s10) (by decide) h.vc.s10 (o := 32) (by decide) (by omega) h1 ?_)
    fun t ⟨r, m, e⟩ => ⟨r, m, ?_⟩
  · rw [Offset.add_add]
    exact in_base (List.mem_append_left _ h.vc.sigR) (by omega) (by omega)
  · rw [e, nibAt_eqN s.mem _ (n := 32) (by omega), h.sc]

/-! ## A cached addition -/

/-- The cached point at `s0` added to slots 0–3. -/
theorem addCached_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h0 : s.gpr .s0 = q) (hq8 : q.toNat % 8 = 0)
    (hr : ∀ k, k + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 k) 8)
    (hd : (⟨q, 128⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 192, 128⟩)
    {Q : Spec.Ed25519.Point} {qa a : EPoint dZ} (hQ : tableAt s.mem q 0 = cache Q) (hq : Rep Q qa)
    (hp : Rep (point (env s.mem b) 0 1 2 3) a) {R : State → Prop}
    (k : ∀ t, Rest fclob s t → Frame [FA b] s.mem t.mem →
      Rep (point (env t.mem b) 0 1 2 3) (a + qa) → env t.mem b 16 = env s.mem b 16 → R t) :
    WP isa (.block pointFromTableQ) s fun t => WP isa (fieldCode pointAddCachedOps) t R := by
  refine WP.mono (pointFromTableQ_ok hc h0 hq8 hr hd) fun s1 ⟨r1, f1, q1, k1⟩ => ?_
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  refine WP.mono (fieldCode_ok pointAddCachedOps hc1.ctx hc1.ws) fun t ⟨kt, et⟩ => k t ?_ ?_ ?_ ?_
  · exact (r1.mono (by decide)).trans kt.rest
  · exact (f1.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨FA b, by simp, Offset.sub _ (by omega) (by omega)⟩).trans kt.frame
  · have p1 : point (env s1.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 := by
      simp only [point, k1 0 (by decide), k1 1 (by decide), k1 2 (by decide), k1 3 (by decide)]
    rw [hQ] at q1
    rw [et, pointAddCached_eval _ Q q1, p1]
    exact Proof.Ed25519.pointAdd_rep hp hq
  · rw [et, pointAddCached_keep _ 16 (by decide), k1 16 (by decide)]

/-- **`k`'s digit `dg`**: the cached `[dg]A` added, unless `dg` is zero. -/
theorem addA_ok {s : State} (h : WCtx b pk sig ch T A K S s) {Aa a : EPoint dZ} (hA : Rep A Aa)
    {dg : Nat} (hdg : dg < 16) (h2 : s.gpr .a2 = BitVec.ofNat 64 dg)
    (hp : Rep (point (env s.mem b) 0 1 2 3) a) :
    WP isa addA s fun t => Rest (.s0 :: .s2 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3) (a + dg • Aa) ∧ env t.mem b 16 = env s.mem b 16 := by
  unfold addA
  refine WP.ite _ (eval_nonzero_ofNat s .a2 (by omega) h2) (fun hb => ?_) (fun hb => ?_)
  · have hd0 : dg ≠ 0 := by simpa using hb
    refine WP.seq ?_
    simp only [List.singleton_append]
    refine wp_subi (imm := 1) (by decide) fun s1 u1 => ?_
    have e1 : s1.gpr .s2 = BitVec.ofNat 64 (dg - 1) := by rw [u1.gpr, h2]; exact sub1_fact dg hdg hd0
    have hc1 : Ctx8 b s1 := h.vc.ctx.of_rest (u1.rest (ws := [.s2]) (by decide)) (by decide)
    refine tableAddr_ok hc1 (start := TA) (n := dg - 1) (by decide) (by omega) e1 fun s2 r2 m2 e2 => ?_
    have hc2 : Ctx8 b s2 := hc1.of_rest r2 (by decide)
    have hq : Rep (aMult A (dg - 1)) (dg • Aa) := by
      have := aMult_rep hA (dg - 1)
      rwa [Nat.sub_add_cancel (by omega)] at this
    refine addCached_ok hc2 e2 (VG.Proof.X448.RISCV64.R64.al8 hc2.al (by rw [TA_eq]; omega))
      (fun k hk => by rw [Offset.add_add]; exact hc2.inR (by rw [TA_eq]; omega))
      (Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by rw [TA_eq]; omega) (by omega))
      (by rw [tableAt_shift, m2, u1.mem, h.tab (dg - 1) (by omega)]) hq (by rw [m2, u1.mem]; exact hp)
      fun t rt ft pt dt => ⟨?_, ?_, pt, ?_⟩
    · exact (u1.rest (by decide)).trans ((r2.mono (by decide)).trans (rt.mono (by decide)))
    · rw [m2, u1.mem] at ft; exact ft
    · rw [dt, m2, u1.mem]
  · have hd0 : dg = 0 := by simpa using hb
    subst hd0
    exact WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, by rw [zero_nsmul, add_zero]; exact hp, rfl⟩

/-- **`S`'s digit `dg`**: the cached `-[dg]B` added, unless `dg` is zero. -/
theorem addB_ok {s : State} (h : WCtx b pk sig ch T A K S s) {a : EPoint dZ}
    {dg : Nat} (hdg : dg < 16) (h2 : s.gpr .a2 = BitVec.ofNat 64 dg)
    (hp : Rep (point (env s.mem b) 0 1 2 3) a) :
    WP isa addB s fun t => Rest (.s0 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3) (a + dg • (-baseAff)) ∧ env t.mem b 16 = env s.mem b 16 := by
  unfold addB
  refine WP.ite _ (eval_nonzero_ofNat s .a2 (by omega) h2) (fun hb => ?_) (fun hb => ?_)
  · have hd0 : dg ≠ 0 := by simpa using hb
    refine WP.seq ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_subi (imm := 1) (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_add fun s3 u3 => ?_
    have e3 : s3.gpr .s0 = T + BitVec.ofNat 64 (128 * (dg - 1)) := by
      rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), h.s5, u2.gpr, u1.gpr, h2, sub1_shl_fact dg hdg hd0]
    have r3 : Rest [.a4, .s0] s s3 :=
      (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    have hc3 : Ctx8 b s3 := h.vc.ctx.of_rest r3 (by decide)
    obtain ⟨q, eq, hq⟩ := Proof.Ed25519.negBaseCached_ok (dg - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hq
    have hfit := h.bs.fit
    refine addCached_ok hc3 e3 (VG.Proof.X448.RISCV64.R64.al8 h.bs.al (by omega)) (fun k hk => by
        rw [Offset.add_add, r3.rd, r3.wr]
        exact in_base (List.mem_append_left _ h.bs.rd) (by omega) (by omega))
      ((h.bs.ws.sub_left (Offset.sub_base T (by omega))).sub_right (Offset.sub_base b (by omega)))
      (by rw [m3, tableAt_static h.bs.words (by omega), eq]) hq (by rw [m3]; exact hp)
      fun t rt ft pt dt => ⟨?_, ?_, pt, ?_⟩
    · exact (r3.mono (by decide)).trans (rt.mono (by decide))
    · rw [m3] at ft; exact ft
    · rw [dt, m3]
  · have hd0 : dg = 0 := by simpa using hb
    subst hd0
    exact WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, by rw [zero_nsmul, add_zero]; exact hp, rfl⟩

/-- `S`'s digit `c`, in the low 64 windows; above them `S`'s digit is zero. -/
theorem windowB_ok {s : State} (h : WCtx b pk sig ch T A K S s) {c : Nat} (hc : c < 128)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 c) (hS : S < 256 ^ 32) {a : EPoint dZ}
    (hp : Rep (point (env s.mem b) 0 1 2 3) a) :
    WP isa windowB s fun t => Rest (.s0 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3) (a + (S / 16 ^ c % 16) • (-baseAff)) ∧
      env t.mem b 16 = env s.mem b 16 := by
  unfold windowB
  refine WP.seq (wp_li (by decide) fun s1 u1 => wp_sltu fun s2 u2 => WP.block_nil ?_)
  have r2 : Rest [.a4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e2 : (s2.gpr .a4 != 0) = decide (c < 64) := by
    rw [u2.gpr, u1.other .s1 (by decide), h1, u1.gpr]; exact sltu_fact c hc
  have e21 : s2.gpr .s1 = BitVec.ofNat 64 c := by rw [r2.gpr _ (by decide), h1]
  have h2 : WCtx b pk sig ch T A K S s2 := h.of r2 (by decide) (by decide) (by rw [m2]; exact Frame.refl _ _)
  refine WP.ite _ (by rw [eval_nonzero, e2]) (fun hb => ?_) (fun hb => ?_)
  · have hc64 : c < 64 := by simpa using hb
    refine WP.seq (WP.mono (digitS_ok h2 hc64 e21) fun s3 ⟨r3, m3, e3⟩ => ?_)
    have h3 : WCtx b pk sig ch T A K S s3 := h2.of r3 (by decide) (by decide) (by rw [m3]; exact Frame.refl _ _)
    refine WP.mono (addB_ok h3 (Nat.mod_lt _ (by decide)) e3 (by rw [m3, m2]; exact hp))
      fun t ⟨rt, ft, pt, dt⟩ => ⟨?_, ?_, pt, ?_⟩
    · exact (r2.mono (by decide)).trans ((r3.mono (by decide)).trans rt)
    · rw [m3, m2] at ft; exact ft
    · rw [dt, m3, m2]
  · have hc64 : 64 ≤ c := by simpa using hb
    refine WP.block_nil ⟨r2.mono (by decide), by rw [m2]; exact Frame.refl _ _, ?_, by rw [m2]⟩
    rw [Proof.Ed25519.nibble_high_zero hS hc64, Nat.zero_mod, zero_nsmul, add_zero, m2]
    exact hp

/-! ## A window -/

/-- **A window**, from `c + 1` windows left to `c`. -/
theorem windowStep_ok {s : State} (h : WCtx b pk sig ch T A K S s) (hd : env s.mem b 16 = Spec.Ed25519.d)
    {Aa : EPoint dZ} (hA : Rep A Aa) (hS : S < 256 ^ 32) {c : Nat} (hc : c < 128)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 (c + 1))
    (hv : RepP (point (env s.mem b) 0 1 2 3) ((K / 16 ^ (c + 1)) • Aa + (S / 16 ^ (c + 1)) • (-baseAff))) :
    WP isa windowStep s fun t => WCtx b pk sig ch T A K S t ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      t.gpr .s1 = BitVec.ofNat 64 c ∧
      Rep (point (env t.mem b) 0 1 2 3) ((K / 16 ^ c) • Aa + (S / 16 ^ c) • (-baseAff)) ∧
      Rest (.s0 :: .s1 :: .s2 :: fclob) s t ∧ Frame [FA b] s.mem t.mem := by
  unfold windowStep
  refine WP.seq (wp_subi (imm := 1) (by decide) fun s1 u1 => WP.block_nil ?_)
  have e1 : s1.gpr .s1 = BitVec.ofNat 64 c := by
    rw [u1.gpr, h1, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  have r1 : Rest [.s1] s s1 := u1.rest (by decide)
  have h1' : WCtx b pk sig ch T A K S s1 := h.of r1 (by decide) (by decide) (by rw [u1.mem]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (fieldCode_ok _ h1'.vc.ctx.ctx h1'.vc.ctx.ws) fun s2 ⟨k2, e2⟩ => ?_)
  have h2 : WCtx b pk sig ch T A K S s2 := h1'.of k2.rest (by decide) (by decide) k2.frame
  have p2 : Rep (point (env s2.mem b) 0 1 2 3)
      ((16 : Nat) • ((K / 16 ^ (c + 1)) • Aa + (S / 16 ^ (c + 1)) • (-baseAff))) := by
    rw [e2, dbl4_eval, u1.mem]; exact dbl4_rep hv
  have d2 : env s2.mem b 16 = Spec.Ed25519.d := by rw [e2, dbl4_keep, u1.mem, hd]
  have e21 : s2.gpr .s1 = BitVec.ofNat 64 c := by rw [k2.rest.gpr _ (by decide), e1]
  refine WP.seq (WP.mono (digitK_ok h2 hc e21) fun s3 ⟨r3, m3, e3⟩ => ?_)
  have h3 : WCtx b pk sig ch T A K S s3 := h2.of r3 (by decide) (by decide) (by rw [m3]; exact Frame.refl _ _)
  have p3 : Rep (point (env s3.mem b) 0 1 2 3)
      ((16 : Nat) • ((K / 16 ^ (c + 1)) • Aa + (S / 16 ^ (c + 1)) • (-baseAff))) := by rw [m3]; exact p2
  refine WP.seq (WP.mono (addA_ok h3 hA (Nat.mod_lt _ (by decide)) e3 p3)
    fun s4 ⟨r4, f4, p4, d4⟩ => ?_)
  have h4 : WCtx b pk sig ch T A K S s4 := h3.of r4 (by decide) (by decide) f4
  have e41 : s4.gpr .s1 = BitVec.ofNat 64 c := by rw [r4.gpr _ (by decide), r3.gpr _ (by decide), e21]
  refine WP.mono (windowB_ok h4 hc e41 hS p4) fun t ⟨rt, ft, pt, dt⟩ =>
    ⟨h4.of rt (by decide) (by decide) ft, by rw [dt, d4, m3, d2], by rw [rt.gpr _ (by decide), e41], ?_, ?_, ?_⟩
  · rw [← Proof.Ed25519.nibble_step Aa (-baseAff) K S c]; exact pt
  · exact (r1.mono (by decide)).trans ((k2.rest.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans (rt.mono (by decide)))))
  · rw [← u1.mem]
    exact k2.frame.trans ((by rw [← m3]; exact f4 : Frame [FA b] s2.mem s4.mem).trans ft)

/-- **The windows**, from `W` left: `[K]A - [S]B` in slots 0–3. -/
theorem windows_ok {W : Nat} (hW1 : 1 ≤ W) (hW : W ≤ 128) {s : State} (h : WCtx b pk sig ch T A K S s)
    (hd : env s.mem b 16 = Spec.Ed25519.d) {Aa : EPoint dZ} (hA : Rep A Aa) (hS : S < 256 ^ 32)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 W)
    (hv : RepP (point (env s.mem b) 0 1 2 3) ((K / 16 ^ W) • Aa + (S / 16 ^ W) • (-baseAff))) :
    WP isa windows s fun t => WCtx b pk sig ch T A K S t ∧ Rest (.s0 :: .s1 :: .s2 :: fclob) s t ∧
      Frame [FA b] s.mem t.mem ∧ Rep (point (env t.mem b) 0 1 2 3) (K • Aa + S • (-baseAff)) := by
  unfold windows
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 128 ∧ WCtx b pk sig ch T A K S t ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ t.gpr .s1 = BitVec.ofNat 64 n ∧
      RepP (point (env t.mem b) 0 1 2 3) ((K / 16 ^ n) • Aa + (S / 16 ^ n) • (-baseAff)) ∧
      Rest (.s0 :: .s1 :: .s2 :: fclob) s t ∧ Frame [FA b] s.mem t.mem) ?_ W s
    ⟨hW1, hW, h, hd, h1, hv, Rest.refl _ _, Frame.refl _ _⟩
  rintro n t ⟨hn1, hn, ht, dt, et, vt, rt, ft⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  refine WP.mono (windowStep_ok ht dt hA hS (by omega) et vt) fun u ⟨hu, du, eu, vu, ru, fu⟩ => ?_
  rw [eval_nonzero_ofNat u .s1 (by omega) eu]
  by_cases hc0 : c = 0
  · subst hc0
    simp only [pow_zero, Nat.div_one] at vu
    exact .inl ⟨by simp, hu, rt.trans ru, ft.trans fu, vu⟩
  · exact .inr ⟨by simp [hc0], c, by omega, by omega, by omega, hu, du, eu, (rep_repP vu), rt.trans ru, ft.trans fu⟩

/-! ## Before and after the windows -/

/-- `A` from the table at 7776 into slots 0–3. -/
theorem rhsRead_ok {s : State} (hc : Ctx8 b s) :
    WP isa (.block (pointTableRead 7776)) s fun t => Rest [.a4, .a5, .s0] s t ∧ Frame [FA b] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = tableAt s.mem b 7776 := by
  unfold pointTableRead
  refine scratchAddr_ok hc (o := 7776) (by decide) fun s1 r1 m1 e1 => ?_
  refine WP.mono (pointFromTable_ok (hc.of_rest r1 (by decide)) e1 (by decide) (by decide))
    fun t ⟨rt, ft, pt, _⟩ => ⟨(r1.mono (by decide)).trans (rt.mono (by decide)), ?_, by rw [pt, m1]⟩
  rw [← m1]
  exact ft.sub fun r hr => ⟨FA b, by simp, by rw [List.mem_singleton.mp hr]; exact Offset.sub b (by decide) (by decide)⟩

/-- What the preparation writes. -/
theorem prepW_sub : ∀ r ∈ [FA b, (⟨b + BitVec.ofNat 64 TA, 1920⟩ : Region)], Region.Sub r ⟨b, 8192⟩ :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub_base _ (by decide)
    · exact Offset.sub_base _ (by rw [TA_eq]; decide)

/-- **The preparation**: `d`, the table of `A` (slots 0–3), the static's address, the identity. -/
theorem strausPrep_ok {s : State} (h : VCtx b pk sig ch s) (hB : BStat b T s) (hT : s.syms bSym = T) :
    WP isa strausPrep s fun t =>
      WCtx b pk sig ch T (point (env s.mem b) 0 1 2 3) (decodeLE (bytesAt s.mem ch 64))
        (decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32)) t ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = Spec.Ed25519.identity ∧
      Rest (.s5 :: .a4 :: .s0 :: .s2 :: fclob) s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem t.mem := by
  unfold strausPrep
  refine WP.seq (WP.mono_syms (fieldCode_ok _ h.ctx.ctx h.ctx.ws) fun s1 ⟨k1, e1⟩ sy1 => ?_)
  have hc1 : Ctx8 b s1 := h.ctx.of_keep k1
  have d1 : env s1.mem b 16 = Spec.Ed25519.d := by rw [e1]; rfl
  have p1 : point (env s1.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 := by rw [e1]; rfl
  refine WP.seq (WP.mono_syms (aTable_ok hc1 d1) fun s2 ⟨r2, f2, hc2, tb2, d2⟩ sy2 => ?_)
  refine WP.seq (wp_lla' fun s3 u3 => WP.block_nil ?_)
  have hc3 : Ctx8 b s3 := hc2.of_rest (u3.rest (ws := [.s5]) (by decide)) (by decide)
  unfold constPoint
  refine WP.mono (fieldCode_ok _ hc3.ctx hc3.ws) fun t ⟨kt, et⟩ => ?_
  obtain ⟨c0, c16⟩ := env_constPoint (env s3.mem b) Spec.Ed25519.identity
  rw [← et] at c0 c16
  have rt : Rest (.s5 :: .a4 :: .s0 :: .s2 :: fclob) s t :=
    (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((u3.rest (by decide)).trans
      (kt.rest.mono (by decide))))
  have ft : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem t.mem := by
    refine (k1.frame.mono (by simp)).trans (f2.trans ?_)
    rw [← u3.mem]; exact kt.frame.mono (by simp)
  have hT3 : s3.gpr .s5 = T := by rw [u3.gpr, sy2, sy1, hT]
  refine ⟨⟨h.of_rest rt (by decide), hB.of_frame rt.rd ft prepW_sub, by rw [kt.rest.gpr _ (by decide), hT3],
    fun j hj => ?_, by rw [bytesAt_ws ft prepW_sub h.chD (by decide)],
    by rw [bytesAt_ws ft prepW_sub (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide)))
      (by decide)]⟩, by rw [c16, u3.mem, d2], c0, rt, ft⟩
  rw [tableAt_keep kt.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact entry_FA hj, u3.mem, tb2 j hj, p1]

/-- The windows' count `W`: 64 when the challenge's top 32 bytes are zero, else 128, with the
challenge below `16 ^ W`. -/
theorem windowCount_ok {s : State} (h : VCtx b pk sig ch s) :
    WP isa windowCount s fun t => Rest [.a4, .a5, .s1] s t ∧ t.mem = s.mem ∧
      ∃ W, (W = 64 ∨ W = 128) ∧ (W = 64 ↔ ∀ i < 32, s.mem (ch + BitVec.ofNat 64 (32 + i)) = 0) ∧
        t.gpr .s1 = BitVec.ofNat 64 W ∧ decodeLE (bytesAt s.mem ch 64) < 16 ^ W := by
  unfold windowCount
  refine WP.seq (WP.mono (challengeHigh_ok h.s11 fun i hi => by
      exact in_base (List.mem_append_left _ h.chR) (by omega) (by omega))
    fun s1 ⟨r1, m1, e1⟩ => ?_)
  refine WP.ite _ (eval_zero s1 .a4) (fun hb => ?_) (fun hb => ?_)
  · have hz := e1.mp (beq_iff_eq.mp hb)
    refine wp_li (by decide) fun t u => WP.block_nil
      ⟨(r1.mono (by decide)).trans (u.rest (by decide)), by rw [u.mem, m1], 64, .inl rfl,
        ⟨fun _ => hz, fun _ => rfl⟩, u.gpr, ?_⟩
    rw [decodeLE_low _ _ hz]
    exact lt_of_lt_of_eq (Proof.Ed25519.decodeLE_lt32 _ _) rfl
  · have hz : ¬ ∀ i < 32, s.mem (ch + BitVec.ofNat 64 (32 + i)) = 0 := fun hz =>
      absurd (beq_iff_eq.mpr (e1.mpr hz)) (by simpa using hb)
    refine wp_li (by decide) fun t u => WP.block_nil
      ⟨(r1.mono (by decide)).trans (u.rest (by decide)), by rw [u.mem, m1], 128, .inr rfl,
        ⟨fun h => absurd h (by decide), fun h => absurd h hz⟩, u.gpr, ?_⟩
    exact lt_of_lt_of_eq (Proof.Ed25519.decodeLE_lt64 _ _) rfl

/-- `-R` from the table at 7904 into slots 4–7; slots 0–3 kept. -/
theorem negR_ok {s : State} (hc : Ctx8 b s) :
    WP isa negR s fun t => Rest (.s0 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧ Ctx8 b t ∧
      point (env t.mem b) 4 5 6 7 = negPoint (tableAt s.mem b 7904) ∧
      point (env t.mem b) 0 1 2 3 = point (env s.mem b) 0 1 2 3 := by
  unfold negR
  refine WP.seq (scratchAddr_ok hc (o := 7904) (by decide) fun s1 r1 m1 e1 => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  refine WP.mono (pointFromTableQ_ok hc1 e1 (VG.Proof.X448.RISCV64.R64.al8 hc1.al (by decide))
    (fun k hk => by rw [Offset.add_add]; exact hc1.inR (by omega))
    (Offset.disjoint _ (.inr (by omega)) (by omega) (by omega))) fun s2 ⟨r2, f2, q2, k2⟩ => ?_
  have hc2 : Ctx8 b s2 := hc1.of_rest r2 (by decide)
  refine WP.mono (fieldCode_ok _ hc2.ctx hc2.ws) fun t ⟨kt, et⟩ => ⟨?_, ?_, hc2.of_keep kt, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans (kt.rest.mono (by decide)))
  · rw [← m1]
    exact (f2.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨FA b, by simp, Offset.sub _ (by omega) (by omega)⟩).trans kt.frame
  · rw [et, show point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] (env s2.mem b)) 4 5 6 7 =
      negPoint (point (env s2.mem b) 4 5 6 7) from rfl, q2, tableAt_shift, m1]
  · rw [et, show point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] (env s2.mem b)) 0 1 2 3 =
      point (env s2.mem b) 0 1 2 3 from rfl]
    simp only [point, k2 0 (by decide), k2 1 (by decide), k2 2 (by decide), k2 3 (by decide), m1]

end

/-- **`[S] B = R + [k] A`** by the windows: what `verifyDecode_ok` takes. -/
theorem rhs_ok : RhsOk := by
  intro b pk sig ch s PK RS h hB hPK hRS
  obtain ⟨Aa, hA⟩ := Proof.Ed25519.decodePoint_rep hPK
  obtain ⟨Ra, hR⟩ := Proof.Ed25519.decodePoint_rep hRS
  unfold verifyRhs
  refine WP.seq (WP.mono_syms (rhsRead_ok h.ctx) fun s1 ⟨r1, f1, p1⟩ sy1 => ?_)
  have h1 : VCtx b pk sig ch s1 := h.of_rest r1 (by decide)
  have hB1 : BStat b (s.syms bSym) s1 := hB.of_frame r1.rd f1 fa_sub
  refine WP.seq (WP.mono (strausPrep_ok h1 hB1 (congrFun sy1 bSym)) fun s2 ⟨h2, d2, p2, r2, f2⟩ => ?_)
  rw [p1] at h2
  refine WP.seq (WP.mono (windowCount_ok h2.vc) fun s3 ⟨r3, m3, W, hW1, _, e3, hK⟩ => ?_)
  have h3 := h2.of r3 (by decide) (by decide) (by rw [m3]; exact Frame.refl _ _)
  rw [h2.k] at hK
  have hS : decodeLE (bytesAt s1.mem (sig + BitVec.ofNat 64 32) 32) < 256 ^ 32 :=
    Proof.Ed25519.decodeLE_lt32 _ _
  have hv : RepP (point (env s3.mem b) 0 1 2 3)
      ((decodeLE (bytesAt s1.mem ch 64) / 16 ^ W) • Aa +
        (decodeLE (bytesAt s1.mem (sig + BitVec.ofNat 64 32) 32) / 16 ^ W) • (-baseAff)) := by
    rw [Nat.div_eq_of_lt hK, Proof.Ed25519.nibble_high_zero hS (by omega), zero_nsmul, zero_nsmul, add_zero,
      m3, p2]
    exact rep_repP Proof.Ed25519.identity_rep
  refine WP.seq (WP.mono (windows_ok (by omega) (by omega) h3 (by rw [m3]; exact d2) hA hS e3 hv) fun s4 ⟨h4, r4, f4, v4⟩ => ?_)
  refine WP.seq (WP.mono (negR_ok h4.vc.ctx) fun s5 ⟨r5, f5, hc5, q5, p5⟩ => ?_)
  rw [m3] at f4
  have hF4 : Frame [FA b, ⟨b + BitVec.ofNat 64 TA, 1920⟩] s.mem s4.mem :=
    (f1.mono (by simp)).trans (f2.trans (f4.mono (by simp)))
  refine WP.mono (pointEqual_ok hc5) fun t ⟨kt, et⟩ => ⟨?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans (kt.rest.mono (by decide))))))
  · refine (hF4.trans ((f5.trans kt.frame).mono (by simp))).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨FA b, by simp, fun _ h => h⟩
    · exact ⟨⟨b + BitVec.ofNat 64 1632, 4096⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · have tR : tableAt s4.mem b 7904 = tableAt s.mem b 7904 := tableAt_keep hF4 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact Offset.disjoint _ (.inr (by rw [TA_eq]; omega)) (by omega) (by rw [TA_eq]; omega)
    have hk : bytesAt s1.mem ch 64 = bytesAt s.mem ch 64 := bytesAt_ws f1 fa_sub h.chD (by decide)
    have hs : bytesAt s1.mem (sig + BitVec.ofNat 64 32) 32 = bytesAt s.mem (sig + BitVec.ofNat 64 32) 32 :=
      bytesAt_ws f1 fa_sub (h.sigD.sub_left (Offset.sub_base sig (d := 32) (n := 32) (by decide))) (by decide)
    rw [et, p5, q5, tR, Proof.Ed25519.window_equation hA hR (rep_repP v4) (rep_repP hR.neg), hk, hs]

end

end VG.Proof.Ed25519.RISCV64
