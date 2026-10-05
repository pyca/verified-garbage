import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-!
# The comb from tables in memory on AArch64: the selection by vectors

The entry of the magnitude `a` of table `j`, selected in constant time with
AdvSIMD (`tselect_ok`). Two groups of vector registers take the odd and the
even entries: each counts its entries in the two lanes of an index register
and compares them with the magnitude in the lanes of `v19`, a mask of all
ones exactly for entry `a`, under which it inserts the `c` pairs of words
of each entry it loads (`selEntryV_ok`). After every entry (`pairsV_ok`)
the groups hold entry `a`'s pairs in the group of its parity and zeros in
the other, and their `orr` holds entry `a`'s, or zeros if `a = 0`
(`passV_ok`). An entry of `n ≤ 4` pairs takes one pass, and `y` is then set
to `R` if `a = 0` (`selOneV_ok`), and both stored (`selXY1_ok`); else `x`'s
pairs are selected and stored, then `y`'s, reading the tables, which lie
outside the working space, after the first stores (`selXY2_ok`). `Z` is `R`
unless `a = 0`, as the scalar code sets it (`TCombSelect`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-! ## Single instructions -/

theorem wp_vop {s : State} {op : VOp} {d : VReg} {x : BitVec 128} {rest : List Instr}
    {Q : State → Prop} (h : op.eval s = some (d, x)) (hq : WP isa (.block rest) (s.setV d x) Q) :
    WP isa (.block (.vop op :: rest)) s Q := by
  rw [← List.singleton_append, WP.block_append_iff]
  have h₁ : WP isa (.block [.vop op]) s fun t => t = s.setV d x := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec, h, Option.map_some, runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left']
  exact WP.mono h₁ fun t ht => by subst ht; exact hq

theorem wp_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} {rest : List Instr} {Q : State → Prop}
    (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16)
    (hq : WP isa (.block rest) (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) Q) :
    WP isa (.block (.ldrq t n off :: rest)) s Q := by
  rw [← List.singleton_append, WP.block_append_iff]
  have h₁ : WP isa (.block [.ldrq t n off]) s fun u =>
      u = s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec, addr, ho, and_self, ite_true, Option.bind_some, State.load, hr,
      Option.map_some, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  exact WP.mono h₁ fun u hu => by subst hu; exact hq

theorem wp_strq {s : State} {t : VReg} {n : Reg} {off : Nat} {Q : State → Prop}
    (ho : off % 16 = 0 ∧ off < 4096 * 16) (hw : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16)
    (hq : Q { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) }) :
    WP isa (.block [.strq t n off]) s Q := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, ho, and_self, ite_true, Option.bind_some, State.store, hw,
    runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  exact hq

/-- `r = v`, keeping the vector registers. -/
theorem const64v_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

/-! ## What the vector code keeps -/

/-- The registers but `gs`, the vector registers but `ws`, the memory and the
regions. -/
structure VKeep (gs : List Reg) (ws : List VReg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ gs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, r ∉ ws → t.v r = s.v r

theorem VKeep.refl (gs : List Reg) (ws : List VReg) (s : State) : VKeep gs ws s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem VKeep.trans {gs : List Reg} {ws : List VReg} {s t u : State} (h₁ : VKeep gs ws s t)
    (h₂ : VKeep gs ws t u) : VKeep gs ws s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩

theorem VKeep.mono {gs gs' : List Reg} {ws ws' : List VReg} {s t : State} (h : VKeep gs ws s t)
    (hg : ∀ r ∈ gs, r ∈ gs') (hw : ∀ r ∈ ws, r ∈ ws') : VKeep gs' ws' s t :=
  ⟨fun r hr => h.gpr r fun hm => hr (hg r hm), h.mem, h.rd, h.wr, h.sp,
    fun r hr => h.v r fun hm => hr (hw r hm)⟩

theorem VKeep.setV (s : State) (d : VReg) (x : BitVec 128) : VKeep [] [d] s (s.setV d x) :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ hr =>
    RegUpd.v_setV_of_ne (s := s) x (by simpa only [List.mem_singleton] using hr)⟩

theorem VKeep.keeps {gs : List Reg} {ws : List VReg} {s t : State} (h : VKeep gs ws s t) :
    Keeps gs s t :=
  ⟨h.gpr, h.mem, h.rd, h.wr, h.sp⟩

/-! ## Lanes -/

/-- A word in both lanes. -/
abbrev dup2 (x : BitVec 64) : BitVec 128 := ofVDwords x x

theorem map2_dup2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 64) :
    VArr.d2.map2 f (dup2 x) (dup2 y) = dup2 (f 64 x y) := by
  simp only [VArr.map2, vdword_ofVDwords_0, vdword_ofVDwords_1]

theorem dup2_zero : dup2 0 = 0 := by decide

theorem cmeq_dup2 (x y : BitVec 64) :
    VArr.d2.map2 (fun w x y => if x = y then BitVec.allOnes w else 0) (dup2 x) (dup2 y) =
      if x = y then BitVec.allOnes 128 else 0 := by
  rw [map2_dup2]
  by_cases h : x = y
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem bit_mask (d n : BitVec 128) (c : Prop) [Decidable c] :
    VSelOp.bit.eval d n (if c then BitVec.allOnes 128 else 0) = if c then n else d := by
  by_cases hc : c
  · simp only [hc, ite_true, VSelOp.eval, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]
  · simp [hc, VSelOp.eval]

theorem ofNat_eq_iff {a m : Nat} (ha : a < 2 ^ 64) (hm : m < 2 ^ 64) :
    (BitVec.ofNat 64 m = BitVec.ofNat 64 a) ↔ a = m := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm] at this
    exact this.symm
  · intro h; rw [h]

theorem vdword_zero {e : Nat} : vdword 0 e = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp [vdword]

theorem ofVDwords_vdword (x : BitVec 128) : ofVDwords (vdword x 0) (vdword x 1) = x :=
  vec64_ext (vdword_ofVDwords_0 _ _) (vdword_ofVDwords_1 _ _)

/-- `[T, T + L)` within a region holds the ranges at offsets of `T` within it. -/
theorem Region.contains_off {r : Region} {T : Addr} {L d n : Nat} (h : r.Contains T L)
    (hd : d + n ≤ L) : r.Contains (T + BitVec.ofNat 64 d) n := by
  unfold Region.Contains at *
  have e : T + BitVec.ofNat 64 d - r.base = (T - r.base) + BitVec.ofNat 64 d := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 d),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((T - r.base).toNat + d % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le d (2 ^ 64)
  omega

/-! ## The groups -/

/-- The vector registers a group writes. -/
def _root_.VG.Impl.Weierstrass.AArch64.SelGroup.wr (G : SelGroup) : List VReg := G.idx :: G.mask :: (G.acc ++ G.ld)

/-- A group's registers apart. -/
structure GOk (G : SelGroup) (c : Nat) : Prop where
  acc : ∀ i < c, ∀ i' < c, i ≠ i' → G.acc.getD i .v0 ≠ G.acc.getD i' .v0
  ld : ∀ i < c, ∀ i' < c, i ≠ i' → G.ld.getD i .v20 ≠ G.ld.getD i' .v20
  acc_ld : ∀ i < c, ∀ i' < c, G.acc.getD i .v0 ≠ G.ld.getD i' .v20
  acc_o : ∀ i < c, G.acc.getD i .v0 ∉ [G.idx, G.mask, .v18, .v19, .v28]
  ld_o : ∀ i < c, G.ld.getD i .v20 ∉ [G.idx, G.mask, .v18, .v19, .v28]
  idx : G.idx ∉ [G.mask, .v18, .v19, .v28]
  mask : G.mask ∉ [.v18, .v19, .v28]
  acc_wr : ∀ i < c, G.acc.getD i .v0 ∈ G.wr
  ld_wr : ∀ i < c, G.ld.getD i .v20 ∈ G.wr

theorem selA_ok {c : Nat} (hc : c ≤ 4) : GOk (selA c) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> revert c <;> decide

theorem selB_ok {c : Nat} (hc : c ≤ 4) : GOk (selB c) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> revert c <;> decide

/-! The two groups apart, and from the registers around them. -/

theorem selB_acc_A : ∀ c ≤ 4, ∀ i < c, (selB c).acc.getD i .v0 ∉ (selA c).wr := by decide
theorem selB_idx_A : ∀ c ≤ 4, (selB c).idx ∉ (selA c).wr := by decide
theorem selA_acc_B : ∀ c ≤ 4, ∀ i < c, (selA c).acc.getD i .v0 ∉ (selB c).wr := by decide
theorem selA_idx_B : ∀ c ≤ 4, (selA c).idx ∉ (selB c).wr := by decide
theorem v18_AB : ∀ c ≤ 4, VReg.v18 ∉ (selA c).wr ++ (selB c).wr := by decide
theorem v19_AB : ∀ c ≤ 4, VReg.v19 ∉ (selA c).wr ++ (selB c).wr := by decide
theorem v28_AB : ∀ c ≤ 4, VReg.v28 ∉ (selA c).wr ++ (selB c).wr := by decide
theorem selA_B : ∀ c ≤ 4, ∀ i < c, ∀ i' < c, (selA c).acc.getD i .v0 ≠ (selB c).acc.getD i' .v0 := by
  decide
theorem selA_o : ∀ c ≤ 4, ∀ i < c,
    (selA c).acc.getD i .v0 ∉ [VReg.v16, .v17, .v18, .v19, .v20, .v28, .v30] := by decide
theorem selB_o : ∀ c ≤ 4, ∀ i < c,
    (selB c).acc.getD i .v0 ∉ [VReg.v16, .v17, .v18, .v19, .v20, .v28, .v30] := by decide
theorem selA_mem : ∀ c ≤ 4, ∀ i < c, (selA c).acc.getD i .v0 ∈ (selA c).acc := by decide
theorem selB_mem : ∀ c ≤ 4, ∀ i < c, (selB c).acc.getD i .v0 ∈ (selB c).acc := by decide

theorem not_mem_map_range {f : Nat → VReg} {k : Nat} {r : VReg} (h : ∀ i < k, f i ≠ r) :
    r ∉ (List.range k).map f := fun hm => by
  obtain ⟨i, hi, e⟩ := List.mem_map.mp hm
  exact h i (List.mem_range.mp hi) e

theorem map_range_sub {f : Nat → VReg} {k : Nat} {ws : List VReg} (h : ∀ i < k, f i ∈ ws) :
    ∀ r ∈ (List.range k).map f, r ∈ ws := fun r hm => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  exact h i (List.mem_range.mp hi)

/-- Pair `i` from byte `o` of entry `m` of the table at `x16`, of `n` words a
coordinate. -/
abbrev ldE (n o : Nat) (s : State) (m i : Nat) : BitVec 128 :=
  s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * n * (m - 1) + o + 16 * i)) 16

/-- The loads of `k` pairs at `o + 16 i`. -/
theorem ldsV_ok (n : Nat) {G : SelGroup} (hG : GOk G n) {s : State} {o : Nat}
    (ho : o + 16 * n ≤ 65536) (ho16 : o % 16 = 0)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (o + 16 * i)) 16) :
    ∀ k ≤ n, WP isa (.block ((List.range k).map fun i => Instr.ldrq (G.ld.getD i .v20) .x16 (o + 16 * i)))
      s fun t =>
      (∀ i < k, t.v (G.ld.getD i .v20) = s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (o + 16 * i)) 16) ∧
      VKeep [] ((List.range k).map fun i => G.ld.getD i .v20) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (ldsV_ok n hG ho ho16 hr k (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    refine wp_ldrq (by omega) (by rw [k₁.rd, k₁.wr, k₁.gpr _ List.not_mem_nil]; exact hr k (by omega))
      (WP.block_nil ⟨fun i hi => ?_, (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
        ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => List.mem_append_right _ h)⟩)
    rcases Nat.lt_or_ge i k with h | h
    · rw [RegUpd.v_setV_of_ne _ _ (hG.ld i (by omega) k (by omega) (by omega)), v₁ i h]
    · obtain rfl : i = k := by omega
      rw [RegUpd.v_setV_self, k₁.mem, k₁.gpr _ List.not_mem_nil]

/-- `BIT` of `k` pairs into the accumulators, under the mask. -/
theorem bselsV_ok (n : Nat) {G : SelGroup} (hG : GOk G n) {s : State} :
    ∀ k ≤ n, WP isa (.block ((List.range k).map fun i =>
        Instr.vop (.bsel .bit (G.acc.getD i .v0) (G.ld.getD i .v20) G.mask))) s fun t =>
      (∀ i < k, t.v (G.acc.getD i .v0) =
        VSelOp.bit.eval (s.v (G.acc.getD i .v0)) (s.v (G.ld.getD i .v20)) (s.v G.mask)) ∧
      VKeep [] ((List.range k).map fun i => G.acc.getD i .v0) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (bselsV_ok n hG k (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    have e1 : s₁.v (G.acc.getD k .v0) = s.v (G.acc.getD k .v0) :=
      k₁.v _ (not_mem_map_range fun i hi => hG.acc i (by omega) k (by omega) (by omega))
    have e2 : s₁.v (G.ld.getD k .v20) = s.v (G.ld.getD k .v20) :=
      k₁.v _ (not_mem_map_range fun i hi => hG.acc_ld i (by omega) k (by omega))
    have e3 : s₁.v G.mask = s.v G.mask :=
      k₁.v _ (not_mem_map_range fun i hi e => hG.acc_o i (by omega) (by rw [e]; simp))
    refine wp_vop (d := G.acc.getD k .v0) (x := VSelOp.bit.eval (s.v (G.acc.getD k .v0)) (s.v (G.ld.getD k .v20)) (s.v G.mask))
      (by simp only [VOp.eval, e1, e2, e3]) (WP.block_nil ⟨fun i hi => ?_,
        (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
        ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => List.mem_append_right _ h)⟩)
    rcases Nat.lt_or_ge i k with h | h
    · rw [RegUpd.v_setV_of_ne _ _ (hG.acc i (by omega) k (by omega) (by omega)), v₁ i h]
    · obtain rfl : i = k := by omega
      rw [RegUpd.v_setV_self]

/-- Entry `m` into a group: its index `m`, and each accumulator entry `m`'s
pair if `m` is the magnitude `a` in `v19`, else what it held. -/
theorem selEntryV_ok (K : TCombCfg) {o c : Nat} {G : SelGroup} (hG : GOk G c) {s : State}
    {a m : Nat} {c0 : BitVec 64} (ha : a < 2 ^ 64) (hm : m < 2 ^ 64) (hidx : s.v G.idx = dup2 c0)
    (hc0 : c0 + 2 = BitVec.ofNat 64 m) (h18 : s.v .v18 = dup2 2)
    (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) (ho : 16 * K.M.n * (m - 1) + o + 16 * c ≤ 65536)
    (ho16 : o % 16 = 0)
    (hr : ∀ i < c, InRegions (s.rd ++ s.wr)
      (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * (m - 1) + o + 16 * i)) 16) :
    WP isa (.block (K.selEntry o c G m)) s fun t =>
      t.v G.idx = dup2 (BitVec.ofNat 64 m) ∧
      (∀ i < c, t.v (G.acc.getD i .v0) =
        if a = m then ldE K.M.n o s m i else s.v (G.acc.getD i .v0)) ∧
      VKeep [] G.wr s t := by
  have hi19 : VReg.v19 ≠ G.idx := fun e => hG.idx (by rw [← e]; simp)
  have hmi : G.mask ≠ G.idx := fun e => hG.idx (by rw [e]; simp)
  rw [TCombCfg.selEntry]
  simp only [List.cons_append, List.nil_append]
  refine wp_vop (d := G.idx) (x := dup2 (BitVec.ofNat 64 m)) (by simp only [VOp.eval, hidx, h18, map2_dup2, hc0]) ?_
  refine wp_vop (d := G.mask) (x := if a = m then BitVec.allOnes 128 else 0)
    (by simp only [VOp.eval, RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ hi19, h19, cmeq_dup2,
      ofNat_eq_iff ha hm]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldsV_ok c hG (o := 16 * K.M.n * (m - 1) + o)
    (s := (s.setV G.idx (dup2 (BitVec.ofNat 64 m))).setV G.mask (if a = m then BitVec.allOnes 128 else 0))
    (by omega)
    (by rw [Nat.add_mod, Nat.mul_assoc, Nat.mul_mod_right, ho16]) (fun i hi => hr i hi) c (Nat.le_refl _))
    fun s₃ ⟨l₃, k₃⟩ => ?_
  refine WP.mono (bselsV_ok c hG (s := s₃) c (Nat.le_refl _)) fun t ⟨b₄, k₄⟩ => ?_
  have nld : ∀ r, (∀ i < c, G.ld.getD i .v20 ≠ r) →
      r ∉ (List.range c).map fun i => G.ld.getD i .v20 := fun _ h => not_mem_map_range h
  have nacc : ∀ r, (∀ i < c, G.acc.getD i .v0 ≠ r) →
      r ∉ (List.range c).map fun i => G.acc.getD i .v0 := fun _ h => not_mem_map_range h
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rw [k₄.v _ (nacc _ fun i hi e => hG.acc_o i hi (by rw [e]; simp)),
      k₃.v _ (nld _ fun i hi e => hG.ld_o i hi (by rw [e]; simp)),
      RegUpd.v_setV_of_ne _ _ (Ne.symm hmi), RegUpd.v_setV_self]
  · have hm₃ : s₃.v G.mask = if a = m then BitVec.allOnes 128 else 0 := by
      rw [k₃.v _ (nld _ fun i hi e => hG.ld_o i hi (by rw [e]; simp)), RegUpd.v_setV_self]
    have hacc : s₃.v (G.acc.getD i .v0) = s.v (G.acc.getD i .v0) := by
      rw [k₃.v _ (nld _ fun i' hi' e => hG.acc_ld i hi i' hi' e.symm),
        RegUpd.v_setV_of_ne _ _ fun e => hG.acc_o i hi (by rw [e]; simp),
        RegUpd.v_setV_of_ne _ _ fun e => hG.acc_o i hi (by rw [e]; simp)]
    rw [b₄ i hi, hacc, l₃ i hi, hm₃, bit_mask]
    rfl
  · have hw : ∀ i < c, G.ld.getD i .v20 ∈ G.wr := hG.ld_wr
    exact ((((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => by
        simp only [List.mem_singleton] at h; simp [SelGroup.wr, h]).trans
      ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => by
        simp only [List.mem_singleton] at h; simp [SelGroup.wr, h])).trans
      (k₃.mono (fun _ h => h) (map_range_sub hG.ld_wr))).trans
      (k₄.mono (fun _ h => h) (map_range_sub hG.acc_wr))

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (x y : α) : (if c then x else y) = x := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) (x y : α) : (if c then x else y) = y := by
  simp [h]

/-- `16 n (2 (q + 1))` split. -/
theorem mul_two_succ (N q : Nat) : N * (2 * (q + 1)) = N * (2 * q) + N + N := by
  rw [show 2 * (q + 1) = 2 * q + 1 + 1 by omega, Nat.mul_succ, Nat.mul_succ]

/-- The registers `rs` cleared. -/
theorem movisV_ok (s : State) : ∀ rs : List VReg,
    WP isa (.block (rs.map fun v => Instr.vop (.movi0 v))) s fun t =>
      (∀ r ∈ rs, t.v r = 0) ∧ VKeep [] rs s t
  | [] => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VKeep.refl _ _ _⟩
  | r :: rs => by
    rw [List.map_cons]
    refine wp_vop (d := r) (x := 0) (by simp only [VOp.eval]) ?_
    refine WP.mono (movisV_ok (s.setV r 0) rs) fun t ⟨z, k⟩ => ⟨fun q hq => ?_, ?_⟩
    · by_cases h : q ∈ rs
      · exact z q h
      · rw [List.mem_cons] at hq
        rcases hq with rfl | hq
        · rw [k.v _ h, RegUpd.v_setV_self]
        · exact absurd hq h
    · exact ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => by
        simp only [List.mem_singleton] at h; simp [h]).trans
        (k.mono (fun _ h => h) fun _ h => List.mem_cons_of_mem _ h)

/-- The groups combined: `A |= B`. -/
theorem orrsV_ok (n : Nat) (hn : n ≤ 4) {s : State} : ∀ k ≤ n,
    WP isa (.block ((List.range k).map fun i => Instr.vop (.logic .orr ((selA n).acc.getD i .v0)
      ((selA n).acc.getD i .v0) ((selB n).acc.getD i .v0)))) s fun t =>
      (∀ i < k, t.v ((selA n).acc.getD i .v0) =
        s.v ((selA n).acc.getD i .v0) ||| s.v ((selB n).acc.getD i .v0)) ∧
      VKeep [] ((List.range k).map fun i => (selA n).acc.getD i .v0) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    have hA := selA_ok hn
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (orrsV_ok n hn k (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    have e1 : s₁.v ((selA n).acc.getD k .v0) = s.v ((selA n).acc.getD k .v0) :=
      k₁.v _ (not_mem_map_range fun i hi => hA.acc i (by omega) k (by omega) (by omega))
    have e2 : s₁.v ((selB n).acc.getD k .v0) = s.v ((selB n).acc.getD k .v0) :=
      k₁.v _ (not_mem_map_range fun i hi => selA_B n hn i (by omega) k (by omega))
    refine wp_vop (d := (selA n).acc.getD k .v0)
      (x := s.v ((selA n).acc.getD k .v0) ||| s.v ((selB n).acc.getD k .v0))
      (by simp only [VOp.eval, e1, e2]) (WP.block_nil ⟨fun i hi => ?_,
        (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
        ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => List.mem_append_right _ h)⟩)
    rcases Nat.lt_or_ge i k with h | h
    · rw [RegUpd.v_setV_of_ne _ _ (hA.acc i (by omega) k (by omega) (by omega)), v₁ i h]
    · obtain rfl : i = k := by omega
      rw [RegUpd.v_setV_self]

/-- Stores of `k` vector registers `f i` at `o + 16 i` of the working space. -/
theorem qstoresV_ok {size : Nat} (f : Nat → VReg) {s : State} {base : Addr} {o : Nat}
    (hs : Scr s base size) (ho16 : o % 16 = 0) : ∀ k, o + 16 * k ≤ size →
    WP isa (.block ((List.range k).map fun i => Instr.strq (f i) .x0 (o + 16 * i))) s fun t =>
      (∀ j < 2 * k, word t.mem base (o + 8 * j) = vdword (s.v (f (j / 2))) (j % 2)) ∧
      KeepRegs [] s t ∧ t.v = s.v ∧ Outside base o (16 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have he := hs.enc
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (qstoresV_ok f hs ho16 k (by omega)) fun s₁ ⟨w₁, k₁, v₁, O₁⟩ => ?_
    have hx0 : s₁.gpr .x0 = base := by rw [k₁.gpr _ List.not_mem_nil, hs.x0]
    refine wp_strq (by omega) (by rw [hx0, k₁.wr]; exact ⟨_, hs.wr, hs.contains (by omega) (by decide)⟩) ?_
    rw [hx0, v₁, ← ofVDwords_vdword (s.v (f k)), write16_dwords, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have Oa := writeW_outside s₁.mem base (d := o + 16 * k) (vdword (s.v (f k)) 0) (by omega)
    have Ob := writeW_outside (s₁.mem.writeW (off base (o + 16 * k)) (vdword (s.v (f k)) 0)) base
      (d := o + 16 * k + 8) (vdword (s.v (f k)) 1) (by omega)
    refine ⟨fun j hj => ?_, k₁.trans ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
    · rcases Nat.lt_or_ge j (2 * k) with h | h
      · rw [Ob.word (by omega) (by omega), Oa.word (by omega) (by omega), w₁ j h]
      · rcases Nat.lt_or_ge j (2 * k + 1) with h' | h'
        · obtain rfl : j = 2 * k := by omega
          rw [Ob.word (by omega) (by omega), show o + 8 * (2 * k) = o + 16 * k by omega, word_writeW_self,
            show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
        · obtain rfl : j = 2 * k + 1 := by omega
          rw [show o + 8 * (2 * k + 1) = o + 16 * k + 8 by omega, word_writeW_self,
            show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega]
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((Oa.mono (by omega) (by omega)).trans (Ob.mono (by omega) (by omega)))

/-- The groups' values combined: entry `a`'s pair if `a ≥ 1`, else zero. -/
theorem orr_par {a H : Nat} (ha : a ≤ H) (L : BitVec 128) :
    ((if 1 ≤ a ∧ a ≤ H ∧ a % 2 = 1 then L else 0) ||| (if 1 ≤ a ∧ a ≤ H ∧ a % 2 = 0 then L else 0)) =
      if 1 ≤ a then L else 0 := by
  by_cases h : 1 ≤ a <;> by_cases hp : a % 2 = 1
  · simp (disch := omega) only [ite_t, ite_f]; simp
  · simp (disch := omega) only [ite_t, ite_f]; simp
  · simp (disch := omega) only [ite_f]; simp
  · simp (disch := omega) only [ite_f]; simp

/-- A word of a loaded pair. -/
theorem vdword_ldE (n o : Nat) (s : State) (a i : Nat) {e : Nat} (he : e < 2) :
    vdword (ldE n o s a i) e = word s.mem (s.gpr .x16) (16 * n * (a - 1) + o + 16 * i + 8 * e) := by
  rw [ldE, vdword_read16 _ _ he, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem zero_eq_iff {a : Nat} (ha : a < 2 ^ 64) : ((0 : BitVec 64) = BitVec.ofNat 64 a) ↔ a = 0 :=
  ofNat_eq_iff (m := 0) ha (by decide)

/-- Words given word by word. -/
theorem wordsVal_of_words₂ {m m' : Mem} {b b' : Addr} : ∀ (o o' k : Nat),
    (∀ j < k, word m b (o + 8 * j) = word m' b' (o' + 8 * j)) → wordsVal m b o k = wordsVal m' b' o' k
  | _, _, 0, _ => rfl
  | o, o', k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [wordsVal, wordsVal, h0, wordsVal_of_words₂ (o + 8) (o' + 8) k fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show o + 8 * (j + 1) = o + 8 + 8 * j by omega,
        show o' + 8 * (j + 1) = o' + 8 + 8 * j by omega] at this]



/-- The pairs of entries `1 … 2q`: the odd ones into `A`, the even ones into
`B`, `c` pairs from byte `o` each. -/
theorem pairsV_ok (K : TCombCfg) {o c : Nat} (hc : c ≤ 4) (hoc : o + 16 * c ≤ 16 * K.M.n)
    (ho16 : o % 16 = 0) {a : Nat} (ha : a < 2 ^ 64) {s : State}
    (h18 : s.v .v18 = dup2 2) (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a))
    {c0 : BitVec 64} (h17 : s.v .v17 = dup2 c0) (hc0 : c0 + 2 = BitVec.ofNat 64 1)
    (h30 : s.v .v30 = dup2 (BitVec.ofNat 64 0))
    (hA : ∀ i < c, s.v ((selA c).acc.getD i .v0) = 0)
    (hB : ∀ i < c, s.v ((selB c).acc.getD i .v0) = 0) :
    ∀ q, 2 * q < 2 ^ 64 → 16 * K.M.n * (2 * q) ≤ 65536 →
      (∀ e < 2 * q, ∀ i < c, InRegions (s.rd ++ s.wr)
        (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * e + o + 16 * i)) 16) →
      WP isa (.block ((List.range q).flatMap fun m =>
        K.selEntry o c (selA c) (2 * m + 1) ++ K.selEntry o c (selB c) (2 * m + 2))) s fun t =>
        t.v .v18 = dup2 2 ∧ t.v .v19 = dup2 (BitVec.ofNat 64 a) ∧
        (∃ c', t.v .v17 = dup2 c' ∧ c' + 2 = BitVec.ofNat 64 (2 * q + 1)) ∧
        t.v .v30 = dup2 (BitVec.ofNat 64 (2 * q)) ∧
        (∀ i < c, t.v ((selA c).acc.getD i .v0) =
          if 1 ≤ a ∧ a ≤ 2 * q ∧ a % 2 = 1 then ldE K.M.n o s a i else 0) ∧
        (∀ i < c, t.v ((selB c).acc.getD i .v0) =
          if 1 ≤ a ∧ a ≤ 2 * q ∧ a % 2 = 0 then ldE K.M.n o s a i else 0) ∧
        VKeep [] ((selA c).wr ++ (selB c).wr) s t
  | 0, _, _, _ => WP.block_nil ⟨h18, h19, ⟨c0, h17, hc0⟩, h30,
      fun i hi => by rw [hA i hi]; simp (disch := omega) only [ite_f],
      fun i hi => by rw [hB i hi]; simp (disch := omega) only [ite_f],
      VKeep.refl _ _ _⟩
  | q + 1, hq, ho, hr => by
    have hA' := selA_ok hc
    have hB' := selB_ok hc
    have ho' := mul_two_succ (16 * K.M.n) q
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (pairsV_ok K hc hoc ho16 ha h18 h19 h17 hc0 h30 hA hB q (by omega) (by omega)
      fun e he i hi => hr e (by omega) i hi) fun s₁ ⟨a18, a19, ⟨c₁, a17, ac₁⟩, a30, vA, vB, k₁⟩ => ?_
    have n18 := v18_AB _ hc
    have n19 := v19_AB _ hc
    rw [WP.block_append_iff]
    refine WP.mono (selEntryV_ok K hA' (s := s₁) (m := 2 * q + 1) ha (by omega) a17 ac₁ a18 a19
      (by rw [show 2 * q + 1 - 1 = 2 * q by omega]; omega) ho16 fun i hi => by
        rw [k₁.rd, k₁.wr, k₁.gpr _ List.not_mem_nil, show 2 * q + 1 - 1 = 2 * q by omega]
        exact hr (2 * q) (by omega) i hi) fun s₂ ⟨i₂, v₂, k₂⟩ => ?_
    have b18 : s₂.v .v18 = dup2 2 := by
      rw [k₂.v _ fun h => n18 (List.mem_append_left _ h), a18]
    have b19 : s₂.v .v19 = dup2 (BitVec.ofNat 64 a) := by
      rw [k₂.v _ fun h => n19 (List.mem_append_left _ h), a19]
    refine WP.mono (selEntryV_ok K hB' (s := s₂) (m := 2 * q + 2) (c0 := BitVec.ofNat 64 (2 * q)) ha
      (by omega) (by rw [k₂.v _ (selB_idx_A _ hc)]; exact a30)
      (by rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]) b18 b19
      (by rw [show 2 * q + 2 - 1 = 2 * q + 1 by omega, Nat.mul_succ]; omega) ho16 fun i hi => by
        rw [k₂.rd, k₂.wr, k₂.gpr _ List.not_mem_nil, k₁.rd, k₁.wr, k₁.gpr _ List.not_mem_nil,
          show 2 * q + 2 - 1 = 2 * q + 1 by omega]
        exact hr (2 * q + 1) (by omega) i hi) fun t ⟨i₃, v₃, k₃⟩ => ?_
    have hld : ∀ m i, ldE K.M.n o s₂ m i = ldE K.M.n o s m i ∧ ldE K.M.n o s₁ m i = ldE K.M.n o s m i :=
      fun m i => by
        refine ⟨?_, ?_⟩ <;>
          simp only [ldE, k₂.mem, k₂.gpr _ List.not_mem_nil, k₁.mem, k₁.gpr _ List.not_mem_nil]
    refine ⟨?_, ?_, ⟨BitVec.ofNat 64 (2 * q + 1), ?_, ?_⟩, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · rw [k₃.v _ fun h => n18 (List.mem_append_right _ h), b18]
    · rw [k₃.v _ fun h => n19 (List.mem_append_right _ h), b19]
    · exact (k₃.v _ (selA_idx_B _ hc)).trans i₂
    · rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat,
        show 2 * q + 1 + 2 = 2 * (q + 1) + 1 by omega]
    · rw [show 2 * (q + 1) = 2 * q + 2 by omega]; exact i₃
    · rw [k₃.v _ (selA_acc_B _ hc i hi), v₂ i hi, vA i hi, (hld _ _).2]
      by_cases h : a = 2 * q + 1
      · subst h; simp (disch := omega) only [ite_t, ↓reduceIte]
      · rw [ite_f h]
        by_cases h' : 1 ≤ a ∧ a ≤ 2 * q ∧ a % 2 = 1
        · simp (disch := omega) only [ite_t]
        · simp (disch := omega) only [ite_f]
    · rw [v₃ i hi, k₂.v _ (selB_acc_A _ hc i hi), vB i hi, (hld _ _).1]
      by_cases h : a = 2 * q + 2
      · subst h; simp (disch := omega) only [ite_t, ↓reduceIte]
      · rw [ite_f h]
        by_cases h' : 1 ≤ a ∧ a ≤ 2 * q ∧ a % 2 = 0
        · simp (disch := omega) only [ite_t]
        · simp (disch := omega) only [ite_f]
    · exact (k₁.trans (k₂.mono (fun _ h => h) fun _ h => List.mem_append_left _ h)).trans
        (k₃.mono (fun _ h => h) fun _ h => List.mem_append_right _ h)

theorem VKeep.setV' {ws : List VReg} (s : State) {d : VReg} (x : BitVec 128) (h : d ∈ ws) :
    VKeep [] ws s (s.setV d x) :=
  (VKeep.setV s d x).mono (fun _ h => h) fun _ h' => by
    rw [List.mem_singleton] at h'; rw [h']; exact h

/-- The broadcasts: the magnitude in both lanes of `v19`, `x5` in both of
`v28` and `2 x5` in both of `v18`. -/
theorem bcastV_ok (s : State) :
    WP isa (.block selBcast) s fun t =>
      t.v .v19 = dup2 (s.gpr .x2) ∧ t.v .v28 = dup2 (s.gpr .x5) ∧
      t.v .v18 = dup2 (s.gpr .x5 + s.gpr .x5) ∧ VKeep [] [.v18, .v19, .v28] s t := by
  apply WP.of_runBlock
  simp only [selBcast, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval, Option.map_some,
    RegUpd.v_setV, RegUpd.gpr_setV, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  rw [map2_dup2]
  refine ⟨trivial, trivial, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.v_setV, hr.1, hr.2.1, hr.2.2, ↓reduceIte]

theorem regs_not_acc : ∀ c ≤ 4, ∀ r ∈ [VReg.v16, .v17, .v18, .v19, .v20, .v28, .v30],
    r ∉ (selA c).acc ++ (selB c).acc := by decide

/-- A pass: `A`'s `c` accumulators hold entry `a`'s pairs from byte `o` if
`1 ≤ a ≤ H`, else zeros. -/
theorem passV_ok (K : TCombCfg) {o c : Nat} (hc : c ≤ 4) (hoc : o + 16 * c ≤ 16 * K.M.n)
    (ho16 : o % 16 = 0) {a : Nat} (ha : a ≤ K.H) (hH2 : K.H % 2 = 0) (hH : 16 * K.M.n * K.H ≤ 65536)
    (hHlt : K.H < 2 ^ 64) {s : State}
    (h18 : s.v .v18 = dup2 2) (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) (h28 : s.v .v28 = dup2 1)
    (hr : ∀ e < K.H, ∀ i < c, InRegions (s.rd ++ s.wr)
      (s.gpr .x16 + BitVec.ofNat 64 (16 * K.M.n * e + o + 16 * i)) 16) :
    WP isa (.block (K.selPass o c)) s fun t =>
      (∀ i < c, t.v ((selA c).acc.getD i .v0) = if 1 ≤ a then ldE K.M.n o s a i else 0) ∧
      t.v .v18 = s.v .v18 ∧ t.v .v19 = s.v .v19 ∧ t.v .v28 = s.v .v28 ∧
      VKeep [] ((selA c).wr ++ (selB c).wr) s t := by
  have hA := selA_ok hc
  have ha64 : a < 2 ^ 64 := by omega
  have h2H : 2 * (K.H / 2) = K.H := by omega
  have nAB := regs_not_acc _ hc
  rw [TCombCfg.selPass]
  iterate 3 rw [WP.block_append_iff]
  refine wp_vop (d := .v17) (x := 0) (by simp only [VOp.eval, selA]) ?_
  refine wp_vop (d := .v17) (x := dup2 (0 - 1))
    (by simp only [VOp.eval, selA, RegUpd.v_setV_self,
      RegUpd.v_setV_of_ne _ _ (show VReg.v28 ≠ .v17 by decide), h28]
        rw [← dup2_zero, map2_dup2]) ?_
  refine wp_vop (d := .v30) (x := 0) (by simp only [VOp.eval, selB]) (WP.block_nil ?_)
  have k₁ : VKeep [] ((selA c).wr ++ (selB c).wr) s
      (((s.setV .v17 0).setV .v17 (dup2 (0 - 1))).setV .v30 0) :=
    ((VKeep.setV' _ _ (by simp [SelGroup.wr, selA])).trans (VKeep.setV' _ _ (by simp [SelGroup.wr, selA]))).trans
      (VKeep.setV' _ _ (by simp [SelGroup.wr, selB]))
  have i17 : (((s.setV .v17 0).setV .v17 (dup2 (0 - 1))).setV .v30 0).v .v17 = dup2 (0 - 1) := by
    rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_setV_self]
  have i30 : (((s.setV .v17 0).setV .v17 (dup2 (0 - 1))).setV .v30 0).v .v30 = dup2 (BitVec.ofNat 64 0) := by
    rw [RegUpd.v_setV_self]; exact dup2_zero.symm
  generalize ((s.setV .v17 0).setV .v17 (dup2 (0 - 1))).setV .v30 0 = s₁ at k₁ i17 i30 ⊢
  have c₁ : ∀ r ∈ [VReg.v18, .v19, .v28], s₁.v r = s.v r := fun r hr => k₁.v r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact v18_AB _ hc
    · exact v19_AB _ hc
    · exact v28_AB _ hc)
  refine WP.mono (movisV_ok s₁ _) fun s₂ ⟨z₂, k₂⟩ => ?_
  have c₂ : ∀ r ∈ [VReg.v16, .v17, .v18, .v19, .v20, .v28, .v30], s₂.v r = s₁.v r := fun r hr =>
    k₂.v r (nAB r hr)
  refine WP.mono (pairsV_ok K hc hoc ho16 ha64 (s := s₂) (c0 := 0 - 1)
    (by rw [c₂ _ (by simp), c₁ _ (by simp), h18]) (by rw [c₂ _ (by simp), c₁ _ (by simp), h19])
    (by rw [c₂ _ (by simp), i17]) (by decide) (by rw [c₂ _ (by simp), i30])
    (fun i hi => z₂ _ (List.mem_append_left _ (selA_mem _ hc i hi)))
    (fun i hi => z₂ _ (List.mem_append_right _ (selB_mem _ hc i hi)))
    (K.H / 2) (by omega) (by rw [h2H]; omega) fun e he i hi => by
      rw [k₂.rd, k₂.wr, k₂.gpr _ List.not_mem_nil, k₁.rd, k₁.wr, k₁.gpr _ List.not_mem_nil]
      exact hr e (by omega) i hi) fun s₃ ⟨p18, p19, _, _, pA, pB, k₃⟩ => ?_
  rw [h2H] at pA pB
  refine WP.mono (orrsV_ok c hc (s := s₃) c (Nat.le_refl _)) fun t ⟨o₄, k₄⟩ => ?_
  have hld : ∀ i, ldE K.M.n o s₂ a i = ldE K.M.n o s a i := fun i => by
    simp only [ldE, k₂.mem, k₂.gpr _ List.not_mem_nil, k₁.mem, k₁.gpr _ List.not_mem_nil]
  have nacc : ∀ r ∈ [VReg.v18, .v19, .v28], r ∉ (List.range c).map fun i => (selA c).acc.getD i .v0 :=
    fun r hr => not_mem_map_range fun i hi e => selA_o _ hc i hi (by
      rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp)
  have kv : ∀ r ∈ [VReg.v18, .v19, .v28], t.v r = s.v r := fun r hr => by
    rw [k₄.v _ (nacc r hr), k₃.v _ ?_, c₂ _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp), c₁ r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact v18_AB _ hc
    · exact v19_AB _ hc
    · exact v28_AB _ hc
  refine ⟨fun i hi => ?_, kv _ (by simp), kv _ (by simp), kv _ (by simp), ?_⟩
  · rw [o₄ i hi, pA i hi, pB i hi, orr_par ha, hld]
  · refine (((k₁.trans (k₂.mono (fun _ h => h) fun _ h => ?_)).trans k₃).trans
      (k₄.mono (fun _ h => h) (map_range_sub fun i hi => ?_)))
    · rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (by simp [SelGroup.wr, h])
      · exact List.mem_append_right _ (by simp [SelGroup.wr, h])
    · exact List.mem_append_left _ (hA.acc_wr i hi)

/-- `A`'s accumulators `h + i` set to `R`'s pairs under the mask in `v16`. -/
theorem fixV_ok (K : TCombCfg) {c h : Nat} (hc : c ≤ 4) {s : State} : ∀ k, h + k ≤ c →
    WP isa (.block ((List.range k).flatMap fun i =>
      const64 .x6 (wordOf K.one (2 * i)) ++ ([.vop (.ins .d2 .v20 0 .x6)] : List Instr) ++
      const64 .x6 (wordOf K.one (2 * i + 1)) ++ ([.vop (.ins .d2 .v20 1 .x6),
      .vop (.bsel .bit ((selA c).acc.getD (h + i) .v0) .v20 .v16)] : List Instr))) s fun t =>
      (∀ i < k, t.v ((selA c).acc.getD (h + i) .v0) =
        VSelOp.bit.eval (s.v ((selA c).acc.getD (h + i) .v0))
          (ofVDwords (wordOf K.one (2 * i)) (wordOf K.one (2 * i + 1))) (s.v .v16)) ∧
      VKeep [.x6] (.v20 :: (List.range k).map fun i => (selA c).acc.getD (h + i) .v0) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    have hA := selA_ok hc
    have ho := selA_o _ hc (h + k) (by omega)
    have h20 : (selA c).acc.getD (h + k) .v0 ≠ .v20 := fun e => ho (by rw [e]; simp)
    have h16 : (selA c).acc.getD (h + k) .v0 ≠ .v16 := fun e => ho (by rw [e]; simp)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (fixV_ok K hc k (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
    have e1 : s₁.v ((selA c).acc.getD (h + k) .v0) = s.v ((selA c).acc.getD (h + k) .v0) :=
      k₁.v _ (by
        simp only [List.mem_cons, not_or]
        exact ⟨h20, not_mem_map_range fun i hi e => hA.acc _ (by omega) _ (by omega) (by omega) e⟩)
    have e16 : s₁.v .v16 = s.v .v16 := k₁.v _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨by decide, not_mem_map_range fun i hi e =>
        selA_o _ hc (h + i) (by omega) (by rw [e]; simp)⟩)
    rw [List.append_assoc, List.append_assoc, List.singleton_append, WP.block_append_iff]
    refine WP.mono (const64v_ok s₁ .x6 _) fun s₂ ⟨g₂, kk₂, vv₂⟩ => ?_
    refine wp_vop (d := .v20) (x := setLane (s₁.v .v20) 64 0 (wordOf K.one (2 * k)))
      (by simp only [VOp.eval, vv₂, g₂, Nat.zero_lt_two, ite_true]) ?_
    rw [WP.block_append_iff]
    refine WP.mono (const64v_ok _ .x6 _) fun s₃ ⟨g₃, kk₃, vv₃⟩ => ?_
    refine wp_vop (d := .v20) (x := ofVDwords (wordOf K.one (2 * k)) (wordOf K.one (2 * k + 1)))
      (by simp only [VOp.eval, vv₃, g₃, RegUpd.v_setV_self, Nat.one_lt_two, ite_true, setLane_two]) ?_
    refine wp_vop (d := (selA c).acc.getD (h + k) .v0)
      (x := VSelOp.bit.eval (s.v ((selA c).acc.getD (h + k) .v0))
        (ofVDwords (wordOf K.one (2 * k)) (wordOf K.one (2 * k + 1))) (s.v .v16))
      (by simp only [VOp.eval, RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ h20,
        RegUpd.v_setV_of_ne _ _ (show VReg.v16 ≠ .v20 by decide), vv₃, vv₂, e1, e16])
      (WP.block_nil ⟨fun i hi => ?_, ?_⟩)
    · rcases Nat.lt_or_ge i k with hik | hik
      · have hi' := selA_o _ hc (h + i) (by omega)
        rw [RegUpd.v_setV_of_ne _ _ (hA.acc _ (by omega) _ (by omega) (by omega)),
          RegUpd.v_setV_of_ne _ _ fun e => hi' (by rw [e]; simp), vv₃,
          RegUpd.v_setV_of_ne _ _ fun e => hi' (by rw [e]; simp), vv₂, v₁ i hik]
      · obtain rfl : i = k := by omega
        rw [RegUpd.v_setV_self]
    · have kst : VKeep [.x6] [.v20, (selA c).acc.getD (h + k) .v0] s₁
          (((s₃.setV .v20 (ofVDwords (wordOf K.one (2 * k)) (wordOf K.one (2 * k + 1)))).setV
            ((selA c).acc.getD (h + k) .v0)
            (VSelOp.bit.eval (s.v ((selA c).acc.getD (h + k) .v0))
              (ofVDwords (wordOf K.one (2 * k)) (wordOf K.one (2 * k + 1))) (s.v .v16)))) :=
        ⟨fun r hr => (kk₃.gpr r hr).trans (kk₂.gpr r hr), kk₃.mem.trans kk₂.mem, kk₃.rd.trans kk₂.rd,
          kk₃.wr.trans kk₂.wr, kk₃.sp.trans kk₂.sp, fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            rw [RegUpd.v_setV_of_ne _ _ hr.2, RegUpd.v_setV_of_ne _ _ hr.1, vv₃,
              RegUpd.v_setV_of_ne _ _ hr.1, vv₂]⟩
      refine (k₁.mono (fun _ h => h) fun r h => ?_).trans (kst.mono (fun _ h => h) fun r h => ?_)
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ ?_
          rw [List.map_append]; exact List.mem_append_left _ h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ ?_
          rw [List.map_append]; exact List.mem_append_right _ (by simp)

/-- `y`'s pairs: the mask of `a = 0` into `v16`, and `A`'s accumulators
`h … h + k - 1` set to `R`'s pairs if `a = 0`. -/
theorem selOneV_ok (K : TCombCfg) {c h k : Nat} (hc : c ≤ 4) (hk : h + k ≤ c) {a : Nat}
    (ha : a < 2 ^ 64) {s : State} (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) :
    WP isa (.block (K.selOne c h k)) s fun t =>
      (∀ i < k, t.v ((selA c).acc.getD (h + i) .v0) = if a = 0 then
        ofVDwords (wordOf K.one (2 * i)) (wordOf K.one (2 * i + 1))
        else s.v ((selA c).acc.getD (h + i) .v0)) ∧
      VKeep [.x6] (.v16 :: .v20 :: (List.range k).map fun i => (selA c).acc.getD (h + i) .v0) s t := by
  rw [TCombCfg.selOne, WP.block_append_iff]
  refine wp_vop (d := .v16) (x := 0) (by simp only [VOp.eval]) ?_
  refine wp_vop (d := .v16) (x := if (0 : BitVec 64) = BitVec.ofNat 64 a then BitVec.allOnes 128 else 0)
    (by simp only [VOp.eval, RegUpd.v_setV_self,
      RegUpd.v_setV_of_ne _ _ (show VReg.v19 ≠ .v16 by decide), h19]
        rw [← dup2_zero, cmeq_dup2, dup2_zero]) (WP.block_nil ?_)
  refine WP.mono (fixV_ok K hc (h := h) k hk) fun t ⟨f, kt⟩ => ⟨fun i hi => ?_, ?_⟩
  · have ho := selA_o _ hc (h + i) (by omega)
    rw [f i hi, RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ fun e => ho (by rw [e]; simp),
      RegUpd.v_setV_of_ne _ _ fun e => ho (by rw [e]; simp), bit_mask]
    by_cases h0 : a = 0
    · rw [ite_t ((zero_eq_iff ha).mpr h0), ite_t h0]
    · rw [ite_f ((zero_eq_iff ha).not.mpr h0), ite_f h0]
  · exact (((VKeep.setV' _ _ (List.mem_cons_self ..)).trans (VKeep.setV' _ _ (List.mem_cons_self ..))).mono
      (fun _ h => absurd h List.not_mem_nil) fun _ h => h).trans
      (kt.mono (fun _ h => h) fun _ h => List.mem_cons_of_mem _ h)

/-- The pairs of every entry of a table in one region. -/
theorem tbl_region {rs : List Region} {X : Addr} {n H o c : Nat} (hreg : InRegions rs X (16 * n * H))
    (hoc : o + 16 * c ≤ 16 * n) :
    ∀ e < H, ∀ i < c, InRegions rs (X + BitVec.ofNat 64 (16 * n * e + o + 16 * i)) 16 :=
  fun e he i hi => by
    obtain ⟨r, hr, hc⟩ := hreg
    refine ⟨r, hr, Region.contains_off hc ?_⟩
    have := Nat.mul_le_mul_left (16 * n) (show e + 1 ≤ H by omega)
    rw [Nat.mul_succ] at this
    omega

/-- What the selection of `x` and `y` leaves: entry `a`'s `x` and `y` of the
table at `X` in `E` if `a ≥ 1`, else `(0, R)`. -/
structure SelXY (K : TCombCfg) (base : Addr) (size : Nat) (s : State) (a : Nat) (X : Addr)
    (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n =
    if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1)) K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n =
    if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one
  keep : KeepRegs [.x6] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n)] s.mem t.mem
  scr : Scr t base size

/-- `x` and `y` from word equations. -/
theorem selXY_vals (K : TCombCfg) {t : State} {base X : Addr} {a : Nat} (hone : K.one < 2 ^ (64 * K.M.n))
    {Mx My : Mem} (wx : ∀ j < K.M.n, word t.mem base (K.E.x + 8 * j) =
      if 1 ≤ a then word Mx X (16 * K.M.n * (a - 1) + 8 * j) else 0)
    (wy : ∀ j < K.M.n, word t.mem base (K.E.y + 8 * j) =
      if 1 ≤ a then word My X (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j) else wordOf K.one j) :
    wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ a then wordsVal Mx X (16 * K.M.n * (a - 1)) K.M.n else 0) ∧
    wordsVal t.mem base K.E.y K.M.n =
      (if 1 ≤ a then wordsVal My X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one) := by
  constructor
  · by_cases h : 1 ≤ a
    · rw [ite_t h]
      exact wordsVal_of_words₂ _ _ _ fun jj hj => by rw [wx jj hj, ite_t h]
    · rw [ite_f h]
      exact wordsVal_of_shifts _ _ _ _ 0 (Nat.two_pow_pos _) fun jj hj => by
        rw [wx jj hj, ite_f h]; simp
  · by_cases h : 1 ≤ a
    · rw [ite_t h]
      exact wordsVal_of_words₂ _ _ _ fun jj hj => by rw [wy jj hj, ite_t h, Nat.add_assoc]
    · rw [ite_f h]
      exact wordsVal_of_shifts _ _ _ _ _ hone fun jj hj => by rw [wy jj hj, ite_f h]; rfl

/-- An entry of `n ≤ 4` pairs: one pass, `y = R` if `a = 0`, and both stored. -/
theorem selXY1_ok (K : TCombCfg) (hn : K.M.n ≤ 4) (hn2 : K.M.n % 2 = 0) {s : State} {base : Addr}
    {size : Nat} (hs : Scr s base size) {a : Nat} {X : Addr} (ha : a ≤ K.H) (hH2 : K.H % 2 = 0)
    (hH : 16 * K.M.n * K.H ≤ 32768) (hHlt : K.H < 2 ^ 64) (h16 : s.gpr .x16 = X)
    (h18 : s.v .v18 = dup2 2) (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) (h28 : s.v .v28 = dup2 1)
    (hEx : K.E.x + 8 * K.M.n ≤ size) (hEy : K.E.y + 8 * K.M.n ≤ size)
    (hE16 : K.E.x % 16 = 0 ∧ K.E.y % 16 = 0)
    (axy : K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n))
    (hreg : InRegions (s.rd ++ s.wr) X (16 * K.M.n * K.H)) :
    WP isa (.block (K.selPass 0 K.M.n ++ K.selOne K.M.n (K.M.n / 2) (K.M.n / 2) ++
      selStore K.M.n 0 (K.M.n / 2) K.E.x ++ selStore K.M.n (K.M.n / 2) (K.M.n / 2) K.E.y)) s
      (SelXY K base size s a X) := by
  have hnw := hs.nowrap
  have hA := selA_ok hn
  have ha64 : a < 2 ^ 64 := by omega
  iterate 3 rw [WP.block_append_iff]
  refine WP.mono (passV_ok K (o := 0) (c := K.M.n) hn (by omega) (by decide) ha hH2 (by omega) hHlt
    h18 h19 h28 fun e he i hi => by rw [h16]; exact tbl_region hreg (by omega) e he i hi)
    fun s₁ ⟨v₁, _, a19, _, k₁⟩ => ?_
  refine WP.mono (selOneV_ok K (c := K.M.n) (h := K.M.n / 2) (k := K.M.n / 2) hn (by omega) ha64
    (by rw [a19, h19])) fun s₂ ⟨f₂, k₂⟩ => ?_
  have K02 : Keeps [.x6] s s₂ := (k₁.keeps.mono fun _ h => absurd h List.not_mem_nil).trans k₂.keeps
  have hs₂ : Scr s₂ base size := hs.of_keeps K02 (by decide)
  refine WP.mono (qstoresV_ok (fun i => (selA K.M.n).acc.getD (0 + i) .v0) hs₂ hE16.1 (K.M.n / 2)
    (by omega)) fun s₃ ⟨w₃, kr₃, v₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs kr₃ (by decide)
  refine WP.mono (qstoresV_ok (fun i => (selA K.M.n).acc.getD (K.M.n / 2 + i) .v0) hs₃ hE16.2
    (K.M.n / 2) (by omega)) fun t ⟨w₄, kr₄, v₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs kr₄ (by decide)
  have hn16 : 16 * (K.M.n / 2) = 8 * K.M.n := by omega
  rw [hn16] at O₃ O₄
  have vx : ∀ i < K.M.n / 2, s₂.v ((selA K.M.n).acc.getD i .v0) =
      if 1 ≤ a then ldE K.M.n 0 s a i else 0 := fun i hi => by
    have ho := selA_o _ hn i (by omega)
    rw [k₂.v _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => ho (by rw [e]; simp), fun e => ho (by rw [e]; simp),
        not_mem_map_range fun i' hi' e => hA.acc _ (by omega) _ (by omega) (by omega) e.symm⟩),
      v₁ i (by omega)]
  have vy : ∀ i < K.M.n / 2, s₂.v ((selA K.M.n).acc.getD (K.M.n / 2 + i) .v0) =
      if 1 ≤ a then ldE K.M.n 0 s a (K.M.n / 2 + i)
      else ofVDwords (wordOf K.one (2 * i)) (wordOf K.one (2 * i + 1)) := fun i hi => by
    rw [f₂ i hi, v₁ _ (by omega)]
    by_cases h : 1 ≤ a
    · rw [ite_f (show ¬ a = 0 by omega), ite_t h, ite_t h]
    · rw [ite_t (show a = 0 by omega), ite_f h]
  have wx : ∀ j < K.M.n, word t.mem base (K.E.x + 8 * j) =
      if 1 ≤ a then word s.mem X (16 * K.M.n * (a - 1) + 8 * j) else 0 := fun j hj => by
    rw [O₄.word (by omega) (by omega), w₃ j (by omega)]
    simp only [Nat.zero_add]
    rw [vx _ (by omega)]
    by_cases h : 1 ≤ a
    · rw [ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)), h16,
        show 16 * K.M.n * (a - 1) + 0 + 16 * (j / 2) + 8 * (j % 2) = 16 * K.M.n * (a - 1) + 8 * j by omega]
    · rw [ite_f h, ite_f h, vdword_zero]
  have wy : ∀ j < K.M.n, word t.mem base (K.E.y + 8 * j) =
      if 1 ≤ a then word s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j) else wordOf K.one j :=
    fun j hj => by
      rw [w₄ j (by omega), v₃, vy _ (by omega)]
      by_cases h : 1 ≤ a
      · rw [ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)), h16,
          show 16 * K.M.n * (a - 1) + 0 + 16 * (K.M.n / 2 + j / 2) + 8 * (j % 2) =
            16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j by omega]
      · rw [ite_f h, ite_f h]
        rcases Nat.mod_two_eq_zero_or_one j with e | e
        · rw [e, vdword_ofVDwords_0, show 2 * (j / 2) = j by omega]
        · rw [e, vdword_ofVDwords_1, show 2 * (j / 2) + 1 = j by omega]
  obtain ⟨ex, ey⟩ := selXY_vals K hone wx wy
  refine ⟨ex, ey, ((Keeps.regs K02).trans (kr₃.mono fun _ h => absurd h List.not_mem_nil)).trans
    (kr₄.mono fun _ h => absurd h List.not_mem_nil), fun x hx => ?_, hs₄⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  rw [O₄ x (by omega), O₃ x (by omega), K02.mem]

/-- An entry of `n > 4` pairs: `x`'s in one pass, stored, then `y`'s in
another, reading the tables, which lie outside the working space (`hout`),
after the stores. -/
theorem selXY2_ok (K : TCombCfg) (hn : K.M.n ≤ 8) (h4 : ¬ 2 * K.M.n ≤ 8) (hn2 : K.M.n % 2 = 0)
    {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} {X : Addr} (ha : a ≤ K.H)
    (hH2 : K.H % 2 = 0) (hH : 16 * K.M.n * K.H ≤ 32768) (hHlt : K.H < 2 ^ 64) (h16 : s.gpr .x16 = X)
    (h18 : s.v .v18 = dup2 2) (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) (h28 : s.v .v28 = dup2 1)
    (hEx : K.E.x + 8 * K.M.n ≤ size) (hEy : K.E.y + 8 * K.M.n ≤ size)
    (hE16 : K.E.x % 16 = 0 ∧ K.E.y % 16 = 0)
    (axy : K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n))
    (hreg : InRegions (s.rd ++ s.wr) X (16 * K.M.n * K.H))
    (hout : ∀ e < K.H, ∀ i < 2 * K.M.n, ∀ b < 8,
      size ≤ ofs base (X + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i) + BitVec.ofNat 64 b)) :
    WP isa (.block (K.selPass 0 (K.M.n / 2) ++ selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.x ++
      K.selPass (8 * K.M.n) (K.M.n / 2) ++ K.selOne (K.M.n / 2) 0 (K.M.n / 2) ++
      selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.y)) s (SelXY K base size s a X) := by
  have hnw := hs.nowrap
  have hc : K.M.n / 2 ≤ 4 := by omega
  have ha64 : a < 2 ^ 64 := by omega
  iterate 4 rw [WP.block_append_iff]
  refine WP.mono (passV_ok K (o := 0) (c := K.M.n / 2) hc (by omega) (by decide) ha hH2 (by omega)
    hHlt h18 h19 h28 fun e he i hi => by rw [h16]; exact tbl_region hreg (by omega) e he i hi)
    fun s₁ ⟨v₁, a18, a19, a28, k₁⟩ => ?_
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁.keeps (by decide)
  refine WP.mono (qstoresV_ok (fun i => (selA (K.M.n / 2)).acc.getD (0 + i) .v0) hs₁ hE16.1 (K.M.n / 2)
    (by omega)) fun s₂ ⟨w₂, kr₂, v₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs kr₂ (by decide)
  have g₂ : s₂.gpr .x16 = X := by rw [kr₂.gpr _ List.not_mem_nil, k₁.gpr _ List.not_mem_nil, h16]
  have r₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [kr₂.rd, kr₂.wr, k₁.rd, k₁.wr]
  refine WP.mono (passV_ok K (o := 8 * K.M.n) (c := K.M.n / 2) hc (by omega) (by omega) ha hH2
    (by omega) hHlt (by rw [v₂, a18, h18]) (by rw [v₂, a19, h19]) (by rw [v₂, a28, h28])
    fun e he i hi => by rw [g₂, r₂]; exact tbl_region hreg (by omega) e he i hi)
    fun s₃ ⟨v₃, _, b19, _, k₃⟩ => ?_
  refine WP.mono (selOneV_ok K (c := K.M.n / 2) (h := 0) (k := K.M.n / 2) hc (by omega) ha64
    (by rw [b19, v₂, a19, h19])) fun s₄ ⟨f₄, k₄⟩ => ?_
  have K24 : Keeps [.x6] s₂ s₄ := (k₃.keeps.mono fun _ h => absurd h List.not_mem_nil).trans k₄.keeps
  have hs₄ : Scr s₄ base size := hs₂.of_keeps K24 (by decide)
  refine WP.mono (qstoresV_ok (fun i => (selA (K.M.n / 2)).acc.getD (0 + i) .v0) hs₄ hE16.2 (K.M.n / 2)
    (by omega)) fun t ⟨w₅, kr₅, v₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs kr₅ (by decide)
  have hn16 : 16 * (K.M.n / 2) = 8 * K.M.n := by omega
  rw [hn16] at O₂ O₅
  simp only [Nat.zero_add] at f₄ w₂ w₅
  have wx : ∀ j < K.M.n, word t.mem base (K.E.x + 8 * j) =
      if 1 ≤ a then word s.mem X (16 * K.M.n * (a - 1) + 8 * j) else 0 := fun j hj => by
    rw [O₅.word (by omega) (by omega), K24.mem, w₂ j (by omega), v₁ _ (by omega)]
    by_cases h : 1 ≤ a
    · rw [ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)), h16,
        show 16 * K.M.n * (a - 1) + 0 + 16 * (j / 2) + 8 * (j % 2) = 16 * K.M.n * (a - 1) + 8 * j by omega]
    · rw [ite_f h, ite_f h, vdword_zero]
  have wy : ∀ j < K.M.n, word t.mem base (K.E.y + 8 * j) =
      if 1 ≤ a then word s₂.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j) else wordOf K.one j :=
    fun j hj => by
      rw [w₅ j (by omega), f₄ _ (by omega), v₃ _ (by omega)]
      by_cases h : 1 ≤ a
      · rw [ite_f (show ¬ a = 0 by omega), ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)),
          g₂, show 16 * K.M.n * (a - 1) + 8 * K.M.n + 16 * (j / 2) + 8 * (j % 2) =
            16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j by omega]
      · rw [ite_t (show a = 0 by omega), ite_f h]
        rcases Nat.mod_two_eq_zero_or_one j with e | e
        · rw [e, vdword_ofVDwords_0, show 2 * (j / 2) = j by omega]
        · rw [e, vdword_ofVDwords_1, show 2 * (j / 2) + 1 = j by omega]
  obtain ⟨ex, ey⟩ := selXY_vals K hone wx wy
  have hm : 1 ≤ a → wordsVal s₂.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n =
      wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n := fun h1 => by
    rw [← k₁.mem]
    refine wordsVal_of_bytes _ _ fun i hi b hb => O₂ _ (Or.inr ?_)
    have := hout (a - 1) (by omega) (K.M.n + i) (by omega) b hb
    rw [show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) = 16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
      at this
    omega
  have ey' : wordsVal t.mem base K.E.y K.M.n =
      if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one := by
    rw [ey]
    by_cases h : 1 ≤ a
    · rw [ite_t h, ite_t h, hm h]
    · rw [ite_f h, ite_f h]
  refine ⟨ex, ey', ((((Keeps.regs k₁.keeps).mono fun _ h => absurd h List.not_mem_nil).trans
    (kr₂.mono fun _ h => absurd h List.not_mem_nil)).trans (Keeps.regs K24)).trans
    (kr₅.mono fun _ h => absurd h List.not_mem_nil), fun x hx => ?_, hs₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  rw [O₅ x (by omega), K24.mem, O₂ x (by omega), k₁.mem]

/-- The entry of the magnitude `a ≤ H` of table `j = x19` into `E`, from the
tables at `T` (the static `tsym`'s address): its `x` and `y` if `a ≥ 1`, else
`(0 : R : 0)`; `Z` is `R` unless `a = 0`. -/
theorem tselect_ok (K : TCombCfg) (hn : K.M.n ≤ 8) (hn2 : K.M.n % 2 = 0) {s : State} {base : Addr}
    {size : Nat} (hs : Scr s base size) {j a : Nat} {T : Addr} (hx19 : s.gpr .x19 = BitVec.ofNat 64 j)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha : a ≤ K.H) (hH2 : K.H % 2 = 0)
    (hH : 16 * K.M.n * K.H ≤ 32768) (htb : K.tblBytes < 65536) (hHlt : K.H < 2 ^ 64)
    (hT : s.syms K.tsym = T)
    (hE : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0)
    (hE16 : K.E.x % 16 = 0 ∧ K.E.y % 16 = 0)
    (hap : (K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y))
    (hone : K.one < 2 ^ (64 * K.M.n))
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * K.H))
    (hout : ∀ e < K.H, ∀ i < 2 * K.M.n, ∀ b < 8, size ≤ ofs base
      (T + BitVec.ofNat 64 (j * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i) + BitVec.ofNat 64 b)) :
    WP isa (.block K.select) s fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ a then
        wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ a then
        wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n
        else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ a then K.one else 0) ∧
      KeepRegs (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) s t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem := by
  have hnw := hs.nowrap
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  obtain ⟨axy, axz, ayz⟩ := hap
  have ha64 : a < 2 ^ 64 := by omega
  rw [TCombCfg.select]
  iterate 3 rw [WP.block_append_iff]
  refine WP.mono (selSetup_ok K hx19 hT htb) fun s₁ ⟨e16, e7, e5, e1, k₁⟩ => ?_
  have h2₁ : s₁.gpr .x2 = BitVec.ofNat 64 a := by rw [k₁.gpr _ (by decide), hx2]
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (bcastV_ok s₁) fun s₂ ⟨b19, b28, b18, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂.keeps (by decide)
  have h16 : s₂.gpr .x16 = T + BitVec.ofNat 64 (j * K.tblBytes) := by rw [k₂.gpr _ List.not_mem_nil, e16]
  have h18 : s₂.v .v18 = dup2 2 := by rw [b18, e5]; rfl
  have h19 : s₂.v .v19 = dup2 (BitVec.ofNat 64 a) := by rw [b19, h2₁]
  have h28 : s₂.v .v28 = dup2 1 := by rw [b28, e5]
  have hreg₂ : InRegions (s₂.rd ++ s₂.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * K.H) := by
    rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hreg
  have hXY : WP isa (.block (if 2 * K.M.n ≤ 8 then
      K.selPass 0 K.M.n ++ K.selOne K.M.n (K.M.n / 2) (K.M.n / 2) ++
      selStore K.M.n 0 (K.M.n / 2) K.E.x ++ selStore K.M.n (K.M.n / 2) (K.M.n / 2) K.E.y
    else
      K.selPass 0 (K.M.n / 2) ++ selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.x ++
      K.selPass (8 * K.M.n) (K.M.n / 2) ++ K.selOne (K.M.n / 2) 0 (K.M.n / 2) ++
      selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.y)) s₂
      (SelXY K base size s₂ a (T + BitVec.ofNat 64 (j * K.tblBytes))) := by
    by_cases h2 : 2 * K.M.n ≤ 8
    · rw [ite_t h2]
      exact selXY1_ok K (by omega) hn2 hs₂ ha hH2 hH hHlt h16 h18 h19 h28 hEx.1 hEy.1 hE16 axy hone hreg₂
    · rw [ite_f h2]
      exact selXY2_ok K hn h2 hn2 hs₂ ha hH2 hH hHlt h16 h18 h19 h28 hEx.1 hEy.1 hE16 axy hone hreg₂ hout
  refine WP.mono hXY fun s₃ hxy => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  have g₃ : ∀ r ∈ [Reg.x2, .x5, .x7], s₃.gpr r = s₁.gpr r := fun r hr => by
    have : r ≠ .x6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [hxy.keep.gpr r (by simpa using this), k₂.gpr r List.not_mem_nil]
  rw [TCombCfg.selZ, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (selZ_carry s₃ ha64 (by rw [g₃ _ (by simp), h2₁]) (by rw [g₃ _ (by simp), e5]))
    fun s₄ ⟨c₄, k₄⟩ => ?_
  have hs₄ := hxy.scr.of_keeps k₄ (by decide)
  refine WP.mono (zWords_ok K hs₄ (by rw [k₄.gpr _ (by decide), g₃ _ (by simp), e7]) hEz.1 hEz.2
    K.M.n (Nat.le_refl _)) fun t ⟨wt, _, kt, Ot⟩ => ?_
  have hm₄ : s₄.mem = s₃.mem := k₄.mem
  have b64 : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ 2 ^ 64 := fun d hd => by
    have := (hE d hd).1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ot.wordsVal axz (b64 _ (by simp)), hm₄, hxy.x, hm₂]
  · rw [Ot.wordsVal ayz (b64 _ (by simp)), hm₄, hxy.y, hm₂]
  · refine wordsVal_of_shifts _ _ _ _ _ (by split <;> [exact hone; exact Nat.two_pow_pos _])
      fun i hi => ?_
    rw [wt i hi, c₄]
    by_cases h : 1 ≤ a <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> [rfl; simp]
  · exact (((((Keeps.regs k₁).mono (by sub_regs)).trans
      ((Keeps.regs k₂.keeps).mono fun _ h => absurd h List.not_mem_nil)).trans
      (hxy.keep.mono (by sub_regs))).trans ((Keeps.regs k₄).mono (by sub_regs))).trans (kt.mono (by sub_regs))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    have hxy' : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n)], ofs base x < w.1 ∨ w.1 + w.2 ≤ ofs base x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hx.1, hx.2.1⟩
    rw [Ot x (by omega), hm₄, hxy.unch x hxy', hm₂]

end VG.Proof.Weierstrass.AArch64
