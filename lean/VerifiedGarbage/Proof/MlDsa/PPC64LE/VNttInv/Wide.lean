module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Wide
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNttInv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # ML-DSA's vector inverse NTT on PPC64LE: the butterfly and the layers of `len ≥ 4`

As the forward transform's (`VNtt/Wide.lean`), with `ibfly` (`ibfly_exec`,
`ibfly_lanes`), the table of `invK` (`IEnv`), the blocks' zetas from 63 down
to 1 and `len` doubling. -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt
open VG.Spec.MlDsa (Poly Zq zetas)

/-! ## The inverse butterfly -/

def ibflyD (a b qv : BitVec 128) : BitVec 128 := minV (subV b a) (addV (subV b a) qv)

def ibflyA (a b qv : BitVec 128) : BitVec 128 := minV (addV a b) (subV (addV a b) qv)

def ibflyB (a b z zp qv c : BitVec 128) : BitVec 128 :=
  minV (subV (loV (ibflyD a b qv) z) (loV (permV (mulEV (ibflyD a b qv) zp) (mulOV (ibflyD a b qv) zp) c) qv))
    (subV (subV (loV (ibflyD a b qv) z) (loV (permV (mulEV (ibflyD a b qv) zp) (mulOV (ibflyD a b qv) zp) c) qv)) qv)

set_option linter.unusedSimpArgs false in
theorem ibfly_exec (s : State) {a b : VReg} (hp : Pair a b) :
    WP isa (.block (ibfly a b .v2 .v3)) s fun t =>
      t.vpr a = ibflyA (s.vpr a) (s.vpr b) (s.vpr .v4) ∧
      t.vpr b = ibflyB (s.vpr a) (s.vpr b) (s.vpr .v2) (s.vpr .v3) (s.vpr .v4) (s.vpr .v5) ∧
      VOnly [a, b, .v6, .v7] s t ∧ t.syms = s.syms := by
  unfold ibfly
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_mulE _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_mulO _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine WP.block_nil ?_
    refine ⟨rfl, rfl, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    rotate_left
    all_goals try simp only [gpr_writeV, mem_writeV, rd_writeV, wr_writeV, sp_writeV, lr_writeV, syms_writeV]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4⟩ := hr
    simp only [vpr_writeV, r1, r2, r3, r4, ite_false]

/-- Lane `i` of the inverse butterfly's results, from its operands' lanes. -/
theorem ibfly_lanes {A B Z ZP Q : BitVec 128} {x y z : Zq} {i : Nat} (hi : i < 4)
    (hA : (vword A i).toNat = x.val) (hB : (vword B i).toNat = y.val) (hZ : (vword Z i).toNat = z.val)
    (hZP : (vword ZP i).toNat = z.val * 2 ^ 32 / Spec.MlDsa.q) (hQ : (vword Q i).toNat = Spec.MlDsa.q) :
    (vword (ibflyA A B Q) i).toNat = (x + y).val ∧
    (vword (ibflyB A B Z ZP Q hiC) i).toNat = (z * (y - x)).val := by
  have hhi := vword_hi (ibflyD A B Q) ZP hi
  simp only [ibflyA, ibflyB, vword_minV _ _ hi, vword_addV _ _ hi, vword_subV _ _ hi, vword_loV _ _ hi]
  simp only [ibflyD, vword_minV _ _ hi, vword_addV _ _ hi, vword_subV _ _ hi] at hhi ⊢
  exact ibfly_lane (vword A i) (vword B i) _ (vword Q i) (vword Z i) (vword ZP i) x y z hQ hZ hZP hA hB hhi

/-! ## The product by `f` -/

def smulV (a z zp qv c : BitVec 128) : BitVec 128 :=
  minV (subV (loV a z) (loV (permV (mulEV a zp) (mulOV a zp) c) qv))
    (subV (subV (loV a z) (loV (permV (mulEV a zp) (mulOV a zp) c) qv)) qv)

set_option linter.unusedSimpArgs false in
theorem smul_exec (s : State) {a : VReg} (ha : a = .v8 ∨ a = .v9 ∨ a = .v10 ∨ a = .v11) :
    WP isa (.block (smul a)) s fun t =>
      t.vpr a = smulV (s.vpr a) (s.vpr .v2) (s.vpr .v3) (s.vpr .v4) (s.vpr .v5) ∧
      VOnly [a, .v6, .v7] s t ∧ t.syms = s.syms := by
  unfold smul
  rcases ha with rfl | rfl | rfl | rfl <;>
  · refine wp_vop (eval_mulE _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_mulO _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine WP.block_nil ?_
    refine ⟨rfl, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    rotate_left
    all_goals try simp only [gpr_writeV, mem_writeV, rd_writeV, wr_writeV, sp_writeV, lr_writeV, syms_writeV]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3⟩ := hr
    simp only [vpr_writeV, r1, r2, r3, ite_false]

theorem smul_lanes {A Z ZP Q : BitVec 128} {x z : Zq} {i : Nat} (hi : i < 4)
    (hA : (vword A i).toNat = x.val) (hZ : (vword Z i).toNat = z.val)
    (hZP : (vword ZP i).toNat = z.val * 2 ^ 32 / Spec.MlDsa.q) (hQ : (vword Q i).toNat = Spec.MlDsa.q) :
    (vword (smulV A Z ZP Q hiC) i).toNat = (z * x).val := by
  simp only [smulV, vword_minV _ _ hi, vword_subV _ _ hi, vword_loV _ _ hi]
  exact smul_lane (vword A i) _ (vword Q i) (vword Z i) (vword ZP i) x z hQ hZ hZP hA (vword_hi A ZP hi)

/-! ## What every loop keeps -/

open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add polyRegion polyIs_toNat bflyInv blockN blockN_add
  layerN layerN_succ nttInvLayer nttInvBlk_ok)
open VG.Proof.MlKem.PPC64LE (count_sub count_nz wp_loop_nz ptr_ne ptr_add)

/-- The inverse transform's. -/
abbrev IEnv := EnvK invK

/-- `z'` of block `k - 1` of `len ≥ 4`, in lane 0 of a load from `S + 4(k - 1)`. -/
theorem vword_wideI {s₀ : State} {m : Mem} (h : Tab invK (S s₀) m) {k : Nat} (hk1 : 1 ≤ k) (hk : k < 64) :
    (vword (swapDwords (m.read (S s₀ + BitVec.ofNat 64 (4 * (k - 1))) 16)) 0).toNat = shoup (zeta (64 - k)) := by
  rw [vword_load _ _ (by decide), show (0 : Nat) ^^^ 1 = 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (k - 1) + 4 * 1 = 4 * k by omega_using [hk1], h k (by omega_using [hk1]) (by omega_using [hk]), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (shoup_lt (zeta_lt _)), invK, ite_eq_left hk, scrK_wide hk]

/-! ## Four butterflies -/

/-- After `t` steps of the block from `st` with zeta `zetas k`, the table at
position `p`, from `Q`. -/
structure ISInv (s₀ : State) (Q : Poly) (len k p st t : Nat) (s : State) : Prop where
  env : IEnv s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (st + 4 * t)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (len / 4 - t)
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * p)
  v2 : ∀ i < 4, (vword (s.vpr .v2) i).toNat = (zetas k).val
  v3 : ∀ i < 4, (vword (s.vpr .v3) i).toNat = (zetas k).val * 2 ^ 32 / Spec.MlDsa.q
  poly : PolyIs s.mem (F s₀) (blockN bflyInv Q len (-zetas k) st (4 * t))

theorem lanes_ibfly_v {P : Poly} {m : Mem} {p : Addr} (hP : PolyIs m p P) {j len : Nat} (hj : j + len + 4 ≤ 256)
    {z : Zq} {Z ZP Qv : BitVec 128} (hz : ∀ i < 4, (vword Z i).toNat = z.val)
    (hzp : ∀ i < 4, (vword ZP i).toNat = z.val * 2 ^ 32 / Spec.MlDsa.q)
    (hq : ∀ i < 4, (vword Qv i).toNat = Spec.MlDsa.q) {e : Nat} (he : e < 4) :
    let A := swapDwords (m.read (coeffAddr p j) 16)
    let B := swapDwords (m.read (coeffAddr p (j + len)) 16)
    (vword (ibflyA A B Qv) e).toNat = (P[j + (e ^^^ 1)]! + P[j + len + (e ^^^ 1)]!).val ∧
    (vword (ibflyB A B Z ZP Qv hiC) e).toNat = (z * (P[j + len + (e ^^^ 1)]! - P[j + (e ^^^ 1)]!)).val := by
  intro A B
  have hx := xor1_lt he
  refine ibfly_lanes he ?_ ?_ (hz e he) (hzp e he) (hq e he)
  · rw [vword_loadC _ _ _ he]; exact polyIs_toNat hP (by show _ < 256; omega_using [hj, hx])
  · rw [vword_loadC _ _ _ he]; exact polyIs_toNat hP (by show _ < 256; omega_using [hj, hx])

/-- Four more inverse butterflies of the block, at `j … j+3`. -/
theorem blockNI_four {Q : Poly} {len k : Nat} {st t : Nat} (hl : 4 ≤ len) (ht : 4 * t + 4 ≤ len)
    (hs : st + 2 * len ≤ 256) {i : Nat} (hi : i < 256) :
    (blockN bflyInv Q len (-zetas k) st (4 * (t + 1)))[i]! =
      let P := blockN bflyInv Q len (-zetas k) st (4 * t)
      if st + 4 * t ≤ i ∧ i < st + 4 * t + 4 then P[i]! + P[i + len]!
      else if st + 4 * t + len ≤ i ∧ i < st + 4 * t + len + 4 then zetas k * (P[i]! - P[i - len]!)
      else P[i]! := by
  rw [show 4 * (t + 1) = 4 * t + 4 by omega_using [], blockN_add]
  exact nttInvBlk_ok.get _ _ _ _ _ (by omega_using [hl]) (by omega_using [hl]) (by show _ ≤ 256; omega_using [ht, hs]) _ hi

theorem istep_ok {s₀ : State} (hp : Pre s₀) {Q : Poly} {len k p st t : Nat} (hl : 4 ≤ len) (hd : len % 4 = 0)
    (hs : st + 2 * len ≤ 256) (ht : t < len / 4) {s : State}
    (h : ISInv s₀ Q len k p st t s) :
    WP isa (.block iStepBody) s fun s' =>
      ISInv s₀ Q len k p st (t + 1) s' ∧ (s'.gpr .r10 != 0) = decide (t + 1 ≠ len / 4) := by
  have ht4 : 4 * t + 4 ≤ len := by omega
  have ej : coeffAddr (F s₀) (st + 4 * t) + BitVec.ofNat 64 (4 * len) = coeffAddr (F s₀) (st + 4 * t + len) :=
    coeffAddr_add _ _ _
  have ia := h.env.inR hp (j := st + 4 * t) (by omega_using [hs, ht])
  have ib := h.env.inR hp (j := st + 4 * t + len) (by omega_using [hs, ht])
  have oa := h.env.inW hp (j := st + 4 * t) (by omega_using [hs, ht])
  have ob := h.env.inW hp (j := st + 4 * t + len) (by omega_using [hs, ht])
  unfold iStepBody
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_run s h.r5 h.r9 h.r8 ia (by rw [ej]; exact ib)) fun s₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ibfly_exec s₁ (.inl ⟨rfl, rfl⟩)) fun s₂ ⟨a₂, b₂, vo₂, sy₂⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := by rw [vo₂.gpr, e₁]; rfl
  refine WP.mono (stores_run s₂ (x := coeffAddr (F s₀) (st + 4 * t)) (y := BitVec.ofNat 64 (4 * len))
    (by rw [g₂]; exact h.r5) (by rw [g₂]; exact h.r9) (by rw [g₂]; exact h.r8)
    (by rw [vo₂.wr, e₁]; exact oa) (by rw [vo₂.wr, e₁, ej]; exact ob))
    fun s₃ ⟨m₃, r5, r10, gk, v₃, sy₃, rd₃, wr₃, sp₃, lr₃⟩ => ?_
  have hv : ∀ r : VReg, r ≠ .v0 → r ≠ .v1 → s₁.vpr r = s.vpr r := fun r h0 h1 => by
    rw [e₁]; simp only [vpr_writeV, h0, h1, ite_false]
  have hs₂ : ∀ r : VReg, r ∉ [.v0, .v1, .v6, .v7] → s₃.vpr r = s.vpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₃, vo₂.v r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), hv r hr.1 hr.2.1]
  have m₂ : s₂.mem = s.mem := by rw [vo₂.mem, e₁]; rfl
  have A₁ : s₁.vpr .v0 = swapDwords (s.mem.read (coeffAddr (F s₀) (st + 4 * t)) 16) := by rw [e₁]; rfl
  have B₁ : s₁.vpr .v1 = swapDwords (s.mem.read (coeffAddr (F s₀) (st + 4 * t + len)) 16) := by
    rw [e₁, ← ej]; rfl
  rw [A₁, B₁, hv .v4 (by decide) (by decide)] at a₂
  rw [A₁, B₁, hv .v2 (by decide) (by decide), hv .v3 (by decide) (by decide), hv .v4 (by decide) (by decide),
    hv .v5 (by decide) (by decide), h.env.v5] at b₂
  have lanes := fun e (he : e < 4) => lanes_ibfly_v h.poly (j := st + 4 * t) (len := len) (by omega_using [hs, ht]) h.v2 h.v3
    h.env.v4 he
  have hg : ∀ r, r ≠ .r5 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r h1 h2 => by rw [gk r h1 h2, g₂]
  have e₁rd : s₁.rd = s.rd := by rw [e₁]; rfl
  have e₁wr : s₁.wr = s.wr := by rw [e₁]; rfl
  have e₁sp : s₁.sp = s.sp := by rw [e₁]; rfl
  have e₁lr : s₁.lr = s.lr := by rw [e₁]; rfl
  refine ⟨⟨⟨(hg .r3 (by decide) (by decide)).trans h.env.r3, by rw [hs₂ .v4 (by decide)]; exact h.env.v4,
      (hs₂ .v5 (by decide)).trans h.env.v5,
      (hs₂ .v16 (by decide)).trans h.env.v16, (hs₂ .v17 (by decide)).trans h.env.v17,
      (hs₂ .v18 (by decide)).trans h.env.v18, (hs₂ .v19 (by decide)).trans h.env.v19,
      fun r hr => (hg r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))).trans (h.env.keep r hr),
      by rw [rd₃, vo₂.rd, e₁rd, h.env.rd], by rw [wr₃, vo₂.wr, e₁wr, h.env.wr],
      by rw [sp₃, vo₂.sp, e₁sp, h.env.sp], by rw [lr₃, vo₂.lr, e₁lr, h.env.lr], ?_, ?_⟩,
    ?_, (hg .r8 (by decide) (by decide)).trans h.r8, (hg .r9 (by decide) (by decide)).trans h.r9, ?_,
    (hg .r11 (by decide) (by decide)).trans h.r11, (hg .r7 (by decide) (by decide)).trans h.r7,
    by rw [hs₂ .v2 (by decide)]; exact h.v2, by rw [hs₂ .v3 (by decide)]; exact h.v3, ?_⟩, ?_⟩
  · rw [m₃, m₂, ej]
    exact (h.env.frame.write (by simp) _ (vector_contains _ (by omega_using [hs, ht]))).write (by simp) _
      (vector_contains _ (by omega_using [hs, ht]))
  · rw [m₃, m₂, ej]
    exact tab_write hp (tab_write hp h.env.tab (by omega_using [hs, ht]) _) (by omega_using [hs, ht]) _
  · rw [r5, show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add]
    exact congrArg _ (by omega_using [])
  · rw [r10, g₂, h.r10]; exact count_sub ht
  · rw [m₃, m₂, a₂, b₂, ej]
    refine polyIs_store2 h.poly (by omega_using [hs, ht]) (by omega_using [hs, ht]) (fun e he => ?_) (fun e he => ?_) (fun i hi h1 h2 => ?_)
    · have hx := xor1_lt he
      rw [(lanes e he).1, blockNI_four hl ht4 hs (by omega_using [hs, ht, hx])]
      simp only
      rw [ite_eq_left ⟨by omega_using [], by omega_using [hx]⟩, Nat.add_right_comm (st + 4 * t) len]
    · have hx := xor1_lt he
      rw [(lanes e he).2, blockNI_four hl ht4 hs (by omega_using [hs, ht, hx])]
      simp only
      rw [ite_eq_right (by omega_using [hl]), ite_eq_left ⟨by omega_using [], by omega_using [hx]⟩,
        show st + 4 * t + len + (e ^^^ 1) - len = st + 4 * t + (e ^^^ 1) by omega_using []]
    · rw [blockNI_four hl ht4 hs hi]
      simp only
      rw [ite_eq_right h1, ite_eq_right (by omega_using [h2])]
  · rw [r10, g₂, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub ht]
    exact count_nz ht (by omega_using [hs])

/-! ## Blocks -/

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`, the
blocks before it having taken positions `1 … m` of the table. -/
structure IBInv (s₀ : State) (Q : Poly) (len nb m c : Nat) (s : State) : Prop where
  env : IEnv s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (2 * len * c)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (m + c))
  poly : PolyIs s.mem (F s₀) (layerN bflyInv Q len (fun c => -zetas (2 * nb - 1 - c)) c)

theorem ibstep {s₀ : State} (hp : Pre s₀) {Q : Poly} {len nb m c : Nat} (hl : 4 ≤ len) (hd : len % 4 = 0)
    (hnb : len * nb = 128) (hm : m + 2 * nb = 64) (hc : c < nb) {s : State} (h : IBInv s₀ Q len nb m c s) :
    WP isa iBlockCode s fun s' => IBInv s₀ Q len nb m (c + 1) s' ∧ (s'.gpr .r12 != 0) = decide (c + 1 ≠ nb) := by
  have hnb32 : nb ≤ 32 := by
    have : 4 * nb ≤ len * nb := Nat.mul_le_mul_right _ hl
    omega_using [hm]
  have hlc : len * (c + 1) ≤ 128 := hnb ▸ Nat.mul_le_mul_left _ hc
  have hlc' : len * c + len ≤ 128 := by rw [← Nat.mul_succ]; exact hlc
  have hst : 2 * len * c + 2 * len ≤ 256 := by rw [Nat.mul_assoc]; omega_using [hlc']
  unfold iBlockCode
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  have ia := h.env.inRS hp (b := m + c) (by omega_using [hm, hc])
  refine WP.cons (exec_lxvd2x .v3 .r7 .r9 s (by decide) (by rw [h.r7, h.r9, BitVec.add_zero]; exact ia)) ?_
  refine wp_vop (eval_splat0 _ _ _) ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, wp_nil ?_⟩
  simp only [vpr_writeV, ite_true, h.r7, h.r9, BitVec.add_zero]
  generalize ht₁ : State.write _ _ _ = t₁
  have g₁ : ∀ r, r ≠ .r7 → t₁.gpr r = s.gpr r := fun r hr => by
    rw [← ht₁]; simp only [State.write, gpr_writeV, hr, ite_false]
  have r7₁ : t₁.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (m + (c + 1))) := by
    rw [← ht₁]; simp only [State.write, ite_true, gpr_writeV, h.r7, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 4 * (m + c) + 4 = 4 * (m + (c + 1)) by omega_using []]
  have z₁ : ∀ i < 4, (vword (t₁.vpr .v3) i).toNat = shoup (zeta (2 * nb - 1 - c)) := fun i hi => by
    rw [← ht₁]; simp only [vpr_write, vpr_writeV, ite_true]
    rw [vword_ofVWords _ hi]
    have := vword_wideI h.env.tab (k := m + c + 1) (by omega_using []) (by omega_using [hm, hc])
    rwa [show m + c + 1 - 1 = m + c by omega_using [], show 64 - (m + c + 1) = 2 * nb - 1 - c by omega_using [hm]] at this
  have env₁ : IEnv s₀ t₁ := by
    rw [← ht₁]
    exact ((h.env.writeV (by decide) _).writeV (by decide) _).write (by decide) (by decide) _
  rw [WP.block_append_iff]
  refine WP.mono (zcalc_run t₁ env₁.v4 env₁.v5 (z := fun _ => zeta (2 * nb - 1 - c)) (fun _ _ => zeta_lt _)
    (fun _ _ => zeta_nz _) z₁) fun t₂ ⟨l₂, vo₂, sy₂⟩ => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩
  simp only [State.read, Size.ext, BitVec.setWidth_eq]
  have env₂ : IEnv s₀ t₂ := env₁.of_vonly vo₂ (by decide)
  have g₂ : ∀ r, r ≠ .r7 → t₂.gpr r = s.gpr r := fun r hr => by rw [vo₂.gpr, g₁ r hr]
  have h0 : ISInv s₀ (layerN bflyInv Q len (fun c => -zetas (2 * nb - 1 - c)) c) len (2 * nb - 1 - c)
      (m + (c + 1)) (2 * len * c) 0 (t₂.write .r10 (t₂.gpr .r8 >>> 4)) := by
    refine ⟨env₂.write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r5]; rfl
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r8]
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r9]
    · simp only [State.write, ite_true]; rw [g₂ _ (by decide), h.r8, lsr4 (by omega_using [hlc'])]; rfl
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r11]
    · simp only [State.write, reduceCtorEq, ite_false]; rw [vo₂.gpr, r7₁]
    · intro i hi; simp only [vpr_write]; rw [l₂ i hi, zeta_eq]
    · intro i hi; simp only [vpr_write]; rw [vo₂.v _ (by decide), z₁ i hi, shoup, zeta_eq]; rfl
    · simp only [State.write]; rw [vo₂.mem, ← ht₁]; exact h.poly
  refine WP.seq (wp_loop_nz (fun i t => ISInv s₀ (layerN bflyInv Q len (fun c => -zetas (2 * nb - 1 - c)) c) len
      (2 * nb - 1 - c) (m + (c + 1)) (2 * len * c) i t) (N := len / 4) (by omega_using [hl])
      (fun i hi t ht => istep_ok hp hl hd hst hi ht) (fun t ht => ?_) h0)
  have x5 : t.gpr .r5 + t.gpr .r8 = coeffAddr (F s₀) (2 * len * (c + 1)) := by
    rw [ht.r5, ht.r8, coeffAddr_add]; exact congrArg _ (by rw [Nat.mul_succ]; omega_using [hd])
  refine WP.block_cons_iff.2 ⟨t.write .r5 (t.gpr .r5 + t.gpr .r8), rfl, ?_⟩
  refine WP.block_cons_iff.2 ⟨(t.write .r5 (t.gpr .r5 + t.gpr .r8)).write .r12
    (t.gpr .r5 + t.gpr .r8 - t.gpr .r11), rfl, WP.block_nil ?_⟩
  have g : ∀ r, r ≠ .r5 → r ≠ .r12 → ((t.write .r5 (t.gpr .r5 + t.gpr .r8)).write .r12
      (t.gpr .r5 + t.gpr .r8 - t.gpr .r11)).gpr r = t.gpr r := fun r h1 h2 => by
    simp only [State.write, h1, h2, ite_false]
  refine ⟨⟨(ht.env.write (by decide) (by decide) _).write (by decide) (by decide) _,
    ?_, by rw [g _ (by decide) (by decide), ht.r8], by rw [g _ (by decide) (by decide), ht.r9],
    by rw [g _ (by decide) (by decide), ht.r11], ?_, ?_⟩, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact x5
  · rw [g _ (by decide) (by decide), ht.r7]
  · rw [layerN_succ]
    have := ht.poly
    rwa [show 4 * (len / 4) = len by omega_using [hd]] at this
  · simp only [State.write, ite_true]
    rw [x5, ht.r11, coeffAddr, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
      ptr_ne _ (by rw [Nat.mul_succ]; omega_using [hst]) (by decide)]
    have : 4 * (2 * len * (c + 1)) = 1024 ↔ c + 1 = nb := by
      constructor
      · intro e
        have e' : len * (c + 1) = len * nb := by rw [hnb]; rw [Nat.mul_assoc] at e; omega_using [e]
        exact Nat.eq_of_mul_eq_mul_left (by omega_using [hl]) e'
      · intro e; rw [e, Nat.mul_assoc, hnb]
    simp only [ne_eq, this]

/-! ## Layers -/

/-- What a layer leaves for the next, with `len`, the blocks before it
having taken positions `1 … m` of the table. -/
structure ILInv (s₀ : State) (R : Poly) (len m : Nat) (s : State) : Prop where
  env : IEnv s₀ s
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * m)
  poly : PolyIs s.mem (F s₀) R

theorem lsl1 {x : Nat} (hx : 2 * x < 2 ^ 64) : BitVec.ofNat 64 x <<< 1 = BitVec.ofNat 64 (2 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using [hx]), Nat.mod_eq_of_lt (by omega_using [hx])]
  omega_using []

theorem sub_nz {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  have := ptr_ne 0#64 ha hb
  simpa only [BitVec.zero_add] using this

theorem ilayer_ok {s₀ : State} (hp : Pre s₀) {R : Poly} {len nb m : Nat} (hl : 4 ≤ len) (hd : len % 4 = 0)
    (hnb : len * nb = 128) (hm : m + 2 * nb = 64) {s : State} (h : ILInv s₀ R len m s) :
    WP isa iLayerCode s fun s' => ILInv s₀ (nttInvLayer R len) (2 * len) (m + nb) s' ∧
      (s'.gpr .r12 != 0) = decide (2 * len ≠ 256) := by
  have hnb1 : 1 ≤ nb := by rcases nb with _ | nb <;> simp_all
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ (by omega_using [hl])]
  have hdiv2 : 256 / len = 2 * nb := by
    rw [show 256 = len * (2 * nb) by rw [Nat.mul_left_comm, hnb], Nat.mul_div_cancel_left _ (by omega_using [hl])]
  have hl128 : len ≤ 128 := by have := Nat.le_mul_of_pos_right len hnb1; omega_using [hnb, this]
  unfold iLayerCode
  refine WP.seq (WP.block_cons_iff.2 ⟨s.write .r5 (s.gpr .r3 + BitVec.ofNat 64 0), rfl, WP.block_nil ?_⟩)
  have h0 : IBInv s₀ R len nb m 0 (s.write .r5 (s.gpr .r3 + BitVec.ofNat 64 0)) := by
    refine ⟨h.env.write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, ite_true, h.env.r3, Nat.mul_zero]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false]; exact h.r8
    · simp only [State.write, reduceCtorEq, ite_false]; exact h.r9
    · simp only [State.write, reduceCtorEq, ite_false]; exact h.r11
    · simp only [State.write, reduceCtorEq, ite_false, Nat.add_zero]; exact h.r7
    · exact h.poly
  refine WP.seq (wp_loop_nz (fun c t => IBInv s₀ R len nb m c t) (N := nb) (by omega_using [hnb1])
      (fun c hc t ht => ibstep hp hl hd hnb hm hc ht) (fun t ht => ?_) h0)
  refine WP.block_cons_iff.2 ⟨t.write .r8 (t.gpr .r8 <<< 1), rfl, ?_⟩
  refine WP.block_cons_iff.2 ⟨(t.write .r8 (t.gpr .r8 <<< 1)).write .r12 (t.gpr .r8 <<< 1 - BitVec.ofNat 64 1024),
    rfl, WP.block_nil ?_⟩
  have x8 : t.gpr .r8 <<< 1 = BitVec.ofNat 64 (4 * (2 * len)) := by
    rw [ht.r8, lsl1 (by omega_using [hl128])]; exact congrArg _ (by omega_using [])
  refine ⟨⟨(ht.env.write (by decide) (by decide) _).write (by decide) (by decide) _,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact x8
  · simp only [State.write, reduceCtorEq, ite_false]; exact ht.r9
  · simp only [State.write, reduceCtorEq, ite_false]; exact ht.r11
  · simp only [State.write, reduceCtorEq, ite_false]; rw [ht.r7]
  · have := ht.poly; rwa [nttInvLayer, hdiv, hdiv2]
  · simp only [State.write, ite_true]
    rw [x8, sub_nz (by omega_using [hl128]) (by decide)]
    simp only [ne_eq, show 4 * (2 * len) = 1024 ↔ 2 * len = 256 by omega_using []]

/-- The inverse layers of `len ≥ 4`. -/
def wideInvLens : List Nat := [4, 8, 16, 32, 64, 128]

theorem ifoldl_take_succ (P : Poly) {ℓ : Nat} (hℓ : ℓ < 6) :
    (wideInvLens.take (ℓ + 1)).foldl nttInvLayer P =
      nttInvLayer ((wideInvLens.take ℓ).foldl nttInvLayer P) (4 * 2 ^ ℓ) := by
  rw [List.take_add_one, List.foldl_append,
    List.getElem?_eq_getElem (by rw [show wideInvLens.length = 6 from rfl]; exact hℓ),
    Option.toList_some, List.foldl_cons, List.foldl_nil]
  refine congrArg (nttInvLayer _) ?_
  rcases (by omega_arith : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem iwide_ok {s₀ : State} (hp : Pre s₀) {P : Poly} {s : State} (h : IEnv s₀ s)
    (hP : PolyIs s.mem (F s₀) P) :
    WP isa wideInv s fun s' => ILInv s₀ (wideInvLens.foldl nttInvLayer P) 256 63 s' := by
  unfold wideInv
  refine WP.seq (WP.block_cons_iff.2 ⟨s.write .r8 (BitVec.ofNat 64 16), rfl, WP.block_cons_iff.2
    ⟨(s.write .r8 (BitVec.ofNat 64 16)).write .r11 (s.gpr .r3 + BitVec.ofNat 64 1024), rfl, WP.block_cons_iff.2
    ⟨((s.write .r8 (BitVec.ofNat 64 16)).write .r11 (s.gpr .r3 + BitVec.ofNat 64 1024)).write .r9
      (BitVec.ofNat 64 0), rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩⟩⟩⟩)
  refine wp_loop_nz (fun ℓ t => ILInv s₀ ((wideInvLens.take ℓ).foldl nttInvLayer P) (4 * 2 ^ ℓ) (64 - 64 / 2 ^ ℓ) t)
    (N := 6) (by decide) (fun ℓ hℓ t ht => ?_) (fun t ht => ht) ?_
  · rw [ifoldl_take_succ P hℓ]
    have e : 4 ≤ 4 * 2 ^ ℓ ∧ 4 * 2 ^ ℓ % 4 = 0 ∧ 4 * 2 ^ ℓ * (32 / 2 ^ ℓ) = 128 ∧
        64 - 64 / 2 ^ ℓ + 2 * (32 / 2 ^ ℓ) = 64 ∧ 2 * (4 * 2 ^ ℓ) = 4 * 2 ^ (ℓ + 1) ∧
        64 - 64 / 2 ^ ℓ + 32 / 2 ^ ℓ = 64 - 64 / 2 ^ (ℓ + 1) ∧ (2 * (4 * 2 ^ ℓ) ≠ 256 ↔ ℓ + 1 ≠ 6) := by
      rcases (by omega_arith : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e
    refine WP.mono (ilayer_ok hp (nb := 32 / 2 ^ ℓ) e1 e2 e3 e4 ht) fun t' ⟨a, b⟩ => ⟨?_, ?_⟩
    · rwa [e5, e6] at a
    · rw [b]; exact decide_eq_decide.mpr e7
  · refine ⟨(((h.write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; rw [h.r3]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]
      rw [h.keep .r4 (by decide), BitVec.add_zero]
    · exact hP

end VG.Proof.MlDsa.PPC64LE.VNtt
