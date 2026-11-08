module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Table
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # ML-DSA's vector NTT on PPC64LE: the layers of `len ≥ 4` -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt

/-! ## One step -/

theorem loads_run (s : State) {x y : Addr} (h5 : s.gpr .r5 = x) (h9 : s.gpr .r9 = 0#64) (h8 : s.gpr .r8 = y)
    (ia : InRegions (s.rd ++ s.wr) x 16) (ib : InRegions (s.rd ++ s.wr) (x + y) 16) :
    WP isa (.block [.lxvd2x .v0 .r5 .r9, .lxvd2x .v1 .r5 .r8]) s fun t =>
      t = (s.writeV .v0 (swapDwords (s.mem.read x 16))).writeV .v1 (swapDwords (s.mem.read (x + y) 16)) := by
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v0 .r5 .r9 s (by decide) (by rw [h5, h9, BitVec.add_zero]; exact ia), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v1 .r5 .r8 _ (by decide) (by
    simp only [gpr_writeV, rd_writeV, wr_writeV, h5, h8]; exact ib), ?_⟩
  refine WP.block_nil ?_
  simp only [gpr_writeV, mem_writeV, h5, h8, h9, BitVec.add_zero]

theorem stores_run (s : State) {x y : Addr} (h5 : s.gpr .r5 = x) (h9 : s.gpr .r9 = 0#64) (h8 : s.gpr .r8 = y)
    (oa : InRegions s.wr x 16) (ob : InRegions s.wr (x + y) 16) :
    WP isa (.block [.stxvd2x .v0 .r5 .r9, .stxvd2x .v1 .r5 .r8, .addi .r5 .r5 16, .subi .r10 .r10 1]) s fun t =>
      t.mem = (s.mem.write x 16 (swapDwords (s.vpr .v0))).write (x + y) 16 (swapDwords (s.vpr .v1)) ∧
      t.gpr .r5 = x + 16 ∧ t.gpr .r10 = s.gpr .r10 - 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.vpr = s.vpr ∧ t.syms = s.syms ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr := by
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v0 .r5 .r9 s (by decide) (by rw [h5, h9, BitVec.add_zero]; exact oa), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v1 .r5 .r8 _ (by decide) (by simp only [h5, h8]; exact ob), ?_⟩
  crun [h5, h8, h9]
  intro r h1 h2
  simp [h1, h2]

/-! ## What every loop keeps -/

open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add polyRegion polyIs_toNat bfly blockN blockN_add
  blockN_bfly_get' zetaNat_eq layerN layerN_succ nttLayer)
open VG.Proof.MlKem.PPC64LE (count_sub count_nz wp_loop_nz ptr_ne ptr_add)
open VG.Spec.MlDsa (Poly Zq zetas)

abbrev F (s₀ : State) : Addr := s₀.gpr .r3
abbrev S (s₀ : State) : Addr := s₀.gpr .r4

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  red : VG.Proof.MlDsa.Reduced s₀.mem (F s₀)

/-- The registers the code writes. -/
def written : List Reg := [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The table of `z'` in `scratch`, at `S`: position `p` with zeta `K p`. -/
def Tab (K : Nat → Nat) (S : Addr) (m : Mem) : Prop :=
  ∀ p, 0 < p → p < 256 → m.readW (S + BitVec.ofNat 64 (4 * p)) 32 = BitVec.ofNat 32 (shoup (zeta (K p)))

/-- What every layer keeps, with the table of `K`. -/
structure EnvK (K : Nat → Nat) (s₀ : State) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀
  v4 : ∀ i < 4, (vword (s.vpr .v4) i).toNat = Spec.MlDsa.q
  v5 : s.vpr .v5 = hiC
  v16 : s.vpr .v16 = caC
  v17 : s.vpr .v17 = cbC
  v18 : s.vpr .v18 = ccC
  v19 : s.vpr .v19 = cdC
  keep : ∀ r, r ∉ written → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [polyRegion (F s₀), polyRegion (S s₀)] s₀.mem s.mem
  tab : Tab K (S s₀) s.mem

/-- The forward transform's. -/
abbrev Env := EnvK scrK

theorem EnvK.inRS {K : Nat → Nat} {s₀ s : State} (hp : Pre s₀) (h : EnvK K s₀ s) {b : Nat} (hb : b + 4 ≤ 256) :
    InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 (4 * b)) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  exact ⟨polyRegion (S s₀), by simp, VG.Offset.contains_base (k := 1024) _ (by omega) (by omega)⟩

theorem EnvK.inR {K : Nat → Nat} {s₀ s : State} (hp : Pre s₀) (h : EnvK K s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) j) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, vector_contains _ hj⟩

theorem EnvK.inW {K : Nat → Nat} {s₀ s : State} (hp : Pre s₀) (h : EnvK K s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (F s₀) j) 16 := by
  rw [h.wr, hp.wr]; exact ⟨_, by simp, vector_contains _ hj⟩

theorem EnvK.write {K : Nat → Nat} {s₀ s : State} (h : EnvK K s₀ s) {r : Reg} (hr : r ∈ written) (h3 : r ≠ .r3)
    (x : BitVec 64) : EnvK K s₀ (s.write r x) :=
  { h with
    r3 := by simp only [State.write, Ne.symm h3, ite_false]; exact h.r3
    keep := fun r' hr' => by
      simp only [State.write, show r' ≠ r from fun e => hr' (e ▸ hr), ite_false]; exact h.keep r' hr' }

theorem EnvK.of_vonly {K : Nat → Nat} {s₀ s t : State} (h : EnvK K s₀ s) {vs : List VReg} (hv : VOnly vs s t)
    (hd : ∀ r ∈ vs, r ∉ [.v4, .v5, .v16, .v17, .v18, .v19]) : EnvK K s₀ t :=
  { h with
    r3 := by rw [hv.gpr]; exact h.r3
    v4 := by rw [hv.v _ fun e => hd _ e (by decide)]; exact h.v4
    v5 := by rw [hv.v _ fun e => hd _ e (by decide)]; exact h.v5
    v16 := by rw [hv.v _ fun e => hd _ e (by decide)]; exact h.v16
    v17 := by rw [hv.v _ fun e => hd _ e (by decide)]; exact h.v17
    v18 := by rw [hv.v _ fun e => hd _ e (by decide)]; exact h.v18
    v19 := by rw [hv.v _ fun e => hd _ e (by decide)]; exact h.v19
    keep := fun r hr => by rw [hv.gpr]; exact h.keep r hr
    rd := by rw [hv.rd]; exact h.rd
    wr := by rw [hv.wr]; exact h.wr
    sp := by rw [hv.sp]; exact h.sp
    lr := by rw [hv.lr]; exact h.lr
    frame := by rw [hv.mem]; exact h.frame
    tab := by rw [hv.mem]; exact h.tab }

theorem EnvK.writeV {K : Nat → Nat} {s₀ s : State} (h : EnvK K s₀ s) {d : VReg} (hd : d ∉ [.v4, .v5, .v16, .v17, .v18, .v19])
    (x : BitVec 128) : EnvK K s₀ (s.writeV d x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨d4, d5, d16, d17, d18, d19⟩ := hd
  exact { h with
    v4 := by simp only [vpr_writeV, Ne.symm d4, ite_false]; exact h.v4
    v5 := by simp only [vpr_writeV, Ne.symm d5, ite_false]; exact h.v5
    v16 := by simp only [vpr_writeV, Ne.symm d16, ite_false]; exact h.v16
    v17 := by simp only [vpr_writeV, Ne.symm d17, ite_false]; exact h.v17
    v18 := by simp only [vpr_writeV, Ne.symm d18, ite_false]; exact h.v18
    v19 := by simp only [vpr_writeV, Ne.symm d19, ite_false]; exact h.v19 }

theorem zeta_eq (m : Nat) : zeta m = (zetas m).val := zetaNat_eq m

/-! ## The table in memory -/

theorem eval_splat0 (v : VReg → BitVec 128) (d n : VReg) :
    VOp.eval v (.splat true d n 0) = some (d, ofVWords fun _ => vword (v n) 0) := rfl

/-- A store of 16 bytes to the polynomial leaves the table. -/
theorem tab_write {K : Nat → Nat} {s₀ : State} (hp : Pre s₀) {m : Mem} (h : Tab K (S s₀) m) {j : Nat}
    (hj : j + 4 ≤ 256) (v : BitVec 128) : Tab K (S s₀) (m.write (coeffAddr (F s₀) j) 16 v) := fun p hp0 hp1 => by
  rw [← h p hp0 hp1]
  simp only [Mem.readW]
  rw [Mem.read_write_sep (Region.Disjoint.sep hp.disj.symm (Offset.contains_base _ (by omega) (by omega))
    (vector_contains _ hj)) (by decide)]

/-- `z'` of a block of `len ≥ 4`, in lane 0 of a load from `S + 4(k - 1)`. -/
theorem vword_wide {s₀ : State} {m : Mem} (h : Tab scrK (S s₀) m) {k : Nat} (hk1 : 1 ≤ k) (hk : k < 64) :
    (vword (swapDwords (m.read (S s₀ + BitVec.ofNat 64 (4 * (k - 1))) 16)) 0).toNat = shoup (zeta k) := by
  rw [vword_load _ _ (by decide), show (0 : Nat) ^^^ 1 = 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (k - 1) + 4 * 1 = 4 * k by omega, h k (by omega) (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (shoup_lt (zeta_lt _)), scrK_wide hk]

/-! ## Four butterflies -/

/-- After `t` steps of the block from `st` with zeta `zetas k`, from `Q`. -/
structure SInv (s₀ : State) (Q : Poly) (len k st t : Nat) (s : State) : Prop where
  env : Env s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (st + 4 * t)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (len / 4 - t)
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * k)
  v2 : ∀ i < 4, (vword (s.vpr .v2) i).toNat = (zetas k).val
  v3 : ∀ i < 4, (vword (s.vpr .v3) i).toNat = (zetas k).val * 2 ^ 32 / Spec.MlDsa.q
  poly : PolyIs s.mem (F s₀) (blockN bfly Q len (zetas k) st (4 * t))

theorem lanes_bfly_v {P : Poly} {m : Mem} {p : Addr} (hP : PolyIs m p P) {j len : Nat} (hj : j + len + 4 ≤ 256)
    {z : Zq} {Z ZP Qv : BitVec 128} (hz : ∀ i < 4, (vword Z i).toNat = z.val)
    (hzp : ∀ i < 4, (vword ZP i).toNat = z.val * 2 ^ 32 / Spec.MlDsa.q)
    (hq : ∀ i < 4, (vword Qv i).toNat = Spec.MlDsa.q) {e : Nat} (he : e < 4) :
    let A := swapDwords (m.read (coeffAddr p j) 16)
    let B := swapDwords (m.read (coeffAddr p (j + len)) 16)
    (vword (bflyA A B Z ZP Qv hiC) e).toNat = (P[j + (e ^^^ 1)]! + z * P[j + len + (e ^^^ 1)]!).val ∧
    (vword (bflyB A B Z ZP Qv hiC) e).toNat = (P[j + (e ^^^ 1)]! - z * P[j + len + (e ^^^ 1)]!).val := by
  intro A B
  have hx := xor1_lt he
  refine bfly_lanes he ?_ ?_ (hz e he) (hzp e he) (hq e he)
  · rw [vword_loadC _ _ _ he]; exact polyIs_toNat hP (by show _ < 256; omega)
  · rw [vword_loadC _ _ _ he]; exact polyIs_toNat hP (by show _ < 256; omega)

/-- Four more butterflies of the block, at `j … j+3`. -/
theorem blockN_four {Q : Poly} {len : Nat} {z : Zq} {st t : Nat} (hl : 4 ≤ len) (ht : 4 * t + 4 ≤ len)
    (hs : st + 2 * len ≤ 256) {i : Nat} (hi : i < 256) :
    (blockN bfly Q len z st (4 * (t + 1)))[i]! =
      let P := blockN bfly Q len z st (4 * t)
      if st + 4 * t ≤ i ∧ i < st + 4 * t + 4 then P[i]! + z * P[i + len]!
      else if st + 4 * t + len ≤ i ∧ i < st + 4 * t + len + 4 then P[i - len]! - z * P[i]!
      else P[i]! := by
  rw [show 4 * (t + 1) = 4 * t + 4 by omega, blockN_add]
  exact blockN_bfly_get' _ (by omega) (by omega) (by show _ ≤ 256; omega) hi

theorem step_ok {s₀ : State} (hp : Pre s₀) {Q : Poly} {len k st t : Nat} (hl : 4 ≤ len) (hd : len % 4 = 0)
    (hs : st + 2 * len ≤ 256) (ht : t < len / 4) {s : State}
    (h : SInv s₀ Q len k st t s) :
    WP isa (.block stepBody) s fun s' =>
      SInv s₀ Q len k st (t + 1) s' ∧ (s'.gpr .r10 != 0) = decide (t + 1 ≠ len / 4) := by
  have ht4 : 4 * t + 4 ≤ len := by omega
  have ej : coeffAddr (F s₀) (st + 4 * t) + BitVec.ofNat 64 (4 * len) = coeffAddr (F s₀) (st + 4 * t + len) :=
    coeffAddr_add _ _ _
  have ia := h.env.inR hp (j := st + 4 * t) (by omega)
  have ib := h.env.inR hp (j := st + 4 * t + len) (by omega)
  have oa := h.env.inW hp (j := st + 4 * t) (by omega)
  have ob := h.env.inW hp (j := st + 4 * t + len) (by omega)
  unfold stepBody
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_run s h.r5 h.r9 h.r8 ia (by rw [ej]; exact ib)) fun s₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bfly_exec s₁ (.inl ⟨rfl, rfl⟩)) fun s₂ ⟨a₂, b₂, vo₂, sy₂⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := by rw [vo₂.gpr, e₁]; rfl
  refine WP.mono (stores_run s₂ (x := coeffAddr (F s₀) (st + 4 * t)) (y := BitVec.ofNat 64 (4 * len))
    (by rw [g₂]; exact h.r5) (by rw [g₂]; exact h.r9) (by rw [g₂]; exact h.r8)
    (by rw [vo₂.wr, e₁]; exact oa) (by rw [vo₂.wr, e₁, ej]; exact ob))
    fun s₃ ⟨m₃, r5, r10, gk, v₃, sy₃, rd₃, wr₃, sp₃, lr₃⟩ => ?_
  -- The values the step loads and stores.
  have hv : ∀ r : VReg, r ≠ .v0 → r ≠ .v1 → s₁.vpr r = s.vpr r := fun r h0 h1 => by
    rw [e₁]; simp only [vpr_writeV, h0, h1, ite_false]
  have hs₂ : ∀ r : VReg, r ∉ [.v0, .v1, .v6, .v7] → s₃.vpr r = s.vpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₃, vo₂.v r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), hv r hr.1 hr.2.1]
  have m₂ : s₂.mem = s.mem := by rw [vo₂.mem, e₁]; rfl
  have A₁ : s₁.vpr .v0 = swapDwords (s.mem.read (coeffAddr (F s₀) (st + 4 * t)) 16) := by rw [e₁]; rfl
  have B₁ : s₁.vpr .v1 = swapDwords (s.mem.read (coeffAddr (F s₀) (st + 4 * t + len)) 16) := by
    rw [e₁, ← ej]; rfl
  rw [A₁, B₁, hv .v2 (by decide) (by decide), hv .v3 (by decide) (by decide), hv .v4 (by decide) (by decide),
    hv .v5 (by decide) (by decide), h.env.v5] at a₂ b₂
  have lanes := fun e (he : e < 4) => lanes_bfly_v h.poly (j := st + 4 * t) (len := len) (by omega) h.v2 h.v3
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
    exact (h.env.frame.write (by simp) _ (vector_contains _ (by omega))).write (by simp) _
      (vector_contains _ (by omega))
  · rw [m₃, m₂, ej]
    exact tab_write hp (tab_write hp h.env.tab (by omega) _) (by omega) _
  · rw [r5, show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add]
    exact congrArg _ (by omega)
  · rw [r10, g₂, h.r10]; exact count_sub ht
  · rw [m₃, m₂, a₂, b₂, ej]
    refine polyIs_store2 h.poly (by omega) (by omega) (fun e he => ?_) (fun e he => ?_) (fun i hi h1 h2 => ?_)
    · have hx := xor1_lt he
      rw [(lanes e he).1, blockN_four hl ht4 hs (by omega)]
      simp only
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_right_comm (st + 4 * t) len]
    · have hx := xor1_lt he
      rw [(lanes e he).2, blockN_four hl ht4 hs (by omega)]
      simp only
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
        show st + 4 * t + len + (e ^^^ 1) - len = st + 4 * t + (e ^^^ 1) by omega]
    · rw [blockN_four hl ht4 hs hi]
      simp only
      rw [ite_eq_right h1, ite_eq_right (by omega)]
  · rw [r10, g₂, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub ht]
    exact count_nz ht (by omega)

/-! ## Blocks -/

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (Q : Poly) (len nb c : Nat) (s : State) : Prop where
  env : Env s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (2 * len * c)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (nb + c - 1))
  poly : PolyIs s.mem (F s₀) (layerN bfly Q len (fun c => zetas (nb + c)) c)

theorem lsr4 {len : Nat} (hl : 4 * len < 2 ^ 64) :
    BitVec.ofNat 64 (4 * len) >>> 4 = BitVec.ofNat 64 (len / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bstep {s₀ : State} (hp : Pre s₀) {Q : Poly} {len nb c : Nat} (hl : 4 ≤ len) (hd : len % 4 = 0)
    (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ Q len nb c s) :
    WP isa blockCode s fun s' => BInv s₀ Q len nb (c + 1) s' ∧ (s'.gpr .r12 != 0) = decide (c + 1 ≠ nb) := by
  have hnb32 : nb ≤ 32 := by
    have : 4 * nb ≤ len * nb := Nat.mul_le_mul_right _ hl
    omega
  have hlc : len * (c + 1) ≤ 128 := hnb ▸ Nat.mul_le_mul_left _ hc
  have hk1 : 1 ≤ nb + c := by omega
  have hk : nb + c ≤ 63 := by omega
  have hlc' : len * c + len ≤ 128 := by rw [← Nat.mul_succ]; exact hlc
  have hst : 2 * len * c + 2 * len ≤ 256 := by rw [Nat.mul_assoc]; omega
  have hzk := zeta_lt (nb + c)
  unfold blockCode
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  have ia := h.env.inRS hp (b := nb + c - 1) (by omega)
  refine WP.cons (exec_lxvd2x .v3 .r7 .r9 s (by decide) (by rw [h.r7, h.r9, BitVec.add_zero]; exact ia)) ?_
  refine wp_vop (eval_splat0 _ _ _) ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, wp_nil ?_⟩
  simp only [vpr_writeV, ite_true, h.r7, h.r9, BitVec.add_zero]
  generalize ht₁ : State.write _ _ _ = t₁
  have g₁ : ∀ r, r ≠ .r7 → t₁.gpr r = s.gpr r := fun r hr => by
    rw [← ht₁]; simp only [State.write, gpr_writeV, hr, ite_false]
  have r7₁ : t₁.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (nb + c)) := by
    rw [← ht₁]; simp only [State.write, ite_true, gpr_writeV, h.r7, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 4 * (nb + c - 1) + 4 = 4 * (nb + c) by omega]
  have v₁ : ∀ r, r ≠ .v3 → t₁.vpr r = s.vpr r := fun r hr => by
    rw [← ht₁]; simp only [vpr_write, vpr_writeV, hr, ite_false]
  have z₁ : ∀ i < 4, (vword (t₁.vpr .v3) i).toNat = shoup (zeta (nb + c)) := fun i hi => by
    rw [← ht₁]; simp only [vpr_write, vpr_writeV, ite_true]
    rw [vword_ofVWords _ hi]
    exact vword_wide h.env.tab (by omega) (by omega)
  have env₁ : Env s₀ t₁ := by
    rw [← ht₁]
    exact ((h.env.writeV (by decide) _).writeV (by decide) _).write (by decide) (by decide) _
  rw [WP.block_append_iff]
  refine WP.mono (zcalc_run t₁ env₁.v4 env₁.v5 (z := fun _ => zeta (nb + c)) (fun _ _ => zeta_lt _)
    (fun _ _ => zeta_nz _) z₁) fun t₂ ⟨l₂, vo₂, sy₂⟩ => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩
  simp only [State.read, Size.ext, BitVec.setWidth_eq]
  have env₂ : Env s₀ t₂ := env₁.of_vonly vo₂ (by decide)
  have g₂ : ∀ r, r ≠ .r7 → t₂.gpr r = s.gpr r := fun r hr => by rw [vo₂.gpr, g₁ r hr]
  have h0 : SInv s₀ (layerN bfly Q len (fun c => zetas (nb + c)) c) len (nb + c) (2 * len * c) 0
      (t₂.write .r10 (t₂.gpr .r8 >>> 4)) := by
    refine ⟨env₂.write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r5]; rfl
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r8]
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r9]
    · simp only [State.write, ite_true]; rw [g₂ _ (by decide), h.r8, lsr4 (by omega)]; rfl
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r11]
    · simp only [State.write, reduceCtorEq, ite_false]; rw [vo₂.gpr, r7₁]
    · intro i hi; simp only [vpr_write]; rw [l₂ i hi, zeta_eq]
    · intro i hi; simp only [vpr_write]; rw [vo₂.v _ (by decide), z₁ i hi, shoup, zeta_eq]; rfl
    · simp only [State.write]; rw [vo₂.mem, ← ht₁]; exact h.poly
  refine WP.seq (wp_loop_nz (fun i t => SInv s₀ (layerN bfly Q len (fun c => zetas (nb + c)) c) len (nb + c)
      (2 * len * c) i t) (N := len / 4) (by omega) (fun i hi t ht => step_ok hp hl hd hst hi ht)
      (fun t ht => ?_) h0)
  have x5 : t.gpr .r5 + t.gpr .r8 = coeffAddr (F s₀) (2 * len * (c + 1)) := by
    rw [ht.r5, ht.r8, coeffAddr_add]; exact congrArg _ (by rw [Nat.mul_succ]; omega)
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
  · rw [g _ (by decide) (by decide), ht.r7, show nb + (c + 1) - 1 = nb + c by omega]
  · rw [layerN_succ]
    have := ht.poly
    rwa [show 4 * (len / 4) = len by omega] at this
  · simp only [State.write, ite_true]
    rw [x5, ht.r11, coeffAddr, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
      ptr_ne _ (by rw [Nat.mul_succ]; omega) (by decide)]
    have : 4 * (2 * len * (c + 1)) = 1024 ↔ c + 1 = nb := by
      constructor
      · intro e
        have e' : len * (c + 1) = len * nb := by rw [hnb]; rw [Nat.mul_assoc] at e; omega
        exact Nat.eq_of_mul_eq_mul_left (by omega) e'
      · intro e; rw [e, Nat.mul_assoc, hnb]
    simp only [ne_eq, this]

/-! ## Layers -/

/-- What a layer leaves for the next, with `len` and `nb` blocks from it. -/
structure LInv (s₀ : State) (R : Poly) (len nb : Nat) (s : State) : Prop where
  env : Env s₀ s
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (nb - 1))
  poly : PolyIs s.mem (F s₀) R

theorem lsr1 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 1 = BitVec.ofNat 64 (x / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  first | done | rfl

theorem layer_ok {s₀ : State} (hp : Pre s₀) {R : Poly} {len nb : Nat} (hl : 4 ≤ len) (hd : len % 4 = 0)
    (hnb : len * nb = 128) {s : State} (h : LInv s₀ R len nb s) :
    WP isa layerCode s fun s' => LInv s₀ (nttLayer R len) (len / 2) (2 * nb) s' ∧
      (s'.gpr .r12 != 0) = decide (len / 2 ≠ 2) := by
  have hnb1 : 1 ≤ nb := by rcases nb with _ | nb <;> simp_all
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ (by omega)]
  have hl128 : len ≤ 128 := by have := Nat.le_mul_of_pos_right len hnb1; omega
  unfold layerCode
  refine WP.seq (WP.block_cons_iff.2 ⟨s.write .r5 (s.gpr .r3 + BitVec.ofNat 64 0), rfl, WP.block_nil ?_⟩)
  have h0 : BInv s₀ R len nb 0 (s.write .r5 (s.gpr .r3 + BitVec.ofNat 64 0)) := by
    refine ⟨h.env.write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, ite_true, h.env.r3, Nat.mul_zero]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false]; exact h.r8
    · simp only [State.write, reduceCtorEq, ite_false]; exact h.r9
    · simp only [State.write, reduceCtorEq, ite_false]; exact h.r11
    · simp only [State.write, reduceCtorEq, ite_false, Nat.add_zero]; exact h.r7
    · exact h.poly
  refine WP.seq (wp_loop_nz (fun c t => BInv s₀ R len nb c t) (N := nb) (by omega)
      (fun c hc t ht => bstep hp hl hd hnb hc ht) (fun t ht => ?_) h0)
  refine WP.block_cons_iff.2 ⟨t.write .r8 (t.gpr .r8 >>> 1), rfl, ?_⟩
  refine WP.block_cons_iff.2 ⟨(t.write .r8 (t.gpr .r8 >>> 1)).write .r12 (t.gpr .r8 >>> 1 - BitVec.ofNat 64 8),
    rfl, WP.block_nil ?_⟩
  have x8 : t.gpr .r8 >>> 1 = BitVec.ofNat 64 (4 * (len / 2)) := by
    rw [ht.r8, lsr1 (by omega)]; exact congrArg _ (by omega)
  refine ⟨⟨(ht.env.write (by decide) (by decide) _).write (by decide) (by decide) _,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact x8
  · simp only [State.write, reduceCtorEq, ite_false]; exact ht.r9
  · simp only [State.write, reduceCtorEq, ite_false]; exact ht.r11
  · simp only [State.write, reduceCtorEq, ite_false]; rw [ht.r7, show nb + nb - 1 = 2 * nb - 1 by omega]
  · have := ht.poly; rwa [nttLayer, hdiv]
  · simp only [State.write, ite_true]
    rw [x8]
    have hlt : 4 * (len / 2) < 2 ^ 64 := by omega
    have e : BitVec.ofNat 64 (4 * (len / 2)) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (4 * (len / 2) - 8) := by
      rw [show 4 * (len / 2) = (4 * (len / 2) - 8) + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel,
        Nat.add_sub_cancel]
    rw [e]
    by_cases h2 : len / 2 = 2
    · rw [h2]; rfl
    · have : (BitVec.ofNat 64 (4 * (len / 2) - 8)) ≠ 0#64 := by
        intro e'
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
      simp [this, h2]

/-- The layers of `len ≥ 4`. -/
def wideLens : List Nat := [128, 64, 32, 16, 8, 4]

theorem foldl_take_succ (P : Poly) {ℓ : Nat} (hℓ : ℓ < 6) :
    (wideLens.take (ℓ + 1)).foldl nttLayer P = nttLayer ((wideLens.take ℓ).foldl nttLayer P) (128 / 2 ^ ℓ) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by rw [show wideLens.length = 6 from rfl]; exact hℓ),
    Option.toList_some, List.foldl_cons, List.foldl_nil]
  refine congrArg (nttLayer _) ?_
  rcases (by omega : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem wide_ok {s₀ : State} (hp : Pre s₀) {P : Poly} {s : State} (h : Env s₀ s)
    (hP : PolyIs s.mem (F s₀) P) :
    WP isa wideLayers s fun s' => LInv s₀ (wideLens.foldl nttLayer P) 2 64 s' := by
  unfold wideLayers
  refine WP.seq (WP.block_cons_iff.2 ⟨s.write .r8 (BitVec.ofNat 64 512), rfl, WP.block_cons_iff.2
    ⟨(s.write .r8 (BitVec.ofNat 64 512)).write .r11 (s.gpr .r3 + BitVec.ofNat 64 1024), rfl, WP.block_cons_iff.2
    ⟨((s.write .r8 (BitVec.ofNat 64 512)).write .r11 (s.gpr .r3 + BitVec.ofNat 64 1024)).write .r9
      (BitVec.ofNat 64 0), rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩⟩⟩⟩)
  refine wp_loop_nz (fun ℓ t => LInv s₀ ((wideLens.take ℓ).foldl nttLayer P) (128 / 2 ^ ℓ) (2 ^ ℓ) t)
    (N := 6) (by decide) (fun ℓ hℓ t ht => ?_) (fun t ht => ht) ?_
  · rw [foldl_take_succ P hℓ]
    rcases (by omega : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · refine WP.mono (layer_ok hp (by decide) (by decide) (by decide) ht) fun t' ⟨a, b⟩ => ?_
      simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd] at a b ⊢
      exact ⟨a, b⟩
  · refine ⟨(((h.write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; rw [h.r3]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]
      rw [h.keep .r4 (by decide), BitVec.add_zero]
    · exact hP

end VG.Proof.MlDsa.PPC64LE.VNtt
