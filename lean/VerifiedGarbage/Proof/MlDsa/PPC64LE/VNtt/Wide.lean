module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Table
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
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
  blockN_bfly_get' zetaNat_eq)
open VG.Proof.MlKem.PPC64LE (count_sub count_nz wp_loop_nz ptr_ne ptr_add)
open VG.Spec.MlDsa (Poly Zq zetas)

abbrev F (s₀ : State) : Addr := s₀.gpr .r3
abbrev S (s₀ : State) : Addr := s₀.gpr .r4

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  red : VG.Proof.MlDsa.Reduced s₀.mem (F s₀)

/-- The registers the code writes. -/
def written : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

structure Env (s₀ : State) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀
  r6 : s.gpr .r6 = s₀.syms tblSym
  syms : s.syms = s₀.syms
  v4 : s.vpr .v4 = tblVec 0
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
  frame : Frame [polyRegion (F s₀)] s₀.mem s.mem

theorem Env.inR {s₀ s : State} (hp : Pre s₀) (h : Env s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) j) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, vector_contains _ hj⟩

theorem Env.inW {s₀ s : State} (hp : Pre s₀) (h : Env s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (F s₀) j) 16 := by
  rw [h.wr, hp.wr]; exact ⟨_, by simp, vector_contains _ hj⟩

theorem zeta_eq (m : Nat) : zeta m = (zetas m).val := zetaNat_eq m

/-! ## Four butterflies -/

/-- After `t` steps of the block from `st` with zeta `zetas k`, from `Q`. -/
structure SInv (s₀ : State) (Q : Poly) (len k st t : Nat) (s : State) : Prop where
  env : Env s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (st + 4 * t)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (len / 4 - t)
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = BitVec.ofNat 64 (16 * (6 + 2 * (k - 1) + 2))
  v2 : s.vpr .v2 = tblVec (6 + 2 * (k - 1))
  v3 : s.vpr .v3 = tblVec (6 + 2 * (k - 1) + 1)
  poly : PolyIs s.mem (F s₀) (blockN bfly Q len (zetas k) st (4 * t))

theorem lanes_bfly_v {P : Poly} {m : Mem} {p : Addr} (hP : PolyIs m p P) {j len : Nat} (hj : j + len + 4 ≤ 256)
    {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 63) {e : Nat} (he : e < 4) :
    let A := swapDwords (m.read (coeffAddr p j) 16)
    let B := swapDwords (m.read (coeffAddr p (j + len)) 16)
    (vword (bflyA A B (tblVec (6 + 2 * (k - 1))) (tblVec (6 + 2 * (k - 1) + 1)) (tblVec 0) hiC) e).toNat =
      (P[j + (e ^^^ 1)]! + zetas k * P[j + len + (e ^^^ 1)]!).val ∧
    (vword (bflyB A B (tblVec (6 + 2 * (k - 1))) (tblVec (6 + 2 * (k - 1) + 1)) (tblVec 0) hiC) e).toNat =
      (P[j + (e ^^^ 1)]! - zetas k * P[j + len + (e ^^^ 1)]!).val := by
  intro A B
  have hx := xor1_lt he
  obtain ⟨hz, hzp⟩ := lanes_wide (k := k - 1) (by omega) he
  rw [show k - 1 + 1 = k by omega] at hz hzp
  refine bfly_lanes he ?_ ?_ ?_ ?_ (lanes_q he)
  · rw [vword_loadC _ _ _ he]; exact polyIs_toNat hP (by show _ < 256; omega)
  · rw [vword_loadC _ _ _ he]; exact polyIs_toNat hP (by show _ < 256; omega)
  · rw [hz, zeta_eq]
  · rw [hzp, shoup, zeta_eq]; rfl

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
    (hs : st + 2 * len ≤ 256) (ht : t < len / 4) (hk1 : 1 ≤ k) (hk : k ≤ 63) {s : State}
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
    hv .v5 (by decide) (by decide), h.v2, h.v3, h.env.v4, h.env.v5] at a₂ b₂
  have lanes := fun e (he : e < 4) => lanes_bfly_v h.poly (j := st + 4 * t) (len := len) (by omega) hk1 hk he
  have hg : ∀ r, r ≠ .r5 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r h1 h2 => by rw [gk r h1 h2, g₂]
  have e₁rd : s₁.rd = s.rd := by rw [e₁]; rfl
  have e₁wr : s₁.wr = s.wr := by rw [e₁]; rfl
  have e₁sp : s₁.sp = s.sp := by rw [e₁]; rfl
  have e₁lr : s₁.lr = s.lr := by rw [e₁]; rfl
  have e₁sy : s₁.syms = s.syms := by rw [e₁]; rfl
  have hj := xor1_lt (e := 0) (by decide)
  refine ⟨⟨⟨(hg .r3 (by decide) (by decide)).trans h.env.r3, (hg .r6 (by decide) (by decide)).trans h.env.r6,
      by rw [sy₃, sy₂, e₁sy, h.env.syms], (hs₂ .v4 (by decide)).trans h.env.v4, (hs₂ .v5 (by decide)).trans h.env.v5,
      (hs₂ .v16 (by decide)).trans h.env.v16, (hs₂ .v17 (by decide)).trans h.env.v17,
      (hs₂ .v18 (by decide)).trans h.env.v18, (hs₂ .v19 (by decide)).trans h.env.v19,
      fun r hr => (hg r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))).trans (h.env.keep r hr),
      by rw [rd₃, vo₂.rd, e₁rd, h.env.rd], by rw [wr₃, vo₂.wr, e₁wr, h.env.wr],
      by rw [sp₃, vo₂.sp, e₁sp, h.env.sp], by rw [lr₃, vo₂.lr, e₁lr, h.env.lr], ?_⟩,
    ?_, (hg .r8 (by decide) (by decide)).trans h.r8, (hg .r9 (by decide) (by decide)).trans h.r9, ?_,
    (hg .r11 (by decide) (by decide)).trans h.r11, (hg .r7 (by decide) (by decide)).trans h.r7,
    (hs₂ .v2 (by decide)).trans h.v2, (hs₂ .v3 (by decide)).trans h.v3, ?_⟩, ?_⟩
  · rw [m₃, m₂, ej]
    exact frame_store2 h.env.frame (by omega) (by omega) _ _
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

end VG.Proof.MlDsa.PPC64LE.VNtt
