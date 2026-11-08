module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Table
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Block
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

theorem Env.write {s₀ s : State} (h : Env s₀ s) {r : Reg} (hr : r ∈ written) (h3 : r ≠ .r3) (h6 : r ≠ .r6)
    (x : BitVec 64) : Env s₀ (s.write r x) :=
  { h with
    r3 := by simp only [State.write, Ne.symm h3, ite_false]; exact h.r3
    r6 := by simp only [State.write, Ne.symm h6, ite_false]; exact h.r6
    keep := fun r' hr' => by
      simp only [State.write, show r' ≠ r from fun e => hr' (e ▸ hr), ite_false]; exact h.keep r' hr' }

theorem Env.writeV {s₀ s : State} (h : Env s₀ s) {d : VReg} (hd : d ∉ [.v4, .v5, .v16, .v17, .v18, .v19])
    (x : BitVec 128) : Env s₀ (s.writeV d x) := by
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

/-! ## Loads from the table -/

theorem zetaWords_length : zetaWords.length = 456 := by
  rw [zetaWords_eq, List.length_append, List.length_append, constW_length, length_flatMap _ wideW_length,
    length_flatMap _ narrowW_length]

/-- `ld d`: vector `v` of the table into `d`, and `r7` to the next. -/
theorem ld_run (s : State) (d : VReg) {v : Nat} (hv : v < 228) (h6 : s.gpr .r6 = s.syms tblSym)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 (16 * v)) :
    WP isa (.block (ld d)) s fun t => t = (s.writeV d (tblVec v)).write .r7 (BitVec.ofNat 64 (16 * (v + 1))) := by
  have hin : (s.gpr .r7).toNat = 16 * v := by rw [h7, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.block_cons_iff.2 ⟨s.writeV d (tblVec v), ?_, ?_⟩
  · simp only [reduceExec]
    rw [ite_eq_left ⟨by decide, h6, by rw [hin]; omega, by rw [hin, zetaWords_length]; omega⟩, hin,
      show 16 * v / 8 = 2 * v by omega]
    rfl
  · crun [gpr_writeV, h7]
    rw [show 16 * (v + 1) = 16 * v + 16 by omega, BitVec.ofNat_add]

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

/-! ## Blocks -/

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (Q : Poly) (len nb c : Nat) (s : State) : Prop where
  env : Env s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (2 * len * c)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (4 * len)
  r9 : s.gpr .r9 = 0#64
  r11 : s.gpr .r11 = F s₀ + 1024
  r7 : s.gpr .r7 = BitVec.ofNat 64 (16 * (6 + 2 * (nb + c - 1)))
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
  have h6 : s.gpr .r6 = s.syms tblSym := by rw [h.env.r6, h.env.syms]
  unfold blockCode
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ld_run s .v2 (v := 6 + 2 * (nb + c - 1)) (by omega) h6 h.r7) fun t₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_run t₁ .v3 (v := 6 + 2 * (nb + c - 1) + 1) (by omega)
    (by rw [e₁]; exact h6) (by rw [e₁]; rfl)) fun t₂ e₂ => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩
  simp only [State.read, Size.ext, BitVec.setWidth_eq]
  have g₂ : ∀ r, r ≠ .r7 → t₂.gpr r = s.gpr r := fun r hr => by
    rw [e₂, e₁]; simp only [State.write, gpr_writeV, hr, ite_false]
  have v₂ : ∀ r, t₂.vpr r = if r = .v3 then tblVec (6 + 2 * (nb + c - 1) + 1)
      else if r = .v2 then tblVec (6 + 2 * (nb + c - 1)) else s.vpr r := fun r => by
    rw [e₂, e₁]; simp only [vpr_write, vpr_writeV]
  have env₂ : Env s₀ t₂ := by
    rw [e₂, e₁]
    exact (((h.env.writeV (by decide) _).write (by decide) (by decide) (by decide) _).writeV (by decide) _).write
      (by decide) (by decide) (by decide) _
  have h0 : SInv s₀ (layerN bfly Q len (fun c => zetas (nb + c)) c) len (nb + c) (2 * len * c) 0
      (t₂.write .r10 (t₂.gpr .r8 >>> 4)) := by
    refine ⟨env₂.write (by decide) (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r5]; rfl
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r8]
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r9]
    · simp only [State.write, ite_true]; rw [g₂ _ (by decide), h.r8, lsr4 (by omega)]; rfl
    · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide), h.r11]
    · simp only [State.write, reduceCtorEq, ite_false]; rw [e₂]; simp only [State.write, ite_true]
      first | done | exact congrArg _ (by omega)
    · rw [vpr_write, v₂]; simp
    · rw [vpr_write, v₂]; simp
    · have m₂ : t₂.mem = s.mem := by rw [e₂, e₁]; rfl
      simp only [State.write]; rw [m₂]; exact h.poly
  refine WP.seq (wp_loop_nz (fun i t => SInv s₀ (layerN bfly Q len (fun c => zetas (nb + c)) c) len (nb + c)
      (2 * len * c) i t) (N := len / 4) (by omega) (fun i hi t ht => step_ok hp hl hd hst hi hk1 hk ht)
      (fun t ht => ?_) h0)
  have x5 : t.gpr .r5 + t.gpr .r8 = coeffAddr (F s₀) (2 * len * (c + 1)) := by
    rw [ht.r5, ht.r8, coeffAddr_add]; exact congrArg _ (by rw [Nat.mul_succ]; omega)
  refine WP.block_cons_iff.2 ⟨t.write .r5 (t.gpr .r5 + t.gpr .r8), rfl, ?_⟩
  refine WP.block_cons_iff.2 ⟨(t.write .r5 (t.gpr .r5 + t.gpr .r8)).write .r12
    (t.gpr .r5 + t.gpr .r8 - t.gpr .r11), rfl, WP.block_nil ?_⟩
  have g : ∀ r, r ≠ .r5 → r ≠ .r12 → ((t.write .r5 (t.gpr .r5 + t.gpr .r8)).write .r12
      (t.gpr .r5 + t.gpr .r8 - t.gpr .r11)).gpr r = t.gpr r := fun r h1 h2 => by
    simp only [State.write, h1, h2, ite_false]
  refine ⟨⟨(ht.env.write (by decide) (by decide) (by decide) _).write (by decide) (by decide) (by decide) _,
    ?_, by rw [g _ (by decide) (by decide), ht.r8], by rw [g _ (by decide) (by decide), ht.r9],
    by rw [g _ (by decide) (by decide), ht.r11], ?_, ?_⟩, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact x5
  · rw [g _ (by decide) (by decide), ht.r7]; exact congrArg _ (by omega)
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
  r7 : s.gpr .r7 = BitVec.ofNat 64 (16 * (6 + 2 * (nb - 1)))
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
    refine ⟨h.env.write (by decide) (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  refine ⟨⟨(ht.env.write (by decide) (by decide) (by decide) _).write (by decide) (by decide) (by decide) _,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact x8
  · simp only [State.write, reduceCtorEq, ite_false]; exact ht.r9
  · simp only [State.write, reduceCtorEq, ite_false]; exact ht.r11
  · simp only [State.write, reduceCtorEq, ite_false]; rw [ht.r7]; exact congrArg _ (by omega)
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
    (h7 : s.gpr .r7 = BitVec.ofNat 64 96) (hP : PolyIs s.mem (F s₀) P) :
    WP isa wideLayers s fun s' => LInv s₀ (wideLens.foldl nttLayer P) 2 64 s' := by
  unfold wideLayers
  refine WP.seq (WP.block_cons_iff.2 ⟨s.write .r8 (BitVec.ofNat 64 512), rfl, WP.block_cons_iff.2
    ⟨(s.write .r8 (BitVec.ofNat 64 512)).write .r11 (s.gpr .r3 + BitVec.ofNat 64 1024), rfl, WP.block_cons_iff.2
    ⟨((s.write .r8 (BitVec.ofNat 64 512)).write .r11 (s.gpr .r3 + BitVec.ofNat 64 1024)).write .r9
      (BitVec.ofNat 64 0), rfl, WP.block_nil ?_⟩⟩⟩)
  refine wp_loop_nz (fun ℓ t => LInv s₀ ((wideLens.take ℓ).foldl nttLayer P) (128 / 2 ^ ℓ) (2 ^ ℓ) t)
    (N := 6) (by decide) (fun ℓ hℓ t ht => ?_) (fun t ht => ht) ?_
  · rw [foldl_take_succ P hℓ]
    rcases (by omega : ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · refine WP.mono (layer_ok hp (by decide) (by decide) (by decide) ht) fun t' ⟨a, b⟩ => ?_
      simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd] at a b ⊢
      exact ⟨a, b⟩
  · refine ⟨((h.write (by decide) (by decide) (by decide) _).write (by decide) (by decide) (by decide) _).write
      (by decide) (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false, ite_true]; rw [h.r3]; first | done | rfl
    · simp only [State.write, reduceCtorEq, ite_false]; exact h7
    · exact hP

end VG.Proof.MlDsa.PPC64LE.VNtt
