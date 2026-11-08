module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Wide
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # ML-DSA's vector NTT on PPC64LE: the layers of `len = 2` and `len = 1`

Sixteen coefficients at a time: `transpose` puts lane `k` of vector `r` in
lane `r` of vector `k` (`transpose_run`), so that lane `r` holds the four
coefficients of block `r` of `len = 2`; four butterflies then do both
layers' (`group_ok`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt

/-! ## The transpose -/

theorem vword_ca (n m : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (permV n m caC) i = if i % 2 = 0 then vword n (i / 2) else vword m (i / 2) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 4) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 1) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 5) (by decide) (by decide) (by decide)]; rfl

theorem vword_cb (n m : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (permV n m cbC) i = if i % 2 = 0 then vword n (2 + i / 2) else vword m (2 + i / 2) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 6) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 3) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 7) (by decide) (by decide) (by decide)]; rfl

theorem vword_cc (n m : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (permV n m ccC) i = if i < 2 then vword n i else vword m (i - 2) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 1) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 4) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 5) (by decide) (by decide) (by decide)]; rfl

theorem vword_cd (n m : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (permV n m cdC) i = if i < 2 then vword n (i + 2) else vword m i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 3) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 6) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 7) (by decide) (by decide) (by decide)]; rfl

/-- The four vectors of a group, `v8 … v11`. -/
def tv : Nat → VReg
  | 0 => .v8 | 1 => .v9 | 2 => .v10 | _ => .v11

set_option linter.unusedSimpArgs false in
theorem transpose_run (s : State) (h16 : s.vpr .v16 = caC) (h17 : s.vpr .v17 = cbC)
    (h18 : s.vpr .v18 = ccC) (h19 : s.vpr .v19 = cdC) :
    WP isa (.block transpose) s fun t =>
      (∀ k < 4, ∀ r < 4, vword (t.vpr (tv k)) r = vword (s.vpr (tv r)) k) ∧
      VOnly [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15] s t ∧ t.syms = s.syms := by
  unfold transpose
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine WP.block_nil ⟨fun k hk r hr => ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · rw [h16, h17, h18, h19]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    simp only [tv, vpr_writeV, reduceCtorEq, ite_true, ite_false, vword_cc _ _ (show (0 : Nat) < 4 by decide),
      vword_cc _ _ (show (1 : Nat) < 4 by decide), vword_cc _ _ (show (2 : Nat) < 4 by decide),
      vword_cc _ _ (show (3 : Nat) < 4 by decide), vword_cd _ _ (show (0 : Nat) < 4 by decide),
      vword_cd _ _ (show (1 : Nat) < 4 by decide), vword_cd _ _ (show (2 : Nat) < 4 by decide),
      vword_cd _ _ (show (3 : Nat) < 4 by decide), vword_ca _ _ (show (0 : Nat) < 4 by decide),
      vword_ca _ _ (show (1 : Nat) < 4 by decide), vword_cb _ _ (show (0 : Nat) < 4 by decide),
      vword_cb _ _ (show (1 : Nat) < 4 by decide), vword_ca _ _ (show (2 : Nat) < 4 by decide),
      vword_ca _ _ (show (3 : Nat) < 4 by decide), vword_cb _ _ (show (2 : Nat) < 4 by decide),
      vword_cb _ _ (show (3 : Nat) < 4 by decide), Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub,
      Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨r8, r9, r10, r11, r12, r13, r14, r15⟩ := hr'
    simp only [vpr_writeV, r8, r9, r10, r11, r12, r13, r14, r15, ite_false]

/-! ## The two layers, coefficient by coefficient -/

open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add polyRegion polyIs_toNat polyIs_of_toNat bfly blockN nttLayer
  layF layF1_get layF2_get nttBlk_ok)
open VG.Proof.MlKem.PPC64LE (count_sub count_nz wp_loop_nz)
open VG.Spec.MlDsa (Poly Zq zetas)

theorem layer2_get (W : Poly) {j : Nat} (hj : j < 256) :
    (nttLayer W 2)[j]! = if j % 4 < 2 then W[j]! + zetas (64 + j / 4) * W[j + 2]!
      else W[j - 2]! - zetas (64 + j / 4) * W[j]! := by
  have h := layF2_get nttBlk_ok W (fun c => 64 + c) (b := 64) (by decide) hj
  rw [ite_eq_left (by omega)] at h
  exact h

theorem layer1_get (W : Poly) {j : Nat} (hj : j < 256) :
    (nttLayer W 1)[j]! = if j % 2 = 0 then W[j]! + zetas (128 + j / 2) * W[j + 1]!
      else W[j - 1]! - zetas (128 + j / 2) * W[j]! := by
  have h := layF1_get nttBlk_ok W (fun c => 128 + c) (b := 128) (by decide) hj
  rw [ite_eq_left (by omega)] at h
  exact h

/-- The two layers on block `r` of group `g`, from `W`. -/
theorem layers_block (W : Poly) {g r : Nat} (hg : g < 16) (hr : r < 4) :
    let b := 16 * g + 4 * r
    let L := nttLayer W 2
    let z2 := zetas (64 + 4 * g + r)
    let za := zetas (128 + 8 * g + 2 * r)
    let zb := zetas (128 + 8 * g + 2 * r + 1)
    L[b]! = W[b]! + z2 * W[b + 2]! ∧ L[b + 1]! = W[b + 1]! + z2 * W[b + 3]! ∧
    L[b + 2]! = W[b]! - z2 * W[b + 2]! ∧ L[b + 3]! = W[b + 1]! - z2 * W[b + 3]! ∧
    (nttLayer L 1)[b]! = L[b]! + za * L[b + 1]! ∧ (nttLayer L 1)[b + 1]! = L[b]! - za * L[b + 1]! ∧
    (nttLayer L 1)[b + 2]! = L[b + 2]! + zb * L[b + 3]! ∧ (nttLayer L 1)[b + 3]! = L[b + 2]! - zb * L[b + 3]! := by
  intro b L z2 za zb
  have hb : b + 3 < 256 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [layer2_get W (by omega), ite_eq_left (by omega), show 64 + b / 4 = 64 + 4 * g + r by omega]
  · rw [layer2_get W (by omega), ite_eq_left (by omega), show 64 + (b + 1) / 4 = 64 + 4 * g + r by omega,
      show b + 1 + 2 = b + 3 by omega]
  · rw [layer2_get W (by omega), ite_eq_right (by omega), show 64 + (b + 2) / 4 = 64 + 4 * g + r by omega,
      show b + 2 - 2 = b by omega]
  · rw [layer2_get W (by omega), ite_eq_right (by omega), show 64 + (b + 3) / 4 = 64 + 4 * g + r by omega,
      show b + 3 - 2 = b + 1 by omega]
  · rw [layer1_get L (by omega), ite_eq_left (by omega), show 128 + b / 2 = 128 + 8 * g + 2 * r by omega]
  · rw [layer1_get L (by omega), ite_eq_right (by omega), show 128 + (b + 1) / 2 = 128 + 8 * g + 2 * r by omega,
      show b + 1 - 1 = b by omega]
  · rw [layer1_get L (by omega), ite_eq_left (by omega), show 128 + (b + 2) / 2 = 128 + 8 * g + 2 * r + 1 by omega,
      show b + 2 + 1 = b + 3 by omega]
  · rw [layer1_get L (by omega), ite_eq_right (by omega), show 128 + (b + 3) / 2 = 128 + 8 * g + 2 * r + 1 by omega,
      show b + 3 - 1 = b + 2 by omega]

/-! ## Frames -/

/-- `t` differs from `s` only in the vectors `vs` and the registers `gs`. -/
structure Fr (vs : List VReg) (gs : List Reg) (s t : State) : Prop where
  v : ∀ r, r ∉ vs → t.vpr r = s.vpr r
  g : ∀ r, r ∉ gs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  lr : t.lr = s.lr
  syms : t.syms = s.syms

theorem Fr.trans {vs vs' : List VReg} {gs gs' : List Reg} {s t u : State} (h : Fr vs gs s t)
    (h' : Fr vs' gs' t u) : Fr (vs ++ vs') (gs ++ gs') s u :=
  ⟨fun r hr => by rw [List.mem_append, not_or] at hr; rw [h'.v r hr.2, h.v r hr.1],
   fun r hr => by rw [List.mem_append, not_or] at hr; rw [h'.g r hr.2, h.g r hr.1],
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.lr.trans h.lr,
   h'.syms.trans h.syms⟩

theorem Fr.trans' {vs : List VReg} {gs : List Reg} {s t u : State} (h : Fr vs gs s t)
    (h' : Fr vs gs t u) : Fr vs gs s u :=
  ⟨fun r hr => by rw [h'.v r hr, h.v r hr], fun r hr => by rw [h'.g r hr, h.g r hr],
   h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.lr.trans h.lr,
   h'.syms.trans h.syms⟩

theorem Fr.of_vonly {vs : List VReg} {s t : State} (h : VOnly vs s t) (hs : t.syms = s.syms) : Fr vs [] s t :=
  ⟨h.v, fun r _ => by rw [h.gpr], h.mem, h.rd, h.wr, h.sp, h.lr, hs⟩

theorem Fr.writeV (vs : List VReg) (gs : List Reg) (s : State) {d : VReg} (hd : d ∈ vs) (x : BitVec 128) :
    Fr vs gs s (s.writeV d x) :=
  ⟨fun r hr => by simp only [vpr_writeV, show r ≠ d from fun e => hr (e ▸ hd), ite_false], fun _ _ => rfl,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.write (vs : List VReg) (gs : List Reg) (s : State) {d : Reg} (hd : d ∈ gs) (x : BitVec 64) :
    Fr vs gs s (s.write d x) :=
  ⟨fun _ _ => rfl, fun r hr => by simp only [State.write, show r ≠ d from fun e => hr (e ▸ hd), ite_false],
   rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.mono {vs vs' : List VReg} {gs gs' : List Reg} {s t : State} (h : Fr vs gs s t)
    (hv : ∀ r ∈ vs, r ∈ vs') (hg : ∀ r ∈ gs, r ∈ gs') : Fr vs' gs' s t :=
  ⟨fun r hr => h.v r fun e => hr (hv r e), fun r hr => h.g r fun e => hr (hg r e),
   h.mem, h.rd, h.wr, h.sp, h.lr, h.syms⟩

/-! ## A group's loads -/

theorem loads4_run (s : State) {x : Addr} (h5 : s.gpr .r5 = x) (h9 : s.gpr .r9 = 0#64)
    (h8 : s.gpr .r8 = 16#64) (h11 : s.gpr .r11 = 32#64) (h12 : s.gpr .r12 = 48#64)
    (i0 : InRegions (s.rd ++ s.wr) x 16) (i1 : InRegions (s.rd ++ s.wr) (x + 16#64) 16)
    (i2 : InRegions (s.rd ++ s.wr) (x + 32#64) 16) (i3 : InRegions (s.rd ++ s.wr) (x + 48#64) 16) :
    WP isa (.block [.lxvd2x .v8 .r5 .r9, .lxvd2x .v9 .r5 .r8, .lxvd2x .v10 .r5 .r11, .lxvd2x .v11 .r5 .r12]) s
      fun t => (∀ r < 4, t.vpr (tv r) = swapDwords (s.mem.read (x + BitVec.ofNat 64 (16 * r)) 16)) ∧
        Fr [.v8, .v9, .v10, .v11] [] s t := by
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v8 .r5 .r9 s (by decide) (by rw [h5, h9, BitVec.add_zero]; exact i0), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v9 .r5 .r8 _ (by decide) (by
    simp only [gpr_writeV, rd_writeV, wr_writeV, h5, h8]; exact i1), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v10 .r5 .r11 _ (by decide) (by
    simp only [gpr_writeV, rd_writeV, wr_writeV, h5, h11]; exact i2), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v11 .r5 .r12 _ (by decide) (by
    simp only [gpr_writeV, rd_writeV, wr_writeV, h5, h12]; exact i3), ?_⟩
  refine WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · simp only [gpr_writeV, mem_writeV, h5, h8, h9, h11, h12, BitVec.add_zero]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
      simp only [tv, vpr_writeV, reduceCtorEq, ite_true, ite_false, Nat.reduceMul, BitVec.add_zero]
  · exact (((Fr.writeV [.v8, .v9, .v10, .v11] [] s (by decide) _).trans' (Fr.writeV _ _ _ (by decide) _)).trans'
      (Fr.writeV _ _ _ (by decide) _)).trans' (Fr.writeV _ _ _ (by decide) _)

/-! ## A group's stores -/

theorem stores4_run (s : State) {x : Addr} (h5 : s.gpr .r5 = x) (h9 : s.gpr .r9 = 0#64)
    (h8 : s.gpr .r8 = 16#64) (h11 : s.gpr .r11 = 32#64) (h12 : s.gpr .r12 = 48#64)
    (o0 : InRegions s.wr x 16) (o1 : InRegions s.wr (x + 16#64) 16)
    (o2 : InRegions s.wr (x + 32#64) 16) (o3 : InRegions s.wr (x + 48#64) 16) :
    WP isa (.block [.stxvd2x .v8 .r5 .r9, .stxvd2x .v9 .r5 .r8, .stxvd2x .v10 .r5 .r11, .stxvd2x .v11 .r5 .r12,
      .addi .r5 .r5 64, .subi .r10 .r10 1]) s fun t =>
      t.mem = (((s.mem.write x 16 (swapDwords (s.vpr .v8))).write (x + 16#64) 16 (swapDwords (s.vpr .v9))).write
        (x + 32#64) 16 (swapDwords (s.vpr .v10))).write (x + 48#64) 16 (swapDwords (s.vpr .v11)) ∧
      t.gpr .r5 = x + 64 ∧ t.gpr .r10 = s.gpr .r10 - 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.vpr = s.vpr ∧ t.syms = s.syms ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr := by
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v8 .r5 .r9 s (by decide) (by rw [h5, h9, BitVec.add_zero]; exact o0), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v9 .r5 .r8 _ (by decide) (by simp only [h5, h8]; exact o1), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v10 .r5 .r11 _ (by decide) (by simp only [h5, h11]; exact o2), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v11 .r5 .r12 _ (by decide) (by simp only [h5, h12]; exact o3), ?_⟩
  crun [h5, h8, h9, h11, h12]
  intro r h1 h2
  simp [h1, h2]

/-- Four stores of vectors of coefficients, at `j`, `j + 4`, `j + 8`, `j + 12`. -/
theorem polyIs_store4 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j : Nat} (hj : j + 16 ≤ 256)
    {x : Nat → BitVec 128}
    (hx : ∀ r < 4, ∀ e < 4, (vword (x r) e).toNat = (R[j + 4 * r + (e ^^^ 1)]!).val)
    (hR : ∀ i < 256, ¬(j ≤ i ∧ i < j + 16) → R[i]! = P[i]!) :
    PolyIs ((((m.write (coeffAddr p j) 16 (swapDwords (x 0))).write (coeffAddr p j + 16#64) 16
      (swapDwords (x 1))).write (coeffAddr p j + 32#64) 16 (swapDwords (x 2))).write (coeffAddr p j + 48#64) 16
      (swapDwords (x 3))) p R := by
  have e1 : coeffAddr p j + 16#64 = coeffAddr p (j + 4) := coeffAddr_add p j 4
  have e2 : coeffAddr p j + 32#64 = coeffAddr p (j + 8) := coeffAddr_add p j 8
  have e3 : coeffAddr p j + 48#64 = coeffAddr p (j + 12) := coeffAddr_add p j 12
  rw [e1, e2, e3]
  refine polyIs_of_toNat fun i hi => ?_
  have hi' : i < 256 := hi
  rw [coeffAt_store _ _ (by omega) _ hi', coeffAt_store _ _ (by omega) _ hi', coeffAt_store _ _ (by omega) _ hi',
    coeffAt_store _ _ (by omega) _ hi']
  have key : ∀ r < 4, j + 4 * r ≤ i → i < j + 4 * r + 4 → (vword (x r) ((i - (j + 4 * r)) ^^^ 1)).toNat = (R[i]!).val :=
    fun r hr h1 h2 => by
      rw [hx r hr _ (xor1_lt (by omega)), xor1_xor1, show j + 4 * r + (i - (j + 4 * r)) = i by omega]
  by_cases h3 : j + 12 ≤ i ∧ i < j + 12 + 4
  · rw [ite_eq_left h3]; exact key 3 (by decide) (by omega) (by omega)
  rw [ite_eq_right h3]
  by_cases h2 : j + 8 ≤ i ∧ i < j + 8 + 4
  · rw [ite_eq_left h2]; exact key 2 (by decide) (by omega) (by omega)
  rw [ite_eq_right h2]
  by_cases h1 : j + 4 ≤ i ∧ i < j + 4 + 4
  · rw [ite_eq_left h1]; exact key 1 (by decide) (by omega) (by omega)
  rw [ite_eq_right h1]
  by_cases h0 : j ≤ i ∧ i < j + 4
  · rw [ite_eq_left h0]; have := key 0 (by decide) (by omega) (by omega); simpa using this
  rw [ite_eq_right h0, hR i hi' (by omega), polyIs_toNat hP hi]

/-! ## A group's arithmetic -/

/-- What a group's arithmetic needs of the state. -/
structure CEnv (s₀ : State) (u : State) : Prop where
  v4 : ∀ i < 4, (vword (u.vpr .v4) i).toNat = Spec.MlDsa.q
  v5 : u.vpr .v5 = hiC
  v16 : u.vpr .v16 = caC
  v17 : u.vpr .v17 = cbC
  v18 : u.vpr .v18 = ccC
  v19 : u.vpr .v19 = cdC
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  tab : Tab (S s₀) u.mem

theorem CEnv.fr {s₀ u t : State} (h : CEnv s₀ u) {vs : List VReg} {gs : List Reg} (hf : Fr vs gs u t)
    (hv : ∀ r ∈ vs, r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19) : CEnv s₀ t :=
  ⟨fun i hi => by rw [hf.v _ fun e => (hv _ e).1 rfl]; exact h.v4 i hi,
   by rw [hf.v _ fun e => (hv _ e).2.1 rfl, h.v5],
   by rw [hf.v _ fun e => (hv _ e).2.2.1 rfl, h.v16], by rw [hf.v _ fun e => (hv _ e).2.2.2.1 rfl, h.v17],
   by rw [hf.v _ fun e => (hv _ e).2.2.2.2.1 rfl, h.v18], by rw [hf.v _ fun e => (hv _ e).2.2.2.2.2 rfl, h.v19],
   by rw [hf.rd, h.rd], by rw [hf.wr, h.wr], by rw [hf.mem]; exact h.tab⟩

theorem CEnv.of_env {s₀ s : State} (h : Env s₀ s) : CEnv s₀ s :=
  ⟨h.v4, h.v5, h.v16, h.v17, h.v18, h.v19, h.rd, h.wr, h.tab⟩

/-- Lanes of a vector as values of `ℤ_q`. -/
def Lanes (x : BitVec 128) (f : Nat → Zq) : Prop := ∀ r < 4, (vword x r).toNat = (f r).val

/-- Four `z'` loaded from `S + 4P`, and their `z`. -/
theorem zl_run {s₀ : State} (hp : Pre s₀) (u : State) (hc : CEnv s₀ u) {a b : Reg} (ha : a ≠ .r0) {P : Nat}
    (hP0 : 0 < P) (hP : P + 4 ≤ 256) (hab : u.gpr a + u.gpr b = S s₀ + BitVec.ofNat 64 (4 * P))
    {z : Nat → Zq} (hz : ∀ e < 4, zeta (scrK (P + swap1 e)) = (z e).val) :
    WP isa (.block (.lxvd2x .v3 a b :: zcalc)) u fun t =>
      Lanes (t.vpr .v2) z ∧ (∀ r < 4, (vword (t.vpr .v3) r).toNat = (z r).val * 2 ^ 32 / Spec.MlDsa.q) ∧
      Fr [.v2, .v3, .v6, .v7] [] u t := by
  have ia : InRegions (u.rd ++ u.wr) (u.gpr a + u.gpr b) 16 := by
    rw [hab, hc.rd, hc.wr, hp.rd, hp.wr]
    exact ⟨polyRegion (S s₀), by simp, VG.Offset.contains_base (k := 1024) _ (by omega) (by omega)⟩
  refine WP.cons (exec_lxvd2x .v3 a b u ha ia) ?_
  have h3 : ∀ e < 4, (vword ((u.writeV .v3 (swapDwords (u.mem.read (u.gpr a + u.gpr b) 16))).vpr .v3) e).toNat =
      shoup (zeta (scrK (P + swap1 e))) := fun e he => by
    simp only [vpr_writeV, ite_true]
    rw [hab, vword_load _ _ he, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add,
      hc.tab _ (by omega) (by have := xor1_lt he; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (scrV_lt _), scrV,
      flip_eq he]
  refine WP.mono (zcalc_run _ (fun i hi => by simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hc.v4 i hi)
    (by simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hc.v5) (fun _ _ => zeta_lt _) (fun _ _ => zeta_nz _) h3)
    fun t ⟨l, vo, sy⟩ => ⟨fun r hr => by rw [l r hr, hz r hr], fun r hr => ?_, ?_⟩
  · rw [vo.v _ (by decide), h3 r hr, shoup, hz r hr]; rfl
  · exact (Fr.writeV [.v2, .v3, .v6, .v7] [] u (by decide) _).trans' ((Fr.of_vonly vo sy).mono (by decide) (by simp))

/-- A butterfly whose operands' lanes are known. -/
theorem bfly_lanesV {s₀ u t : State} {a b : VReg} {x y : Nat → Zq} {z : Nat → Zq} (hc : CEnv s₀ u)
    (hz : Lanes (u.vpr .v2) z) (hzp : ∀ r < 4, (vword (u.vpr .v3) r).toNat = (z r).val * 2 ^ 32 / Spec.MlDsa.q)
    (ha : Lanes (u.vpr a) x) (hb : Lanes (u.vpr b) y)
    (hta : t.vpr a = bflyA (u.vpr a) (u.vpr b) (u.vpr .v2) (u.vpr .v3) (u.vpr .v4) (u.vpr .v5))
    (htb : t.vpr b = bflyB (u.vpr a) (u.vpr b) (u.vpr .v2) (u.vpr .v3) (u.vpr .v4) (u.vpr .v5)) :
    Lanes (t.vpr a) (fun r => x r + z r * y r) ∧ Lanes (t.vpr b) (fun r => x r - z r * y r) := by
  rw [hc.v5] at hta htb
  exact ⟨fun r hr => by rw [hta]; exact (bfly_lanes hr (ha r hr) (hb r hr) (hz r hr) (hzp r hr) (hc.v4 r hr)).1,
    fun r hr => by rw [htb]; exact (bfly_lanes hr (ha r hr) (hb r hr) (hz r hr) (hzp r hr) (hc.v4 r hr)).2⟩

theorem lanes_eq {x : BitVec 128} {f f' : Nat → Zq} (h : Lanes x f) (e : ∀ r < 4, f r = f' r) : Lanes x f' :=
  fun r hr => by rw [h r hr, e r hr]

/-- The vectors `core` keeps. -/
def coreV : List VReg := [.v2, .v3, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]

theorem coreV_ok : ∀ r ∈ coreV, r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19 := by decide

/-- A group's code between its loads and its stores. -/
def core : List Instr :=
  transpose ++ ((.lxvd2x .v3 .r6 .r9 :: zcalc) ++ (bfly .v9 .v11 .v2 .v3 ++ (bfly .v8 .v10 .v2 .v3 ++
  ((.lxvd2x .v3 .r7 .r9 :: zcalc) ++ (bfly .v9 .v8 .v2 .v3 ++ ((.lxvd2x .v3 .r7 .r8 :: zcalc) ++
  (.addi .r6 .r6 16 :: .addi .r7 .r7 32 :: (bfly .v11 .v10 .v2 .v3 ++ transpose))))))))

def loads4 : List Instr := [.lxvd2x .v8 .r5 .r9, .lxvd2x .v9 .r5 .r8, .lxvd2x .v10 .r5 .r11, .lxvd2x .v11 .r5 .r12]

def stores4 : List Instr := [.stxvd2x .v8 .r5 .r9, .stxvd2x .v9 .r5 .r8, .stxvd2x .v10 .r5 .r11,
  .stxvd2x .v11 .r5 .r12, .addi .r5 .r5 64, .subi .r10 .r10 1]

theorem groupBody_eq : groupBody = loads4 ++ (core ++ stores4) := by
  simp only [groupBody, loads4, core, stores4, List.append_assoc, List.cons_append, List.nil_append]

theorem core_run {s₀ : State} (hp : Pre s₀) (u : State) (hc : CEnv s₀ u) {g : Nat} (hg : g < 16)
    (h6 : u.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * g)))
    (h7 : u.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * g)))
    (h8 : u.gpr .r8 = 16#64) (h9 : u.gpr .r9 = 0#64) {W : Poly}
    (hin : ∀ r < 4, Lanes (u.vpr (tv r)) (fun e => W[16 * g + 4 * r + (e ^^^ 1)]!)) :
    WP isa (.block core) u fun t =>
      (∀ r < 4, Lanes (t.vpr (tv r)) (fun e => (nttLayer (nttLayer W 2) 1)[16 * g + 4 * r + (e ^^^ 1)]!)) ∧
      Fr coreV [.r6, .r7] u t ∧ t.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * (g + 1))) ∧
      t.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * (g + 1))) := by
  unfold core
  rw [WP.block_append_iff]
  refine WP.mono (transpose_run u hc.v16 hc.v17 hc.v18 hc.v19) fun u₁ ⟨l₁, vo₁, sy₁⟩ => ?_
  have f₁ : Fr coreV [.r6, .r7] u u₁ := (Fr.of_vonly vo₁ sy₁).mono (by decide) (by simp)
  have c₁ : CEnv s₀ u₁ := hc.fr f₁ coreV_ok
  have L : ∀ k < 4, Lanes (u₁.vpr (tv k)) (fun r => W[16 * g + 4 * r + (k ^^^ 1)]!) := fun k hk r hr => by
    rw [l₁ k hk r hr]; exact hin r hr k hk
  have L9 := L 1 (by decide); have L8 := L 0 (by decide); have L11 := L 3 (by decide); have L10 := L 2 (by decide)
  simp only [tv, Nat.reduceXor, Nat.add_zero] at L9 L8 L11 L10
  -- `len = 2`
  rw [WP.block_append_iff]
  refine WP.mono (zl_run hp u₁ c₁ (a := .r6) (b := .r9) (by decide) (P := 64 + 4 * g) (by omega) (by omega)
    (by rw [vo₁.gpr, h6, h9, BitVec.add_zero]) (z := fun r => zetas (64 + 4 * g + r))
    fun e he => by rw [scrK_two hg he, zeta_eq]) fun u₂ ⟨Z₂, P₂, f₂⟩ => ?_
  have c₂ : CEnv s₀ u₂ := c₁.fr f₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (bfly_exec u₂ (.inr (.inl ⟨rfl, rfl⟩))) fun u₃ ⟨a₃, b₃, vo₃, sy₃⟩ => ?_
  obtain ⟨M9, M11⟩ := bfly_lanesV c₂ Z₂ P₂ (by rw [f₂.v _ (by decide)]; exact L9)
    (by rw [f₂.v _ (by decide)]; exact L11) a₃ b₃
  have f₃ := Fr.of_vonly vo₃ sy₃
  have c₃ : CEnv s₀ u₃ := c₂.fr f₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (bfly_exec u₃ (.inr (.inr (.inl ⟨rfl, rfl⟩)))) fun u₄ ⟨a₄, b₄, vo₄, sy₄⟩ => ?_
  obtain ⟨M8, M10⟩ := bfly_lanesV c₃ (by rw [f₃.v _ (by decide)]; exact Z₂)
    (by intro r hr; rw [f₃.v _ (by decide)]; exact P₂ r hr)
    (by rw [f₃.v _ (by decide), f₂.v _ (by decide)]; exact L8)
    (by rw [f₃.v _ (by decide), f₂.v _ (by decide)]; exact L10) a₄ b₄
  have f₄ := Fr.of_vonly vo₄ sy₄
  have c₄ : CEnv s₀ u₄ := c₃.fr f₄ (by decide)
  have g₄ : ∀ r, u₄.gpr r = u.gpr r := fun r => by
    rw [f₄.g _ (by simp), f₃.g _ (by simp), f₂.g _ (by simp), vo₁.gpr]
  -- `len = 1`, the even pairs
  rw [WP.block_append_iff]
  refine WP.mono (zl_run hp u₄ c₄ (a := .r7) (b := .r9) (by decide) (P := 128 + 8 * g) (by omega) (by omega)
    (by rw [g₄, g₄, h7, h9, BitVec.add_zero]) (z := fun r => zetas (128 + 8 * g + 2 * r))
    fun e he => by rw [scrK_even hg he, zeta_eq]) fun u₅ ⟨Z₅, P₅, f₅⟩ => ?_
  have c₅ : CEnv s₀ u₅ := c₄.fr f₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (bfly_exec u₅ (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))) fun u₆ ⟨a₆, b₆, vo₆, sy₆⟩ => ?_
  obtain ⟨N9, N8⟩ := bfly_lanesV c₅ Z₅ P₅
    (by rw [f₅.v _ (by decide), f₄.v _ (by decide)]; exact M9)
    (by rw [f₅.v _ (by decide)]; exact M8) a₆ b₆
  have f₆ := Fr.of_vonly vo₆ sy₆
  have c₆ : CEnv s₀ u₆ := c₅.fr f₆ (by decide)
  have g₆ : ∀ r, u₆.gpr r = u.gpr r := fun r => by rw [f₆.g _ (by simp), f₅.g _ (by simp), g₄]
  -- `len = 1`, the odd pairs
  rw [WP.block_append_iff]
  refine WP.mono (zl_run hp u₆ c₆ (a := .r7) (b := .r8) (by decide) (P := 132 + 8 * g) (by omega) (by omega)
    (by rw [g₆, g₆, h7, h8, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (128 + 8 * g) + 16 = 4 * (132 + 8 * g) by omega])
    (z := fun r => zetas (128 + 8 * g + 2 * r + 1))
    fun e he => by rw [scrK_odd hg he, zeta_eq]) fun u₇ ⟨Z₇, P₇, f₇⟩ => ?_
  have c₇ : CEnv s₀ u₇ := c₆.fr f₇ (by decide)
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, ?_⟩⟩
  generalize hu₈ : State.write (State.write u₇ _ _) _ _ = u₈
  have f₈ : Fr [] [.r6, .r7] u₇ u₈ := by
    rw [← hu₈]; exact (Fr.write _ _ _ (by decide) _).trans' (Fr.write _ _ _ (by decide) _)
  have r6₈ : u₈.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * (g + 1))) := by
    rw [← hu₈]; simp only [State.write, reduceCtorEq, ite_false, ite_true]
    rw [f₇.g _ (by simp), g₆, h6, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (64 + 4 * g) + 16 = 4 * (64 + 4 * (g + 1)) by omega]
  have r7₈ : u₈.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * (g + 1))) := by
    rw [← hu₈]; simp only [State.write, reduceCtorEq, ite_false, ite_true]
    rw [f₇.g _ (by simp), g₆, h7, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (128 + 8 * g) + 32 = 4 * (128 + 8 * (g + 1)) by omega]
  have c₈ : CEnv s₀ u₈ := c₇.fr f₈ (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (bfly_exec u₈ (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))) fun u₉ ⟨a₉, b₉, vo₉, sy₉⟩ => ?_
  obtain ⟨N11, N10⟩ := bfly_lanesV c₈ (by rw [f₈.v _ (by simp)]; exact Z₇)
    (by intro r hr; rw [f₈.v _ (by simp)]; exact P₇ r hr)
    (by rw [f₈.v _ (by simp), f₇.v _ (by decide), f₆.v _ (by decide), f₅.v _ (by decide), f₄.v _ (by decide)]
        exact M11)
    (by rw [f₈.v _ (by simp), f₇.v _ (by decide), f₆.v _ (by decide), f₅.v _ (by decide)]; exact M10) a₉ b₉
  have f₉ := Fr.of_vonly vo₉ sy₉
  have c₉ : CEnv s₀ u₉ := c₈.fr f₉ (by decide)
  -- back
  refine WP.mono (transpose_run u₉ c₉.v16 c₉.v17 c₉.v18 c₉.v19) fun u₁₀ ⟨l₁₀, vo₁₀, sy₁₀⟩ => ?_
  have f₁₀ := Fr.of_vonly vo₁₀ sy₁₀
  have P9 := N9
  rw [← f₇.v .v9 (by decide), ← f₈.v .v9 (by simp), ← f₉.v .v9 (by decide)] at P9
  have P8 := N8
  rw [← f₇.v .v8 (by decide), ← f₈.v .v8 (by simp), ← f₉.v .v8 (by decide)] at P8
  refine ⟨fun r hr e he => ?_, ?_, ?_, ?_⟩
  · obtain ⟨e0, e1, e2, e3, t0, t1, t2, t3⟩ := layers_block W hg hr
    rw [l₁₀ r hr e he]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
      simp only [tv, Nat.reduceXor]
    · rw [P8 r hr, t1, e0, e1]
    · rw [P9 r hr, Nat.add_zero, t0, e0, e1]
    · rw [N10 r hr, t3, e2, e3]
    · rw [N11 r hr, t2, e2, e3]
  · exact (((((((((f₁.trans' (f₂.mono (by decide) (by simp))).trans' (f₃.mono (by decide) (by simp))).trans'
      (f₄.mono (by decide) (by simp))).trans' (f₅.mono (by decide) (by simp))).trans' (f₆.mono (by decide) (by simp))).trans'
      (f₇.mono (by decide) (by simp))).trans' (f₈.mono (by simp) (by simp))).trans' (f₉.mono (by decide) (by simp))).trans'
      (f₁₀.mono (by decide) (by simp)))
  · rw [f₁₀.g _ (by simp), f₉.g _ (by simp), r6₈]
  · rw [f₁₀.g _ (by simp), f₉.g _ (by simp), r7₈]

/-! ## Groups -/

/-- The polynomial after `g` groups, from `W`. -/
def mix (g : Nat) (W : Poly) : Poly :=
  Vector.ofFn fun i => if i.val < 16 * g then (nttLayer (nttLayer W 2) 1)[i.val]! else W[i.val]!

theorem mix_get (g : Nat) (W : Poly) {i : Nat} (hi : i < 256) :
    (mix g W)[i]! = if i < 16 * g then (nttLayer (nttLayer W 2) 1)[i]! else W[i]! := by
  rw [VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
  simp only [mix, Vector.getElem_ofFn]

/-- After `g` groups, from `W`. -/
structure GInv (s₀ : State) (W : Poly) (g : Nat) (s : State) : Prop where
  env : Env s₀ s
  r5 : s.gpr .r5 = coeffAddr (F s₀) (16 * g)
  r9 : s.gpr .r9 = 0#64
  r8 : s.gpr .r8 = 16#64
  r11 : s.gpr .r11 = 32#64
  r12 : s.gpr .r12 = 48#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (16 - g)
  r6 : s.gpr .r6 = S s₀ + BitVec.ofNat 64 (4 * (64 + 4 * g))
  r7 : s.gpr .r7 = S s₀ + BitVec.ofNat 64 (4 * (128 + 8 * g))
  poly : PolyIs s.mem (F s₀) (mix g W)

theorem group_ok {s₀ : State} (hp : Pre s₀) {W : Poly} {g : Nat} (hg : g < 16) {s : State}
    (h : GInv s₀ W g s) :
    WP isa (.block groupBody) s fun s' => GInv s₀ W (g + 1) s' ∧ (s'.gpr .r10 != 0) = decide (g + 1 ≠ 16) := by
  have ea : ∀ k, coeffAddr (F s₀) (16 * g) + BitVec.ofNat 64 (4 * k) = coeffAddr (F s₀) (16 * g + k) :=
    fun k => coeffAddr_add _ _ _
  have e16 : coeffAddr (F s₀) (16 * g) + 16#64 = coeffAddr (F s₀) (16 * g + 4) := ea 4
  have e32 : coeffAddr (F s₀) (16 * g) + 32#64 = coeffAddr (F s₀) (16 * g + 8) := ea 8
  have e48 : coeffAddr (F s₀) (16 * g) + 48#64 = coeffAddr (F s₀) (16 * g + 12) := ea 12
  rw [groupBody_eq, WP.block_append_iff]
  refine WP.mono (loads4_run s h.r5 h.r9 h.r8 h.r11 h.r12 (h.env.inR hp (by omega))
    (by rw [e16]; exact h.env.inR hp (by omega)) (by rw [e32]; exact h.env.inR hp (by omega))
    (by rw [e48]; exact h.env.inR hp (by omega))) fun u₁ ⟨l₁, f₁⟩ => ?_
  have c₁ : CEnv s₀ u₁ := (CEnv.of_env h.env).fr f₁ (by decide)
  have hin : ∀ r < 4, Lanes (u₁.vpr (tv r)) (fun e => W[16 * g + 4 * r + (e ^^^ 1)]!) := fun r hr e he => by
    have hx := xor1_lt he
    rw [l₁ r hr, show 16 * r = 4 * (4 * r) by omega, ea, vword_loadC _ _ _ he, polyIs_toNat h.poly (by show _ < 256; omega),
      mix_get _ _ (by omega), ite_eq_right (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (core_run hp u₁ c₁ hg (by rw [f₁.g _ (by simp)]; exact h.r6) (by rw [f₁.g _ (by simp)]; exact h.r7)
    (by rw [f₁.g _ (by simp)]; exact h.r8) (by rw [f₁.g _ (by simp)]; exact h.r9) hin)
    fun u₂ ⟨l₂, f₂, r6₂, r7₂⟩ => ?_
  have g₂ : ∀ r, r ∉ [.r6, .r7] → u₂.gpr r = s.gpr r := fun r hr => by
    rw [f₂.g r hr, f₁.g r (by simp)]
  refine WP.mono (stores4_run u₂ (x := coeffAddr (F s₀) (16 * g)) (by rw [g₂ _ (by decide), h.r5])
    (by rw [g₂ _ (by decide), h.r9]) (by rw [g₂ _ (by decide), h.r8]) (by rw [g₂ _ (by decide), h.r11])
    (by rw [g₂ _ (by decide), h.r12]) (by rw [f₂.wr, f₁.wr]; exact h.env.inW hp (by omega))
    (by rw [f₂.wr, f₁.wr, e16]; exact h.env.inW hp (by omega))
    (by rw [f₂.wr, f₁.wr, e32]; exact h.env.inW hp (by omega))
    (by rw [f₂.wr, f₁.wr, e48]; exact h.env.inW hp (by omega)))
    fun u₃ ⟨m₃, r5₃, r10₃, gk₃, v₃, sy₃, rd₃, wr₃, sp₃, lr₃⟩ => ?_
  have hm : u₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have hv : ∀ r, r ∉ [.v8, .v9, .v10, .v11] ++ coreV → u₃.vpr r = s.vpr r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [v₃, f₂.v r hr.2, f₁.v r hr.1]
  have hg₃ : ∀ r, r ≠ .r5 → r ≠ .r10 → r ∉ [.r6, .r7] → u₃.gpr r = s.gpr r := fun r h5 h10 h67 => by
    rw [gk₃ r h5 h10, g₂ r h67]
  have g₂10 : u₂.gpr .r10 = s.gpr .r10 := g₂ _ (by decide)
  refine ⟨⟨⟨(hg₃ .r3 (by decide) (by decide) (by decide)).trans h.env.r3,
      fun i hi => by rw [hv .v4 (by decide)]; exact h.env.v4 i hi,
      (hv .v5 (by decide)).trans h.env.v5, (hv .v16 (by decide)).trans h.env.v16,
      (hv .v17 (by decide)).trans h.env.v17, (hv .v18 (by decide)).trans h.env.v18,
      (hv .v19 (by decide)).trans h.env.v19,
      fun r hr => (hg₃ r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
        (fun e => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at e
          rcases e with rfl | rfl <;> decide))).trans (h.env.keep r hr),
      by rw [rd₃, f₂.rd, f₁.rd, h.env.rd], by rw [wr₃, f₂.wr, f₁.wr, h.env.wr],
      by rw [sp₃, f₂.sp, f₁.sp, h.env.sp], by rw [lr₃, f₂.lr, f₁.lr, h.env.lr], ?_, ?_⟩,
    ?_, (hg₃ .r9 (by decide) (by decide) (by decide)).trans h.r9,
    (hg₃ .r8 (by decide) (by decide) (by decide)).trans h.r8,
    (hg₃ .r11 (by decide) (by decide) (by decide)).trans h.r11,
    (hg₃ .r12 (by decide) (by decide) (by decide)).trans h.r12, ?_,
    by rw [gk₃ _ (by decide) (by decide), r6₂], by rw [gk₃ _ (by decide) (by decide), r7₂], ?_⟩, ?_⟩
  · rw [m₃, hm, e16, e32, e48]
    exact (((h.env.frame.write (by simp) _ (vector_contains _ (j := 16 * g) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 4) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 8) (by omega))).write (by simp) _
      (vector_contains _ (j := 16 * g + 12) (by omega))
  · rw [m₃, hm, e16, e32, e48]
    exact tab_write hp (j := 16 * g + 12) (tab_write hp (j := 16 * g + 8) (tab_write hp (j := 16 * g + 4)
      (tab_write hp (j := 16 * g) h.env.tab (by omega) _) (by omega) _) (by omega) _) (by omega) _
  · rw [r5₃, show (64 : BitVec 64) = BitVec.ofNat 64 (4 * 16) from rfl, ea]
    exact congrArg _ (by omega)
  · rw [r10₃, g₂10, h.r10]; exact count_sub hg
  · rw [m₃, hm]
    refine polyIs_store4 (x := fun r => u₂.vpr (tv r)) h.poly (by omega) (fun r hr e he => ?_) (fun i hi hn => ?_)
    · rw [mix_get _ _ (by have := xor1_lt he; omega), ite_eq_left (by have := xor1_lt he; omega)]
      exact l₂ r hr e he
    · rw [mix_get _ _ hi, mix_get _ _ hi]
      by_cases hi' : i < 16 * g
      · rw [ite_eq_left (by omega), ite_eq_left hi']
      · rw [ite_eq_right (by omega), ite_eq_right hi']
  · rw [r10₃, g₂10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
    exact count_nz hg (by decide)

theorem mix_zero (W : Poly) : mix 0 W = W :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by rw [mix_get _ _ hi, ite_eq_right (by omega)]

theorem mix_sixteen (W : Poly) : mix 16 W = nttLayer (nttLayer W 2) 1 :=
  VG.Proof.MlDsa.Arith.ext_getElem! fun i hi => by rw [mix_get _ _ hi, ite_eq_left (by show i < 256; exact hi)]

theorem narrow_ok {s₀ : State} (hp : Pre s₀) {R : Poly} {s : State} (h : LInv s₀ R 2 64 s) :
    WP isa narrowLayers s fun s' => Env s₀ s' ∧ PolyIs s'.mem (F s₀) (nttLayer (nttLayer R 2) 1) := by
  unfold narrowLayers
  refine WP.seq (WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl,
    WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl,
    WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩⟩⟩⟩⟩⟩⟩)
  refine wp_loop_nz (fun g t => GInv s₀ R g t) (N := 16) (by decide) (fun g hg t ht => group_ok hp hg ht)
    (fun t ht => ⟨ht.env, by rw [← mix_sixteen]; exact ht.poly⟩) ?_
  have r4 : s.gpr .r4 = S s₀ := h.env.keep .r4 (by decide)
  refine ⟨((((((h.env.write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.write, reduceCtorEq, ite_false, ite_true]
  · rw [h.env.r3, coeffAddr]
  · exact h.r9
  · rw [r4]
  · rw [r4]
  · rw [mix_zero]; exact h.poly

end VG.Proof.MlDsa.PPC64LE.VNtt
