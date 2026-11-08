module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNttInv.Verified
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VMul
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNttInv.Verified
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.VMul
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub

/-! # ML-DSA's vector `multiplyNTT` on PPC64LE: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

One lane of Montgomery's reduction (`mont_lane`) and of the product by
`2³² mod q` (`mul_lanes`); `mont` run one instruction at a time
(`mont_exec`); four coefficients of `h` per iteration (`MInv`, `mstep_ok`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt
open VG.Proof.MlDsa (PolyIs coeffAt Reduced polyAt)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add polyRegion polyAt_val polyIs_of_toNat coeffAt_frame
  val_mul val_add' mul_get add_get)
open VG.Proof.MlKem.PPC64LE (count_sub count_nz wp_loop_nz)
open VG.Spec.MlDsa (Poly Zq)

/-! ## One lane -/

/-- Montgomery's reduction of `a·b`: a value less than `q` that is `a·b·2⁻³²`
modulo `q`, from the high words `H` of `a·b` and `M` of `m·q`. -/
theorem mont_lane (a b qv qi H M : BitVec 32) (hqv : qv.toNat = 8380417) (hqi : qi.toNat = 58728449)
    (ha : a.toNat < 8380417) (hb : b.toNat < 8380417)
    (hH : H.toNat = a.toNat * b.toNat / 2 ^ 32) (hM : M.toNat = (a * b * qi).toNat * qv.toNat / 2 ^ 32) :
    (minu32 (H - M) (H - M + qv)).toNat < 8380417 ∧
    (minu32 (H - M) (H - M + qv)).toNat * 2 ^ 32 % 8380417 = a.toNat * b.toNat % 8380417 := by
  have hm : (a * b * qi).toNat = a.toNat * b.toNat % 2 ^ 32 * 58728449 % 2 ^ 32 := by
    rw [BitVec.toNat_mul, BitVec.toNat_mul, hqi]
  generalize hP : a.toNat * b.toNat = P at hH hm
  generalize hmv : (a * b * qi).toNat = m at hM hm
  rw [hqv] at hM
  have hP' : P < 8380417 * 8380417 := hP ▸ Nat.mul_lt_mul'' ha hb
  have hmlt : m < 2 ^ 32 := by rw [hm]; exact Nat.mod_lt _ (by decide)
  generalize hL : P % 2 ^ 32 = L at hm
  have hLm : m * 8380417 % 2 ^ 32 = L := by
    have hL' : L < 2 ^ 32 := hL ▸ Nat.mod_lt _ (by decide)
    rw [hm, Nat.mod_mul_mod, show L * 58728449 * 8380417 = L + L * 114592 * 2 ^ 32 by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hL']
  have dP := Nat.div_add_mod P (2 ^ 32)
  have dM := Nat.div_add_mod (m * 8380417) (2 ^ 32)
  rw [hL] at dP
  rw [hLm] at dM
  rw [← hH] at dP
  rw [← hM] at dM
  have hHq : H.toNat < qv.toNat := by rw [hqv]; omega
  have hMq : M.toNat < qv.toNat := by rw [hqv]; omega
  rw [minu_sub_lane (by rw [hqv]; decide) hHq hMq, hqv]
  refine ⟨Nat.mod_lt _ (by decide), ?_⟩
  rw [Nat.mod_mul_mod]
  have e : (H.toNat + (8380417 - M.toNat)) * 2 ^ 32 + m * 8380417 = P + 2 ^ 32 * 8380417 := by
    rw [hqv] at hMq; omega
  have := congrArg (· % 8380417) e
  simp only [Nat.add_mul_mod_self_right] at this
  exact this

/-! ## Montgomery's reduction, vector by vector -/

def montM (a b qi : BitVec 128) : BitVec 128 := loV (loV a b) qi

def montV (a b qv qi c : BitVec 128) : BitVec 128 :=
  minV (subV (permV (mulEV a b) (mulOV a b) c) (permV (mulEV (montM a b qi) qv) (mulOV (montM a b qi) qv) c))
    (addV (subV (permV (mulEV a b) (mulOV a b) c) (permV (mulEV (montM a b qi) qv) (mulOV (montM a b qi) qv) c)) qv)

set_option linter.unusedSimpArgs false in
theorem mont_exec (s : State) :
    WP isa (.block mont) s fun t =>
      t.vpr .v8 = montV (s.vpr .v8) (s.vpr .v9) (s.vpr .v4) (s.vpr .v13) (s.vpr .v5) ∧
      VOnly [.v8, .v6, .v7, .v10, .v11] s t ∧ t.syms = s.syms := by
  unfold mont
  refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_mulE _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_mulO _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_mulE _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_mulO _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine WP.block_nil ?_
  refine ⟨rfl, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  rotate_left
  all_goals try simp only [gpr_writeV, mem_writeV, rd_writeV, wr_writeV, sp_writeV, lr_writeV, syms_writeV]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3, r4, r5⟩ := hr
  simp only [vpr_writeV, r1, r2, r3, r4, r5, ite_false]

/-- Lane `i` of `f·g mod q`. -/
theorem mul_lanes {A B Q QI Z ZP : BitVec 128} {x y : Zq} {i : Nat} (hi : i < 4)
    (hA : (vword A i).toNat = x.val) (hB : (vword B i).toNat = y.val) (hQ : (vword Q i).toNat = Spec.MlDsa.q)
    (hQI : (vword QI i).toNat = 58728449) (hZ : (vword Z i).toNat = (4193792 : Zq).val)
    (hZP : (vword ZP i).toNat = (4193792 : Zq).val * 2 ^ 32 / Spec.MlDsa.q) :
    (vword (smulV (montV A B Q QI hiC) Z ZP Q hiC) i).toNat = (x * y).val := by
  have hH := vword_hi A B hi
  have hM := vword_hi (montM A B QI) Q hi
  simp only [montM, vword_loV _ _ hi] at hM
  obtain ⟨l, e⟩ := mont_lane (vword A i) (vword B i) (vword Q i) (vword QI i) _ _ hQ hQI
    (by rw [hA]; exact x.isLt) (by rw [hB]; exact y.isLt) hH hM
  have hR : (vword (montV A B Q QI hiC) i).toNat = (⟨_, l⟩ : Zq).val := by
    simp only [montV, vword_minV _ _ hi, vword_subV _ _ hi, vword_addV _ _ hi]; rfl
  rw [smul_lanes hi hR hZ hZP hQ, val_mul, val_mul, ← hA, ← hB, ← e]
  show 4193792 * _ % 8380417 = _ % 8380417
  rw [Nat.mul_comm, Nat.mul_mod, Nat.mul_mod _ (2 ^ 32)]

/-! ## The loop -/

section
variable (s₀ : State)
abbrev MH : Addr := s₀.gpr .r3
abbrev MF : Addr := s₀.gpr .r4
abbrev MG : Addr := s₀.gpr .r5
end

structure MPre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (MF s₀), polyRegion (MG s₀)]
  wr : s₀.wr = [polyRegion (MH s₀)]
  hf : (polyRegion (MH s₀)).Disjoint (polyRegion (MF s₀))
  hg : (polyRegion (MH s₀)).Disjoint (polyRegion (MG s₀))
  fitH : (MH s₀).toNat + 1024 ≤ 2 ^ 64
  fitF : (MF s₀).toNat + 1024 ≤ 2 ^ 64
  fitG : (MG s₀).toNat + 1024 ≤ 2 ^ 64
  redF : Reduced s₀.mem (MF s₀)
  redG : Reduced s₀.mem (MG s₀)

def mwritten : List Reg := [.r3, .r4, .r5, .r9, .r10, .r11, .r12]

/-- After `i` iterations, from `s₀`, coefficient `j < 4i` of `h` holding `R`'s. -/
structure MInv (R : Poly) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = coeffAddr (MH s₀) (4 * i)
  r4 : s.gpr .r4 = coeffAddr (MF s₀) (4 * i)
  r5 : s.gpr .r5 = coeffAddr (MG s₀) (4 * i)
  r9 : s.gpr .r9 = 0#64
  r10 : s.gpr .r10 = BitVec.ofNat 64 (64 - i)
  v4 : ∀ i < 4, (vword (s.vpr .v4) i).toNat = Spec.MlDsa.q
  v5 : s.vpr .v5 = hiC
  v13 : ∀ i < 4, (vword (s.vpr .v13) i).toNat = 58728449
  v2 : ∀ i < 4, (vword (s.vpr .v2) i).toNat = (4193792 : Zq).val
  v3 : ∀ i < 4, (vword (s.vpr .v3) i).toNat = (4193792 : Zq).val * 2 ^ 32 / Spec.MlDsa.q
  keep : ∀ r, r ∉ mwritten → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [polyRegion (MH s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, (coeffAt s.mem (MH s₀) j).toNat =
    if j < 4 * i then (R[j]!).val else (coeffAt s₀.mem (MH s₀) j).toNat

/-- The lanes of a load from `f` or `g`, as on entry. -/
theorem mload_lanes {s₀ : State} {m : Mem} (hf : Frame [polyRegion (MH s₀)] s₀.mem m)
    {p : Addr} (hd : (polyRegion (MH s₀)).Disjoint (polyRegion p)) (hr : Reduced s₀.mem p) {i : Nat}
    (hi : i < 64) {e : Nat} (he : e < 4) :
    (vword (swapDwords (m.read (coeffAddr p (4 * i)) 16)) e).toNat = ((polyAt s₀.mem p)[4 * i + (e ^^^ 1)]!).val := by
  have hx := xor1_lt he
  rw [vword_loadC _ _ _ he, coeffAt_frame hf (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd.symm) (by show _ < 256; omega),
    polyAt_val hr (by show _ < 256; omega)]

theorem mtail_run (s : State) {x y z : Addr} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = z)
    (h9 : s.gpr .r9 = 0#64) (o : InRegions s.wr x 16) :
    WP isa (.block [.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16,
      .subi .r10 .r10 1]) s fun t =>
      t.mem = s.mem.write x 16 (swapDwords (s.vpr .v8)) ∧ t.gpr .r3 = x + 16 ∧ t.gpr .r4 = y + 16 ∧
      t.gpr .r5 = z + 16 ∧ t.gpr .r10 = s.gpr .r10 - 1 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.vpr = s.vpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr := by
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v8 .r3 .r9 s (by decide) (by rw [h3, h9, BitVec.add_zero]; exact o), ?_⟩
  crun [h3, h4, h5, h9]
  intro r h1 h2 h3 h4
  simp [h1, h2, h3, h4]

theorem mstep_ok {s₀ : State} (hp : MPre s₀) {R : Poly} {i : Nat} (hi : i < 64) {s : State}
    (h : MInv R s₀ i s) {body : List Instr}
    (hbody : ∀ u : State, u.gpr .r3 = coeffAddr (MH s₀) (4 * i) → u.gpr .r9 = 0#64 →
      InRegions (u.rd ++ u.wr) (coeffAddr (MH s₀) (4 * i)) 16 →
      (∀ i < 4, (vword (u.vpr .v4) i).toNat = Spec.MlDsa.q) → u.vpr .v5 = hiC →
      (∀ i < 4, (vword (u.vpr .v13) i).toNat = 58728449) →
      (∀ i < 4, (vword (u.vpr .v2) i).toNat = (4193792 : Zq).val) →
      (∀ i < 4, (vword (u.vpr .v3) i).toNat = (4193792 : Zq).val * 2 ^ 32 / Spec.MlDsa.q) →
      (∀ e < 4, (vword (u.vpr .v8) e).toNat = ((polyAt s₀.mem (MF s₀))[4 * i + (e ^^^ 1)]!).val) →
      (∀ e < 4, (vword (u.vpr .v9) e).toNat = ((polyAt s₀.mem (MG s₀))[4 * i + (e ^^^ 1)]!).val) →
      (∀ e < 4, (vword (swapDwords (u.mem.read (coeffAddr (MH s₀) (4 * i)) 16)) e).toNat =
        (coeffAt s₀.mem (MH s₀) (4 * i + (e ^^^ 1))).toNat) →
      WP isa (.block body) u fun t => (∀ e < 4, (vword (t.vpr .v8) e).toNat = (R[4 * i + (e ^^^ 1)]!).val) ∧
        VOnly [.v8, .v9, .v6, .v7, .v10, .v11] u t) :
    WP isa (.block (([.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] : List Instr) ++ body ++
      ([.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1] : List Instr))) s
      fun s' => MInv R s₀ (i + 1) s' ∧ (s'.gpr .r10 != 0) = decide (i + 1 ≠ 64) := by
  have iF : InRegions (s.rd ++ s.wr) (coeffAddr (MF s₀) (4 * i)) 16 := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, vector_contains _ (by omega)⟩
  have iG : InRegions (s.rd ++ s.wr) (coeffAddr (MG s₀) (4 * i)) 16 := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, vector_contains _ (by omega)⟩
  have iH : InRegions (s.rd ++ s.wr) (coeffAddr (MH s₀) (4 * i)) 16 := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, vector_contains _ (by omega)⟩
  have oH : InRegions s.wr (coeffAddr (MH s₀) (4 * i)) 16 := by
    rw [h.wr, hp.wr]; exact ⟨_, by simp, vector_contains _ (by omega)⟩
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v8 .r4 .r9 s (by decide) (by rw [h.r4, h.r9, BitVec.add_zero]; exact iF), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v9 .r5 .r9 _ (by decide) (by
    simp only [gpr_writeV, rd_writeV, wr_writeV, h.r5, h.r9, BitVec.add_zero]; exact iG), WP.block_nil ?_⟩
  simp only [gpr_writeV, mem_writeV, h.r4, h.r5, h.r9, BitVec.add_zero]
  generalize hu : State.writeV _ _ _ = u
  have gu : u.gpr = s.gpr := by rw [← hu]; rfl
  have mu : u.mem = s.mem := by rw [← hu]; rfl
  have vu : ∀ r, r ≠ .v8 → r ≠ .v9 → u.vpr r = s.vpr r := fun r h8 h9 => by
    rw [← hu]; simp only [vpr_writeV, h8, h9, ite_false]
  have A : u.vpr .v8 = swapDwords (s.mem.read (coeffAddr (MF s₀) (4 * i)) 16) := by
    rw [← hu]; simp only [vpr_writeV, reduceCtorEq, ite_false, ite_true]
  have B : u.vpr .v9 = swapDwords (s.mem.read (coeffAddr (MG s₀) (4 * i)) 16) := by
    rw [← hu]; simp only [vpr_writeV, ite_true]
  rw [WP.block_append_iff]
  refine WP.mono (hbody u (by rw [gu]; exact h.r3) (by rw [gu]; exact h.r9)
    (by rw [show u.rd = s.rd by rw [← hu]; rfl, show u.wr = s.wr by rw [← hu]; rfl]; exact iH)
    (by rw [vu _ (by decide) (by decide)]; exact h.v4) (by rw [vu _ (by decide) (by decide)]; exact h.v5)
    (by rw [vu _ (by decide) (by decide)]; exact h.v13) (by rw [vu _ (by decide) (by decide)]; exact h.v2)
    (by rw [vu _ (by decide) (by decide)]; exact h.v3)
    (fun e he => by rw [A]; exact mload_lanes h.frame hp.hf hp.redF hi he)
    (fun e he => by rw [B]; exact mload_lanes h.frame hp.hg hp.redG hi he)
    (fun e he => by
      have hx := xor1_lt he
      rw [mu, vword_loadC _ _ _ he, h.coeff _ (by omega), ite_eq_right (by omega)]))
    fun t ⟨lanes, vo⟩ => ?_
  have gt : t.gpr = s.gpr := by rw [vo.gpr, gu]
  refine WP.mono (mtail_run t (x := coeffAddr (MH s₀) (4 * i)) (y := coeffAddr (MF s₀) (4 * i))
    (z := coeffAddr (MG s₀) (4 * i)) (by rw [gt]; exact h.r3) (by rw [gt]; exact h.r4) (by rw [gt]; exact h.r5)
    (by rw [gt]; exact h.r9) (by rw [vo.wr, show u.wr = s.wr by rw [← hu]; rfl]; exact oH))
    fun s' ⟨m', r3', r4', r5', r10', g', v', rd', wr', sp', lr'⟩ => ?_
  have hv : ∀ r, r ∉ [.v8, .v9, .v6, .v7, .v10, .v11] → s'.vpr r = s.vpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v', vo.v r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      vu r hr.1 hr.2.1]
  have hg : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → s'.gpr r = s.gpr r := fun r a b c d => by
    rw [g' r a b c d, gt]
  have ea : ∀ (p : Addr), coeffAddr p (4 * i) + 16 = coeffAddr p (4 * (i + 1)) := fun p => by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add]
    exact congrArg _ (by omega)
  refine ⟨⟨by rw [r3', ea], by rw [r4', ea], by rw [r5', ea], (hg .r9 (by decide) (by decide) (by decide) (by decide)).trans h.r9,
    by rw [r10', gt, h.r10]; exact count_sub hi,
    by rw [hv .v4 (by decide)]; exact h.v4, (hv .v5 (by decide)).trans h.v5,
    by rw [hv .v13 (by decide)]; exact h.v13, by rw [hv .v2 (by decide)]; exact h.v2,
    by rw [hv .v3 (by decide)]; exact h.v3,
    fun r hr => (hg r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
      (fun e => hr (e ▸ by decide))).trans (h.keep r hr),
    by rw [rd', vo.rd, show u.rd = s.rd by rw [← hu]; rfl, h.rd],
    by rw [wr', vo.wr, show u.wr = s.wr by rw [← hu]; rfl, h.wr],
    by rw [sp', vo.sp, show u.sp = s.sp by rw [← hu]; rfl, h.sp],
    by rw [lr', vo.lr, show u.lr = s.lr by rw [← hu]; rfl, h.lr], ?_, ?_⟩, ?_⟩
  · rw [m', vo.mem, mu]
    exact h.frame.write (by simp) _ (vector_contains _ (by omega))
  · intro j hj
    rw [m', vo.mem, mu, coeffAt_store _ _ (by omega) _ hj]
    by_cases hj1 : 4 * i ≤ j ∧ j < 4 * i + 4
    · rw [ite_eq_left hj1, ite_eq_left (by omega)]
      have := lanes ((j - 4 * i) ^^^ 1) (xor1_lt (by omega))
      rwa [xor1_xor1, show 4 * i + (j - 4 * i) = j by omega] at this
    · rw [ite_eq_right hj1, h.coeff j hj]
      by_cases hj2 : j < 4 * i
      · rw [ite_eq_left hj2, ite_eq_left (by omega)]
      · rw [ite_eq_right hj2, ite_eq_right (by omega)]
  · rw [r10', gt, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

/-! ## The constants -/

theorem mhead_ok {s₀ : State} {R : Poly} :
    WP isa (.block mulConsts) s₀ (MInv R s₀ 0) := by
  unfold mulConsts splatW
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (consts_run s₀) fun t₁ h₁ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (splat_imm t₁ (d := .v13) (v := qInv) (by decide)) fun t₂ ⟨l₂, f₂⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (splat_imm t₂ (d := .v2) (v := rMod) (by decide)) fun t₃ ⟨l₃, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (splat_imm t₃ (d := .v3) (v := shoup rMod) (by decide)) fun t₄ ⟨l₄, f₄⟩ => ?_
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩⟩
  have f : Fr [.v13, .v2, .v3] [.r12] t₁ t₄ :=
    ((f₂.mono (by decide) (by simp)).trans' (f₃.mono (by decide) (by simp))).trans' (f₄.mono (by decide) (by simp))
  have g : ∀ r, r ≠ .r11 → r ≠ .r12 → t₄.gpr r = s₀.gpr r := fun r h11 h12 => by
    rw [f.g _ (by simp [h12]), h₁.gpr r h11 h12]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false]; rw [g _ (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · simp only [State.write, reduceCtorEq, ite_false]; rw [g _ (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · simp only [State.write, reduceCtorEq, ite_false]; rw [g _ (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]
  · simp only [State.write, ite_true]
  · intro i hi; show (vword (t₄.vpr .v4) i).toNat = _; rw [f.v _ (by decide)]; exact h₁.q i hi
  · show t₄.vpr .v5 = _; rw [f.v _ (by decide)]; exact h₁.v5
  · intro i hi; show (vword (t₄.vpr .v13) i).toNat = _
    rw [f₄.v _ (by decide), f₃.v _ (by decide), l₂ i hi]; rfl
  · intro i hi; show (vword (t₄.vpr .v2) i).toNat = _; rw [f₄.v _ (by decide), l₃ i hi]; rfl
  · intro i hi; show (vword (t₄.vpr .v3) i).toNat = _; rw [l₄ i hi]; rfl
  · have h9 : r ≠ .r9 := fun e => hr (e ▸ by decide)
    have h10 : r ≠ .r10 := fun e => hr (e ▸ by decide)
    simp only [State.write, h9, h10, ite_false]
    exact g r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))
  · show t₄.rd = _; rw [f.rd, h₁.rd]
  · show t₄.wr = _; rw [f.wr, h₁.wr]
  · show t₄.sp = _; rw [f.sp, h₁.sp]
  · show t₄.lr = _; rw [f.lr, h₁.lr]
  · show Frame _ s₀.mem t₄.mem
    rw [f.mem, h₁.mem]; exact Frame.refl _ _
  · show (coeffAt t₄.mem _ j).toNat = _
    rw [f.mem, h₁.mem, ite_eq_right (by omega)]

theorem mloop_ok {s₀ : State} {R : Poly} {body : List Instr}
    (hstep : ∀ i < 64, ∀ s, MInv R s₀ i s →
      WP isa (.block (([.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] : List Instr) ++ body ++
        ([.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1] : List Instr))) s
        fun s' => MInv R s₀ (i + 1) s' ∧ (s'.gpr .r10 != 0) = decide (i + 1 ≠ 64)) :
    WP isa (.seq (.block mulConsts) (.loop (.block (([.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] : List Instr) ++ body ++
        ([.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1] : List Instr)))
      (.nonzero .d .r10))) s₀ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧ PolyIs s.mem (MH s₀) R :=
  WP.seq (WP.mono mhead_ok fun s h => wp_loop_nz (MInv R s₀) (N := 64) (by decide) hstep
    (fun t ht => ⟨fun r hr => ht.keep r (by revert r hr; decide), ht.sp, ht.lr,
      polyIs_of_toNat fun j hj => by rw [ht.coeff j hj, ite_eq_left (by show j < 256; exact hj)]⟩) h)

/-! ## The two bodies -/

theorem vmul_body (u : State) (h5 : u.vpr .v5 = hiC) :
    WP isa (.block (mont ++ smul .v8)) u fun t =>
      t.vpr .v8 = smulV (montV (u.vpr .v8) (u.vpr .v9) (u.vpr .v4) (u.vpr .v13) hiC) (u.vpr .v2) (u.vpr .v3)
        (u.vpr .v4) hiC ∧ VOnly [.v8, .v9, .v6, .v7, .v10, .v11] u t := by
  rw [WP.block_append_iff]
  refine WP.mono (mont_exec u) fun t₁ ⟨a₁, vo₁, _⟩ => WP.mono (smul_exec t₁ (.inl rfl)) fun t ⟨a, vo, _⟩ => ⟨?_, ?_⟩
  · rw [a, a₁, vo₁.v _ (by decide), vo₁.v _ (by decide), vo₁.v _ (by decide), vo₁.v _ (by decide), h5]
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      have e1 : r ∉ [.v8, .v6, .v7] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.2.1, hr.2.2.2.1⟩
      have e2 : r ∉ [.v8, .v6, .v7, .v10, .v11] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
      rw [vo.v r e1, vo₁.v r e2]
    all_goals first
      | (rw [vo.gpr, vo₁.gpr]) | (rw [vo.mem, vo₁.mem]) | (rw [vo.rd, vo₁.rd]) | (rw [vo.wr, vo₁.wr])
      | (rw [vo.sp, vo₁.sp]) | (rw [vo.lr, vo₁.lr])

theorem vmulBody_eq : vmulBody = ([.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] : List Instr) ++ (mont ++ smul .v8) ++
    ([.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1] : List Instr) := by
  simp only [vmulBody, List.append_assoc]

def addTail : List Instr :=
  [.lxvd2x .v9 .r3 .r9, .vop (.add false .v6 .v8 .v9), .vop (.sub true .v7 .v6 .v4), .vop (.minu true .v8 .v6 .v7)]

theorem vmulAddBody_eq : vmulAddBody = ([.lxvd2x .v8 .r4 .r9, .lxvd2x .v9 .r5 .r9] : List Instr) ++ ((mont ++ smul .v8) ++ addTail) ++
    ([.stxvd2x .v8 .r3 .r9, .addi .r3 .r3 16, .addi .r4 .r4 16, .addi .r5 .r5 16, .subi .r10 .r10 1] : List Instr) := by
  simp only [vmulAddBody, addTail, List.append_assoc, List.cons_append, List.nil_append]

/-- `v8 ← min(v8 + h, v8 + h − q)`, `h` loaded from `[r3]`. -/
theorem addTail_run (u : State) {x : Addr} (h3 : u.gpr .r3 = x) (h9 : u.gpr .r9 = 0#64)
    (hx : InRegions (u.rd ++ u.wr) x 16) :
    WP isa (.block addTail) u fun t =>
      t.vpr .v8 = minV (addV (u.vpr .v8) (swapDwords (u.mem.read x 16)))
        (subV (addV (u.vpr .v8) (swapDwords (u.mem.read x 16))) (u.vpr .v4)) ∧
      VOnly [.v8, .v9, .v6, .v7] u t := by
  unfold addTail
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v9 .r3 .r9 u (by decide) (by rw [h3, h9, BitVec.add_zero]; exact hx), ?_⟩
  rw [h3, h9, BitVec.add_zero]
  refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine WP.block_nil ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem vonly_mono {vs vs' : List VReg} {s t : State} (h : VOnly vs s t) (hv : ∀ r ∈ vs, r ∈ vs') : VOnly vs' s t :=
  ⟨fun r hr => h.v r fun e => hr (hv r e), h.gpr, h.mem, h.rd, h.wr, h.sp, h.lr⟩

theorem vonly_trans {vs : List VReg} {s t u : State} (h : VOnly vs s t) (h' : VOnly vs t u) : VOnly vs s u :=
  ⟨fun r hr => by rw [h'.v r hr, h.v r hr], by rw [h'.gpr, h.gpr], by rw [h'.mem, h.mem], by rw [h'.rd, h.rd],
    by rw [h'.wr, h.wr], by rw [h'.sp, h.sp], by rw [h'.lr, h.lr]⟩

theorem mul_body_lanes {s₀ : State} {i : Nat} (hi : i < 64) (u : State)
    (h4 : ∀ i < 4, (vword (u.vpr .v4) i).toNat = Spec.MlDsa.q) (h5 : u.vpr .v5 = hiC)
    (h13 : ∀ i < 4, (vword (u.vpr .v13) i).toNat = 58728449)
    (h2 : ∀ i < 4, (vword (u.vpr .v2) i).toNat = (4193792 : Zq).val)
    (h3 : ∀ i < 4, (vword (u.vpr .v3) i).toNat = (4193792 : Zq).val * 2 ^ 32 / Spec.MlDsa.q)
    (hA : ∀ e < 4, (vword (u.vpr .v8) e).toNat = ((polyAt s₀.mem (MF s₀))[4 * i + (e ^^^ 1)]!).val)
    (hB : ∀ e < 4, (vword (u.vpr .v9) e).toNat = ((polyAt s₀.mem (MG s₀))[4 * i + (e ^^^ 1)]!).val) :
    WP isa (.block (mont ++ smul .v8)) u fun t =>
      (∀ e < 4, (vword (t.vpr .v8) e).toNat =
        ((Spec.MlDsa.multiplyNTT (polyAt s₀.mem (MF s₀)) (polyAt s₀.mem (MG s₀)))[4 * i + (e ^^^ 1)]!).val) ∧
      VOnly [.v8, .v9, .v6, .v7, .v10, .v11] u t :=
  WP.mono (vmul_body u h5) fun t ⟨e, vo⟩ => ⟨fun k hk => by
    rw [e, mul_lanes hk (hA k hk) (hB k hk) (h4 k hk) (h13 k hk) (h2 k hk) (h3 k hk),
      mul_get _ _ (by have := xor1_lt hk; show _ < 256; omega)], vo⟩

/-! ## Verified -/

theorem mpre_of {s : State} (h : (Proof.MlDsa.mulContract PPC64LE.abi).pre s) : MPre s := by
  sig_pre [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem mpre_of_add {s : State} (h : (Proof.MlDsa.mulAddContract PPC64LE.abi).pre s) :
    MPre s ∧ Reduced s.mem (MH s) := by
  sig_pre [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩, h8⟩

/-- A state satisfying the precondition. -/
def msatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem vmul_correct {s₀ : State} (hp : MPre s₀) :
    WP isa vmul s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (MH s₀) (Spec.MlDsa.multiplyNTT (polyAt s₀.mem (MF s₀)) (polyAt s₀.mem (MG s₀))) := by
  unfold vmul
  rw [vmulBody_eq]
  exact mloop_ok fun i hi s h => mstep_ok hp hi h
    fun u _ _ _ h4 h5 h13 h2 h3 hA hB _ => mul_body_lanes hi u h4 h5 h13 h2 h3 hA hB

theorem vmulAdd_correct {s₀ : State} (hp : MPre s₀) (hrH : Reduced s₀.mem (MH s₀)) :
    WP isa vmulAdd s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (MH s₀) (Spec.MlDsa.add (polyAt s₀.mem (MH s₀))
        (Spec.MlDsa.multiplyNTT (polyAt s₀.mem (MF s₀)) (polyAt s₀.mem (MG s₀)))) := by
  unfold vmulAdd
  rw [vmulAddBody_eq]
  refine mloop_ok fun i hi s h => mstep_ok hp hi h fun u r3 r9 ix h4 h5 h13 h2 h3 hA hB hH => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_body_lanes hi u h4 h5 h13 h2 h3 hA hB) fun t ⟨lt, vo⟩ =>
    WP.mono (addTail_run t (x := coeffAddr (MH s₀) (4 * i)) (by rw [vo.gpr]; exact r3) (by rw [vo.gpr]; exact r9)
      (by rw [vo.rd, vo.wr]; exact ix)) fun t' ⟨e, vo'⟩ => ⟨fun k hk => ?_, vonly_trans vo (vonly_mono vo' (by decide))⟩
  have hx := xor1_lt hk
  have hk' : 4 * i + (k ^^^ 1) < 256 := by omega
  have hq : 2 * (vword (t.vpr .v4) k).toNat ≤ 2 ^ 32 := by rw [vo.v _ (by decide), h4 k hk]; decide
  have hq0 : 0 < (vword (t.vpr .v4) k).toNat := by rw [vo.v _ (by decide), h4 k hk]; decide
  have hhv : (vword (swapDwords (t.mem.read (coeffAddr (MH s₀) (4 * i)) 16)) k).toNat =
      ((polyAt s₀.mem (MH s₀))[4 * i + (k ^^^ 1)]!).val := by
    rw [vo.mem, hH k hk, polyAt_val hrH hk']
  rw [e, vword_minV _ _ hk, vword_subV _ _ hk, vword_addV _ _ hk,
    minu_add_lane hq0 hq (by rw [lt k hk, vo.v _ (by decide), h4 k hk]; exact Fin.isLt _)
      (by rw [hhv, vo.v _ (by decide), h4 k hk]; exact Fin.isLt _),
    lt k hk, hhv, vo.v _ (by decide), h4 k hk, add_get _ _ hk', val_add', Nat.add_comm]

theorem vmul_verified : Verified PPC64LE.target vmul (Proof.MlDsa.mulContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun s₁ s₂ _ _ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := vmul_correct (mpre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    refine ⟨h.1, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · refine ⟨msatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Proof.MlDsa.PPC64LE.Arith.AddSub.reduced_zero _
        | decide +kernel

theorem vmulAdd_verified : Verified PPC64LE.target vmulAdd (Proof.MlDsa.mulAddContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun s₁ s₂ _ _ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨hp, hrH⟩ := mpre_of_add hs
    obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := vmulAdd_correct hp hrH
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs] at h
    refine ⟨h.1, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · refine ⟨msatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.mulAddContract, Proof.MlDsa.mulSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Proof.MlDsa.PPC64LE.Arith.AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.VNtt
