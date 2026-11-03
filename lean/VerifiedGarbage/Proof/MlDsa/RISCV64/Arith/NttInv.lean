module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Lazy
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Lazy
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic

/-!
# ML-DSA on RISC-V: `vg_mldsa_inv_ntt`

As `vg_mldsa_ntt` (`Ntt.lean`) and PPC64LE's (`Proof/MlDsa/PPC64LE/Arith/NttInv.lean`),
with the lazy inverse butterflies (`ibfly_ok`, `lp_ibfly`, `Lazy.lean`'s
`opIB`), the table of the negated zetas read from `m = 255` down, and the
layers with `len = 2^ℓ`, which leave words less than `256 q` congruent to
the specification's (`nttLIB_rel`); then the loop multiplying every
coefficient by `8347681 = 256⁻¹ mod q` and reducing it (`scaleNB`, `SInv`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith.NttInv

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Arith
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.RISCV64.Arith
open VG.Proof.MlDsa.RISCV64.Arith.Ntt (F S P Pre Env Env.inW Env.inR Env.inRS bpost_ok lpre_ok sub_low satState
  LPoly len_mem)
open VG.Proof.MlDsa.RISCV64.Arith.Lazy (LP lp_writeW lp_lift w64 w64_load toW toW_store z64 opIB opIBn layerIB
  Rel lift residue layerIB_rel)

/-- The inverse butterflies of a block, on words. -/
abbrev iblk : LPoly → Nat → Nat → Nat → Nat → LPoly := fun f len k st t =>
  VG.Proof.MlDsa.Arith.Lazy.blockN (VG.Proof.MlDsa.Arith.Lazy.bfly opIBn) f len (zetas k) st t
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ ptr_add ptr_ne lsr2 align4_add
  toNat_setWidth64 setWidth64_ofNat kept preserved_sub)

/-! ## Values -/

/-- An inverse butterfly writes `f[j]`, then `f[j + len]`. -/
theorem lp_ibfly {m : Mem} {F : Addr} {W : LPoly} (h : LP m F W) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32} (h₁ : v₁.toNat = (opIBn W[j]! W[j + len]! z).1.val)
    (h₂ : v₂.toNat = (opIBn W[j]! W[j + len]! z).2.val) :
    LP ((m.writeW (coeffAddr F j) v₁).writeW (coeffAddr F (j + len)) v₂) F
      (VG.Proof.MlDsa.Arith.Lazy.bfly opIBn W j len z) := by
  intro i hi
  rw [VG.Proof.MlDsa.Arith.Lazy.bfly_get _ _ hl hj _ hi, coeffAt_writeW _ _ hi hj,
    coeffAt_writeW _ _ hi (by omega_arith)]
  by_cases e2 : j + len = i
  · subst e2; rw [ite_eq_left rfl, ite_eq_right (by omega_arith), ite_eq_left rfl, h₂]
  · rw [ite_eq_right e2, ite_eq_right (Ne.symm e2)]
    by_cases e1 : j = i
    · subst e1; rw [ite_eq_left rfl, ite_eq_left rfl, h₁]
    · rw [ite_eq_right e1, ite_eq_right (Ne.symm e1), h i hi]

/-! ## The inverse butterfly -/

section
variable {s : State} {x y z c : BitVec 64}

theorem ibfly_ok (h5 : s.gpr .a2 = x) (h6 : s.gpr .a3 = y) (h7 : s.gpr .a4 = z) (h8 : s.gpr .a5 = 2201172575745)
    (h9 : s.gpr .a6 = 8380417) (h11 : s.gpr .t1 = c) (h12 : s.gpr .t5 = 1072693376)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr y 4) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) :
    WP isa (.block ibflyBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = y + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧
      s'.gpr .a7 = s.gpr .a7 ∧ s'.gpr .t5 = 1072693376 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW x (((s.mem.readW x 32).setWidth 64 + (s.mem.readW y 32).setWidth 64).setWidth 32)).writeW
        y ((barv (z * ((s.mem.readW x 32).setWidth 64 - (s.mem.readW y 32).setWidth 64 + 1072693376))).setWidth 32) := by
  rw [show ibflyBody = ([.load .w .t2 .a2 0, .load .w .t0 .a3 0, .add .t3 .t2 .t0, .store .w .t3 .a2 0,
      .sub .t0 .t2 .t0, .add .t0 .t0 .t5, .mul .t0 .a4 .t0] : List Instr) ++
    (barrett .t0 .t3 ++ ([.store .w .t0 .a3 0, .addi .a2 .a2 4, .addi .a3 .a3 4, .addi .t1 .t1 (-1)] : List Instr)) by
      simp only [ibflyBody, List.cons_append, List.nil_append]]
  refine WP.block_append ?_
  crun [h5, h6, h7, h12, ia, ib, oa, ax, ay]
  refine barrett_ok (by decide) (by decide) (by simp [h8]) (by simp [h9]) fun s' k => ?_
  have g := k.other
  crun [kept, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h5, h6, h7, h8, h9, h11, h12, oa, ob, ax, ay,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## Loops -/

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 256, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (negZetaTab j)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- After `t` inverse butterflies of the block from `st` with the zeta
`-zetas k` of the layer with `len`, from `Q`: the zeta pointer is at
`k - 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : LPoly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env 1072693376 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (k - 1))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  a3 : s.gpr .a3 = F s₀ + BitVec.ofNat 64 (4 * (st + len + t))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (-zetas k).val
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (len - t)
  poly : LP s.mem (F s₀) (iblk Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : LPoly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block ibflyBody) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .t1 != 0) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + len + t)) = coeffAddr (F s₀) (st + t + len) := by
    rw [show st + len + t = st + t + len by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := h.poly (st + t) (by rw [n_eq]; omega_arith)
  have vb := h.poly (st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (ibfly_ok h.a2 h.a3 h.a4 h.env.a5 h.env.a6 h.t1 h.env.t5
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb)
    (align4_add hp.alF _) (align4_add hp.alF _))
    fun s' ⟨r5, r6, r11, r3, r4, r7, r8, r9, r10, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12, fun r hr => (kp r hr).trans (h.env.kept r hr),
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, ?_, r7,
        r10.trans h.a7, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ ca).writeW (List.mem_singleton_self _) _ cb
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r6, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub ht
  · rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, w64_load va, w64_load vb,
      show iblk Q len k st (t + 1) = VG.Proof.MlDsa.Arith.Lazy.bfly opIBn (iblk Q len k st t) (st + t) len (zetas k)
        from VG.Proof.MlDsa.Arith.Lazy.blockN_succ _ _ _ _ _ _]
    exact lp_ibfly h.poly hl (by rw [n_eq]; omega_arith) _ (toW_store _) (toW_store _)
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub ht]
    exact count_nz ht (by omega_arith)

/-! ## Blocks -/

section
variable {s : State} {x4 x5 x10 : BitVec 64}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h4 : s.gpr .a1 = x4) (h5 : s.gpr .a2 = x5) (h10 : s.gpr .a7 = x10)
    (i4 : InRegions (s.rd ++ s.wr) x4 4) (a4 : x4.toNat % 4 = 0) :
    WP isa (.block [.load .w .a4 .a1 0, .addi .a1 .a1 (-4), .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2]) s
      fun s' => s'.gpr .a4 = (s.mem.readW x4 32).setWidth 64 ∧ s'.gpr .a1 = x4 - 4 ∧
        s'.gpr .a3 = x5 + x10 ∧ s'.gpr .t1 = x10 >>> 2 ∧ s'.gpr .a2 = x5 ∧ s'.gpr .a7 = x10 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h4, h5, h10, i4, a4, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : LPoly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env 1072693376 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (2 * nb - 1 - c))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  poly : LP s.mem (F s₀) (VG.Proof.MlDsa.Arith.Lazy.layF iblk Q len (fun c => 256 / len - 1 - c) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : LPoly} {len nb c : Nat}
    (hl : 0 < len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttInvBlockCode s fun s' =>
      BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .t0 != 0) = decide (c + 1 ≠ nb) := by
  have hdiv : 256 / len = 2 * nb := by
    rw [show 256 = len * (2 * nb) by rw [Nat.mul_left_comm, hnb], Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  have hnb1 : nb ≤ 128 := by
    have : nb ≤ len * nb := Nat.le_mul_of_pos_left nb hl
    omega_arith
  have hk : 2 * nb - 1 - c < 256 := by omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (2 * nb - 1 - c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (2 * nb - 1 - c))) 32).setWidth 64 =
      BitVec.ofNat 64 (-zetas (256 / len - 1 - c)).val := by
    have ez : negZetaTab (2 * nb - 1 - c) = (-zetas (2 * nb - 1 - c)).val := negZetaNat_eq _
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, hdiv, ez, setWidth64_ofNat (by have := val_lt (-zetas (2 * nb - 1 - c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok h.a1 h.a2 h.a7 (h.env.inRS hp cS)
    (align4_add (by have := hp.alS; omega) _))
    fun s₁ ⟨r7, r4, r6, r11, r5, r10, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (VG.Proof.MlDsa.Arith.Lazy.layF iblk Q len (fun c => 256 / len - 1 - c) c) len
      (256 / len - 1 - c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
      fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_,
      m ▸ h.poly⟩
    · rw [r4, hdiv, show 4 * (2 * nb - 1 - c) = 4 * (2 * nb - 1 - c - 1) + 4 by omega_arith, BitVec.ofNat_add,
        ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [r7, vz]
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_nz (FInv s₀ m₁ (VG.Proof.MlDsa.Arith.Lazy.layF iblk Q len (fun c => 256 / len - 1 - c) c) len
    (256 / len - 1 - c) (2 * len * c)) hl (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.a3) fun s' ⟨r5, r0, r3, r4, r8, r9, r10, r12, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6, r12.trans h₂.env.t5,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.a7, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, hdiv, show 2 * nb - 1 - c - 1 = 2 * nb - 1 - (c + 1) by omega_arith]
  · rw [r5]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, VG.Proof.MlDsa.Arith.Lazy.layF, foldl_range_succ, ← VG.Proof.MlDsa.Arith.Lazy.layF]
    exact h₂.poly
  · rw [r0, h₂.env.a0, ptr_ne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT⁻¹`. -/
def nttInvL (ℓ : Nat) (w : Poly) : Poly := (nttInvLens.take ℓ).foldl nttInvLayer w

theorem nttInvL_succ (w : Poly) {ℓ : Nat} (hℓ : ℓ < 8) :
    nttInvL (ℓ + 1) w = nttInvLayer (nttInvL ℓ w) (2 ^ ℓ) := by
  have e : nttInvLens[ℓ]'(by simp [nttInvLens]; omega_arith) = 2 ^ ℓ := by
    revert ℓ; decide
  unfold nttInvL
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttInvLens]; omega_arith), e]
  rfl

theorem nttInv_eq_nttInvL (w : Poly) : nttInv w = (nttInvL 8 w).map (· * 8347681) := by
  rw [nttInv_eq_layers]; rfl

/-- The first `ℓ` layers of the inverse butterflies on words. -/
def nttLIB (ℓ : Nat) (W : LPoly) : LPoly := (nttInvLens.take ℓ).foldl layerIB W

theorem nttLIB_succ (W : LPoly) {ℓ : Nat} (hℓ : ℓ < 8) : nttLIB (ℓ + 1) W = layerIB (nttLIB ℓ W) (2 ^ ℓ) := by
  have e : nttInvLens[ℓ]'(by simp [nttInvLens]; omega_arith) = 2 ^ ℓ := by
    revert ℓ; decide
  unfold nttLIB
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttInvLens]; omega_arith), e]
  rfl

theorem pow_mem : ∀ ℓ < 8, 2 ^ ℓ ∈ [1, 2, 4, 8, 16, 32, 64, 128] ∧ 1 ≤ 2 ^ ℓ ∧ 2 ^ ℓ ≤ 128 := by decide

/-- After `ℓ` layers, words less than `2^ℓ q` congruent to the
specification's. -/
theorem nttLIB_rel (f : Poly) : ∀ ℓ ≤ 8, Rel (2 ^ ℓ) (nttLIB ℓ (lift f)) (nttInvL ℓ f)
  | 0, _ => Lazy.lift_rel f
  | ℓ + 1, h => by
    obtain ⟨m, b1, b2⟩ := pow_mem ℓ (by omega_arith)
    rw [nttLIB_succ _ (by omega_arith), nttInvL_succ _ (by omega_arith), Nat.pow_succ, Nat.mul_comm]
    exact layerIB_rel b1 b2 (nttLIB_rel f ℓ (by omega_arith)) m

/-- What the layers' loop counters are: layer `ℓ` has `len = 2^ℓ` and
`128 >>> ℓ` blocks. -/
theorem layer_facts : ∀ ℓ < 8, 0 < 2 ^ ℓ ∧ 2 ^ ℓ * (128 >>> ℓ) = 128 ∧ 0 < 128 >>> ℓ ∧
    2 * (128 >>> ℓ) - 1 - (128 >>> ℓ) = 256 >>> (ℓ + 1) - 1 ∧ 2 * (128 >>> ℓ) = 256 >>> ℓ ∧
    128 / 2 ^ ℓ = 128 >>> ℓ ∧
    BitVec.ofNat 64 (4 * 2 ^ ℓ) <<< 1 = BitVec.ofNat 64 (4 * 2 ^ (ℓ + 1)) ∧
    (BitVec.ofNat 64 (4 * 2 ^ (ℓ + 1)) - 1024 != 0) = decide (ℓ + 1 ≠ 8) := by
  decide

section
variable {s : State} {x10 : BitVec 64}

theorem lpost_ok (h10 : s.gpr .a7 = x10) :
    WP isa (.block [.shift .sll .d .a7 .a7 1, .addi .t0 .a7 (-1024)]) s fun s' =>
      s'.gpr .a7 = x10 <<< 1 ∧ s'.gpr .t0 = x10 <<< 1 - 1024 ∧ s'.gpr .a0 = s.gpr .a0 ∧
        s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h10, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env 1072693376 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (256 >>> ℓ - 1))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * 2 ^ ℓ)
  poly : LP s.mem (F s₀) (nttLIB ℓ (lift (P s₀)))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 8) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttInvLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .t0 != 0) = decide (ℓ + 1 ≠ 8) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.a0)
    fun s₁ ⟨r5, r3, r4, r8, r9, r10, r12, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (nttLIB ℓ (lift (P s₀))) (2 ^ ℓ) (128 >>> ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
      rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.a1, Nat.sub_zero, f5], ?_, r10.trans h.a7, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_nz (BInv s₀ m₁ (nttLIB ℓ (lift (P s₀))) (2 ^ ℓ) (128 >>> ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.a7) fun s' ⟨r10, r0, r3, r4, r8, r9, r12, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6, r12.trans h₂.env.t5,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, f4]
  · rw [r10, f7]
  · rw [m, nttLIB_succ _ hℓ, layerIB]
    exact (congrArg (fun b => LP s₂.mem (F s₀) (VG.Proof.MlDsa.Arith.Lazy.layF iblk (nttLIB ℓ (lift (P s₀)))
      (2 ^ ℓ) (fun c => 256 / 2 ^ ℓ - 1 - c) b)) f6).mpr h₂.poly
  · rw [r0, f7, f8]

/-! ## The scaling by `256⁻¹` -/

/-- The first `i` words of `W` multiplied by `8347681` and reduced. -/
def scaleNB (W : LPoly) (i : Nat) : LPoly :=
  (List.range i).foldl (fun w j => w.set! j (Fin.ofNat _ (w[j]!.val * 8347681 % q))) W

theorem scaleNB_succ (W : LPoly) (i : Nat) :
    scaleNB W (i + 1) = (scaleNB W i).set! i (Fin.ofNat _ ((scaleNB W i)[i]!.val * 8347681 % q)) :=
  foldl_range_succ _ _ _

theorem scaleNB_zero (W : LPoly) : scaleNB W 0 = W := rfl

theorem scaleNB_get (W : LPoly) : ∀ i ≤ n, ∀ j < n,
    (scaleNB W i)[j]! = if j < i then Fin.ofNat _ (W[j]!.val * 8347681 % q) else W[j]!
  | 0, _, j, _ => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | i + 1, hi, j, hj => by
    have ih := scaleNB_get W i (by omega_arith)
    rw [scaleNB_succ]
    by_cases e : i = j
    · subst e
      rw [VG.Proof.MlDsa.Arith.Lazy.getElem!_set!_self _ hj, ih i hj, ite_eq_right (Nat.lt_irrefl i),
        ite_eq_left (Nat.lt_succ_self i)]
    · rw [VG.Proof.MlDsa.Arith.Lazy.getElem!_set!_ne _ hj e, ih j hj]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hji, ite_eq_right (by omega_arith)]

/-- A word times `8347681`, reduced, as `scaleBody` stores it. -/
theorem scale_store (x : VG.Proof.MlDsa.Arith.Lazy.Word) :
    ((red (w64 x * BitVec.ofNat 64 8347681)).setWidth 32).toNat =
      (Fin.ofNat 4294967296 (x.val * 8347681 % q) : VG.Proof.MlDsa.Arith.Lazy.Word).val := by
  have hx := x.isLt
  have hq : x.val * 8347681 % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  have hw : (w64 x * BitVec.ofNat 64 8347681).toNat = x.val * 8347681 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_setWidth, red_toNat, hw, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

/-- Words less than `256 q`, each multiplied by `8347681` and reduced. -/
theorem scale_full {m : Mem} {p : Addr} {W : LPoly} {f : Poly} (hr : Rel 256 W f) (h : LP m p (scaleNB W 256)) :
    PolyIs m p (f.map (· * 8347681)) := polyIs_of_toNat fun i hi => by
  have hi' : i < 256 := by rw [n_eq] at hi; exact hi
  rw [h i hi, scaleNB_get W 256 (by rw [n_eq]) i hi, ite_eq_left hi', map_mul_get _ _ hi, ← (hr i hi').2,
    Fin.val_ofNat, Fin.val_mul, Fin.val_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q ≤ 4294967296)),
    show ((8347681 : Zq)).val = 8347681 from rfl, Nat.mod_mul_mod]

/-- After `i` words of `W` scaled. -/
structure SInv (s₀ : State) (m₁ : Mem) (W : LPoly) (i : Nat) (s : State) : Prop where
  env : Env 1072693376 s₀ m₁ s
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * i)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8347681
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  poly : LP s.mem (F s₀) (scaleNB W i)

section
variable {s : State} {x c : BitVec 64}

theorem scale_ok {k : BitVec 64} (h5 : s.gpr .a2 = x) (h7 : s.gpr .a4 = k) (h8 : s.gpr .a5 = 2201172575745)
    (h9 : s.gpr .a6 = 8380417) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (oa : InRegions s.wr x 4) (ax : x.toNat % 4 = 0) :
    WP isa (.block scaleBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a4 = s.gpr .a4 ∧
      s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧ s'.gpr .t5 = s.gpr .t5 ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((red ((s.mem.readW x 32).setWidth 64 * k)).setWidth 32) := by
  rw [show scaleBody = ([.load .w .t2 .a2 0, .mul .t2 .t2 .a4] : List Instr) ++ (reduce .t2 .t3 ++
      ([.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)] : List Instr)) by
    simp only [scaleBody, List.cons_append, List.nil_append]]
  refine WP.block_append ?_
  crun [h5, h7, ia, ax]
  refine reduce_ok (by decide) (by decide) (by decide) (by simp [h8]) (by simp [h9])
    fun s' k => ?_
  have g := k.other
  crun [kept, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h5, h7, h8, h9, h11, oa, ax,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

theorem sstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {W : LPoly} {i : Nat} (hi : i < 256) {s : State}
    (h : SInv s₀ m₁ W i s) :
    WP isa (.block scaleBody) s fun s' => SInv s₀ m₁ W (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have ca := coeff_contains (F s₀) (i := i) (by rw [n_eq]; omega_arith)
  have va := h.poly i (by rw [n_eq]; omega_arith)
  refine WP.mono (scale_ok h.a2 h.a4 h.env.a5 h.env.a6 h.t1 (h.env.inR hp ca) (h.env.inW hp ca)
    (align4_add hp.alF _))
    fun s' ⟨r5, r11, r3, r7, r8, r9, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, ?_, r7.trans h.a4, ?_, ?_⟩, ?_⟩
  · rw [m]; exact h.env.frame.writeW (List.mem_singleton_self _) _ ca
  · rw [r5]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub hi
  · rw [m, show F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i from rfl, ← coeffAt_eq, w64_load va,
      scaleNB_succ]
    exact lp_writeW h.poly (by rw [n_eq]; omega_arith) _ (scale_store _)
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by omega_arith)

/-! ## Setup -/

/-- The table stored in `scratch`. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table negZetaTab .a1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .t2 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have a8 : (s₀.gpr .a1).toNat % 8 = 0 := hp.alS
  refine WP.mono (table_ok negZetaTab negZetaTab_lt (b := .a1) (by decide) rfl
    (by omega) fun k hk => wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    exact sub_low _ (by omega_arith)
  exact ⟨⟨fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩,
    h₂.gpr, h₂.rd, h₂.wr, h₂.sp⟩

/-- `loadImm r (128 q)`, as instructions with their immediates. -/
theorem loadImm_q128 (r : Reg) : loadImm r 1072693376 = [.lui r 0x3FF00, .addi r r 128] := by
  simp only [loadImm, hi20]; rfl

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ loadImm .t5 1072693376 ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 1020, .li .a7 4] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1024 ∧ s'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 1020 ∧
        s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧ s'.gpr .t5 = 1072693376 ∧ s'.gpr .a7 = 4 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [consts, loadM_eq, loadImm_q, loadImm_q128, List.cons_append, List.nil_append]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table negZetaTab .a1 ++ consts ++ loadImm .t5 1072693376 ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 1020, .li .a7 4] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_assoc]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r12, r10, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .a0 (by decide)], r8, r9, r12, fun r hr => ?_, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩,
    by rw [r4, e .a1 (by decide)]; rfl, r10, m ▸ lp_lift hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide)]

/-- The block between the layers and the scaling: `a4 = 8347681`, `a2 = f`, the count. -/
theorem mid_ok {s : State} :
    WP isa (.block (loadImm .a4 8347681 ++ ([.addi .a2 .a0 (-1024), .li .t1 256] : List Instr))) s
      fun s' => s'.gpr .a4 = BitVec.ofNat 64 8347681 ∧ s'.gpr .a2 = s.gpr .a0 - 1024 ∧
        s'.gpr .t1 = BitVec.ofNat 64 256 ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧
        s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [loadImm_inv, List.cons_append, List.nil_append]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

/-! ## Correctness -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (F s₀) (Spec.MlDsa.nttInv (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_)
  refine WP.seq (wp_loop_nz (LInv s₀ s₁.mem) (N := 8) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => ?_) h₁)
  refine WP.seq (WP.mono mid_ok fun s₂ ⟨r7, r5, r11, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (SInv s₀ s₁.mem (nttLIB 8 (lift (P s₀)))) (N := 256) (by decide)
    (fun i hi s h => sstep hp hi h) (fun s' h' => ⟨fun r hr => h'.env.kept r (preserved_sub r hr), h'.env.sp,
      h'.env.kept .ra (by decide), by
        rw [nttInv_eq_nttInvL]; exact scale_full (nttLIB_rel (P s₀) 8 (by decide)) h'.poly⟩) ?_
  refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
    fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
    wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, r7, r11, ?_⟩
  · rw [r5, h.env.a0, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
  · rw [m, scaleNB_zero]; exact h.poly

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.nttInvContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem verified : Verified RISCV64.target nttInv (Proof.MlDsa.nttInvContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Arith.NttInv
