module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Saving
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Saving
meta import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ML-DSA on PPC64LE: `vg_mldsa_ntt`

As ML-KEM's on PPC64LE (`Proof/MlKem/PPC64LE/Ntt.lean`): the table of the
zetas stored (`setup_ok`); then the three nested loops of `nttLayer`,
`layerN` and `blockN` (`Proof/MlDsa/Arith/Ntt.lean`), with an invariant
each (`LInv`, `BInv`, `FInv`) saying which polynomial `f` holds; the
butterfly is symbolically executed once for any pointers (`bfly_ok`), and
writes the coefficients `bfly` writes (`polyIs_bfly`). The body runs inside
the frames saving `r14` and `r15` (`saving_ok`). Layer `ℓ` has
`len = 128 / 2^ℓ` and `2^ℓ` blocks.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Arith.Ntt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Arith
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.PPC64LE.Arith
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ ptr_add ptr_ne lsr2)

/-! ## Registers -/

/-- The preserved registers the transforms never write. -/
def kept : List Reg := [.r2, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27,
  .r28, .r29, .r30, .r31]

theorem kept_of : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ∈ kept := by decide

/-! ## Values -/

theorem bfly_vals (a b z : Zq) :
    ((fixd (BitVec.ofNat 64 a.val - red (BitVec.ofNat 64 z.val * BitVec.ofNat 64 b.val))).setWidth 32).toNat =
      (a - z * b).val ∧
    ((fixd (BitVec.ofNat 64 a.val + red (BitVec.ofNat 64 z.val * BitVec.ofNat 64 b.val) - 8380417)).setWidth 32).toNat =
      (a + z * b).val := by
  have ha := (toNat_val64 a).symm ▸ val_lt a
  have ht : (red (BitVec.ofNat 64 z.val * BitVec.ofNat 64 b.val)).toNat < q := by rw [red_mul]; exact val_lt _
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_setWidth, fixd_sub ha ht, toNat_val64, red_mul, val_sub',
      Nat.add_sub_assoc (Nat.le_of_lt (val_lt (z * b))), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q ≤ 2 ^ 32))]
  · rw [BitVec.toNat_setWidth, fixd_add ha ht, toNat_val64, red_mul, val_add',
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q ≤ 2 ^ 32))]

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem polyIs_bfly {m : Mem} {F : Addr} {f : Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32} (h₁ : v₁.toNat = (f[j]! - z * f[j + len]!).val)
    (h₂ : v₂.toNat = (f[j]! + z * f[j + len]!).val) :
    PolyIs ((m.writeW (coeffAddr F (j + len)) v₁).writeW (coeffAddr F j) v₂) F (bfly f j len z) := by
  have e1 := polyIs_writeW h hj _ h₁
  have e2 := polyIs_writeW e1 (j := j) (by omega_arith) (f[j]! + z * f[j + len]!) h₂
  simp only [bfly]
  rwa [getElem!_set!_ne _ (by omega_arith) (by omega_arith)]

/-! ## The butterfly -/

section
variable {s : State} {x y z c : BitVec 64}

theorem bfly_ok (h5 : s.gpr .r5 = x) (h6 : s.gpr .r6 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = M)
    (h9 : s.gpr .r9 = 8380417) (h11 : s.gpr .r11 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr y 4) :
    WP isa (.block bflyBody) s fun s' =>
      s'.gpr .r5 = x + 4 ∧ s'.gpr .r6 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = M ∧ s'.gpr .r9 = 8380417 ∧
      s'.gpr .r10 = s.gpr .r10 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW y ((fixd ((s.mem.readW x 32).setWidth 64 -
            red (z * (s.mem.readW y 32).setWidth 64))).setWidth 32)).writeW x
          ((fixd ((s.mem.readW x 32).setWidth 64 + red (z * (s.mem.readW y 32).setWidth 64) - 8380417)).setWidth 32) := by
  crun [bflyBody, reduce, fixup, red, bar, fixd, kept, h5, h6, h7, h8, h9, h11, ia, ib, oa, ob,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## Loops -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .r3
abbrev S : Addr := s₀.gpr .r4
abbrev P : Poly := polyAt s₀.mem (F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  sp : 96 ≤ s₀.sp.toNat
  bF : (below s₀.sp 96).Disjoint (polyRegion (F s₀))
  bS : (below s₀.sp 96).Disjoint (polyRegion (S s₀))
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (F s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 256, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTab j)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps. -/
structure Env (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀ + BitVec.ofNat 64 1024
  r8 : s.gpr .r8 = M
  r9 : s.gpr .r9 = 8380417
  kept : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [polyRegion (F s₀)] m₁ s.mem

theorem Env.inW {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} (h : Env s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (F s₀)).Contains a k) : InRegions s.wr a k := by
  rw [h.wr, hp.wr]; exact ⟨_, by simp, hc⟩

theorem Env.inR {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} (h : Env s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (F s₀)).Contains a k) : InRegions (s.rd ++ s.wr) a k := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, hc⟩

theorem Env.inRS {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} (h : Env s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (S s₀)).Contains a k) : InRegions (s.rd ++ s.wr) a k := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, hc⟩

/-- After `t` butterflies of the block from `st` with the zeta `zetas k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r4 : s.gpr .r4 = S s₀ + BitVec.ofNat 64 (4 * (k + 1))
  r5 : s.gpr .r5 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  r6 : s.gpr .r6 = F s₀ + BitVec.ofNat 64 (4 * (st + len + t))
  r7 : s.gpr .r7 = BitVec.ofNat 64 (zetas k).val
  r10 : s.gpr .r10 = BitVec.ofNat 64 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (len - t)
  poly : PolyIs s.mem (F s₀) (blockN bfly Q len (zetas k) st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : Poly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block bflyBody) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .r11 != 0) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + len + t)) = coeffAddr (F s₀) (st + t + len) := by
    rw [show st + len + t = st + t + len by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := polyIs_toNat h.poly (i := st + t) (by rw [n_eq]; omega_arith)
  have vb := polyIs_toNat h.poly (i := st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (bfly_ok h.r5 h.r6 h.r7 h.env.r8 h.env.r9 h.r11
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb))
    fun s' ⟨r5, r6, r11, r3, r4, r7, r8, r9, r10, kp, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.r3, r8, r9, fun r hr => (kp r hr).trans (h.env.kept r hr), lr.trans h.env.lr,
        rd.trans h.env.rd, wr.trans h.env.wr, ?_⟩, r4.trans h.r4, ?_, ?_, r7,
        r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r6, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub ht
  · have hv : ∀ {v : BitVec 32} {x : Zq}, v.toNat = x.val → v.setWidth 64 = BitVec.ofNat 64 x.val := fun hv => by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_setWidth64, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt ‹Zq›; omega_arith)]
    rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, hv va, hv vb, blockN_succ]
    exact polyIs_bfly h.poly hl (by rw [n_eq]; omega_arith) _ (bfly_vals _ _ _).1 (bfly_vals _ _ _).2
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub ht]
    exact count_nz ht (by omega_arith)

/-! ## Blocks -/

section
variable {s : State} {x4 x5 x10 y : BitVec 64}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h4 : s.gpr .r4 = x4) (h5 : s.gpr .r5 = x5) (h10 : s.gpr .r10 = x10)
    (i4 : InRegions (s.rd ++ s.wr) x4 4) :
    WP isa (.block [.load .w .r7 .r4 0, .addi .r4 .r4 4, .add .r6 .r5 .r10, .lsr .d .r11 .r10 2]) s
      fun s' => s'.gpr .r7 = (s.mem.readW x4 32).setWidth 64 ∧ s'.gpr .r4 = x4 + 4 ∧
        s'.gpr .r6 = x5 + x10 ∧ s'.gpr .r11 = x10 >>> 2 ∧ s'.gpr .r5 = x5 ∧ s'.gpr .r10 = x10 ∧
        s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h4, h5, h10, i4, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

/-- The end of a block: the next block's start, compared with the end. -/
theorem bpost_ok (h6 : s.gpr .r6 = y) :
    WP isa (.block [.addi .r5 .r6 0, .sub .r0 .r5 .r3]) s fun s' =>
      s'.gpr .r5 = y ∧ s'.gpr .r0 = y - s.gpr .r3 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r4 = s.gpr .r4 ∧
        s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h6, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r4 : s.gpr .r4 = S s₀ + BitVec.ofNat 64 (4 * (nb + c))
  r5 : s.gpr .r5 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 64 (4 * len)
  poly : PolyIs s.mem (F s₀) (layerN bfly Q len (fun c => zetas (128 / len + c)) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (hl : 0 < len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttBlockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .r0 != 0) = decide (c + 1 ≠ nb) := by
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  have hk : nb + c < 256 := by
    have : nb ≤ len * nb := Nat.le_mul_of_pos_left nb hl
    omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 32).setWidth 64 =
      BitVec.ofNat 64 (zetas (128 / len + c)).val := by
    have ez : zetaTab (nb + c) = (zetas (nb + c)).val := zetaNat_eq (nb + c)
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, hdiv, ez, setWidth64_ofNat (by have := val_lt (zetas (nb + c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok h.r4 h.r5 h.r10 (h.env.inRS hp cS))
    fun s₁ ⟨r7, r4, r6, r11, r5, r10, r3, r8, r9, kp, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (layerN bfly Q len (fun c => zetas (128 / len + c)) c) len (128 / len + c)
      (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.r3, r8.trans h.env.r8, r9.trans h.env.r9,
      fun r hr => (kp r hr).trans (h.env.kept r hr), lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_,
      m ▸ h.poly⟩
    · rw [r4, hdiv]
      exact (ptr_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega_arith])
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [r7, vz]
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_nz (FInv s₀ m₁ (layerN bfly Q len (fun c => zetas (128 / len + c)) c) len (128 / len + c)
    (2 * len * c)) hl (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.r6) fun s' ⟨r5, r0, r3, r4, r8, r9, r10, kp, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.r3, r8.trans h₂.env.r8, r9.trans h₂.env.r9,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r4, h₂.r4, hdiv, Nat.add_assoc]
  · rw [r5]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, layerN_succ]; exact h₂.poly
  · rw [r0, h₂.env.r3, ptr_ne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT`. -/
def nttL (ℓ : Nat) (w : Poly) : Poly := (nttLens.take ℓ).foldl nttLayer w

theorem nttL_succ (w : Poly) {ℓ : Nat} (hℓ : ℓ < 8) : nttL (ℓ + 1) w = nttLayer (nttL ℓ w) (128 >>> ℓ) := by
  have e : nttLens[ℓ]'(by simp [nttLens]; omega_arith) = 128 >>> ℓ := by
    revert ℓ; decide
  unfold nttL
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttLens]; omega_arith), e]
  rfl

theorem ntt_eq_nttL (w : Poly) : ntt w = nttL 8 w := by
  rw [ntt_eq_layers]; rfl

/-- What the layers' loop counters are: layer `ℓ` has `len = 128 >>> ℓ` and
`2^ℓ` blocks. -/
theorem layer_facts : ∀ ℓ < 8, 0 < 128 >>> ℓ ∧ (128 >>> ℓ) * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 128 / (128 >>> ℓ) = 2 ^ ℓ ∧
    BitVec.ofNat 64 (512 >>> ℓ) >>> 1 = BitVec.ofNat 64 (512 >>> (ℓ + 1)) ∧
    (BitVec.ofNat 64 (512 >>> (ℓ + 1)) - 2 != 0) = decide (ℓ + 1 ≠ 8) ∧ 512 >>> ℓ = 4 * (128 >>> ℓ) := by
  decide

section
variable {s : State} {x3 x10 : BitVec 64}

theorem lpre_ok (h3 : s.gpr .r3 = x3) :
    WP isa (.block [.subi .r5 .r3 1024]) s fun s' =>
      s'.gpr .r5 = x3 - 1024 ∧ s'.gpr .r3 = x3 ∧ s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r8 = s.gpr .r8 ∧
        s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h3, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.lsr .d .r10 .r10 1, .subi .r0 .r10 2]) s fun s' =>
      s'.gpr .r10 = x10 >>> 1 ∧ s'.gpr .r0 = x10 >>> 1 - 2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h10, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r4 : s.gpr .r4 = S s₀ + BitVec.ofNat 64 (4 * 2 ^ ℓ)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (512 >>> ℓ)
  poly : PolyIs s.mem (F s₀) (nttL ℓ (P s₀))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 8) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .r0 != 0) = decide (ℓ + 1 ≠ 8) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.r3)
    fun s₁ ⟨r5, r3, r4, r8, r9, r10, kp, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (nttL ℓ (P s₀)) (128 >>> ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.r8, r9.trans h.env.r9, fun r hr => (kp r hr).trans (h.env.kept r hr),
      lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, m ▸ h.env.frame⟩,
      by rw [r4, h.r4, Nat.add_zero], ?_, by rw [r10, h.r10, f8], ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_nz (BInv s₀ m₁ (nttL ℓ (P s₀)) (128 >>> ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.r10) fun s' ⟨r10, r0, r3, r4, r8, r9, kp, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.r3, r8.trans h₂.env.r8, r9.trans h₂.env.r9,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.r4, f4]
  · rw [r10, ← f8, f6]
  · rw [m, nttL_succ _ hℓ]
    exact (congrArg (fun b => PolyIs s₂.mem (F s₀) (layerN bfly (nttL ℓ (P s₀)) (128 >>> ℓ)
      (fun c => zetas (128 / (128 >>> ℓ) + c)) b)) f5).mpr h₂.poly
  · rw [r0, ← f8, f6, f7]

/-! ## Setup -/

theorem sub_low (p : Addr) {k L : Nat} (h : k ≤ L) : Region.Sub ⟨p, k⟩ ⟨p, L⟩ := fun a ha => by
  simp only [Region.Contains] at ha ⊢; omega_arith

theorem zetaTab_lt (k : Nat) : zetaTab k < 2 ^ 23 := by
  have := zetaNat_lt k; rw [q_eq] at this; exact Nat.lt_trans this (by decide)

/-- The table stored, from the state the body starts in. -/
theorem table_base {s₀ : State} (hp : Pre s₀) {s : State} (hs : BodyStart s₀ s) :
    WP isa (.block (table zetaTab .r4)) s fun s' =>
      Setup s₀ s'.mem ∧ (∀ r, r ≠ .r12 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.lr = s₀.lr := by
  have fS := hp.fitS
  refine WP.mono (table_ok zetaTab zetaTab_lt (b := .r4) (by decide) (by decide) (by rw [hs.gpr])
    fun k hk => by rw [hs.wr, hp.wr]; exact ⟨polyRegion (S s₀), by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s₂ h₂ => ?_
  have fr : Frame [below s₀.sp 96, polyRegion (S s₀)] s₀.mem s₂.mem :=
    (hs.frame.mono (by simp)).trans (h₂.frame.sub fun r hr => ⟨polyRegion (S s₀), by simp, by
      rw [List.mem_singleton] at hr; subst hr; exact sub_low (S s₀) (Nat.le_refl 1024)⟩)
  refine ⟨⟨fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.bF.symm
    · exact hp.disj) ⟨hp.red, rfl⟩⟩, fun r hr => (h₂.gpr r hr).trans (by rw [hs.gpr]),
    h₂.rd.trans hs.rd, h₂.wr.trans hs.wr, h₂.lr.trans hs.lr⟩

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr))) s
      fun s' => s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 1024 ∧ s'.gpr .r4 = s.gpr .r4 + 4 ∧
        s'.gpr .r8 = M ∧ s'.gpr .r9 = 8380417 ∧ s'.gpr .r10 = 512 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_lsl (by decide)) (WP.cons exec_ori
    (WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_addi (by decide) (by decide))
    (WP.cons (exec_addi (by decide) (by decide)) (WP.cons (exec_li (by decide)) (wp_nil ?_)))))))))
  refine ⟨by simp [State.write], by simp [State.write], ?_, ?_, by simp [State.write], fun r hr => ?_,
    rfl, rfl, rfl, rfl, rfl⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact consts_r8
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; exact loadImm_val (by decide)
  · have : r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 := by revert r hr; decide
    simp [State.write, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem setup_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : BodyStart s₀ s) :
    WP isa (.block (table zetaTab .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr))) s
      fun s' => Setup s₀ s'.mem ∧ LInv s₀ s'.mem 0 s' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (table_base hp hs) fun s₂ ⟨hm, e, rd, wr, lr⟩ => ?_
  refine WP.mono tail_ok fun s' ⟨r3, r4, r8, r9, r10, kp, lr', m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .r3 (by decide)], r8, r9, fun r hr => ?_, lr'.trans lr, rd'.trans rd,
    wr'.trans wr, by rw [m]; exact Frame.refl _ _⟩, by rw [r4, e .r4 (by decide)]; rfl, r10, m ▸ hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide)]

/-! ## Correctness -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : BodyStart s₀ s) :
    WP isa (.seq (.block (table zetaTab .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr))) (.loop nttLayerCode (.nonzero .d .r0))) s
      fun s' => (∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
        PolyIs s'.mem (F s₀) (ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp hs) fun s₁ ⟨hm, h₁⟩ => ?_)
  refine wp_loop_nz (LInv s₀ s₁.mem) (N := 8) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => ?_) h₁
  exact ⟨fun r hr h14 h15 => h.env.kept r (kept_of r hr h14 h15), h.env.lr, by rw [ntt_eq_nttL]; exact h.poly⟩

theorem sdepth_ntt : sdepth (.seq (.block (table zetaTab .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr))) (.loop nttLayerCode (.nonzero .d .r0)) :
      Prog isa) = 0 := rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (F s₀) (Spec.MlDsa.ntt (P s₀)) :=
  saving_ok (P := fun m => PolyIs m (F s₀) (Spec.MlDsa.ntt (P s₀))) hp.sp (fun R hR => by
      rw [hp.wr] at hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact hp.bF
      · exact hp.bS)
    (by rw [sdepth_ntt]; decide) (body_ok hp body_state)

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.nttContract PPC64LE.abi 96).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h2, h3, h4, h1, h5, h6, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified PPC64LE.target ntt (Proof.MlDsa.nttContract PPC64LE.abi 96) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.PPC64LE.Add.ctRegs [.r3, .r4] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Arith.Ntt
