module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.MlKem.NttLayer
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-!
# ML-KEM on PPC64LE: `vg_mlkem_ntt`

As on 32-bit ARM (`Proof/MlKem/Arm/Ntt.lean`): `r14` and `r15` saved and
the table of the zetas stored (`setup_ok`); then the three nested loops of
`nttLayer`, `nttBlock` and `nttBlockN` (`Proof/MlKem/Ntt.lean`), with an
invariant each (`LInv`, `BInv`, `FInv`) saying which polynomial `f` holds;
the butterfly is symbolically executed once for any pointers (`bfly_ok`),
and writes the coefficients `bfly` writes (`polyIs_bfly`); then the
registers restored. Layer `ℓ` has `len = 128 / 2^ℓ` and `2^ℓ` blocks.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Ntt

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

/-! ## Values -/

theorem bfly_vals (a b z : Zq) :
    (fixq (BitVec.ofNat 64 a.val - red (BitVec.ofNat 64 z.val * BitVec.ofNat 64 b.val))).setWidth 32 =
      BitVec.ofNat 32 (a - z * b).val ∧
    (fixq (BitVec.ofNat 64 a.val + red (BitVec.ofNat 64 z.val * BitVec.ofNat 64 b.val) - 3329)).setWidth 32 =
      BitVec.ofNat 32 (a + z * b).val := by
  have ha := (toNat_val64 a).symm ▸ val_lt a
  have ht : (red (BitVec.ofNat 64 z.val * BitVec.ofNat 64 b.val)).toNat < q := by rw [red_mul]; exact val_lt _
  refine ⟨setWidth32_ofNat ?_ (by have := val_lt (a - z * b); omega_arith),
    setWidth32_ofNat ?_ (by have := val_lt (a + z * b); omega_arith)⟩
  · rw [fixq_sub ha ht, toNat_val64, red_mul, val_sub', Nat.add_sub_assoc (Nat.le_of_lt (val_lt (z * b)))]
  · rw [fixq_add ha ht, toNat_val64, red_mul, val_add']

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem polyIs_bfly {m : Mem} {F : Addr} {f : Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) :
    PolyIs ((m.writeW (coeffAddr F (j + len)) (BitVec.ofNat 32 (f[j]! - z * f[j + len]!).val)).writeW
      (coeffAddr F j) (BitVec.ofNat 32 (f[j]! + z * f[j + len]!).val)) F (bfly f j len z) := by
  have h1 := polyIs_writeW h hj (f[j]! - z * f[j + len]!)
  have h2 := polyIs_writeW h1 (j := j) (by omega_arith) (f[j]! + z * f[j + len]!)
  simp only [bfly]
  rwa [getElem!_set!_ne _ (by omega_arith) (by omega_arith)]

/-! ## The butterfly -/

section
variable {s : State} {x y z c : BitVec 64}

theorem bfly_ok (h5 : s.gpr .r5 = x) (h6 : s.gpr .r6 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = C)
    (h9 : s.gpr .r9 = 3329) (h11 : s.gpr .r11 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr y 4) :
    WP isa (.block bflyBody) s fun s' =>
      s'.gpr .r5 = x + 4 ∧ s'.gpr .r6 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = C ∧ s'.gpr .r9 = 3329 ∧
      s'.gpr .r10 = s.gpr .r10 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW y ((fixq ((s.mem.readW x 32).setWidth 64 -
            red (z * (s.mem.readW y 32).setWidth 64))).setWidth 32)).writeW x
          ((fixq ((s.mem.readW x 32).setWidth 64 + red (z * (s.mem.readW y 32).setWidth 64) - 3329)).setWidth 32) := by
  crunr [bflyBody, reduce, barrett, fixup, red, bar, fixq, kept, h5, h6, h7, h8, h9, h11, ia, ib, oa, ob,
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
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (F s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : Saved m₁ (S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTable.getD j 0)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps. -/
structure Env (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀ + BitVec.ofNat 64 1024
  r8 : s.gpr .r8 = C
  r9 : s.gpr .r9 = 3329
  kept : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
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

/-- After `t` butterflies of the block from `st` with the zeta `zeta k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r4 : s.gpr .r4 = S s₀ + BitVec.ofNat 64 (4 * (k + 1))
  r5 : s.gpr .r5 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  r6 : s.gpr .r6 = F s₀ + BitVec.ofNat 64 (4 * (st + len + t))
  r7 : s.gpr .r7 = BitVec.ofNat 64 (zeta k).val
  r10 : s.gpr .r10 = BitVec.ofNat 64 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (len - t)
  poly : PolyIs s.mem (F s₀) (nttBlockN Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : Poly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block bflyBody) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .r11 != 0) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + len + t)) = coeffAddr (F s₀) (st + t + len) := by
    rw [show st + len + t = st + t + len by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := polyIs_coeffAt h.poly (i := st + t) (by rw [n_eq]; omega_arith)
  have vb := polyIs_coeffAt h.poly (i := st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (bfly_ok h.r5 h.r6 h.r7 h.env.r8 h.env.r9 h.r11
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb))
    fun s' ⟨r5, r6, r11, r3, r4, r7, r8, r9, r10, kp, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.r3, r8, r9, fun r hr => (kp r hr).trans (h.env.kept r hr), lr.trans h.env.lr,
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.r4, ?_, ?_, r7,
        r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r6, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub ht
  · have hv : ∀ x : Zq, (BitVec.ofNat 32 x.val).setWidth 64 = BitVec.ofNat 64 x.val := fun x =>
      setWidth64_ofNat (by have := val_lt x; omega_arith)
    rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, va, vb, hv, hv, (bfly_vals _ _ _).1, (bfly_vals _ _ _).2,
      nttBlockN_succ]
    exact polyIs_bfly h.poly hl (by rw [n_eq]; omega_arith) _
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
  crunr [kept, h4, h5, h10, i4, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

/-- The end of a block: the next block's start, compared with the end. -/
theorem bpost_ok (h6 : s.gpr .r6 = y) :
    WP isa (.block [.addi .r5 .r6 0, .sub .r0 .r5 .r3]) s fun s' =>
      s'.gpr .r5 = y ∧ s'.gpr .r0 = y - s.gpr .r3 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r4 = s.gpr .r4 ∧
        s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crunr [kept, h6, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r4 : s.gpr .r4 = S s₀ + BitVec.ofNat 64 (4 * (nb + c))
  r5 : s.gpr .r5 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 64 (4 * len)
  poly : PolyIs s.mem (F s₀) (nttLayerN Q len c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttBlockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .r0 != 0) = decide (c + 1 ≠ nb) := by
  have hl : 0 < len := by omega_arith
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  have hk : nb + c < 128 := by
    have : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
    omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 32).setWidth 64 =
      BitVec.ofNat 64 (zeta (128 / len + c)).val := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, zetaTable_eq, zetas_getD hk, hdiv,
      setWidth64_ofNat (by have := val_lt (zeta (nb + c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok h.r4 h.r5 h.r10 (h.env.inRS hp cS))
    fun s₁ ⟨r7, r4, r6, r11, r5, r10, r3, r8, r9, kp, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (nttLayerN Q len c) len (128 / len + c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.r3, r8.trans h.env.r8, r9.trans h.env.r9,
      fun r hr => (kp r hr).trans (h.env.kept r hr), lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_,
      m ▸ h.poly⟩
    · rw [r4, hdiv]
      exact (ptr_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega_arith])
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [r7, vz]
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_nz (FInv s₀ m₁ (nttLayerN Q len c) len (128 / len + c) (2 * len * c)) hl
    (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.r6) fun s' ⟨r5, r0, r3, r4, r8, r9, r10, kp, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.r3, r8.trans h₂.env.r8, r9.trans h₂.env.r9,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r4, h₂.r4, hdiv, Nat.add_assoc]
  · rw [r5]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, nttLayerN_succ]; exact h₂.poly
  · rw [r0, h₂.env.r3, ptr_ne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- What the layers' loop counters are: layer `ℓ` has `len = 128 >>> ℓ` and
`2^ℓ` blocks. -/
theorem layer_facts : ∀ ℓ < 7, 2 ≤ 128 >>> ℓ ∧ (128 >>> ℓ) * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 128 / (128 >>> ℓ) = 2 ^ ℓ ∧
    BitVec.ofNat 64 (4 * (128 >>> ℓ)) >>> 1 = BitVec.ofNat 64 (4 * (128 >>> (ℓ + 1))) ∧
    (BitVec.ofNat 64 (4 * (128 >>> (ℓ + 1))) - 4 != 0) = decide (ℓ + 1 ≠ 7) := by
  decide

section
variable {s : State} {x3 x10 : BitVec 64}

theorem lpre_ok (h3 : s.gpr .r3 = x3) :
    WP isa (.block [.subi .r5 .r3 1024]) s fun s' =>
      s'.gpr .r5 = x3 - 1024 ∧ s'.gpr .r3 = x3 ∧ s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r8 = s.gpr .r8 ∧
        s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crunr [kept, h3, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.lsr .d .r10 .r10 1, .subi .r0 .r10 4]) s fun s' =>
      s'.gpr .r10 = x10 >>> 1 ∧ s'.gpr .r0 = x10 >>> 1 - 4 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r9 = s.gpr .r9 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crunr [kept, h10, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r4 : s.gpr .r4 = S s₀ + BitVec.ofNat 64 (4 * 2 ^ ℓ)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (4 * (128 >>> ℓ))
  poly : PolyIs s.mem (F s₀) (nttL ℓ (P s₀))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .r0 != 0) = decide (ℓ + 1 ≠ 7) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.r3)
    fun s₁ ⟨r5, r3, r4, r8, r9, r10, kp, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (nttL ℓ (P s₀)) (128 >>> ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.r8, r9.trans h.env.r9, fun r hr => (kp r hr).trans (h.env.kept r hr),
      lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.r4, Nat.add_zero], ?_, r10.trans h.r10, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_nz (BInv s₀ m₁ (nttL ℓ (P s₀)) (128 >>> ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.r10) fun s' ⟨r10, r0, r3, r4, r8, r9, kp, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.r3, r8.trans h₂.env.r8, r9.trans h₂.env.r9,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.r4, f4]
  · rw [r10, f6]
  · rw [m, nttL_succ _ hℓ, nttLayer, f5]
    exact h₂.poly
  · rw [r0, f6, f7]

/-! ## Setup and the end -/

theorem sub_low (p : Addr) {k L : Nat} (h : k ≤ L) : Region.Sub ⟨p, k⟩ ⟨p, L⟩ := fun a ha => by
  simp only [Region.Contains] at ha ⊢; omega_arith

/-- `r14` and `r15` saved and the table stored. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r4 512 ++ table zetaTable .r4)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp ∧ s.lr = s₀.lr := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have e8 : S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 8 = S s₀ + BitVec.ofNat 64 520 := ptr_add _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (b := .r4) (by decide) (off := 512) (by decide) (by decide) rfl (wS (by omega_arith))
    (by rw [e8]; exact wS (by omega_arith))) fun s₁ ⟨g1, lr1, sp1, rd1, wr1, m1⟩ => ?_
  refine WP.mono (table_ok zetaTable (by decide) (b := .r4) (by decide) (by decide) (by rw [g1])
    fun k hk => by rw [wr1]; exact wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    have f1 : Frame [polyRegion (S s₀)] s₀.mem s₁.mem := by
      rw [m1, e8]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
        ).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    refine f1.trans (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton] at hr; subst hr
    exact sub_low _ (by omega_arith)
  have hsav : Saved s₁.mem (S s₀ + BitVec.ofNat 64 512) s₀.gpr := by
    rw [m1]; exact saved_write _ _ _
  have hm : Setup s₀ s₂.mem := by
    refine ⟨⟨?_, ?_⟩, fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩
    · rw [h₂.frame.readW (Region.contains_self _ 8) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)]
      exact hsav.1
    · rw [h₂.frame.readW (Region.contains_self _ 8) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [e8]
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)]
      exact hsav.2
  exact ⟨hm, fun r hr => (h₂.gpr r hr).trans (by rw [g1]), h₂.rd.trans rd1, h₂.wr.trans wr1,
    h₂.sp.trans sp1, h₂.lr.trans lr1⟩

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr))) s
      fun s' => s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 1024 ∧ s'.gpr .r4 = s.gpr .r4 + 4 ∧
        s'.gpr .r8 = C ∧ s'.gpr .r9 = 3329 ∧ s'.gpr .r10 = 512 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.lr = s.lr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crunr [consts, kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r4 512 ++ table zetaTable .r4 ++ consts ++
      ([.addi .r3 .r3 1024, .addi .r4 .r4 4, .li .r10 512] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp, lr⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r10, kp, lr', m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .r3 (by decide)], r8, r9, fun r hr => ?_, lr'.trans lr, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩, by rw [r4, e .r4 (by decide)]; rfl, r10, m ▸ hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide)]

/-- `r14` and `r15` restored from `S + 512`, through `r4 + off`. -/
theorem restore_end {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State} (he : Env s₀ m₁ s)
    {off : Nat} (ho : off + 8 < 2 ^ 15) (ho4 : off % 4 = 0)
    (hA : s.gpr .r4 + BitVec.ofNat 64 off = S s₀ + BitVec.ofNat 64 512) :
    WP isa (.block (restoreRegs .r4 off)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧ s'.mem = s.mem := by
  have fS := hp.fitS
  have e8 : S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 8 = S s₀ + BitVec.ofNat 64 520 := ptr_add _ _ _
  have rS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 o) k := fun h' =>
    he.inRS hp (Offset.contains_base _ h' (by omega_arith))
  have dj : ∀ {o : Nat}, o + 8 ≤ 1024 → ∀ r ∈ [polyRegion (F s₀)],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 o, 8⟩ r := fun ho r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact hp.disj.symm.sub_left (Offset.sub_base _ ho)
  refine WP.mono (restore_ok (b := .r4) (by decide) (by decide) ho ho4 hA (rS (by omega_arith))
    (by rw [e8]; exact rS (by omega_arith))) fun s' ⟨r14, r15, kp, lr, sp, m⟩ =>
      ⟨preserved_of (g := s₀.gpr) ?_ ?_ (fun r hr => (kp r hr).trans (he.kept r hr)),
        sp.trans he.sp, lr.trans he.lr, m⟩
  · rw [r14, he.frame.readW (Region.contains_self _ 8) (dj (by omega_arith)) (by decide)]
    exact hm.sav.1
  · rw [r15, e8, he.frame.readW (Region.contains_self _ 8) (dj (by omega_arith)) (by decide), ← e8]
    exact hm.sav.2

theorem restore_ok' {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h : LInv s₀ m₁ 7 s) :
    WP isa (.block (restoreRegs .r4 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧ PolyIs s'.mem (F s₀) (Spec.MlKem.ntt (P s₀)) :=
  WP.mono (restore_end hp hm h.env (by decide) (by decide) (by rw [h.r4, BitVec.add_zero]))
    fun s' ⟨h1, h2, h3, m⟩ => ⟨h1, h2, h3, by rw [m, ntt_eq_nttL]; exact h.poly⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_nz (LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => restore_ok' hp hm h) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.nttContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified PPC64LE.target Impl.MlKem.PPC64LE.ntt (Proof.MlKem.nttContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r3, .r4] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Ntt
