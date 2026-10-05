import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.Ntt`. -/
section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_ntt`

The registers saved and the table of the zetas stored (`setup_ok`); then the
three nested loops of `nttLayer`, `nttBlock` and `nttBlockN`
(`Proof/MlKem/Ntt.lean`), with an invariant each (`LInv`, `BInv`, `FInv`)
saying which polynomial `f` holds; the butterfly is symbolically executed once
for any pointers (`bfly_ok`), and writes the coefficients `bfly` writes
(`polyIs_bfly`); then the registers restored. Layer `ℓ` has `len = 128 / 2^ℓ`
and `2^ℓ` blocks.
-/

namespace VG.Proof.MlKem.Arm.Ntt

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## Values -/

theorem toNat_val (x : Zq) : (BitVec.ofNat 32 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

theorem bfly_vals (a b z : Zq) :
    fixq (BitVec.ofNat 32 a.val - red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 z.val * BitVec.ofNat 32 b.val)) =
      BitVec.ofNat 32 (a - z * b).val ∧
    fixq (BitVec.ofNat 32 a.val + red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 z.val * BitVec.ofNat 32 b.val) - 3328 - 1) =
      BitVec.ofNat 32 (a + z * b).val := by
  rw [red_mul]
  have ha := (VG.Proof.MlKem.Arm.Ntt.toNat_val a).symm ▸ val_lt a
  have ht := (VG.Proof.MlKem.Arm.Ntt.toNat_val (z * b)).symm ▸ val_lt (z * b)
  refine ⟨ofNat_val_eq ?_, ofNat_val_eq ?_⟩
  · rw [fixq_sub ha ht, VG.Proof.MlKem.Arm.Ntt.toNat_val, VG.Proof.MlKem.Arm.Ntt.toNat_val, val_sub', Nat.add_sub_assoc (Nat.le_of_lt (z * b).isLt)]
  · rw [fixq_add ha ht, VG.Proof.MlKem.Arm.Ntt.toNat_val, VG.Proof.MlKem.Arm.Ntt.toNat_val, val_add']

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem polyIs_bfly {m : Mem} {F : Addr} {f : VG.Spec.MlKem.Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) :
    PolyIs ((m.writeW (coeffAddr F (j + len)) (BitVec.ofNat 32 (f[j]! - z * f[j + len]!).val)).writeW
      (coeffAddr F j) (BitVec.ofNat 32 (f[j]! + z * f[j + len]!).val)) F (bfly f j len z) := by
  have h1 := polyIs_writeW h hj (f[j]! - z * f[j + len]!)
  have h2 := polyIs_writeW h1 (j := j) (by omega) (f[j]! + z * f[j + len]!)
  simp only [bfly]
  rwa [getElem!_set!_ne _ (by omega) (by omega)]

/-! ## The butterfly -/

section
variable {s : State} {x y z c : BitVec 32}

theorem bfly_ok (h2 : s.gpr .r2 = x) (h3 : s.gpr .r3 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = VG.Proof.MlKem.Arm.C)
    (h11 : s.gpr .r11 = c)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4) :
    WP isa (.block bflyBody) s fun s' =>
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r3 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = VG.Proof.MlKem.Arm.C ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
            red VG.Proof.MlKem.Arm.C (z * s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32)))).writeW
        (State.addr (x + BitVec.ofNat 32 0))
          (fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
            red VG.Proof.MlKem.Arm.C (z * s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32) - 3328 - 1)) := by
  run_block [bflyBody, reduce, barrett, subQ, fixup, red, bar, fixq, h2, h3, h7, h8, h11, ia, ib, oa, ob,
    and_self, and_true]

end

/-! ## Loops -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev ps : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (VG.Proof.MlKem.Arm.Ntt.pf s₀)
abbrev S : Addr := State.addr (VG.Proof.MlKem.Arm.Ntt.ps s₀)
abbrev P : VG.Spec.MlKem.Poly := polyAt s₀.mem (VG.Proof.MlKem.Arm.Ntt.F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀), polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀)]
  disj : (polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀)).Disjoint (polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀))
  fitF : (VG.Proof.MlKem.Arm.Ntt.pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (VG.Proof.MlKem.Arm.Ntt.ps s₀).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s₀.mem (VG.Proof.MlKem.Arm.Ntt.F s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : VG.Proof.MlKem.Arm.Saved m₁ (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTable.getD j 0)
  poly : PolyIs m₁ (VG.Proof.MlKem.Arm.Ntt.F s₀) (VG.Proof.MlKem.Arm.Ntt.P s₀)

/-- What every loop keeps. -/
structure Env (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + 1024
  r8 : s.gpr .r8 = VG.Proof.MlKem.Arm.C
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀)] m₁ s.mem

/-- After `t` butterflies of the block from `st` with the zeta `zeta k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : VG.Spec.MlKem.Poly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (k + 1))
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * (st + t))
  r3 : s.gpr .r3 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * (st + len + t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 (zeta k).val
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (len - t))
  poly : PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (nttBlockN Q len k st t)

theorem fstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} {Q : VG.Spec.MlKem.Poly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : VG.Proof.MlKem.Arm.Ntt.FInv s₀ m₁ Q len k st t s) :
    WP isa (.block bflyBody) s fun s' => VG.Proof.MlKem.Arm.Ntt.FInv s₀ m₁ Q len k st (t + 1) s' ∧ s'.z = decide (t + 1 = len) := by
  have fF := hp.fitF
  have ea := addr_coeff (i := 4 * (st + t)) (o := 0) (j := st + t) fF (by omega) (by omega)
  have eb := addr_coeff (i := 4 * (st + len + t)) (o := 0) (j := st + t + len) fF (by omega) (by omega)
  have ca := coeff_contains (VG.Proof.MlKem.Arm.Ntt.F s₀) (i := st + t) (by rw [n_eq]; omega)
  have cb := coeff_contains (VG.Proof.MlKem.Arm.Ntt.F s₀) (i := st + t + len) (by rw [n_eq]; omega)
  have iW : ∀ {a : Addr}, (polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀)).Contains a 4 → InRegions s.wr a 4 := fun hc => by
    rw [h.env.wr, hp.wr]; exact inRegions_of (by simp) hc
  have iR : ∀ {a : Addr}, (polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀)).Contains a 4 → InRegions (s.rd ++ s.wr) a 4 := fun hc => by
    rw [h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) hc
  have va := polyIs_coeffAt h.poly (i := st + t) (by rw [n_eq]; omega)
  have vb := polyIs_coeffAt h.poly (i := st + t + len) (by rw [n_eq]; omega)
  refine WP.mono (VG.Proof.MlKem.Arm.Ntt.bfly_ok h.r2 h.r3 h.r7 h.env.r8 h.r11 (by rw [ea]; exact iR ca) (by rw [eb]; exact iR cb)
    (by rw [ea]; exact iW ca) (by rw [eb]; exact iW cb))
    fun s' ⟨r2, r3, r11, z, r0, r1, r7, r8, r10, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r0.trans h.env.r0, r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp,
        ?_⟩, r1.trans h.r1, ?_, ?_, r7, r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r2, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r3, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub (k := 1) ht
  · rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, va, vb, (VG.Proof.MlKem.Arm.Ntt.bfly_vals _ _ _).1, (VG.Proof.MlKem.Arm.Ntt.bfly_vals _ _ _).2,
      nttBlockN_succ]
    exact VG.Proof.MlKem.Arm.Ntt.polyIs_bfly h.poly hl (by rw [n_eq]; omega) _
  · rw [z]; exact count_z (k := 1) ht (by decide) (by omega)

/-! ## Blocks -/

section
variable {s : State} {x0 x1 x2 x10 y : BitVec 32}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h10 : s.gpr .r10 = x10)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldr .r7 .r1 0, .dp .add .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
        .mov .r11 (.shifted .r10 .lsr 2)]) s fun s' =>
      s'.gpr .r7 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 ∧ s'.gpr .r1 = x1 + 4 ∧
      s'.gpr .r3 = x2 + x10 ∧ s'.gpr .r11 = x10 >>> 2 ∧ s'.gpr .r2 = x2 ∧ s'.gpr .r10 = x10 ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h1, h2, h10, i1, and_self, and_true]

/-- The end of a block: the next block's start, compared with the end. -/
theorem bpost_ok (h0 : s.gpr .r0 = x0) (h3 : s.gpr .r3 = y) :
    WP isa (.block [.mov .r2 (.reg .r3), .cmp .r2 (.reg .r0)]) s fun s' =>
      s'.gpr .r2 = y ∧ s'.z = (y - x0 == 0) ∧ s'.gpr .r0 = x0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, h3, and_self, and_true]

end

theorem lsr2 {len : Nat} (h : 4 * len < 2 ^ 32) :
    BitVec.ofNat 32 (4 * len) >>> 2 = BitVec.ofNat 32 (1 * (len - 0)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  omega

theorem ptr_add_add (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Two pointers from `p` are equal exactly when their offsets are. -/
theorem ptr_sub_beq (p : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (p + BitVec.ofNat 32 a - (p + BitVec.ofNat 32 b) == 0) = decide (a = b) := by
  rw [VG.Proof.MlKem.Arm.sub_beq_zero]
  by_cases h : a = b
  · subst h; simp
  · have : p + BitVec.ofNat 32 a ≠ p + BitVec.ofNat 32 b := fun e => h (by
      have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp e)
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    simp [this, h]

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : VG.Spec.MlKem.Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (nb + c))
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  poly : PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (nttLayerN Q len c)

theorem bstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ m₁) {Q : VG.Spec.MlKem.Poly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : VG.Proof.MlKem.Arm.Ntt.BInv s₀ m₁ Q len nb c s) :
    WP isa nttBlockCode s fun s' => VG.Proof.MlKem.Arm.Ntt.BInv s₀ m₁ Q len nb (c + 1) s' ∧ s'.z = decide (c + 1 = nb) := by
  have hl : 0 < len := by omega
  have fF := hp.fitF
  have fS := hp.fitS
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hk : nb + c < 128 := by
    have : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
    omega
  have eS := addr_ptr (VG.Proof.MlKem.Arm.Ntt.ps s₀) (4 * (nb + c)) 0 (by omega)
  have cS : (polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀)).Contains (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 (4 * (nb + c) + 0)) 4 :=
    contains_off (by omega) (by omega)
  have vz : s.mem.readW (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 (4 * (nb + c) + 0)) 32 =
      BitVec.ofNat 32 (zeta (128 / len + c)).val := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), Nat.add_zero, hm.tab _ hk, zetaTable_eq, zetas_getD hk, hdiv]
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Ntt.bpre_ok h.r1 h.r2 h.r10 (by
    rw [eS, h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cS))
    fun s₁ ⟨r7, r1, r3, r11, r2, r10, r0, r8, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : VG.Proof.MlKem.Arm.Ntt.FInv s₀ m₁ (nttLayerN Q len c) len (128 / len + c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r0.trans h.env.r0, r8.trans h.env.r8, lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_, m ▸ h.poly⟩
    · rw [r1, hdiv]
      exact (VG.Proof.MlKem.Arm.Ntt.ptr_add_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega])
    · rw [r2, Nat.add_zero]
    · rw [r3, VG.Proof.MlKem.Arm.Ntt.ptr_add_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega]
    · rw [r7, eS, vz]
    · rw [r11, VG.Proof.MlKem.Arm.Ntt.lsr2 (by omega)]
  refine wp_loop_ne (VG.Proof.MlKem.Arm.Ntt.FInv s₀ m₁ (nttLayerN Q len c) len (128 / len + c) (2 * len * c)) hl
    (fun t ht s h => VG.Proof.MlKem.Arm.Ntt.fstep hp hl (by omega) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (VG.Proof.MlKem.Arm.Ntt.bpost_ok h₂.env.r0 h₂.r3) fun s' ⟨r2, z, r0, r1, r8, r10, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0, r8.trans h₂.env.r8, lr.trans h₂.env.lr, rd.trans h₂.env.rd, wr.trans h₂.env.wr,
      sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, hdiv, Nat.add_assoc]
  · rw [r2]; congr 2; rw [Nat.mul_succ]; omega
  · rw [m, nttLayerN_succ]; exact h₂.poly
  · rw [z, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, VG.Proof.MlKem.Arm.Ntt.ptr_sub_beq _ (by omega) (by decide)]
    refine decide_eq_decide.mpr ⟨fun e => ?_, fun e => ?_⟩
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.eq_of_mul_eq_mul_left hl this
    · subst e; rw [Nat.mul_add, Nat.mul_one] at *; omega

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT`. -/
def layers (f : VG.Spec.MlKem.Poly) (ℓ : Nat) : VG.Spec.MlKem.Poly := (nttLens.take ℓ).foldl nttLayer f

theorem layers_succ (f : VG.Spec.MlKem.Poly) {ℓ : Nat} (h : ℓ < 7) :
    VG.Proof.MlKem.Arm.Ntt.layers f (ℓ + 1) = nttLayer (VG.Proof.MlKem.Arm.Ntt.layers f ℓ) (128 / 2 ^ ℓ) := by
  have e : ∀ ℓ < 7, nttLens[ℓ]? = some (128 / 2 ^ ℓ) := by decide
  rw [VG.Proof.MlKem.Arm.Ntt.layers, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem layers_seven (f : VG.Spec.MlKem.Poly) : VG.Proof.MlKem.Arm.Ntt.layers f 7 = ntt f := by
  rw [ntt_eq_layers]; rfl

/-- What the layers' loop counters are. -/
theorem layer_facts : ∀ ℓ < 7, 2 ≤ 128 / 2 ^ ℓ ∧ 128 / 2 ^ ℓ * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 2 ^ ℓ ≤ 64 ∧
    BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ)) >>> 1 = BitVec.ofNat 32 (4 * (128 / 2 ^ (ℓ + 1))) ∧
    (BitVec.ofNat 32 (4 * (128 / 2 ^ (ℓ + 1))) - 4 == 0) = decide (ℓ + 1 = 7) := by
  decide

section
variable {s : State} {x0 x10 : BitVec 32}

theorem lpre_ok (h0 : s.gpr .r0 = x0) :
    WP isa (.block [.dp .sub .r2 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r2 = x0 - 1024 ∧ s'.gpr .r0 = x0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, and_self, and_true]

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.mov .r10 (.shifted .r10 .lsr 1), .cmp .r10 (.imm 4)]) s fun s' =>
      s'.gpr .r10 = x10 >>> 1 ∧ s'.z = (x10 >>> 1 - 4 == 0) ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h10, and_self, and_true]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * 2 ^ ℓ)
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ))
  poly : PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (VG.Proof.MlKem.Arm.Ntt.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) ℓ)

theorem lstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : VG.Proof.MlKem.Arm.Ntt.LInv s₀ m₁ ℓ s) :
    WP isa nttLayerCode s fun s' => VG.Proof.MlKem.Arm.Ntt.LInv s₀ m₁ (ℓ + 1) s' ∧ s'.z = decide (ℓ + 1 = 7) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7⟩ := VG.Proof.MlKem.Arm.Ntt.layer_facts ℓ hℓ
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Ntt.lpre_ok h.env.r0) fun s₁ ⟨r2, r0, r1, r8, r10, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : VG.Proof.MlKem.Arm.Ntt.BInv s₀ m₁ (VG.Proof.MlKem.Arm.Ntt.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) ℓ) (128 / 2 ^ ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r0, r8.trans h.env.r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr,
      sp.trans h.env.sp, m ▸ h.env.frame⟩, by rw [r1, h.r1, Nat.add_zero], ?_, r10.trans h.r10, ?_⟩
    · rw [r2, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (VG.Proof.MlKem.Arm.Ntt.BInv s₀ m₁ (VG.Proof.MlKem.Arm.Ntt.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) ℓ) (128 / 2 ^ ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => VG.Proof.MlKem.Arm.Ntt.bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (VG.Proof.MlKem.Arm.Ntt.lpost_ok h₂.r10) fun s' ⟨r10, z, r0, r1, r8, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0.trans h₂.env.r0, r8.trans h₂.env.r8, lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, f4]
  · rw [r10, f6]
  · have e : 128 / (128 / 2 ^ ℓ) = 2 ^ ℓ :=
      Nat.div_eq_of_eq_mul_left (by omega) (by rw [Nat.mul_comm]; exact f2.symm)
    rw [m, VG.Proof.MlKem.Arm.Ntt.layers_succ _ hℓ, nttLayer, e]
    exact h₂.poly
  · rw [z, f6, f7]

/-! ## Setup and the end -/

/-- The registers saved and the table stored. -/
theorem setup_base {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ table zetaTable .r1)) s₀ fun s =>
      VG.Proof.MlKem.Arm.Ntt.Setup s₀ s.mem ∧ (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r1 (off := 512) (by decide) (fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g1 : (s₁.gpr .r1) = VG.Proof.MlKem.Arm.Ntt.ps s₀ := by rw [h₁.gpr]
  refine WP.mono (table_ok zetaTable (by decide) (b := .r1) (by decide) (by rw [g1]; exact fit_le (by decide) fS)
    fun k hk => by rw [g1, h₁.wr]; exact wS (by omega)) fun s₂ h₂ => ?_
  have hS : (VG.Proof.MlKem.Arm.Ntt.S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have fr : Frame [polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g1, ← add_ofNat_zero (State.addr (VG.Proof.MlKem.Arm.Ntt.ps s₀))]
      exact region_sub_off (by decide)
  have hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
    · rw [h₂.frame.readW (r := ⟨VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g1, add_ofNat_add, ← add_ofNat_zero (State.addr (VG.Proof.MlKem.Arm.Ntt.ps s₀))]
        exact region_disj_off (by omega) (by omega) (by omega) hS
    · have := h₂.tab j hj; rwa [g1] at this
    · exact polyIs_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
        ⟨hp.red, rfl⟩
  exact ⟨hm, fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr]), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem setup_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ table zetaTable .r1 ++ consts ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 4), .mov .r10 (.imm 512)] : List Instr)))
      s₀ fun s => VG.Proof.MlKem.Arm.Ntt.Setup s₀ s.mem ∧ VG.Proof.MlKem.Arm.Ntt.LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.Arm.Ntt.setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have elr := e .lr (by decide)
  run_block [consts, e0, e1, elr, rd, wr, sp, consts_val, hm, true_and]
  exact ⟨⟨rfl, rfl, by simp [elr], rfl, rfl, rfl, Frame.refl _ _⟩, rfl, rfl, hm.poly⟩

theorem restore_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ m₁) {s : State}
    (h : VG.Proof.MlKem.Arm.Ntt.LInv s₀ m₁ 7 s) :
    WP isa (.block (restoreRegs .r1 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (ntt (VG.Proof.MlKem.Arm.Ntt.P s₀)) := by
  have fS := hp.fitS
  have hS : (VG.Proof.MlKem.Arm.Ntt.S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 0 = VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 512 := by
    rw [h.r1, addr_add (by omega), add_ofNat_zero]
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 0) (by decide) (by rw [h.r1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [h.env.frame.readW (r := ⟨VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega))
    fun i hi => by
      rw [e1, h.env.rd, h.env.wr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀)) (by simp) (contains_off (by omega) (by omega)))
    fun s' h' => ⟨preserved_of_restore h' h.env.lr, h'.sp.trans h.env.sp, ?_⟩
  rw [h'.mem, ← VG.Proof.MlKem.Arm.Ntt.layers_seven]
  exact h.poly

theorem correct {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (Spec.MlKem.ntt (VG.Proof.MlKem.Arm.Ntt.P s₀)) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Ntt.setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_ne (VG.Proof.MlKem.Arm.Ntt.LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => VG.Proof.MlKem.Arm.Ntt.lstep hp hm hℓ h)
    (fun s h => VG.Proof.MlKem.Arm.Ntt.restore_ok hp hm h) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.nttContract Arm.abi).pre s) : VG.Proof.MlKem.Arm.Ntt.Pre s := by
  sig_pre [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.ntt (Spec.MlKem.nttContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlKem.Arm.Ntt.pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlKem.Arm.Ntt.correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlKem.Arm.Ntt.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlKem.Arm.Ntt

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.Arm.NttInv`. -/
section

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Proof/MlKem/Arm/Ntt.lean`, whose setup facts and
environment it shares): the three nested loops of `nttInvLayer`, `nttInvBlock`
and `nttInvBlockN`, with the zeta pointer going down; the inverse butterfly
symbolically executed once (`ibfly_ok`) writes the coefficients `bflyInv`
writes (`polyIs_ibfly`); then the loop multiplying every coefficient by 3303
(`sstep`). Layer `ℓ` has `len = 2^(ℓ+1)` and `64 / 2^ℓ` blocks.
-/

namespace VG.Proof.MlKem.Arm.NttInv

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)
open VG.Proof.MlKem.Arm.Ntt (toNat_val pf ps F S P Pre Setup Env bpost_ok lpre_ok ptr_add_add ptr_sub_beq
  lsr2 satState setup_base)

/-! ## Values -/

theorem ibfly_vals (a b z : Zq) :
    fixq (BitVec.ofNat 32 a.val + BitVec.ofNat 32 b.val - 3328 - 1) = BitVec.ofNat 32 (a + b).val ∧
    red VG.Proof.MlKem.Arm.C (BitVec.ofNat 32 z.val * fixq (BitVec.ofNat 32 b.val - BitVec.ofNat 32 a.val)) =
      BitVec.ofNat 32 (z * (b - a)).val := by
  have ha := (VG.Proof.MlKem.Arm.Ntt.toNat_val a).symm ▸ val_lt a
  have hb := (VG.Proof.MlKem.Arm.Ntt.toNat_val b).symm ▸ val_lt b
  have e1 : fixq (BitVec.ofNat 32 a.val + BitVec.ofNat 32 b.val - 3328 - 1) = BitVec.ofNat 32 (a + b).val :=
    ofNat_val_eq (by rw [fixq_add ha hb, VG.Proof.MlKem.Arm.Ntt.toNat_val, VG.Proof.MlKem.Arm.Ntt.toNat_val, val_add'])
  have e2 : fixq (BitVec.ofNat 32 b.val - BitVec.ofNat 32 a.val) = BitVec.ofNat 32 (b - a).val :=
    ofNat_val_eq (by rw [fixq_sub hb ha, VG.Proof.MlKem.Arm.Ntt.toNat_val, VG.Proof.MlKem.Arm.Ntt.toNat_val, val_sub',
      Nat.add_sub_assoc (Nat.le_of_lt a.isLt)])
  exact ⟨e1, by rw [e2, red_mul]⟩

/-- An inverse butterfly writes `f[j]`, then `f[j + len]`. -/
theorem polyIs_ibfly {m : Mem} {F : Addr} {f : VG.Spec.MlKem.Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) :
    PolyIs ((m.writeW (coeffAddr F j) (BitVec.ofNat 32 (f[j]! + f[j + len]!).val)).writeW
      (coeffAddr F (j + len)) (BitVec.ofNat 32 (z * (f[j + len]! - f[j]!)).val)) F (bflyInv f j len z) := by
  have h1 := polyIs_writeW h (j := j) (by omega) (f[j]! + f[j + len]!)
  have h2 := polyIs_writeW h1 hj (z * (f[j + len]! - f[j]!))
  simp only [bflyInv]
  rwa [getElem!_set!_ne _ hj (by omega)]

/-! ## The inverse butterfly -/

section
variable {s : State} {x y z c : BitVec 32}

theorem ibfly_ok (h2 : s.gpr .r2 = x) (h3 : s.gpr .r3 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = VG.Proof.MlKem.Arm.C)
    (h11 : s.gpr .r11 = c)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4) :
    WP isa (.block ibflyBody) s fun s' =>
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r3 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = VG.Proof.MlKem.Arm.C ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
          (fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
            s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 - 3328 - 1))).writeW
        (State.addr (y + BitVec.ofNat 32 0))
          (red VG.Proof.MlKem.Arm.C (z * fixq (s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))) := by
  run_block [ibflyBody, reduce, barrett, subQ, fixup, red, bar, fixq, h2, h3, h7, h8, h11, ia, ib, oa, ob,
    and_self, and_true]

end

/-! ## Butterflies of a block -/

/-- After `t` inverse butterflies of the block from `st` with the zeta
`zeta k` of the layer with `len`, from `Q`, the zeta pointer at `R1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (R1 : BitVec 32) (Q : VG.Spec.MlKem.Poly) (len k st : Nat) (t : Nat) (s : State) :
    Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = R1
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * (st + t))
  r3 : s.gpr .r3 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * (st + len + t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 (zeta k).val
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (len - t))
  poly : PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (nttInvBlockN Q len k st t)

theorem fstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} {R1 : BitVec 32} {Q : VG.Spec.MlKem.Poly} {len k st t : Nat}
    (hl : 0 < len) (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : VG.Proof.MlKem.Arm.NttInv.FInv s₀ m₁ R1 Q len k st t s) :
    WP isa (.block ibflyBody) s fun s' =>
      VG.Proof.MlKem.Arm.NttInv.FInv s₀ m₁ R1 Q len k st (t + 1) s' ∧ s'.z = decide (t + 1 = len) := by
  have fF := hp.fitF
  have ea := addr_coeff (i := 4 * (st + t)) (o := 0) (j := st + t) fF (by omega) (by omega)
  have eb := addr_coeff (i := 4 * (st + len + t)) (o := 0) (j := st + t + len) fF (by omega) (by omega)
  have ca := coeff_contains (VG.Proof.MlKem.Arm.Ntt.F s₀) (i := st + t) (by rw [n_eq]; omega)
  have cb := coeff_contains (VG.Proof.MlKem.Arm.Ntt.F s₀) (i := st + t + len) (by rw [n_eq]; omega)
  have iW : ∀ {a : Addr}, (polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀)).Contains a 4 → InRegions s.wr a 4 := fun hc => by
    rw [h.env.wr, hp.wr]; exact inRegions_of (by simp) hc
  have iR : ∀ {a : Addr}, (polyRegion (VG.Proof.MlKem.Arm.Ntt.F s₀)).Contains a 4 → InRegions (s.rd ++ s.wr) a 4 := fun hc => by
    rw [h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) hc
  have va := polyIs_coeffAt h.poly (i := st + t) (by rw [n_eq]; omega)
  have vb := polyIs_coeffAt h.poly (i := st + t + len) (by rw [n_eq]; omega)
  refine WP.mono (VG.Proof.MlKem.Arm.NttInv.ibfly_ok h.r2 h.r3 h.r7 h.env.r8 h.r11 (by rw [ea]; exact iR ca) (by rw [eb]; exact iR cb)
    (by rw [ea]; exact iW ca) (by rw [eb]; exact iW cb))
    fun s' ⟨r2, r3, r11, z, r0, r1, r7, r8, r10, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r0.trans h.env.r0, r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp,
        ?_⟩, r1.trans h.r1, ?_, ?_, r7, r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ ca).writeW (List.mem_singleton_self _) _ cb
  · rw [r2, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r3, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub (k := 1) ht
  · rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, va, vb, (VG.Proof.MlKem.Arm.NttInv.ibfly_vals _ _ (zeta k)).1, (VG.Proof.MlKem.Arm.NttInv.ibfly_vals _ _ _).2,
      nttInvBlockN_succ]
    exact VG.Proof.MlKem.Arm.NttInv.polyIs_ibfly h.poly hl (by rw [n_eq]; omega) (zeta k)
  · rw [z]; exact count_z (k := 1) ht (by decide) (by omega)

/-! ## Blocks -/

section
variable {s : State} {x1 x2 x10 : BitVec 32}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h10 : s.gpr .r10 = x10)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldr .r7 .r1 0, .dp .sub .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
        .mov .r11 (.shifted .r10 .lsr 2)]) s fun s' =>
      s'.gpr .r7 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 ∧ s'.gpr .r1 = x1 - 4 ∧
      s'.gpr .r3 = x2 + x10 ∧ s'.gpr .r11 = x10 >>> 2 ∧ s'.gpr .r2 = x2 ∧ s'.gpr .r10 = x10 ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h1, h2, h10, i1, and_self, and_true]

end

theorem ptr_sub4 (p : BitVec 32) {a : Nat} (ha : 1 ≤ a) (h : 4 * a < 2 ^ 32) :
    p + BitVec.ofNat 32 (4 * a) - 4 = p + BitVec.ofNat 32 (4 * (a - 1)) := by
  bv_omega

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : VG.Spec.MlKem.Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (256 / len - 1 - c))
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  poly : PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (nttInvLayerN Q len c)

theorem bstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ m₁) {Q : VG.Spec.MlKem.Poly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : VG.Proof.MlKem.Arm.NttInv.BInv s₀ m₁ Q len nb c s) :
    WP isa nttInvBlockCode s fun s' => VG.Proof.MlKem.Arm.NttInv.BInv s₀ m₁ Q len nb (c + 1) s' ∧ s'.z = decide (c + 1 = nb) := by
  have hl : 0 < len := by omega
  have fF := hp.fitF
  have fS := hp.fitS
  have hdiv : 256 / len = 2 * nb := by
    rw [show 256 = len * (2 * nb) by rw [← Nat.mul_assoc, Nat.mul_comm len 2, Nat.mul_assoc, hnb],
      Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hnb64 : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
  have hk : 256 / len - 1 - c < 128 := by omega
  have eS := addr_ptr (VG.Proof.MlKem.Arm.Ntt.ps s₀) (4 * (256 / len - 1 - c)) 0 (by omega)
  have cS : (polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀)).Contains (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c) + 0)) 4 :=
    contains_off (by omega) (by omega)
  have vz : s.mem.readW (VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c) + 0)) 32 =
      BitVec.ofNat 32 (zeta (256 / len - 1 - c)).val := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), Nat.add_zero, hm.tab _ hk, zetaTable_eq, zetas_getD hk]
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.NttInv.bpre_ok h.r1 h.r2 h.r10 (by
    rw [eS, h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cS))
    fun s₁ ⟨r7, r1, r3, r11, r2, r10, r0, r8, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have R1 : s₁.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (256 / len - 1 - (c + 1))) := by
    rw [r1, VG.Proof.MlKem.Arm.NttInv.ptr_sub4 _ (by omega) (by omega), Nat.sub_sub]
  have h₁ : VG.Proof.MlKem.Arm.NttInv.FInv s₀ m₁ (VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (256 / len - 1 - (c + 1)))) (nttInvLayerN Q len c) len
      (256 / len - 1 - c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r0.trans h.env.r0, r8.trans h.env.r8, lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, R1, ?_, ?_, ?_, r10, ?_, m ▸ h.poly⟩
    · rw [r2, Nat.add_zero]
    · rw [r3, VG.Proof.MlKem.Arm.Ntt.ptr_add_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega]
    · rw [r7, eS, vz]
    · rw [r11, VG.Proof.MlKem.Arm.Ntt.lsr2 (by omega)]
  refine wp_loop_ne (VG.Proof.MlKem.Arm.NttInv.FInv s₀ m₁ _ (nttInvLayerN Q len c) len (256 / len - 1 - c) (2 * len * c)) hl
    (fun t ht s h => VG.Proof.MlKem.Arm.NttInv.fstep hp hl (by omega) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (VG.Proof.MlKem.Arm.Ntt.bpost_ok h₂.env.r0 h₂.r3) fun s' ⟨r2, z, r0, r1, r8, r10, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0, r8.trans h₂.env.r8, lr.trans h₂.env.lr, rd.trans h₂.env.rd, wr.trans h₂.env.wr,
      sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, r1.trans h₂.r1, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r2]; congr 2; rw [Nat.mul_succ]; omega
  · rw [m, nttInvLayerN_succ]; exact h₂.poly
  · rw [z, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, VG.Proof.MlKem.Arm.Ntt.ptr_sub_beq _ (by omega) (by decide)]
    refine decide_eq_decide.mpr ⟨fun e => ?_, fun e => ?_⟩
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.eq_of_mul_eq_mul_left hl this
    · subst e; rw [Nat.mul_add, Nat.mul_one] at *; omega

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT⁻¹`. -/
def layers (f : VG.Spec.MlKem.Poly) (ℓ : Nat) : VG.Spec.MlKem.Poly := (nttInvLens.take ℓ).foldl nttInvLayer f

theorem layers_succ (f : VG.Spec.MlKem.Poly) {ℓ : Nat} (h : ℓ < 7) :
    VG.Proof.MlKem.Arm.NttInv.layers f (ℓ + 1) = nttInvLayer (VG.Proof.MlKem.Arm.NttInv.layers f ℓ) (2 ^ (ℓ + 1)) := by
  have e : ∀ ℓ < 7, nttInvLens[ℓ]? = some (2 ^ (ℓ + 1)) := by decide
  rw [VG.Proof.MlKem.Arm.NttInv.layers, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem layers_seven (f : VG.Spec.MlKem.Poly) : (VG.Proof.MlKem.Arm.NttInv.layers f 7).map (· * 3303) = nttInv f := by
  rw [nttInv_eq_layers]; rfl

/-- What the layers' loop counters are. -/
theorem layer_facts : ∀ ℓ < 7, (2 : Nat) ≤ 2 ^ (ℓ + 1) ∧ (2 ^ (ℓ + 1) * (64 / 2 ^ ℓ) : Nat) = 128 ∧
    (0 : Nat) < 64 / 2 ^ ℓ ∧ (256 / 2 ^ (ℓ + 1) - 1 - 0 : Nat) = 128 / 2 ^ ℓ - 1 ∧
    (256 / 2 ^ (ℓ + 1) - 1 - 64 / 2 ^ ℓ : Nat) = 128 / 2 ^ (ℓ + 1) - 1 ∧
    BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1)) <<< 1 = BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1 + 1)) ∧
    (BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1 + 1)) - 1024 == 0) = decide (ℓ + 1 = 7) := by
  decide

section
variable {s : State} {x10 : BitVec 32}

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.mov .r10 (.shifted .r10 .lsl 1), .cmp .r10 (.imm 1024)]) s fun s' =>
      s'.gpr .r10 = x10 <<< 1 ∧ s'.z = (x10 <<< 1 - 1024 == 0) ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h10, and_self, and_true]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ - 1))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * 2 ^ (ℓ + 1))
  poly : PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (VG.Proof.MlKem.Arm.NttInv.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) ℓ)

theorem lstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ : Mem} (hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : VG.Proof.MlKem.Arm.NttInv.LInv s₀ m₁ ℓ s) :
    WP isa nttInvLayerCode s fun s' => VG.Proof.MlKem.Arm.NttInv.LInv s₀ m₁ (ℓ + 1) s' ∧ s'.z = decide (ℓ + 1 = 7) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := VG.Proof.MlKem.Arm.NttInv.layer_facts ℓ hℓ
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.Ntt.lpre_ok h.env.r0) fun s₁ ⟨r2, r0, r1, r8, r10, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : VG.Proof.MlKem.Arm.NttInv.BInv s₀ m₁ (VG.Proof.MlKem.Arm.NttInv.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) ℓ) (2 ^ (ℓ + 1)) (64 / 2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r0, r8.trans h.env.r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr,
      sp.trans h.env.sp, m ▸ h.env.frame⟩, by rw [r1, h.r1, f4], ?_, r10.trans h.r10, ?_⟩
    · rw [r2, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (VG.Proof.MlKem.Arm.NttInv.BInv s₀ m₁ (VG.Proof.MlKem.Arm.NttInv.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) ℓ) (2 ^ (ℓ + 1)) (64 / 2 ^ ℓ)) f3
    (fun c hc s h => VG.Proof.MlKem.Arm.NttInv.bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (VG.Proof.MlKem.Arm.NttInv.lpost_ok h₂.r10) fun s' ⟨r10, z, r0, r1, r8, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0.trans h₂.env.r0, r8.trans h₂.env.r8, lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, f5]
  · rw [r10, f6]
  · have e : 128 / 2 ^ (ℓ + 1) = 64 / 2 ^ ℓ :=
      Nat.div_eq_of_eq_mul_left (by omega) (by rw [Nat.mul_comm]; exact f2.symm)
    rw [m, VG.Proof.MlKem.Arm.NttInv.layers_succ _ hℓ, nttInvLayer, e]
    exact h₂.poly
  · rw [z, f6, f7]

/-! ## Multiplication by 3303 -/

section
variable {s : State} {x y c : BitVec 32}

theorem scale_ok (h2 : s.gpr .r2 = x) (h7 : s.gpr .r7 = y) (h8 : s.gpr .r8 = VG.Proof.MlKem.Arm.C) (h11 : s.gpr .r11 = c)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block scaleBody) s fun s' =>
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r7 = y ∧ s'.gpr .r8 = VG.Proof.MlKem.Arm.C ∧
      s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (red VG.Proof.MlKem.Arm.C (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 * y)) := by
  run_block [scaleBody, reduce, barrett, subQ, fixup, red, bar, fixq, h2, h7, h8, h11, ia, oa,
    and_self, and_true]

end

theorem c3303 : BitVec.ofNat 32 (3303 : Zq).val = (BitVec.ofNat 16 3303).setWidth 32 := by decide

/-- After `i` coefficients multiplied by 3303, of `R` in `m₂`. -/
structure SInv (s₀ : State) (m₁ m₂ : Mem) (R : VG.Spec.MlKem.Poly) (i : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.Arm.Ntt.Env s₀ m₁ s
  r1 : s.gpr .r1 = VG.Proof.MlKem.Arm.Ntt.ps s₀ + BitVec.ofNat 32 (4 * (128 / 2 ^ 7 - 1))
  r2 : s.gpr .r2 = VG.Proof.MlKem.Arm.Ntt.pf s₀ + BitVec.ofNat 32 (4 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (3303 : Zq).val
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (256 - i))
  coeff : ∀ j < 256, coeffAt s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) j =
    if j < i then BitVec.ofNat 32 ((R.map (· * 3303))[j]!).val else coeffAt m₂ (VG.Proof.MlKem.Arm.Ntt.F s₀) j

theorem sstep {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ m₂ : Mem} {R : VG.Spec.MlKem.Poly} (hR : PolyIs m₂ (VG.Proof.MlKem.Arm.Ntt.F s₀) R) {i : Nat}
    (hi : i < 256) {s : State} (h : VG.Proof.MlKem.Arm.NttInv.SInv s₀ m₁ m₂ R i s) :
    WP isa (.block scaleBody) s fun s' => VG.Proof.MlKem.Arm.NttInv.SInv s₀ m₁ m₂ R (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fF := hp.fitF
  have ea := addr_coeff (i := 4 * i) (o := 0) (j := i) fF (by omega) (by omega)
  have ca := coeff_contains (VG.Proof.MlKem.Arm.Ntt.F s₀) (i := i) (by rw [n_eq]; omega)
  have va : coeffAt s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) i = BitVec.ofNat 32 (R[i]!).val := by
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]; exact polyIs_coeffAt hR (by rw [n_eq]; omega)
  refine WP.mono (VG.Proof.MlKem.Arm.NttInv.scale_ok h.r2 h.r7 h.env.r8 h.r11
    (by rw [ea, h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) ca)
    (by rw [ea, h.env.wr, hp.wr]; exact inRegions_of (by simp) ca))
    fun s' ⟨r2, r11, z, r0, r1, r7, r8, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r0.trans h.env.r0, r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp,
        ?_⟩, r1.trans h.r1, ?_, r7, ?_, ?_⟩, ?_⟩
  · rw [m, ea]; exact h.env.frame.writeW (List.mem_singleton_self _) _ ca
  · rw [r2]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub (k := 1) hi
  · rw [m, ea, ← coeffAt_eq, va, red_mul]
    exact coeff_one (a := i) hi h.coeff (by rw [map_mul_get _ (by rw [n_eq]; exact hi)])
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## Setup, the middle and the end -/

theorem setup_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ table zetaTable .r1 ++ consts ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 508), .mov .r10 (.imm 8)] : List Instr)))
      s₀ fun s => VG.Proof.MlKem.Arm.Ntt.Setup s₀ s.mem ∧ VG.Proof.MlKem.Arm.NttInv.LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.Arm.Ntt.setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have elr := e .lr (by decide)
  run_block [consts, e0, e1, elr, rd, wr, sp, consts_val, hm, true_and]
  exact ⟨⟨rfl, rfl, by simp [elr], rfl, rfl, rfl, Frame.refl _ _⟩, rfl, rfl, hm.poly⟩

theorem mid_ok {s₀ : State} {m₁ : Mem} {s : State} (h : VG.Proof.MlKem.Arm.NttInv.LInv s₀ m₁ 7 s) :
    WP isa (.block [.movw .r7 3303, .dp .sub .r2 .r0 (.imm 1024), .mov .r11 (.imm 256)]) s
      (VG.Proof.MlKem.Arm.NttInv.SInv s₀ m₁ s.mem (VG.Proof.MlKem.Arm.NttInv.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) 7) 0) := by
  have e0 := h.env.r0
  run_block [e0, BitVec.add_sub_cancel]
  refine ⟨⟨by simp [e0], by simp [h.env.r8], by simp [h.env.lr], h.env.rd, h.env.wr, h.env.sp, h.env.frame⟩,
    by simp [h.r1], by simp, by simp [VG.Proof.MlKem.Arm.NttInv.c3303], by simp, fun j _ => by simp⟩

theorem restore_ok {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) {m₁ m₂ : Mem} (hm : VG.Proof.MlKem.Arm.Ntt.Setup s₀ m₁) {R : VG.Spec.MlKem.Poly} {s : State}
    (h : VG.Proof.MlKem.Arm.NttInv.SInv s₀ m₁ m₂ R 256 s) :
    WP isa (.block (restoreRegs .r1 512)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (R.map (· * 3303)) := by
  have fS := hp.fitS
  have hS : (VG.Proof.MlKem.Arm.Ntt.S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 512 = VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 512 := by
    rw [h.r1]; simp
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 512) (by decide) (by rw [h.r1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [h.env.frame.readW (r := ⟨VG.Proof.MlKem.Arm.Ntt.S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega))
    fun i hi => by
      rw [e1, h.env.rd, h.env.wr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (VG.Proof.MlKem.Arm.Ntt.S s₀)) (by simp) (contains_off (by omega) (by omega)))
    fun s' h' => ⟨preserved_of_restore h' h.env.lr, h'.sp.trans h.env.sp, ?_⟩
  rw [h'.mem]
  exact polyIs_of_coeffAt fun j hj => by
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega)]

theorem correct {s₀ : State} (hp : VG.Proof.MlKem.Arm.Ntt.Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (VG.Proof.MlKem.Arm.Ntt.F s₀) (Spec.MlKem.nttInv (VG.Proof.MlKem.Arm.Ntt.P s₀)) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.Arm.NttInv.setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  refine wp_loop_ne (VG.Proof.MlKem.Arm.NttInv.LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => VG.Proof.MlKem.Arm.NttInv.lstep hp hm hℓ h)
    (fun s₂ h₂ => WP.seq (WP.mono (VG.Proof.MlKem.Arm.NttInv.mid_ok h₂) fun s₃ h₃ => WP.seq ?_)) h₁
  refine wp_loop_ne (VG.Proof.MlKem.Arm.NttInv.SInv s₀ s₁.mem s₂.mem (VG.Proof.MlKem.Arm.NttInv.layers (VG.Proof.MlKem.Arm.Ntt.P s₀) 7)) (N := 256) (by decide)
    (fun i hi s h => VG.Proof.MlKem.Arm.NttInv.sstep hp h₂.poly hi h) (fun s h => ?_) h₃
  refine WP.mono (VG.Proof.MlKem.Arm.NttInv.restore_ok hp hm h) fun s' ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩
  rw [← VG.Proof.MlKem.Arm.NttInv.layers_seven]; exact h3

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.nttInvContract Arm.abi).pre s) : VG.Proof.MlKem.Arm.Ntt.Pre s := by
  sig_pre [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem verified : Verified Arm.target Impl.MlKem.Arm.nttInv (Spec.MlKem.nttInvContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlKem.Arm.NttInv.pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlKem.Arm.NttInv.correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlKem.Arm.Ntt.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.Arm.NttInv

end
