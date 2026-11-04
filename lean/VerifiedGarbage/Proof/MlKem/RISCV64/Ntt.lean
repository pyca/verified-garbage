module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lazy
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Lazy
meta import VerifiedGarbage.Proof.MlKem.NttLayer
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic

/-!
# ML-KEM on RISC-V: `vg_mlkem_ntt`

As on PPC64LE (`Proof/MlKem/PPC64LE/Ntt.lean`), with no registers to save:
the table of the zetas stored (`setup_ok`); then the three nested loops of
`layerB`, `layF` and `wBlockN` on words (`Lazy.lean`, `Proof/MlKem/Blocks.lean`),
with an invariant each (`LInv`, `BInv`, `FInv`) saying which words `f` holds
(`LP`); the lazy butterfly is symbolically executed once for any (aligned)
pointers (`bfly_ok`), and stores the words `opB` gives (`lp_bfly`). Layer `ℓ`
has `len = 128 / 2^ℓ` and `2^ℓ` blocks. The seven layers leave words less
than `15 q` congruent to `NTT f` (`nttLB_rel`), which the last loop reduces,
coefficient by coefficient (`CInv`, `cstep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Ntt

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Proof.MlKem.RISCV64.Lazy (Word WPoly LP lp_writeW lp_lift w64 w64_load toW toW_store z64 opB layerB Rel
  lift residue layerB_rel barM redM redM_toNat barQ)
open VG.Proof.MlKem (wbfly wBlockN wbfly_get layF)

/-- The forward butterflies of a block, on words. -/
abbrev fblk : WPoly → Nat → Nat → Nat → Nat → WPoly := wBlockN opB

/-! ## Values -/

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem lp_bfly {m : Mem} {F : Addr} {W : WPoly} (h : LP m F W) {j len : Nat}
    (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32} (h₁ : v₁.toNat = (opB W[j]! W[j + len]! z).2.val)
    (h₂ : v₂.toNat = (opB W[j]! W[j + len]! z).1.val) :
    LP ((m.writeW (coeffAddr F (j + len)) v₁).writeW (coeffAddr F j) v₂) F (wbfly opB W j len z) :=
  lp_writeW (lp_writeW h hj _ h₁) (by omega_arith) _ h₂

/-! ## Loops on two pointers -/

/-- A `do … while (a ≠ b)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `a ≠ b` exactly when it is not the last. -/
theorem wp_loop_ne {body : Prog isa} {a b : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr a != s'.gpr b) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.ne a b)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .ne a b) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.ne a b) s' = some (decide (i + 1 ≠ N)) := by
    show (some (s'.gpr a != s'.gpr b) : Option Bool) = _
    rw [hz]
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega, i + 1, by omega, rfl, hs'⟩

/-- Two pointers into the same buffer differ exactly when their offsets do. -/
theorem ptr_bne (p : BitVec 64) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a != p + BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have h2 : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    have h3 : p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := fun e => h2 (by
      have := congrArg (· - p) e
      simpa using this)
    simp [h3, h]

/-! ## The butterfly -/

section
variable {s : State} {x z : BitVec 64} {o : Nat}

theorem bfly_ok (ho : o < 2048) (h5 : s.gpr .a2 = x) (h7 : s.gpr .a4 = z)
    (h8 : s.gpr .a5 = 5541226816974932) (h9 : s.gpr .a6 = 3329) (h12 : s.gpr .t5 = 6658)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 o) 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr (x + BitVec.ofNat 64 o) 4) (ax : x.toNat % 4 = 0)
    (ay : (x + BitVec.ofNat 64 o).toNat % 4 = 0) :
    WP isa (.block (bflyBody o)) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = s.gpr .a3 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧
      s'.gpr .t5 = 6658 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (x + BitVec.ofNat 64 o) (((s.mem.readW x 32).setWidth 64 -
            barM (z * (s.mem.readW (x + BitVec.ofNat 64 o) 32).setWidth 64) + 6658).setWidth 32)).writeW x
          (((s.mem.readW x 32).setWidth 64 +
            barM (z * (s.mem.readW (x + BitVec.ofNat 64 o) 32).setWidth 64)).setWidth 32) := by
  crun [bflyBody, barrettM, barM, barQ, kept, ho, h5, h7, h8, h9, h12, ia, ib, oa, ob, ax, ay,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## Loops -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .a0
abbrev S : Addr := s₀.gpr .a1
abbrev P : Poly := polyAt s₀.mem (F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (F s₀)
  alF : (F s₀).toNat % 4 = 0
  alS : (S s₀).toNat % 8 = 0

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTable.getD j 0)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps, with the constant `k5` in `t5`. -/
structure Env (k5 : BitVec 64) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  a0 : s.gpr .a0 = F s₀ + BitVec.ofNat 64 1024
  a5 : s.gpr .a5 = 5541226816974932
  a6 : s.gpr .a6 = 3329
  t5 : s.gpr .t5 = k5
  kept : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (F s₀)] m₁ s.mem

theorem Env.inW {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} {k5 : BitVec 64} (h : Env k5 s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (F s₀)).Contains a k) : InRegions s.wr a k := by
  rw [h.wr, hp.wr]; exact ⟨_, by simp, hc⟩

theorem Env.inR {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} {k5 : BitVec 64} (h : Env k5 s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (F s₀)).Contains a k) : InRegions (s.rd ++ s.wr) a k := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, hc⟩

theorem Env.inRS {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} {k5 : BitVec 64} (h : Env k5 s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (S s₀)).Contains a k) : InRegions (s.rd ++ s.wr) a k := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, hc⟩

/-- After `t` butterflies of the block from `st` with the zeta `zeta k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`, and `a3` at
the end of the block's first half. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (k + 1))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  a3 : s.gpr .a3 = F s₀ + BitVec.ofNat 64 (4 * (st + len))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (zeta k).val
  poly : LP s.mem (F s₀) (fblk Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : WPoly} {len k st t : Nat} (hl : 4 * len < 2048)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block (bflyBody (4 * len))) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .a2 != s'.gpr .a3) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + t)) + BitVec.ofNat 64 (4 * len) =
      coeffAddr (F s₀) (st + t + len) := by
    rw [ptr_add, show 4 * (st + t) + 4 * len = 4 * (st + t + len) by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := h.poly (st + t) (by rw [n_eq]; omega_arith)
  have vb := h.poly (st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (bfly_ok hl h.a2 h.a4 h.env.a5 h.env.a6 h.env.t5
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb)
    (align4_add hp.alF _) (by rw [eb]; exact align4_add hp.alF _))
    fun s' ⟨r5, r6, r3, r4, r7, r8, r9, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12, fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
        wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, r6.trans h.a3, r7, ?_⟩, ?_⟩
  · rw [m, eb, ea]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [m, eb, ea, ← coeffAt_eq, ← coeffAt_eq, w64_load va, w64_load vb,
      show fblk Q len k st (t + 1) = wbfly opB (fblk Q len k st t) (st + t) len (zeta k)
        from foldl_range'_succ _ _ _ _]
    exact lp_bfly h.poly (by rw [n_eq]; omega_arith) _ (toW_store _) (toW_store _)
  · have e2 : s'.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t + 1)) := by rw [r5]; exact ptr_succ _ 4 _
    rw [e2, r6, h.a3, ptr_bne _ (by omega_arith) (by omega_arith)]
    exact decide_eq_decide.mpr ⟨fun e e' => e (by omega_arith), fun e e' => e (by omega_arith)⟩

/-! ## Blocks -/

section
variable {s : State} {x4 x5 y : BitVec 64} {o : Nat}

/-- The start of a block: its zeta, and the end of its first half. -/
theorem bpre_ok (ho : o < 2048) (h4 : s.gpr .a1 = x4) (h5 : s.gpr .a2 = x5)
    (i4 : InRegions (s.rd ++ s.wr) x4 4) (a4 : x4.toNat % 4 = 0) :
    WP isa (.block [.load .w .a4 .a1 0, .addi .a1 .a1 4, .addi .a3 .a2 o]) s
      fun s' => s'.gpr .a4 = (s.mem.readW x4 32).setWidth 64 ∧ s'.gpr .a1 = x4 + 4 ∧
        s'.gpr .a3 = x5 + BitVec.ofNat 64 o ∧ s'.gpr .a2 = x5 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine Steps.wp_lwu (a := x4) (by decide) (by rw [h4]; simp) a4 i4 fun s₁ u₁ =>
    Steps.wp_addi (by decide) fun s₂ u₂ => Steps.wp_addi ho fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .a4 → r ≠ .a1 → r ≠ .a3 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4]; rfl,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h5],
    by rw [g _ (by decide) (by decide) (by decide), h5],
    g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide),
    fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide),
    by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp]⟩

/-- The end of a block: the next block's start. -/
theorem bpost_ok (ho : o < 2048) (h5 : s.gpr .a2 = y) :
    WP isa (.block [.addi .a2 .a2 o]) s fun s' =>
      s'.gpr .a2 = y + BitVec.ofNat 64 o ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a1 = s.gpr .a1 ∧
        s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine Steps.wp_addi ho fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, h5], u₁.other _ (by decide),
    u₁.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide),
    fun r hr => u₁.other r (by revert r; decide), u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (nb + c))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  poly : LP s.mem (F s₀) (layF fblk Q len (fun c => 128 / len + c) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : WPoly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (ho : 4 * len < 2048) (hnb : len * nb = 128) (hc : c < nb) {s : State}
    (h : BInv s₀ m₁ Q len nb c s) :
    WP isa (nttBlockCode (4 * len)) s fun s' =>
      BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .a2 != s'.gpr .a0) = decide (c + 1 ≠ nb) := by
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
  refine WP.seq (WP.mono (bpre_ok ho h.a1 h.a2 (h.env.inRS hp cS) (align4_add (by have := hp.alS; omega) _))
    fun s₁ ⟨r7, r4, r6, r5, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (layF fblk Q len (fun c => 128 / len + c) c) len (128 / len + c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
      fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, m ▸ h.poly⟩
    · rw [r4, hdiv]
      exact (ptr_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega_arith])
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len) by omega_arith]
    · rw [r7, vz]
  refine wp_loop_ne (FInv s₀ m₁ (layF fblk Q len (fun c => 128 / len + c) c) len (128 / len + c) (2 * len * c)) hl
    (fun t ht s h => fstep hp ho (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok ho h₂.a2) fun s' ⟨r5, r3, r4, r8, r9, r12, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6, r12.trans h₂.env.t5,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, hdiv, Nat.add_assoc]
  · rw [r5, ptr_add]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, layF, foldl_range_succ, ← layF]; exact h₂.poly
  · rw [r5, r3, h₂.env.a0, ptr_add, show (1024 : Nat) = 4 * 256 from rfl,
      ptr_bne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- What the layers' loops count: layer `ℓ` has `len = 128 >>> ℓ` and `2^ℓ`
blocks, and its code is the `ℓ`-th of `nttOffs`. -/
theorem layer_facts : ∀ ℓ < 7, 2 ≤ 128 >>> ℓ ∧ (128 >>> ℓ) * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 128 / (128 >>> ℓ) = 2 ^ ℓ ∧ 4 * (128 >>> ℓ) < 2048 ∧
    nttOffs.drop ℓ = 4 * (128 >>> ℓ) :: nttOffs.drop (ℓ + 1) := by
  decide

section
variable {s : State} {x3 : BitVec 64}

theorem lpre_ok (h3 : s.gpr .a0 = x3) :
    WP isa (.block [.addi .a2 .a0 (-1024)]) s fun s' =>
      s'.gpr .a2 = x3 - 1024 ∧ s'.gpr .a0 = x3 ∧ s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a5 = s.gpr .a5 ∧
        s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h3, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- The first `ℓ` layers of the butterflies on words. -/
def nttLB (ℓ : Nat) (W : WPoly) : WPoly := (nttLens.take ℓ).foldl layerB W

theorem nttLB_succ (W : WPoly) {ℓ : Nat} (hℓ : ℓ < 7) : nttLB (ℓ + 1) W = layerB (nttLB ℓ W) (128 >>> ℓ) := by
  have e : nttLens[ℓ]'(by simp [nttLens]; omega_arith) = 128 >>> ℓ := by
    revert ℓ; decide
  unfold nttLB
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttLens]; omega_arith), e]
  rfl

theorem len_mem : ∀ ℓ < 7, 128 >>> ℓ ∈ [2, 4, 8, 16, 32, 64, 128] := by decide

/-- After `ℓ` layers, words less than `(2ℓ + 1) q` congruent to the
specification's. -/
theorem nttLB_rel (f : Poly) : ∀ ℓ ≤ 7, Rel (2 * ℓ + 1) (nttLB ℓ (lift f)) (nttL ℓ f)
  | 0, _ => Lazy.lift_rel f
  | ℓ + 1, h => by
    rw [nttLB_succ _ (by omega_arith), nttL_succ _ (by omega_arith)]
    exact layerB_rel (by omega_arith) (nttLB_rel f ℓ (by omega_arith)) (len_mem ℓ (by omega_arith))

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * 2 ^ ℓ)
  poly : LP s.mem (F s₀) (nttLB ℓ (lift (P s₀)))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa (nttLayerCode (4 * (128 >>> ℓ))) s (LInv s₀ m₁ (ℓ + 1)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, -⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.a0)
    fun s₁ ⟨r5, r3, r4, r8, r9, r12, kp, m, rd, wr, sp⟩ => ?_)
  have h₁ : BInv s₀ m₁ (nttLB ℓ (lift (P s₀))) (128 >>> ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
      rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.a1, Nat.add_zero], ?_, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (BInv s₀ m₁ (nttLB ℓ (lift (P s₀))) (128 >>> ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f6 f2 hc h) (fun s₂ h₂ => ⟨h₂.env, ?_, ?_⟩) h₁
  · rw [h₂.a1, f4]
  · rw [nttLB_succ _ hℓ, layerB]
    exact (congrArg (fun b => LP s₂.mem (F s₀) (layF fblk (nttLB ℓ (lift (P s₀))) (128 >>> ℓ)
      (fun c => 128 / (128 >>> ℓ) + c) b)) f5).mpr h₂.poly

/-- The layers from `ℓ` on. -/
theorem layers_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) :
    ∀ j ℓ, ℓ + j = 7 → ∀ s, LInv s₀ m₁ ℓ s → WP isa (layers nttLayerCode (nttOffs.drop ℓ)) s (LInv s₀ m₁ 7)
  | 0, ℓ, h, s, hs => by
    obtain rfl : ℓ = 7 := by omega
    exact WP.block_nil hs
  | j + 1, ℓ, h, s, hs => by
    have hℓ : ℓ < 7 := by omega
    rw [(layer_facts ℓ hℓ).2.2.2.2.2.2]
    exact WP.seq (WP.mono (lstep hp hm hℓ hs) fun s' h' => layers_ok hp hm j (ℓ + 1) (by omega) s' h')

/-! ## Setup and the end -/

theorem sub_low (p : Addr) {k L : Nat} (h : k ≤ L) : Region.Sub ⟨p, k⟩ ⟨p, L⟩ := fun a ha => by
  simp only [Region.Contains] at ha ⊢; omega_arith

/-- The table stored in `scratch`. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTable .a1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .t0 → r ≠ .t2 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have a8 : (s₀.gpr .a1).toNat % 8 = 0 := hp.alS
  refine WP.mono (table_ok zetaTable (by decide) (b := .a1) (by decide) (by decide) rfl
    (by omega) fun k hk => wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    exact sub_low _ (by omega_arith)
  exact ⟨⟨fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩,
    h₂.gpr, h₂.rd, h₂.wr, h₂.sp⟩

theorem tail_ok {s : State} :
    WP isa (.block (constsM ++ ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1024 ∧ s'.gpr .a1 = s.gpr .a1 + 4 ∧
        s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .t5 = 6658 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [constsM, loadM, liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTable .a1 ++ constsM ++
      ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r12, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .a0 (by decide) (by decide)], r8, r9, r12, fun r hr => ?_, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩,
    by rw [r4, e .a1 (by decide) (by decide)]; rfl, m ▸ lp_lift hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide) (by revert r hr; decide)]

/-! ## The reduction -/

/-- The first `i` words of `W` reduced modulo `q`. -/
def canonN (W : WPoly) (i : Nat) : WPoly :=
  (List.range i).foldl (fun w j => w.set! j (Fin.ofNat _ (w[j]!.val % q))) W

theorem canonN_zero (W : WPoly) : canonN W 0 = W := rfl

theorem canonN_succ (W : WPoly) (i : Nat) :
    canonN W (i + 1) = (canonN W i).set! i (Fin.ofNat _ ((canonN W i)[i]!.val % q)) :=
  foldl_range_succ _ _ _

theorem canonN_get (W : WPoly) : ∀ i ≤ n, ∀ j < n,
    (canonN W i)[j]! = if j < i then Fin.ofNat _ (W[j]!.val % q) else W[j]!
  | 0, _, j, _ => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | i + 1, hi, j, hj => by
    have ih := canonN_get W i (by omega_arith)
    rw [canonN_succ]
    by_cases e : i = j
    · subst e
      rw [VG.Proof.MlKem.vget_set_self _ hj, ih i hj, ite_eq_right (Nat.lt_irrefl i),
        ite_eq_left (Nat.lt_succ_self i)]
    · rw [VG.Proof.MlKem.vget_set_ne _ hj e, ih j hj]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hji, ite_eq_right (by omega_arith)]

/-- A word reduced modulo `q`, as `reduceM` stores it. -/
theorem red_store (x : Word) :
    ((redM (w64 x)).setWidth 32).toNat = (Fin.ofNat 4294967296 (x.val % q) : Word).val := by
  have hq : x.val % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [BitVec.toNat_setWidth, redM_toNat, Lazy.w64_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

/-- After `i` words of `W` reduced. -/
structure CInv (s₀ : State) (m₁ : Mem) (W : WPoly) (i : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  poly : LP s.mem (F s₀) (canonN W i)

section
variable {s : State} {x c : BitVec 64}

theorem canon_ok (h5 : s.gpr .a2 = x) (h8 : s.gpr .a5 = 5541226816974932)
    (h9 : s.gpr .a6 = 3329) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (oa : InRegions s.wr x 4) (ax : x.toNat % 4 = 0) :
    WP isa (.block canonBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .t5 = s.gpr .t5 ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((redM ((s.mem.readW x 32).setWidth 64)).setWidth 32) := by
  crun [canonBody, reduceM, barrettM, fixup, redM, barM, barQ, fixq, kept, h5, h8, h9, h11, ia, oa, ax,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

theorem cstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {W : WPoly} {i : Nat} (hi : i < 256) {s : State}
    (h : CInv s₀ m₁ W i s) :
    WP isa (.block canonBody) s fun s' => CInv s₀ m₁ W (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have ca := coeff_contains (F s₀) (i := i) (by rw [n_eq]; omega_arith)
  have va := h.poly i (by rw [n_eq]; omega_arith)
  refine WP.mono (canon_ok h.a2 h.env.a5 h.env.a6 h.t1 (h.env.inR hp ca) (h.env.inW hp ca)
    (align4_add hp.alF _))
    fun s' ⟨r5, r11, r3, r8, r9, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [m]; exact h.env.frame.writeW (List.mem_singleton_self _) _ ca
  · rw [r5]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub hi
  · rw [m, show F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i from rfl, ← coeffAt_eq, w64_load va,
      canonN_succ]
    exact lp_writeW h.poly (by rw [n_eq]; omega_arith) _ (red_store _)
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by omega_arith)

/-- Words less than `15 q`, each reduced: the polynomial they are congruent to. -/
theorem canon_full {m : Mem} {p : Addr} {W : WPoly} {f : Poly} (hr : Rel 15 W f) (h : LP m p (canonN W 256)) :
    PolyIs m p f := polyIs_of_toNat fun i hi => by
  have hi' : i < 256 := by rw [n_eq] at hi; exact hi
  rw [h i hi, canonN_get W 256 (by rw [n_eq]) i hi, ite_eq_left hi', ← (hr i hi').2, Fin.val_ofNat, Fin.val_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q ≤ 4294967296))]

theorem cpre_ok {s : State} :
    WP isa (.block [.addi .a2 .a0 (-1024), .li .t1 256]) s
      fun s' => s'.gpr .a2 = s.gpr .a0 - 1024 ∧ s'.gpr .t1 = BitVec.ofNat 64 256 ∧ s'.gpr .a0 = s.gpr .a0 ∧
        s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_)
  refine WP.seq (WP.mono (layers_ok hp hm 7 0 rfl s₁ h₁) fun s h => ?_)
  refine WP.seq (WP.mono cpre_ok fun s₂ ⟨r5, r11, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (CInv s₀ s₁.mem (nttLB 7 (lift (P s₀)))) (N := 256) (by decide)
    (fun i hi s h => cstep hp hi h) (fun s' h' => ⟨fun r hr => h'.env.kept r (preserved_sub r hr), h'.env.sp,
      h'.env.kept .ra (by decide), by
        rw [ntt_eq_nttL]; exact canon_full (nttLB_rel (P s₀) 7 (by decide)) h'.poly⟩) ?_
  refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
    fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
    wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, r11, ?_⟩
  · rw [r5, h.env.a0, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
  · rw [m, canonN_zero]; exact h.poly

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlKem.nttContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified RISCV64.target Impl.MlKem.RISCV64.ntt (Proof.MlKem.nttContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs]
    exact h
  · sig_pub [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Ntt
