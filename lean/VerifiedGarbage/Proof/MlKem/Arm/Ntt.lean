module

public import VerifiedGarbage.Proof.MlKem.Arm.Reduce
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.Arm.Reduce
meta import VerifiedGarbage.Proof.MlKem.Arm.Add
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_ntt`

The registers saved and the table of the zetas stored (`setup_ok`); then the
three nested loops of `layerF`, `layF` and `wBlockN` on words
(`Reduce.lean`, `Proof/MlKem/Blocks.lean`), with an invariant each (`LInv`,
`BInv`, `FInv`) saying which words `f` holds (`LP`); the butterfly is
symbolically executed once for any pointers (`bfly_ok`), and stores the
words `opF` gives (`lp_bfly`). Layer `ℓ` has `len = 128 / 2^ℓ` and `2^ℓ`
blocks. The seven layers leave words less than `15 q` congruent to `NTT f`
(`layersW_rel`), which the last loop reduces (`canon_ok`, `map_ok`); then
the registers restored.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.Ntt

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The butterfly -/

section
variable {s : State} {x y z zp k c : BitVec 32}

theorem bfly_ok (h2 : s.gpr .r2 = x) (h3 : s.gpr .r3 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = Nq)
    (h9 : s.gpr .r9 = zp) (h11 : s.gpr .r11 = c) (h12 : s.gpr .r12 = k)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4) :
    WP isa (.block bflyBody) s fun s' =>
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r3 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = Nq ∧ s'.gpr .r9 = zp ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r12 = k ∧ s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 + k -
            bmz (s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32) z zp)).writeW
        (State.addr (x + BitVec.ofNat 32 0))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
            bmz (s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32) z zp) := by
  run_block [bflyBody, mulz, bmz, h2, h3, h7, h8, h9, h11, h12, ia, ib, oa, ob, and_self, and_true]

end

/-! ## Loops -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev ps : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (pf s₀)
abbrev S : Addr := State.addr (ps s₀)
abbrev P : Poly := polyAt s₀.mem (F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s₀).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s₀.mem (F s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : Saved m₁ (S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    BitVec.ofNat 32 (zetaQuot (zetaTable.getD j 0) + 65536 * zetaTable.getD j 0)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps. -/
structure Env (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + 1024
  r8 : s.gpr .r8 = Nq
  r12 : s.gpr .r12 = 6658
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (F s₀)] m₁ s.mem

/-- The zeta `zeta k` and its quotient, in `r7` and `r9`. -/
def ZetaIn (k : Nat) (s : State) : Prop :=
  s.gpr .r7 = BitVec.ofNat 32 (zeta k).val ∧ s.gpr .r9 = BitVec.ofNat 32 (zetaQuot (zeta k).val)

/-- After `t` butterflies of the block from `st` with the zeta `zeta k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (k + 1))
  r2 : s.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * (st + t))
  r3 : s.gpr .r3 = pf s₀ + BitVec.ofNat 32 (4 * (st + len + t))
  zeta : ZetaIn k s
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (len - t))
  poly : LP s.mem (F s₀) (wBlockN opF Q len k st t)

/-- One more butterfly of a block. -/
theorem wBlockN_succ (op : Word → Word → Zq → Word × Word) (f : WPoly) (len k st t : Nat) :
    wBlockN op f len k st (t + 1) = wbfly op (wBlockN op f len k st t) (st + t) len (zeta k) := by
  rw [wBlockN, foldl_range'_succ, ← wBlockN]

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : WPoly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block bflyBody) s fun s' => FInv s₀ m₁ Q len k st (t + 1) s' ∧ s'.z = decide (t + 1 = len) := by
  have fF := hp.fitF
  have ea := addr_coeff (i := 4 * (st + t)) (o := 0) (j := st + t) fF (by omega_arith) (by omega_arith)
  have eb := addr_coeff (i := 4 * (st + len + t)) (o := 0) (j := st + t + len) fF (by omega_arith) (by omega_arith)
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have iW : ∀ {a : Addr}, (polyRegion (F s₀)).Contains a 4 → InRegions s.wr a 4 := fun hc => by
    rw [h.env.wr, hp.wr]; exact inRegions_of (by simp) hc
  have iR : ∀ {a : Addr}, (polyRegion (F s₀)).Contains a 4 → InRegions (s.rd ++ s.wr) a 4 := fun hc => by
    rw [h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) hc
  have va := lp_word h.poly (j := st + t) (by rw [n_eq]; omega_arith)
  have vb := lp_word h.poly (j := st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (bfly_ok h.r2 h.r3 h.zeta.1 h.env.r8 h.zeta.2 h.r11 h.env.r12 (by rw [ea]; exact iR ca)
    (by rw [eb]; exact iR cb) (by rw [ea]; exact iW ca) (by rw [eb]; exact iW cb))
    fun s' ⟨r2, r3, r11, z, r0, r1, r7, r8, r9, r10, r12, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r0.trans h.env.r0, r8, r12, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp,
        ?_⟩, r1.trans h.r1, ?_, ?_, ⟨r7, r9⟩, r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r2, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r3, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub (k := 1) ht
  · rw [m, ea, eb, va, vb, wBlockN_succ]
    exact lp_bfly h.poly opF hl (by rw [n_eq]; omega_arith) _ (toW_val _).symm (toW_val _).symm
  · rw [z]; exact count_z (k := 1) ht (by decide) (by omega_arith)

/-! ## Blocks -/

section
variable {s : State} {x0 x1 x2 x10 y : BitVec 32}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h10 : s.gpr .r10 = x10)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (zetaLoad ++ ([.dp .add .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
        .mov .r11 (.shifted .r10 .lsr 2)] : List Instr))) s fun s' =>
      s'.gpr .r7 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 >>> 16 ∧
      s'.gpr .r9 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 -
        (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 >>> 16) <<< 16 ∧ s'.gpr .r1 = x1 + 4 ∧
      s'.gpr .r3 = x2 + x10 ∧ s'.gpr .r11 = x10 >>> 2 ∧ s'.gpr .r2 = x2 ∧ s'.gpr .r10 = x10 ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [zetaLoad, h1, h2, h10, i1, and_self, and_true]

/-- The end of a block: the next block's start, compared with the end. -/
theorem bpost_ok (h0 : s.gpr .r0 = x0) (h3 : s.gpr .r3 = y) :
    WP isa (.block [.mov .r2 (.reg .r3), .cmp .r2 (.reg .r0)]) s fun s' =>
      s'.gpr .r2 = y ∧ s'.z = (y - x0 == 0) ∧ s'.gpr .r0 = x0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, h3, and_self, and_true]

end

theorem lsr2 {len : Nat} (h : 4 * len < 2 ^ 32) :
    BitVec.ofNat 32 (4 * len) >>> 2 = BitVec.ofNat 32 (1 * (len - 0)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  omega_arith

theorem ptr_add_add (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Two pointers from `p` are equal exactly when their offsets are. -/
theorem ptr_sub_beq (p : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (p + BitVec.ofNat 32 a - (p + BitVec.ofNat 32 b) == 0) = decide (a = b) := by
  rw [sub_beq_zero]
  by_cases h : a = b
  · subst h; simp
  · have : p + BitVec.ofNat 32 a ≠ p + BitVec.ofNat 32 b := fun e => h (by
      have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp e)
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    simp [this, h]

/-- The zeta of index `k` of the table, unpacked. -/
theorem zeta_unpack {k : Nat} (hk : k < 128) :
    BitVec.ofNat 32 (zetaQuot (zetaTable.getD k 0) + 65536 * zetaTable.getD k 0) >>> 16 =
        BitVec.ofNat 32 (zeta k).val ∧
      BitVec.ofNat 32 (zetaQuot (zetaTable.getD k 0) + 65536 * zetaTable.getD k 0) -
          (BitVec.ofNat 32 (zetaQuot (zetaTable.getD k 0) + 65536 * zetaTable.getD k 0) >>> 16) <<< 16 =
        BitVec.ofNat 32 (zetaQuot (zeta k).val) := by
  rw [zetaTable_eq, zetas_getD hk]
  have hz := val_lt (zeta k)
  exact unpack (by omega_using [hz]) (zetaQuot_lt (zeta k).isLt)

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (nb + c))
  r2 : s.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  poly : LP s.mem (F s₀) (layF (wBlockN opF) Q len (fun c => 128 / len + c) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : WPoly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttBlockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ s'.z = decide (c + 1 = nb) := by
  have hl : 0 < len := by omega_arith
  have fF := hp.fitF
  have fS := hp.fitS
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hk : nb + c < 128 := by
    have : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
    omega_arith
  have eS := addr_ptr (ps s₀) (4 * (nb + c)) 0 (by omega_arith)
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (nb + c) + 0)) 4 :=
    contains_off (by omega_arith) (by omega_arith)
  have vz : s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (nb + c) + 0)) 32 =
      BitVec.ofNat 32 (zetaQuot (zetaTable.getD (nb + c) 0) + 65536 * zetaTable.getD (nb + c) 0) := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), Nat.add_zero, hm.tab _ hk]
  refine WP.seq (WP.mono (bpre_ok h.r1 h.r2 h.r10 (by
    rw [eS, h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cS))
    fun s₁ ⟨r7, r9, r1, r3, r11, r2, r10, r0, r8, r12, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (layF (wBlockN opF) Q len (fun c => 128 / len + c) c) len (128 / len + c)
      (2 * len * c) 0 s₁ := by
    refine ⟨⟨r0.trans h.env.r0, r8.trans h.env.r8, r12.trans h.env.r12, lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_, m ▸ h.poly⟩
    · rw [r1, hdiv]
      exact (ptr_add_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega_arith])
    · rw [r2, Nat.add_zero]
    · rw [r3, ptr_add_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [hdiv]
      exact ⟨by rw [r7, eS, vz]; exact (zeta_unpack hk).1, by rw [r9, eS, vz]; exact (zeta_unpack hk).2⟩
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_ne (FInv s₀ m₁ (layF (wBlockN opF) Q len (fun c => 128 / len + c) c) len (128 / len + c)
    (2 * len * c)) hl (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.env.r0 h₂.r3) fun s' ⟨r2, z, r0, r1, r8, r10, r12, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0, r8.trans h₂.env.r8, r12.trans h₂.env.r12, lr.trans h₂.env.lr, rd.trans h₂.env.rd, wr.trans h₂.env.wr,
      sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, hdiv, Nat.add_assoc]
  · rw [r2]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, layF, foldl_range_succ, ← layF]; exact h₂.poly
  · rw [z, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, ptr_sub_beq _ (by omega_arith) (by decide)]
    refine decide_eq_decide.mpr ⟨fun e => ?_, fun e => ?_⟩
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this
    · subst e; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT`. -/
def layers (f : Poly) (ℓ : Nat) : Poly := (nttLens.take ℓ).foldl nttLayer f

theorem layers_succ (f : Poly) {ℓ : Nat} (h : ℓ < 7) :
    layers f (ℓ + 1) = nttLayer (layers f ℓ) (128 / 2 ^ ℓ) := by
  have e : ∀ ℓ < 7, nttLens[ℓ]? = some (128 / 2 ^ ℓ) := by decide
  rw [layers, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem layers_seven (f : Poly) : layers f 7 = ntt f := by
  rw [ntt_eq_layers]; rfl

/-- The first `ℓ` layers of the butterflies on words. -/
def layersW (W : WPoly) (ℓ : Nat) : WPoly := (nttLens.take ℓ).foldl layerF W

theorem layersW_succ (W : WPoly) {ℓ : Nat} (h : ℓ < 7) :
    layersW W (ℓ + 1) = layerF (layersW W ℓ) (128 / 2 ^ ℓ) := by
  have e : ∀ ℓ < 7, nttLens[ℓ]? = some (128 / 2 ^ ℓ) := by decide
  rw [layersW, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem len_mem : ∀ ℓ < 7, 128 / 2 ^ ℓ ∈ [2, 4, 8, 16, 32, 64, 128] := by decide

/-- After `ℓ` layers, words less than `(2ℓ + 1) q` congruent to the
specification's. -/
theorem layersW_rel (f : Poly) : ∀ ℓ ≤ 7, Rel (2 * ℓ + 1) (layersW (lift f) ℓ) (layers f ℓ)
  | 0, _ => lift_rel f
  | ℓ + 1, h => by
    rw [layersW_succ _ (by omega_arith), layers_succ _ (by omega_arith)]
    exact layerF_rel (by omega_arith) (layersW_rel f ℓ (by omega_arith)) (len_mem ℓ (by omega_arith))

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
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, and_self, and_true]

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.mov .r10 (.shifted .r10 .lsr 1), .cmp .r10 (.imm 4)]) s fun s' =>
      s'.gpr .r10 = x10 >>> 1 ∧ s'.z = (x10 >>> 1 - 4 == 0) ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h10, and_self, and_true]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * 2 ^ ℓ)
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ))
  poly : LP s.mem (F s₀) (layersW (lift (P s₀)) ℓ)

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ s'.z = decide (ℓ + 1 = 7) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.r0) fun s₁ ⟨r2, r0, r1, r8, r10, r12, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (layersW (lift (P s₀)) ℓ) (128 / 2 ^ ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r0, r8.trans h.env.r8, r12.trans h.env.r12, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr,
      sp.trans h.env.sp, m ▸ h.env.frame⟩, by rw [r1, h.r1, Nat.add_zero], ?_, r10.trans h.r10, ?_⟩
    · rw [r2, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (BInv s₀ m₁ (layersW (lift (P s₀)) ℓ) (128 / 2 ^ ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.r10) fun s' ⟨r10, z, r0, r1, r8, r12, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0.trans h₂.env.r0, r8.trans h₂.env.r8, r12.trans h₂.env.r12, lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, f4]
  · rw [r10, f6]
  · have e : 128 / (128 / 2 ^ ℓ) = 2 ^ ℓ :=
      Nat.div_eq_of_eq_mul_left (by omega_arith) (by rw [Nat.mul_comm]; exact f2.symm)
    rw [m, layersW_succ _ hℓ, layerF]
    exact (congrArg (fun b => LP s₂.mem (F s₀) (layF (wBlockN opF) (layersW (lift (P s₀)) ℓ) (128 / 2 ^ ℓ)
      (fun c => 128 / (128 / 2 ^ ℓ) + c) b)) e).mpr h₂.poly
  · rw [z, f6, f7]

/-! ## A loop over the coefficients -/

/-- The code `body` replaces the coefficient at `r2` by `g` of it, moves `r2`
to the next, and counts down in `r11`, keeping what `C` says of the
registers. -/
def MapOk (body : List Instr) (g : BitVec 32 → BitVec 32) (C : State → Prop) : Prop :=
  ∀ (s : State) (x c : BitVec 32), s.gpr .r2 = x → s.gpr .r11 = c → C s →
    InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
    InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
    WP isa (.block body) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ C s' ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- The loop of such a body over the 256 coefficients of `f`. -/
theorem map_ok {body : List Instr} {g : BitVec 32 → BitVec 32} {C : State → Prop} (hb : MapOk body g C)
    {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h2 : s.gpr .r2 = pf s₀) (h11 : s.gpr .r11 = BitVec.ofNat 32 256) (hC : C s) :
    WP isa (.loop (.block body) .ne) s fun s' =>
      (∀ j < 256, coeffAt s'.mem (F s₀) j = g (coeffAt s.mem (F s₀) j)) ∧
        Frame [polyRegion (F s₀)] s.mem s'.mem ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .lr = s.gpr .lr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have fF := hp.fitF
  refine wp_loop_ne (fun t s' => s'.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * t) ∧
      s'.gpr .r11 = BitVec.ofNat 32 (1 * (256 - t)) ∧ C s' ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [polyRegion (F s₀)] s.mem s'.mem ∧
      ∀ j < 256, coeffAt s'.mem (F s₀) j =
        if j < t then g (coeffAt s.mem (F s₀) j) else coeffAt s.mem (F s₀) j) (N := 256) (by decide)
    (fun t ht s' ⟨r2, r11, hC', r1, lr, rd, wr, sp, hf, hc⟩ => ?_)
    (fun s' ⟨_, _, _, r1, lr, rd, wr, sp, hf, hc⟩ =>
      ⟨fun j hj => by rw [hc j hj, ite_eq_left hj], hf, r1, lr, rd, wr, sp⟩)
    ⟨by rw [h2, Nat.mul_zero]; exact (BitVec.add_zero _).symm, h11, hC, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun j _ => by rw [ite_eq_right (Nat.not_lt_zero j)]⟩
  have ea := addr_coeff (i := 4 * t) (o := 0) (j := t) fF (by omega_arith) (by omega_arith)
  have ca := coeff_contains (F s₀) (i := t) (by rw [n_eq]; exact ht)
  refine WP.mono (hb s' _ _ r2 r11 hC'
      (by rw [ea, rd, wr, hrd, hwr, hp.rd, hp.wr]; exact inRegions_of (by simp) ca)
      (by rw [ea, wr, hwr, hp.wr]; exact inRegions_of (by simp) ca))
    fun s'' ⟨hm, r2', r11', hz, hC'', r1', lr', rd', wr', sp'⟩ =>
      ⟨⟨?_, ?_, hC'', r1'.trans r1, lr'.trans lr, rd'.trans rd, wr'.trans wr, sp'.trans sp, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [r2']; exact ptr_succ _ 4 _
  · rw [r11']; exact count_sub (k := 1) ht
  · rw [hm, ea]; exact hf.writeW (List.mem_singleton_self _) _ ca
  · rw [hm, ea, ← coeffAt_eq, coeffAt_writeW _ _ (show j < n by rw [n_eq]; exact hj) (by rw [n_eq]; exact ht),
      hc j hj, hc t ht, ite_eq_right (Nat.lt_irrefl t)]
    by_cases e : t = j
    · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self t)]
    · rw [ite_eq_right e]
      by_cases hj' : j < t
      · rw [ite_eq_left hj', ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hj', ite_eq_right (by omega_arith)]
  · rw [hz]; exact count_z (k := 1) ht (by decide) (by decide)

/-- What the last loop keeps: `-q` in `r8` and `40318` in `r9`. -/
def CanonIn (s : State) : Prop := s.gpr .r8 = Nq ∧ s.gpr .r9 = 40318

theorem canon_ok : MapOk canonBody bcan CanonIn := by
  intro s x c h2 h11 ⟨h8, h9⟩ ia oa
  run_block [canonBody, bcan, CanonIn, h2, h8, h9, h11, ia, oa, and_self, and_true]

theorem canonPre_ok {s : State} {x0 : BitVec 32} (h0 : s.gpr .r0 = x0) :
    WP isa (.block [.movw .r9 40318, .dp .sub .r2 .r0 (.imm 1024), .mov .r11 (.imm 256)]) s fun s' =>
      s'.gpr .r9 = 40318 ∧ s'.gpr .r2 = x0 - 1024 ∧ s'.gpr .r11 = BitVec.ofNat 32 256 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, and_self, and_true]

/-! ## Setup and the end -/

/-- The registers saved and the table stored. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega_arith))
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r1 (off := 512) (by decide) (fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega_arith)) fun s₁ h₁ => ?_
  have g1 : (s₁.gpr .r1) = ps s₀ := by rw [h₁.gpr]
  refine WP.mono (tableZ_ok zetaTable (by decide) (b := .r1) (by decide) (by rw [g1]; exact fit_le (by decide) fS)
    fun k hk => by rw [g1, h₁.wr]; exact wS (by omega_arith)) fun s₂ h₂ => ?_
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g1, ← add_ofNat_zero (State.addr (ps s₀))]
      exact region_sub_off (by decide)
  have hm : Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
    · rw [h₂.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g1, add_ofNat_add, ← add_ofNat_zero (State.addr (ps s₀))]
        exact region_disj_off (by omega_arith) (by omega_arith) (by omega_arith) hS
    · have := h₂.tab j hj; rwa [g1] at this
    · exact polyIs_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
        ⟨hp.red, rfl⟩
  exact ⟨hm, fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr]), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 4), .mov .r10 (.imm 512)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have elr := e .lr (by decide)
  run_block [constsN, e0, e1, elr, rd, wr, sp, constsN_val, hm, true_and]
  exact ⟨⟨rfl, rfl, by simp, by simp [elr], rfl, rfl, rfl, Frame.refl _ _⟩, rfl, rfl, lp_lift hm.poly⟩

/-- The registers restored, from a state that kept the working space. -/
theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 512) (hlr : s.gpr .lr = s₀.gpr .lr) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) (hf : Frame [polyRegion (F s₀)] m₁ s.mem) {f : Poly}
    (hP : PolyIs s.mem (F s₀) f) :
    WP isa (.block (restoreRegs .r1 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (F s₀) f := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 0 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h1, addr_add (by omega_arith), add_ofNat_zero]
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 0) (by decide) (by rw [h1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega_arith))
    fun i hi => by
      rw [e1, hrd, hwr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun s' h' => ⟨preserved_of_restore h' hlr, h'.sp.trans hsp, ?_⟩
  rw [h'.mem]
  exact hP

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  refine wp_loop_ne (LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => ?_) h₁
  refine WP.seq (WP.mono (canonPre_ok h.env.r0) fun s₂ ⟨r9, r2, r11, r1, r8, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  refine WP.mono (map_ok canon_ok hp (rd.trans h.env.rd) (wr.trans h.env.wr)
    (by rw [r2, BitVec.add_sub_cancel]) r11 ⟨r8.trans h.env.r8, r9⟩)
    fun s₃ ⟨hc, hf, r1', lr', rd', wr', sp'⟩ => ?_
  refine restore_ok hp hm ((r1'.trans r1).trans h.r1) ((lr'.trans lr).trans h.env.lr)
    ((rd'.trans rd).trans h.env.rd) ((wr'.trans wr).trans h.env.wr) ((sp'.trans sp).trans h.env.sp)
    (h.env.frame.trans (m ▸ hf)) ?_
  have hr := layersW_rel (P s₀) 7 (Nat.le_refl 7)
  rw [← layers_seven]
  refine polyIs_of_toNat fun j hj => ?_
  have hj' : j < 256 := by rw [n_eq] at hj; exact hj
  have hw := h.poly j hj
  rw [hc j hj', m, bcan_toNat (by rw [hw]; exact (hr j hj').1), hw, ← (hr j hj').2, Fin.val_ofNat]

/-! ## Verified -/

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

end VG.Proof.MlKem.Arm.Ntt
