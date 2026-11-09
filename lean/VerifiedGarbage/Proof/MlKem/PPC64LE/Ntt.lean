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
import VerifiedGarbage.Proof.MlKem.PPC64LE.NttVBfly
import VerifiedGarbage.Proof.Framework.PPC64LE.VWords
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on PPC64LE: `vg_mlkem_ntt`

The vector NTT (`Impl/MlKem/PPC64LE/Ntt.lean`): the table of `ζ` and `ζ'`
stored (`ztable_ok`) and the constant vectors built (`vconsts_ok`,
`setup_ok`); then the six layers with `len ≥ 4` as three nested loops of
`nttLayer`, `nttBlock` and `nttBlockN` (`Proof/MlKem/Ntt.lean`), with an
invariant each (`LInv`, `BInv`, `FInv`) saying which polynomial `f` holds,
four butterflies a step (`fstep`, from `VBfly.body_ok` and
`VBfly.group_poly`); then the last layer, `len = 2`, two blocks a step
(`PInv`, `pstep`). Layer `ℓ` has `len = 128 / 2^ℓ` and `2^ℓ` blocks. The
inverse NTT (`Proof/MlKem/PPC64LE/NttInv.lean`) shares the setup
(`vsetup_ok`) and what every loop keeps (`VEnv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Ntt

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem

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

theorem sub_low (p : Addr) {k L : Nat} (h : k ≤ L) : Region.Sub ⟨p, k⟩ ⟨p, L⟩ := fun a ha => by
  simp only [Region.Contains] at ha ⊢; omega_arith

/-! ## The vector NTT: the table of `ζ` and `ζ'` -/

/-- After the first `k` entries of the table of `ζ` and `ζ' = ⌊ζ · 2³² / q⌋` at `B`. -/
structure ZInv (B : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  vpr : s.vpr = s₀.vpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [⟨B, 1024⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (B + BitVec.ofNat 64 (8 * j)) 32 = BitVec.ofNat 32 (zeta j).val ∧
    s.mem.readW (B + BitVec.ofNat 64 (8 * j + 4)) 32 = BitVec.ofNat 32 (zetaPrime (zeta j).val)

theorem ztable_ok {b : Reg} (hb : b ≠ .r12) (hb0 : b ≠ .r0) {s₀ : State} {B : Addr} (hB : s₀.gpr b = B)
    (hwr : ∀ o, o + 4 ≤ 1024 → InRegions s₀.wr (B + BitVec.ofNat 64 o) 4) :
    WP isa (.block (ztable b)) s₀ (ZInv B s₀ 128) := by
  refine wp_range_flatMap (M := isa) (ZInv B s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hz : (zeta k).val < 3329 := val_lt _
  simp only [zetaTable_eq, zetas_getD hk]
  have gb : s.gpr b = B := (h.gpr b hb).trans hB
  refine WP.cons (exec_li (show (zeta k).val < 2 ^ 15 by omega)) ?_
  refine WP.cons (exec_store_w hb0 (show 8 * k < 2 ^ 15 by omega) ?_) ?_
  · rw [RegUpd.gpr_write_of_ne _ _ hb, gb, RegUpd.wr_write, h.wr]; exact hwr _ (by omega)
  refine WP.cons exec_lis (WP.cons exec_ori ?_)
  refine WP.cons (exec_store_w hb0 (show 8 * k + 4 < 2 ^ 15 by omega) ?_) (wp_nil ?_)
  · simp only [RegUpd.gpr_write, RegUpd.wr_write, hb, ite_false, gb, h.wr]; exact hwr _ (by omega)
  have v1 : (BitVec.ofNat 64 (zeta k).val).setWidth 32 = BitVec.ofNat 32 (zeta k).val :=
    setWidth32_ofNat (by rw [BitVec.toNat_ofNat]; omega) (by omega)
  refine ⟨fun r hr => ?_, h.vpr, h.rd, h.wr, h.sp, h.lr, ?_, fun j hj => ?_⟩
  · simp only [RegUpd.gpr_write, hr, ite_false]; exact h.gpr r hr
  · simp only [RegUpd.gpr_write, RegUpd.mem_write, hb, gb, ite_false, ite_true, v1, lis_ori]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [RegUpd.gpr_write, RegUpd.mem_write, hb, gb, ite_false, ite_true, v1, lis_ori]
    by_cases ej : j = k
    · subst ej
      refine ⟨?_, Mem.readW_writeW_self32 _ _ _⟩
      rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self32]
    · obtain ⟨t1, t2⟩ := h.tab j (by omega)
      refine ⟨?_, ?_⟩
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), t1]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), t2]

/-! ## The vector NTT: the constants -/

theorem hi_lo (v : BitVec 128) : v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · simp only [show i < 64 by omega, decide_true, Bool.true_and, Nat.zero_add]
  · simp only [show i - 64 < 64 by omega, decide_true, Bool.true_and]
    exact congrArg v.getLsbD (by omega)

/-- What `vconst` and `vconsts` change. -/
structure VC (vs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ vs → s'.vpr r = s.vpr r
  g : ∀ r, r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

theorem vconst_ok {s : State} (d : VReg) (v : BitVec 128) (hd : d ≠ .v15) (hdz : d ≠ .v14)
    (hz : s.vpr .v14 = 0) :
    WP isa (.block (vconst d v)) s fun s' => s'.vpr d = v ∧ VC [d, .v15] s s' := by
  rw [vconst, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const64_ok .r11 _ s) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (const64_ok .r12 _ _) fun s₂ e₂ => ?_
  subst e₂
  refine WP.mono (pair_ok d .v15 .v14 .r11 .r12 _ hd hdz (by decide) (by rw [vpr_write, vpr_write]; exact hz))
    fun s₃ ⟨h₃, hv⟩ => ⟨?_, fun r hr => ?_, fun r h11 h12 => ?_, hv.mem, hv.rd, hv.wr, hv.sp, hv.lr⟩
  · rw [h₃, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self, RegUpd.gpr_write_self, hi_lo]
  · rw [hv.v r hr, vpr_write, vpr_write]
  · rw [hv.gpr, RegUpd.gpr_write_of_ne _ _ h12, RegUpd.gpr_write_of_ne _ _ h11]

theorem exec_splat0 (s : State) : exec (.vop (.splatImm true .v14 0)) s = some (s.writeV .v14 0) := rfl

/-- The constant vectors the loops read. -/
structure Consts (s : State) : Prop where
  v0 : s.vpr .v0 = qVec
  v1 : s.vpr .v1 = ctlHi
  v2 : s.vpr .v2 = ctlLo
  v3 : s.vpr .v3 = ctlHi2
  v12 : s.vpr .v12 = ctlPw
  v13 : s.vpr .v13 = ctlPwp

theorem Consts.write {s : State} (h : Consts s) (r : Reg) (v : BitVec 64) : Consts (s.write r v) :=
  ⟨h.v0, h.v1, h.v2, h.v3, h.v12, h.v13⟩

theorem vconsts_ok {s : State} :
    WP isa (.block vconsts) s fun s' => Consts s' ∧ VC [.v0, .v1, .v2, .v3, .v12, .v13, .v14, .v15] s s' := by
  rw [vconsts]
  iterate 6 rw [WP.block_append_iff]
  refine WP.cons (exec_splat0 s) (wp_nil ?_)
  have z₀ : (s.writeV .v14 0).vpr .v14 = 0 := by rw [vpr_writeV]; rfl
  refine WP.mono (vconst_ok .v0 qVec (by decide) (by decide) z₀) fun s₁ ⟨e₁, c₁⟩ => ?_
  have z₁ := (c₁.v .v14 (by decide)).trans z₀
  refine WP.mono (vconst_ok .v1 ctlHi (by decide) (by decide) z₁) fun s₂ ⟨e₂, c₂⟩ => ?_
  have z₂ := (c₂.v .v14 (by decide)).trans z₁
  refine WP.mono (vconst_ok .v2 ctlLo (by decide) (by decide) z₂) fun s₃ ⟨e₃, c₃⟩ => ?_
  have z₃ := (c₃.v .v14 (by decide)).trans z₂
  refine WP.mono (vconst_ok .v3 ctlHi2 (by decide) (by decide) z₃) fun s₄ ⟨e₄, c₄⟩ => ?_
  have z₄ := (c₄.v .v14 (by decide)).trans z₃
  refine WP.mono (vconst_ok .v12 ctlPw (by decide) (by decide) z₄) fun s₅ ⟨e₅, c₅⟩ => ?_
  have z₅ := (c₅.v .v14 (by decide)).trans z₄
  refine WP.mono (vconst_ok .v13 ctlPwp (by decide) (by decide) z₅) fun s₆ ⟨e₆, c₆⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, e₆⟩, ⟨fun r hr => ?_, fun r h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [c₆.v _ (by decide), c₅.v _ (by decide), c₄.v _ (by decide), c₃.v _ (by decide), c₂.v _ (by decide), e₁]
  · rw [c₆.v _ (by decide), c₅.v _ (by decide), c₄.v _ (by decide), c₃.v _ (by decide), e₂]
  · rw [c₆.v _ (by decide), c₅.v _ (by decide), c₄.v _ (by decide), e₃]
  · rw [c₆.v _ (by decide), c₅.v _ (by decide), e₄]
  · rw [c₆.v _ (by decide), e₅]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n0, n1, n2, n3, n12, n13, n14, n15⟩ := hr
    rw [c₆.v _ (by simp [n13, n15]), c₅.v _ (by simp [n12, n15]), c₄.v _ (by simp [n3, n15]),
      c₃.v _ (by simp [n2, n15]), c₂.v _ (by simp [n1, n15]), c₁.v _ (by simp [n0, n15]), vpr_writeV,
      ite_eq_right n14]
  · rw [c₆.g r h11 h12, c₅.g r h11 h12, c₄.g r h11 h12, c₃.g r h11 h12, c₂.g r h11 h12, c₁.g r h11 h12]; rfl
  · rw [c₆.mem, c₅.mem, c₄.mem, c₃.mem, c₂.mem, c₁.mem]; rfl
  · rw [c₆.rd, c₅.rd, c₄.rd, c₃.rd, c₂.rd, c₁.rd]; rfl
  · rw [c₆.wr, c₅.wr, c₄.wr, c₃.wr, c₂.wr, c₁.wr]; rfl
  · rw [c₆.sp, c₅.sp, c₄.sp, c₃.sp, c₂.sp, c₁.sp]; rfl
  · rw [c₆.lr, c₅.lr, c₄.lr, c₃.lr, c₂.lr, c₁.lr]; rfl

/-! ## The vector NTT: what every loop keeps -/

open VG.Proof.MlKem.PPC64LE.VBfly

/-- What the setup leaves in memory `m₁`: the table at `S` and the polynomial. -/
structure VSetup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (8 * j)) 32 = BitVec.ofNat 32 (zeta j).val ∧
    m₁.readW (S s₀ + BitVec.ofNat 64 (8 * j + 4)) 32 = BitVec.ofNat 32 (zetaPrime (zeta j).val)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps. -/
structure VEnv (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  r3 : s.gpr .r3 = F s₀
  r4 : s.gpr .r4 = S s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  c : Consts s
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (F s₀)] m₁ s.mem

theorem pres_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧
    r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem VEnv.rowR {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} (h : VEnv s₀ m₁ s) {j : Nat}
    (hj : j + 4 ≤ 256) : InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) j) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨polyRegion (F s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem VEnv.rowW {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} (h : VEnv s₀ m₁ s) {j : Nat}
    (hj : j + 4 ≤ 256) : InRegions s.wr (coeffAddr (F s₀) j) 16 := by
  rw [h.wr, hp.wr]; exact ⟨polyRegion (F s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem VEnv.rowZ {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} (h : VEnv s₀ m₁ s) {k : Nat}
    (hk : k + 1 < 128) : InRegions (s.rd ++ s.wr) (S s₀ + BitVec.ofNat 64 (8 * k)) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨polyRegion (S s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem toNat_zp (z : Zq) : (BitVec.ofNat 32 (zetaPrime z.val)).toNat = z.val * 2 ^ 32 / 3329 := by
  rw [BitVec.toNat_ofNat, zetaPrime, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := val_lt z; omega))]

/-- The words of the entries `k` and `k + 1` of the table, loaded by `lxvd2x`. -/
theorem VEnv.zrow {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : VSetup s₀ m₁) {s : State} (h : VEnv s₀ m₁ s)
    {k : Nat} (hk : k + 1 < 128) :
    vword (swapDwords (s.mem.read (S s₀ + BitVec.ofNat 64 (8 * k)) 16)) 1 = BitVec.ofNat 32 (zeta k).val ∧
    vword (swapDwords (s.mem.read (S s₀ + BitVec.ofNat 64 (8 * k)) 16)) 0 =
      BitVec.ofNat 32 (zetaPrime (zeta k).val) ∧
    vword (swapDwords (s.mem.read (S s₀ + BitVec.ofNat 64 (8 * k)) 16)) 3 = BitVec.ofNat 32 (zeta (k + 1)).val ∧
    vword (swapDwords (s.mem.read (S s₀ + BitVec.ofNat 64 (8 * k)) 16)) 2 =
      BitVec.ofNat 32 (zetaPrime (zeta (k + 1)).val) := by
  have fS := hp.fitS
  rw [h.frame.read (r := polyRegion (S s₀)) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)]
  rw [vword_load _ _ (by decide), vword_load _ _ (by decide), vword_load _ _ (by decide), vword_load _ _ (by decide)]
  simp only [Nat.reduceXor, Nat.reduceMul, ptr_add]
  obtain ⟨a0, a1⟩ := hm.tab k (by omega)
  obtain ⟨b0, b1⟩ := hm.tab (k + 1) hk
  rw [Nat.add_zero, a0, a1, show 8 * k + 8 = 8 * (k + 1) by omega, b0,
    show 8 * k + 12 = 8 * (k + 1) + 4 by omega, b1]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem sub_nz {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  have := ptr_ne 0 ha hb
  rwa [show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_add, BitVec.zero_add] at this

/-! ## The vector NTT: groups of four butterflies -/

/-- After `g` groups of four butterflies of the block from `st` with the
zeta `zeta k` of the layer with `len`, from `Q`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len k st : Nat) (g : Nat) (s : State) : Prop where
  env : VEnv s₀ m₁ s
  r5 : s.gpr .r5 = BitVec.ofNat 64 (4 * (st + 4 * g))
  r6 : s.gpr .r6 = BitVec.ofNat 64 (4 * (st + 4 * g + len))
  r7 : s.gpr .r7 = BitVec.ofNat 64 (8 * (k + 1))
  r9 : s.gpr .r9 = BitVec.ofNat 64 (4 * len)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (len / 4 - g)
  v4 : ∀ i < 4, vword (s.vpr .v4) i = BitVec.ofNat 32 (zeta k).val
  v5 : ∀ i < 4, vword (s.vpr .v5) i = BitVec.ofNat 32 (zetaPrime (zeta k).val)
  poly : PolyIs s.mem (F s₀) (nttBlockN Q len k st (4 * g))

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : Poly} {len k st g : Nat}
    (hs : st + 2 * len ≤ 256) (hg : g < len / 4) {s : State} (h : FInv s₀ m₁ Q len k st g s) :
    WP isa (.block vbflyBody) s fun s' =>
      FInv s₀ m₁ Q len k st (g + 1) s' ∧ (s'.gpr .r10 != 0) = decide (g + 1 ≠ len / 4) := by
  have ht : 4 * g + 4 ≤ len := by omega
  have eA : s.gpr .r3 + s.gpr .r5 = coeffAddr (F s₀) (st + 4 * g) := by rw [h.env.r3, h.r5]
  have eB : s.gpr .r3 + s.gpr .r6 = coeffAddr (F s₀) (st + 4 * g + len) := by rw [h.env.r3, h.r6]
  refine WP.mono (body_ok (eA ▸ h.env.rowR hp (by omega)) (eB ▸ h.env.rowR hp (by omega))
    (eA ▸ h.env.rowW hp (by omega)) (eB ▸ h.env.rowW hp (by omega))
    (fun i hi => by rw [eA, row_lane h.poly (by omega) hi, toNat_val32]; exact val_lt _)
    (fun i hi => by rw [eB, row_lane h.poly (by omega) hi, toNat_val32]; exact val_lt _)
    (fun i hi => by rw [h.v4 i hi, toNat_val32]; exact val_lt _)
    (fun i hi => by rw [h.v5 i hi, h.v4 i hi, toNat_zp, toNat_val32]) h.env.c.v0 h.env.c.v1)
    fun s' ⟨A, B, hA, hB, m, r5, r6, r10, kp⟩ => ⟨⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      kp.lr.trans h.env.lr, kp.rd.trans h.env.rd, kp.wr.trans h.env.wr, kp.sp.trans h.env.sp, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [kp.g _ (by decide) (by decide) (by decide), h.env.r3]
  · rw [kp.g _ (by decide) (by decide) (by decide), h.env.r4]
  · obtain ⟨-, n5, n6, -, -, n10, -⟩ := pres_ne r hr
    rw [kp.g r n5 n6 n10, h.env.kept r hr]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v0]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v1]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v2]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v3]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v12]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v13]
  · rw [m, eA, eB]
    exact (h.env.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).write
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [r5, h.r5, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat]; exact congrArg _ (by omega)
  · rw [r6, h.r6, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat]; exact congrArg _ (by omega)
  · rw [kp.g _ (by decide) (by decide) (by decide), h.r7]
  · rw [kp.g _ (by decide) (by decide) (by decide), h.r9]
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.v4 i hi]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.v5 i hi]
  · rw [m, eA, eB, show 4 * (g + 1) = 4 * g + 4 by omega]
    exact group_poly ht hs h.poly (fun p hp => by rw [hA p hp, eA, eB, h.v4 p hp])
      (fun p hp => by rw [hB p hp, eA, eB, h.v4 p hp])
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
    exact count_nz hg (by omega)

/-! ## The vector NTT: blocks -/

theorem exec_splat1 (d n : VReg) (s : State) :
    exec (.vop (.splat true d n 1)) s = some (s.writeV d (ofVWords fun _ => vword (s.vpr n) 1)) := rfl

theorem exec_splat0' (d n : VReg) (s : State) :
    exec (.vop (.splat true d n 0)) s = some (s.writeV d (ofVWords fun _ => vword (s.vpr n) 0)) := rfl

theorem lsr4 {len : Nat} (h : 4 * len < 2 ^ 64) : BitVec.ofNat 64 (4 * len) >>> 4 = BitVec.ofNat 64 (len / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  omega

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : VEnv s₀ m₁ s
  r5 : s.gpr .r5 = BitVec.ofNat 64 (4 * (2 * len * c))
  r7 : s.gpr .r7 = BitVec.ofNat 64 (8 * (nb + c))
  r9 : s.gpr .r9 = BitVec.ofNat 64 (4 * len)
  poly : PolyIs s.mem (F s₀) (nttLayerN Q len c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : VSetup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (h4 : 4 ≤ len) (hl4 : len % 4 = 0) (hnb : len * nb = 128) (hc : c < nb) {s : State}
    (h : BInv s₀ m₁ Q len nb c s) :
    WP isa vblockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .r0 != 0) = decide (c + 1 ≠ nb) := by
  have hl : 0 < len := by omega
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hk : nb + c + 1 < 128 := by
    have : 4 * nb ≤ 128 := hnb ▸ Nat.mul_le_mul_right nb h4
    omega
  have hb : 2 * len * (c + 1) ≤ 256 := by
    have := Nat.mul_le_mul_left len (show c + 1 ≤ nb from hc)
    rw [Nat.mul_assoc]; omega
  have ez : s.gpr .r4 + s.gpr .r7 = S s₀ + BitVec.ofNat 64 (8 * (nb + c)) := by rw [h.env.r4, h.r7]
  obtain ⟨z1, z0, -, -⟩ := h.env.zrow hp hm hk
  rw [vblockCode, WP.seq_iff]
  refine WP.cons (exec_lxvd2x .v11 .r4 .r7 s (by decide) (ez ▸ h.env.rowZ hp hk)) ?_
  refine WP.cons (exec_splat1 _ _ _) (WP.cons (exec_splat0' _ _ _) ?_)
  refine WP.cons (exec_addi (by decide) (by decide)) (WP.cons exec_add ?_)
  refine WP.cons (exec_lsr_d (by decide)) (wp_nil ?_)
  rw [WP.seq_iff]
  refine wp_loop_nz (FInv s₀ m₁ (nttLayerN Q len c) len (nb + c) (2 * len * c)) (N := len / 4) (by omega)
    (fun g hg t ht => fstep hp (by omega_arith) hg ht) (fun s₂ h₂ => ?_) ?_
  · refine WP.cons (exec_addi (by decide) (by decide)) (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_))
    have e5 : BitVec.ofNat 64 (4 * (2 * len * c + 4 * (len / 4) + len)) + BitVec.ofNat 64 0 =
        BitVec.ofNat 64 (4 * (2 * len * (c + 1))) := by
      rw [add_ofNat]; exact congrArg _ (by rw [Nat.mul_succ]; omega_arith)
    refine ⟨⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, h₂.env.lr, h₂.env.rd, h₂.env.wr, h₂.env.sp,
      h₂.env.frame⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.env.r3]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.env.r4]
    · obtain ⟨n0, n5, -⟩ := pres_ne r hr
      simp only [RegUpd.gpr_write, n0, n5, ite_false, h₂.env.kept r hr]
    · exact h₂.env.c.v0
    · exact h₂.env.c.v1
    · exact h₂.env.c.v2
    · exact h₂.env.c.v3
    · exact h₂.env.c.v12
    · exact h₂.env.c.v13
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h₂.r6, e5]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.r7]; exact congrArg _ (by omega)
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.r9]
    · have hp2 := h₂.poly
      rw [show 4 * (len / 4) = len by omega] at hp2
      rw [nttLayerN_succ, hdiv, nttBlock]; exact hp2
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h₂.r6, e5]
      rw [sub_nz (by omega) (by decide)]
      have e8 : 4 * (2 * len * (c + 1)) = 8 * (len * (c + 1)) := by rw [Nat.mul_assoc 2]; omega
      have key : 4 * (2 * len * (c + 1)) = 1024 ↔ c + 1 = nb := by
        rw [e8]
        constructor
        · intro e; exact Nat.eq_of_mul_eq_mul_left hl (by omega)
        · intro e; subst e; omega
      exact decide_eq_decide.mpr (not_congr key)
  · refine ⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, h.env.lr, h.env.rd, h.env.wr, h.env.sp,
      h.env.frame⟩, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.env.r3]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.env.r4]
    · obtain ⟨-, -, n6, n7, -, n10, -⟩ := pres_ne r hr
      simp only [RegUpd.gpr_write, gpr_writeV, n6, n7, n10, ite_false, h.env.kept r hr]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v0]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v1]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v2]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v3]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v12]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v13]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.r5, Nat.mul_zero, Nat.add_zero]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, ite_true, h.r5, h.r9, add_ofNat]
      exact congrArg _ (by omega)
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, ite_true, h.r7]
      rw [add_ofNat]; exact congrArg _ (by omega)
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.r9]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, ite_true, h.r9, Nat.sub_zero]
      exact lsr4 (by omega)
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, ite_true, vword_ofVWords _ hi, ez, z1]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, ite_true, vword_ofVWords _ hi, ez, z0]
    · rw [Nat.mul_zero, nttBlockN_zero]; exact h.poly

/-! ## The vector NTT: layers -/

/-- What the layers' loop counters are: layer `ℓ < 6` has `len = 128 >>> ℓ`
and `2^ℓ` blocks. -/
theorem layer_facts : ∀ ℓ < 6, 4 ≤ 128 >>> ℓ ∧ (128 >>> ℓ) % 4 = 0 ∧ (128 >>> ℓ) * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 128 / (128 >>> ℓ) = 2 ^ ℓ ∧
    BitVec.ofNat 64 (4 * (128 >>> ℓ)) >>> 1 = BitVec.ofNat 64 (4 * (128 >>> (ℓ + 1))) ∧
    (BitVec.ofNat 64 (4 * (128 >>> (ℓ + 1))) - BitVec.ofNat 64 8 != 0) = decide (ℓ + 1 ≠ 6) := by
  decide

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : VEnv s₀ m₁ s
  r7 : s.gpr .r7 = BitVec.ofNat 64 (8 * 2 ^ ℓ)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (4 * (128 >>> ℓ))
  poly : PolyIs s.mem (F s₀) (nttL ℓ (P s₀))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : VSetup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 6) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa vlayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .r0 != 0) = decide (ℓ + 1 ≠ 6) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := layer_facts ℓ hℓ
  rw [vlayerCode, WP.seq_iff]
  refine WP.cons (exec_li (by decide)) (wp_nil ?_)
  rw [WP.seq_iff]
  refine wp_loop_nz (BInv s₀ m₁ (nttL ℓ (P s₀)) (128 >>> ℓ) (2 ^ ℓ)) f4
    (fun c hc t ht => bstep hp hm f1 f2 f3 hc ht) (fun s₂ h₂ => ?_) ?_
  · refine WP.cons (exec_lsr_d (by decide)) (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_))
    refine ⟨⟨⟨?_, ?_, fun r hr => ?_, (h₂.env.c.write _ _).write _ _, h₂.env.lr, h₂.env.rd, h₂.env.wr, h₂.env.sp,
      h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.env.r3]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.env.r4]
    · obtain ⟨n0, -, -, -, n9, -⟩ := pres_ne r hr
      simp only [RegUpd.gpr_write, n0, n9, ite_false, h₂.env.kept r hr]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.r7, f5]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h₂.r9, f7]
    · rw [nttL_succ _ (by omega), nttLayer, f6]; exact h₂.poly
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h₂.r9, f7, f8]
  · refine ⟨⟨?_, ?_, fun r hr => ?_, h.env.c.write _ _, h.env.lr, h.env.rd, h.env.wr, h.env.sp, h.env.frame⟩,
      ?_, ?_, ?_, ?_⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h.env.r3]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h.env.r4]
    · obtain ⟨-, n5, -⟩ := pres_ne r hr
      simp only [RegUpd.gpr_write, n5, ite_false, h.env.kept r hr]
    · simp only [RegUpd.gpr_write, ite_true, Nat.mul_zero]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h.r7, Nat.add_zero]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h.r9]
    · rw [nttLayerN_zero]; exact h.poly

/-! ## The vector NTT: the last layer, two blocks at a time -/

/-- After `i` steps of the last layer (`len = 2`), from `nttL 6`. -/
structure PInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  env : VEnv s₀ m₁ s
  r5 : s.gpr .r5 = BitVec.ofNat 64 (32 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 64 (8 * (64 + 2 * i))
  r10 : s.gpr .r10 = BitVec.ofNat 64 (32 - i)
  poly : PolyIs s.mem (F s₀) (nttLayerN (nttL 6 (P s₀)) 2 (2 * i))

theorem pstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : VSetup s₀ m₁) {i : Nat} (hi : i < 32) {s : State}
    (h : PInv s₀ m₁ i s) :
    WP isa (.block vbfly2Body) s fun s' => PInv s₀ m₁ (i + 1) s' ∧ (s'.gpr .r10 != 0) = decide (i + 1 ≠ 32) := by
  have ez : s.gpr .r4 + s.gpr .r7 = S s₀ + BitVec.ofNat 64 (8 * (64 + 2 * i)) := by rw [h.env.r4, h.r7]
  have eA : s.gpr .r3 + s.gpr .r5 = coeffAddr (F s₀) (4 * (2 * i)) := by
    rw [h.env.r3, h.r5]; exact congrArg (F s₀ + ·) (congrArg _ (by omega))
  have eB : s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16) = coeffAddr (F s₀) (4 * (2 * i) + 4) := by
    rw [h.env.r3, h.r5, add_ofNat]; exact congrArg (F s₀ + ·) (congrArg _ (by omega))
  obtain ⟨z1, z0, z3, z2⟩ := h.env.zrow hp hm (k := 64 + 2 * i) (by omega)
  rw [← ez] at z1 z0 z3 z2
  refine WP.mono (body2_ok (ez ▸ h.env.rowZ hp (by omega)) (eA ▸ h.env.rowR hp (by omega))
    (eB ▸ h.env.rowR hp (by omega)) (eA ▸ h.env.rowW hp (by omega)) (eB ▸ h.env.rowW hp (by omega)) rfl rfl rfl
    (fun j hj => by rw [eA, row_lane h.poly (by omega) hj, toNat_val32]; exact val_lt _)
    (fun j hj => by rw [eB, row_lane h.poly (by omega) hj, toNat_val32]; exact val_lt _)
    (by rw [z1, toNat_val32]; exact val_lt _) (by rw [z3, toNat_val32]; exact val_lt _)
    (by rw [z0, z1, toNat_zp, toNat_val32]) (by rw [z2, z3, toNat_zp, toNat_val32])
    h.env.c.v0 h.env.c.v1 h.env.c.v2 h.env.c.v3 h.env.c.v12 h.env.c.v13)
    fun s' ⟨A, B, hA, hB, m, r5, r7, r10, kp⟩ => ⟨⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      kp.lr.trans h.env.lr, kp.rd.trans h.env.rd, kp.wr.trans h.env.wr, kp.sp.trans h.env.sp, ?_⟩,
      ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kp.g _ (by decide) (by decide) (by decide) (by decide), h.env.r3]
  · rw [kp.g _ (by decide) (by decide) (by decide) (by decide), h.env.r4]
  · obtain ⟨-, n5, n6, n7, -, n10, -⟩ := pres_ne r hr
    rw [kp.g r n5 n6 n7 n10, h.env.kept r hr]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v0]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v1]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v2]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v3]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v12]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v13]
  · rw [m, eA, eB]
    exact (h.env.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).write
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [r5, h.r5, add_ofNat]; exact congrArg _ (by omega)
  · rw [r7, h.r7, add_ofNat]; exact congrArg _ (by omega)
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
  · rw [m, eA, eB, show 2 * (i + 1) = 2 * i + 2 by omega]
    exact pair_poly (by omega) h.poly z1 z3 (fun p hp => by rw [hA p hp, eA]) (fun p hp => by rw [hB p hp, eB])
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by omega)

/-! ## The vector NTT: setup and the end -/

/-- What every loop keeps survives a write of a register no loop keeps. -/
theorem VEnv.write {s₀ : State} {m₁ : Mem} {s : State} (h : VEnv s₀ m₁ s) {r : Reg} (hr : r ∉ preserved)
    (h3 : r ≠ .r3) (h4 : r ≠ .r4) (v : BitVec 64) : VEnv s₀ m₁ (s.write r v) :=
  ⟨by rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm h3)]; exact h.r3,
    by rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm h4)]; exact h.r4,
    fun r' hr' => by
      rw [RegUpd.gpr_write_of_ne _ _ (fun e : r' = r => hr (e ▸ hr'))]; exact h.kept r' hr',
    h.c.write r v, h.lr, h.rd, h.wr, h.sp, h.frame⟩

/-- The table stored and the constant vectors built. -/
theorem vsetup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (ztable .r4 ++ vconsts)) s₀ fun s => VSetup s₀ s.mem ∧ VEnv s₀ s.mem s := by
  have fS := hp.fitS
  rw [WP.block_append_iff]
  refine WP.mono (ztable_ok (b := .r4) (by decide) (by decide) rfl fun o ho => by
    rw [hp.wr]; exact ⟨polyRegion (S s₀), by simp, Offset.contains_base _ ho (by omega)⟩) fun s₁ hz => ?_
  refine WP.mono vconsts_ok fun s₂ ⟨hc, vc⟩ => ?_
  have g : ∀ r, r ≠ .r11 → r ≠ .r12 → s₂.gpr r = s₀.gpr r :=
    fun r h11 h12 => by rw [vc.g r h11 h12, hz.gpr r h12]
  have hm : VSetup s₀ s₂.mem := by
    rw [vc.mem]
    refine ⟨hz.tab, polyIs_frame hz.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩
  refine ⟨hm, ⟨g _ (by decide) (by decide), g _ (by decide) (by decide), fun r hr => ?_, hc,
    vc.lr.trans hz.lr, vc.rd.trans hz.rd, vc.wr.trans hz.wr, vc.sp.trans hz.sp, Frame.refl _ _⟩⟩
  obtain ⟨-, -, -, -, -, -, n11, n12⟩ := pres_ne r hr
  exact g r n11 n12

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (ztable .r4 ++ vconsts ++ ([.li .r7 8, .li .r9 512] : List Instr))) s₀
      fun s => VSetup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [WP.block_append_iff]
  refine WP.mono (vsetup_ok hp) fun s₂ ⟨hm, he⟩ => ?_
  refine WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide)) (wp_nil ?_))
  exact ⟨hm, ⟨(he.write (by decide) (by decide) (by decide) _).write (by decide) (by decide) (by decide) _,
    rfl, rfl, hm.poly⟩⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  rw [Impl.MlKem.PPC64LE.ntt, WP.seq_iff]
  refine WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_
  rw [WP.seq_iff]
  refine wp_loop_nz (LInv s₀ s₁.mem) (N := 6) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s₂ h₂ => ?_) h₁
  rw [WP.seq_iff]
  refine WP.cons (exec_li (by decide)) (WP.cons (exec_li (by decide)) (wp_nil ?_))
  refine wp_loop_nz (PInv s₀ s₁.mem) (N := 32) (by decide) (fun i hi s h => pstep hp hm hi h)
    (fun s h => ⟨h.env.kept, h.env.sp, h.env.lr, ?_⟩) ?_
  · refine ⟨⟨?_, ?_, fun r hr => ?_, (h₂.env.c.write _ _).write _ _, h₂.env.lr, h₂.env.rd, h₂.env.wr,
      h₂.env.sp, h₂.env.frame⟩, ?_, ?_, ?_, ?_⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.env.r3]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.env.r4]
    · obtain ⟨-, n5, -, -, -, n10, -⟩ := pres_ne r hr
      simp only [RegUpd.gpr_write, n5, n10, ite_false, h₂.env.kept r hr]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.r7]
    · simp only [RegUpd.gpr_write, ite_true]
    · rw [Nat.mul_zero, nttLayerN_zero]; exact h₂.poly
  · rw [ntt_eq_nttL, nttL_succ _ (by decide), nttLayer]; exact h.poly

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

end VG.Proof.MlKem.PPC64LE.Ntt
