import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Layout
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Linear

/-!
# A DES round on AArch64

The round's three parts: the S-boxes' index, the spread round key at `x10`
XORed with `R` (`sIn_ok`), in `v0` and its quarters in `v1`–`v3`; the
S-boxes' outputs by `tbl` (`sOut_ok`, from `select_full_run`); and `L`
XORed with groups of them (`pOut_ok`), checked by evaluation over the lane
domain (`Straight.check`). `round_ok` composes them: the spread
`L ⊕ f(R, K)`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.AArch64.Tbl VG.Bitslice
  VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Impl.Tbl.AArch64 VG.Proof.CmacTripleDes

/-- What the rounds keep in the vector registers: the tables, and 64, 128
and 192 in every byte of `v4`, `v5` and `v6`. -/
structure Consts (s : State) : Prop where
  tab : ∀ k < 256, tbyte s.v k = sTable k
  c64 : s.v .v4 = bc 64
  c128 : s.v .v5 = bc 128
  c192 : s.v .v6 = bc 192

theorem Consts.congr {s s' : State} (h : Consts s)
    (hv : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) : Consts s' where
  tab k hk := by rw [tbyte_congr (fun r a b c d _ _ => hv r a b c d) k hk]; exact h.tab k hk
  c64 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c64
  c128 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c128
  c192 := by rw [hv _ (by decide) (by decide) (by decide) (by decide)]; exact h.c192

/-! ## The index -/

/-- The step of the key pointer. -/
def kstep (down : Bool) : Instr := if down then .subImm .x .x10 .x10 8 else .addImm .x .x10 .x10 8

theorem exec_kstep (s : State) (down : Bool) :
    exec (kstep down) s =
      some (s.write .x .x10 (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8)) := by
  cases down
  · simp only [kstep, Bool.false_eq_true, ite_false, exec_addImm_x (by decide : 8 < 4096),
      State.read, BitVec.setWidth_eq]; rfl
  · simp only [kstep, ite_true, exec_subImm_x (by decide : 8 < 4096), State.read,
      BitVec.setWidth_eq]; rfl

theorem sIn_eq (b : Reg) (down : Bool) : sIn b down =
    [.ldr .x .x5 .x10 0, kstep down, .logic .eor .x .x5 .x5 b, .vop (.ins .d2 .v0 0 .x5),
     .vop (.logic .eor .v1 .v0 .v4), .vop (.logic .eor .v2 .v0 .v5),
     .vop (.logic .eor .v3 .v0 .v6)] := rfl

theorem vbyte_setLane0 (x : BitVec 128) (y : BitVec 64) {e : Nat} (he : e < 8) :
    vbyte (setLane x 64 0 y) e = y.extractLsb' (8 * e) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, setLane, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Nat.mul_zero, Nat.sub_zero,
    show 8 * e + i < 128 by omega, show 8 * e + i < 64 by omega, show ¬ 8 * e + i < 0 by omega]
  simp

theorem sIn_ok (s : State) {b : Reg} (hb5 : b ≠ .x5) (hb10 : b ≠ .x10) (down : Bool)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x10) 8) (hc : Consts s) :
    ∃ s', runBlock isa (sIn b down) s = some s' ∧
      (∀ e < 8, vbyte (s'.v .v0) e =
        (s.mem.readW (s.gpr .x10) 64 ^^^ s.gpr b).extractLsb' (8 * e) 8) ∧
      (∀ e < 16, vbyte (s'.v .v1) e = vbyte (s'.v .v0) e ^^^ 64) ∧
      (∀ e < 16, vbyte (s'.v .v2) e = vbyte (s'.v .v0) e ^^^ 128) ∧
      (∀ e < 16, vbyte (s'.v .v3) e = vbyte (s'.v .v0) e ^^^ 192) ∧
      s'.gpr .x10 = (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8) ∧
      (∀ r, r ≠ .x5 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hk' : InRegions (s.rd ++ s.wr) (s.gpr .x10 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact hk
  let K := s.mem.readW (s.gpr .x10 + BitVec.ofNat 64 0) 64
  let s₁ := s.write .x .x5 K
  let s₂ := s₁.write .x .x10 (if down then s₁.gpr .x10 - 8 else s₁.gpr .x10 + 8)
  let s₃ := s₂.write .x .x5 (s₂.read .x .x5 ^^^ s₂.read .x b)
  let s₄ := s₃.setV .v0 (setLane (s₃.v .v0) 64 0 (s₃.gpr .x5))
  let s₅ := s₄.setV .v1 (s₄.v .v0 ^^^ s₄.v .v4)
  let s₆ := s₅.setV .v2 (s₅.v .v0 ^^^ s₅.v .v5)
  let s₇ := s₆.setV .v3 (s₆.v .v0 ^^^ s₆.v .v6)
  have x5₃ : s₃.gpr .x5 = K ^^^ s.gpr b := by
    simp only [s₃, s₂, s₁, State.read, gpr_write_self, BitVec.setWidth_eq,
      gpr_write_of_ne _ _ _ (by decide : Reg.x5 ≠ .x10), gpr_write_of_ne _ _ _ hb10,
      gpr_write_of_ne _ _ _ hb5]
  have v0₇ : s₇.v .v0 = setLane (s.v .v0) 64 0 (K ^^^ s.gpr b) := by
    simp only [s₇, s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
      v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
    rw [show s₄.v .v0 = setLane (s₃.v .v0) 64 0 (s₃.gpr .x5) from v_setV_self _ _ _, x5₃]; rfl
  have vs : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s₇.v w = s.v w := by
    intro w h0 h1 h2 h3
    simp only [s₇, s₆, s₅, s₄, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h1,
      v_setV_of_ne _ _ h0]; rfl
  have c₄ : ∀ w, w = .v4 ∨ w = .v5 ∨ w = .v6 → s₆.v w = s.v w := by
    intro w hw
    rcases hw with rfl | rfl | rfl <;>
      simp only [s₆, s₅, s₄, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v1),
        v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v0),
        v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v0), v_setV_of_ne _ _ (by decide : VReg.v6 ≠ .v0)] <;> rfl
  have z₆ : s₆.v .v0 = s₇.v .v0 := (v_setV_of_ne _ _ (by decide)).symm
  have z₅ : s₅.v .v0 = s₇.v .v0 := by
    rw [← z₆]; exact (v_setV_of_ne _ _ (by decide)).symm
  have z₄ : s₄.v .v0 = s₇.v .v0 := by
    rw [← z₅]; exact (v_setV_of_ne _ _ (by decide)).symm
  refine ⟨s₇, ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_,
    fun r h5 h10 => ?_, vs, rfl, rfl, rfl, rfl⟩
  · rw [sIn_eq, runBlock_cons, exec_ldr_x (by decide) hk', runStep_some, runBlock_cons,
      exec_kstep, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons,
      exec_insd _ _ _ (by decide), runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_nil]
  · rw [v0₇, vbyte_setLane0 _ _ he]
    simp only [K, BitVec.add_zero]
  · have : s₇.v .v1 = s₄.v .v0 ^^^ s₄.v .v4 := by
      simp only [s₇, s₆, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2)]; exact v_setV_self _ _ _
    rw [this, vbyte_xor, z₄, show s₄.v .v4 = s.v .v4 from by
      rw [← c₄ .v4 (by simp)]; simp only [s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v2),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1)], hc.c64, vbyte_bc _ he]
  · have : s₇.v .v2 = s₅.v .v0 ^^^ s₅.v .v5 := by
      simp only [s₇, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3)]; exact v_setV_self _ _ _
    rw [this, vbyte_xor, z₅, show s₅.v .v5 = s.v .v5 from by
      rw [← c₄ .v5 (by simp)]; simp only [s₆, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v2)],
      hc.c128, vbyte_bc _ he]
  · have : s₇.v .v3 = s₆.v .v0 ^^^ s₆.v .v6 := v_setV_self _ _ _
    rw [this, vbyte_xor, z₆, c₄ .v6 (by simp), hc.c192, vbyte_bc _ he]
  · simp only [s₇, s₆, s₅, s₄, gpr_setV, s₃, gpr_write_of_ne _ _ _ (by decide : Reg.x10 ≠ .x5),
      s₂, gpr_write_self, BitVec.setWidth_eq, s₁]
  · simp only [s₇, s₆, s₅, s₄, gpr_setV, s₃, s₂, s₁, gpr_write_of_ne _ _ _ h5,
      gpr_write_of_ne _ _ _ h10]

/-! ## The S-boxes -/

theorem exec_umovx0 (s : State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d ((s.v n).extractLsb' 0 64)) := by
  simp [exec, Size.bits]

theorem extract_vbyte (v : BitVec 128) {l : Nat} (hl : l < 8) :
    ((v.extractLsb' 0 64).extractLsb' (8 * l) 8) = vbyte v l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [vbyte, hi, show 8 * l + i < 64 by omega]

/-- The S-boxes' outputs `y`, in `x5`: byte `l` is the table's byte at the
index's byte `l`. -/
theorem sOut_ok {s : State} (I : Nat → BitVec 8)
    (h0 : ∀ e < 16, vbyte (s.v .v0) e = I e)
    (h1 : ∀ e < 16, vbyte (s.v .v1) e = I e ^^^ 64)
    (h2 : ∀ e < 16, vbyte (s.v .v2) e = I e ^^^ 128)
    (h3 : ∀ e < 16, vbyte (s.v .v3) e = I e ^^^ 192) :
    ∃ s', runBlock isa sOut s = some s' ∧
      (∀ l < 8, (s'.gpr .x5).extractLsb' (8 * l) 8 = tbyte s.v (I l).toNat) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → s'.v w = s.v w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨d, rund, d0, dv⟩ := select_full_run I h0 h1 h2 h3
  let t := d.write .x .x5 ((d.v .v0).extractLsb' 0 64)
  refine ⟨t, ?_, fun l hl => ?_, fun r hr => ?_, fun w a b c e => ?_, ?_, ?_, ?_, ?_⟩
  · rw [sOut, runBlock_cat_some rund (by rw [runBlock_cons, exec_umovx0, runStep_some, runBlock_nil])]
  · simp only [t, gpr_write_self, BitVec.setWidth_eq]
    rw [extract_vbyte _ hl, d0 l (by omega)]
  · simp only [t, gpr_write_of_ne _ _ _ hr, dv.gpr]
  · simp only [t, v_write]; exact dv.2 w (by simp [a, b, c, e])
  · simp only [t, mem_write, dv.mem]
  · simp only [t, rd_write, dv.rd]
  · simp only [t, wr_write, dv.wr]
  · simp only [t, sp_write]; rw [dv.1]

/-! ## `P` -/

/-- No memory. -/
def oCfg : Cfg := { base := .x15, slots := 0, ext := .x14, exts := 0 }

theorem oCfg_ok (s : State) : Ok oCfg s :=
  ⟨fun k hk => absurd hk (by simp [oCfg]), fun k hk => absurd hk (by simp [oCfg]), by decide,
    fun k hk => absurd hk (by simp [oCfg])⟩

theorem frame_oCfg {s : State} {m m' : Mem} (h : Frame [slotRegion oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

/-- The masks and their registers. -/
def maskConsts : List (Reg × BitVec 64) :=
  pGroups.zipIdx.map fun (g, k) => (maskReg k, BitVec.ofNat 64 g.2)

/-- The mask registers hold the masks. -/
def Masks (s : State) : Prop := ∀ r v, (r, v) ∈ maskConsts → s.gpr r = v

/-- The mask registers are none of the round's others. -/
theorem maskRegs_ne : ∀ p ∈ maskConsts, p.1 ≠ .x5 ∧ p.1 ≠ .x10 ∧ p.1 ≠ .x11 ∧ p.1 ≠ .x12 ∧
    p.1 ≠ .x16 ∧ p.1 ≠ .x6 ∧ p.1 ≠ .x7 ∧ p.1 ≠ .x14 ∧ p.1 ≠ .x15 ∧ p.1 ≠ .x1 ∧ p.1 ≠ .x2 ∧
    p.1 ≠ .x3 ∧ p.1 ≠ .x4 := by
  lit_decide

theorem Masks.congr {s s' : State} (h : Masks s) (hg : ∀ p ∈ maskConsts, s'.gpr p.1 = s.gpr p.1) :
    Masks s' := fun r v hp => by rw [hg (r, v) hp]; exact h r v hp

theorem ySrc_bound : ∀ p < 64, (ySrc p).all (· < 64) = true := by lit_decide

theorem ySrc_lt {p q : Nat} (hp : p < 64) (h : ySrc p = some q) : q < 64 := by
  have := ySrc_bound p hp
  rw [h] at this
  simpa using this

/-- The inputs of `pOut a`: `y` (input word 0) and `a` (input word 1). -/
def pIns (a : Reg) : List (Reg × Nat) := [(.x5, 0), (a, 1)]

/-- Bit `p` of `a` afterwards: bit `ySrc p` of `y` XORed in, where it is spread. -/
def pG (p : Nat) : List Nat :=
  match ySrc p with
  | some q => [q, 64 + p]
  | none => [64 + p]

theorem pOut11_check :
    check (lanes 64 7) oCfg (linExt 2) (pOut .x11) (linEnvC (pIns .x11) maskConsts)
      (linPost 7 [(.x11, pG)]) = true := by
  lit_decide

theorem pOut12_check :
    check (lanes 64 7) oCfg (linExt 2) (pOut .x12) (linEnvC (pIns .x12) maskConsts)
      (linPost 7 [(.x12, pG)]) = true := by
  lit_decide

theorem pOut11_masks :
    maskConsts.all (fun p => (pOut .x11).all fun i => dstOf i != some p.1) = true := by
  lit_decide

theorem pOut12_masks :
    maskConsts.all (fun p => (pOut .x12).all fun i => dstOf i != some p.1) = true := by
  lit_decide

/-- The registers `pOut` keeps. -/
def pKept : List Reg := [.x1, .x2, .x3, .x4, .x5, .x10, .x14, .x15, .x16]

theorem pOut11_kept : (.x12 :: pKept).all (fun r => (pOut .x11).all fun i => dstOf i != some r) = true := by
  lit_decide

theorem pOut12_kept : (.x11 :: pKept).all (fun r => (pOut .x12).all fun i => dstOf i != some r) = true := by
  lit_decide

theorem pOut11_v : (pOut .x11).all (fun i => vdstOf i == none) = true := by lit_decide
theorem pOut12_v : (pOut .x12).all (fun i => vdstOf i == none) = true := by lit_decide

theorem pOut_ok (s : State) {a b : Reg} (hab : (a = .x11 ∧ b = .x12) ∨ (a = .x12 ∧ b = .x11))
    (hm : Masks s) :
    ∃ s', runBlock isa (pOut a) s = some s' ∧
      (∀ p < 64, (s'.gpr a).getLsbD p =
        ((match ySrc p with | some q => (s.gpr .x5).getLsbD q | none => false) ^^ (s.gpr a).getLsbD p)) ∧
      (∀ r ∈ b :: pKept, s'.gpr r = s.gpr r) ∧ Masks s' ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let W (i : Nat) : BitVec 64 := if i = 0 then s.gpr .x5 else s.gpr a
  have go : ∀ (hchk : check (lanes 64 7) oCfg (linExt 2) (pOut a) (linEnvC (pIns a) maskConsts)
        (linPost 7 [(a, pG)]) = true)
      (hkept : (b :: pKept).all (fun r => (pOut a).all fun i => dstOf i != some r) = true)
      (hmk : maskConsts.all (fun p => (pOut a).all fun i => dstOf i != some p.1) = true)
      (hv : (pOut a).all (fun i => vdstOf i == none) = true),
      ∃ s', runBlock isa (pOut a) s = some s' ∧
      (∀ p < 64, (s'.gpr a).getLsbD p =
        ((match ySrc p with | some q => (s.gpr .x5).getLsbD q | none => false) ^^ (s.gpr a).getLsbD p)) ∧
      (∀ r ∈ b :: pKept, s'.gpr r = s.gpr r) ∧ Masks s' ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    intro hchk hkept hmk hv
    obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_okC hchk (oCfg_ok s) W
      (fun r i hri => by
        simp only [pIns, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
        rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
      hm (fun j hj => absurd hj (by simp [oCfg]))
    refine ⟨s', hs', fun p hp => ?_, fun r hr => hoth r (List.all_eq_true.mp hkept r hr),
      hm.congr fun p hp => hoth p.1 (List.all_eq_true.mp hmk p hp), ?_, ?_, hrd, hwr, hsp⟩
    · rw [hout a pG (by simp) p hp, pG]
      split
      · rename_i q hq
        have hq64 : q < 64 := ySrc_lt hp hq
        simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, W,
          Nat.div_eq_of_lt hq64, Nat.mod_eq_of_lt hq64, show (64 + p) / 64 = 1 by omega,
          show (64 + p) % 64 = p by omega, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
      · simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, W, Bool.false_xor,
          show (64 + p) / 64 = 1 by omega, show (64 + p) % 64 = p by omega,
          show (1 : Nat) ≠ 0 by decide, ite_false]
    · exact runBlock_v hv hs'
    · exact frame_oCfg hfr
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact go pOut11_check pOut11_kept pOut11_masks pOut11_v
  · exact go pOut12_check pOut12_kept pOut12_masks pOut12_v

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem xSrc_rot_lt : ∀ p < 64, (xSrc p + 32 - rot) % 32 < 32 := by decide

/-- The bit of `y` that `P` takes for a spread bit: box `i`'s output bit `q`. -/
theorem y_bit {y : BitVec 64} (I : Nat → BitVec 8) (T : Nat → BitVec 8)
    (hy : ∀ l < 8, y.extractLsb' (8 * l) 8 = T (I l).toNat) {i q : Nat} (hi : i < 8)
    (hpos : posOf i q < 8) :
    y.getLsbD (8 * laneOf i + posOf i q) = (T (I (laneOf i)).toNat).getLsbD (posOf i q) := by
  rw [← hy _ (laneOf_lt i hi), BitVec.getLsbD_extractLsb', decide_eq_true hpos, Bool.true_and]

theorem posOf_lt : ∀ i < 8, ∀ q < 4, posOf i q < 8 := by decide

/-- One round: `a := a ⊕ f(b, K)`, spread, with the spread round key at
`x10`, moving it to the next. -/
theorem round_ok {s : State} {a b : Reg} (hab : (a = .x11 ∧ b = .x12) ∨ (a = .x12 ∧ b = .x11))
    (down : Bool) (hc : Consts s) (hm : Masks s) (hk : InRegions (s.rd ++ s.wr) (s.gpr .x10) 8)
    {l r : BitVec 32} {K : BitVec 64} (hl : s.gpr a = spreadW l) (hr : s.gpr b = spreadW r)
    (hK : s.mem.readW (s.gpr .x10) 64 = spread K) :
    ∃ s', runBlock isa (round a b down) s = some s' ∧
      s'.gpr a = spreadW (l ^^^ Spec.TripleDes.roundFunction r (K.setWidth 48)) ∧
      s'.gpr .x10 = (if down then s.gpr .x10 - 8 else s.gpr .x10 + 8) ∧
      (∀ g ∈ b :: [.x1, .x2, .x3, .x4, .x14, .x15, .x16], s'.gpr g = s.gpr g) ∧
      Consts s' ∧ Masks s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hb5 : b ≠ .x5 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hb10 : b ≠ .x10 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have ha5 : a ≠ .x5 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have ha10 : a ≠ .x10 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain ⟨s₁, h₁, i₀, i₁, i₂, i₃, x10₁, g₁, v₁, m₁, rd₁, wr₁, sp₁⟩ := sIn_ok s hb5 hb10 down hk hc
  have hc₁ : Consts s₁ := hc.congr v₁
  let I : Nat → BitVec 8 := fun e => vbyte (s₁.v .v0) e
  obtain ⟨s₂, h₂, y₂, g₂, v₂, m₂, rd₂, wr₂, sp₂⟩ := sOut_ok (s := s₁) I (fun _ _ => rfl)
    (fun e he => i₁ e he) (fun e he => i₂ e he) (fun e he => i₃ e he)
  have hc₂ : Consts s₂ := hc₁.congr v₂
  have hm₂ : Masks s₂ := hm.congr fun p hp => by
    obtain ⟨n5, n10, -⟩ := maskRegs_ne p hp
    rw [g₂ _ n5, g₁ _ n5 n10]
  obtain ⟨s₃, h₃, a₃, k₃, hm₃, v₃, m₃, rd₃, wr₃, sp₃⟩ := pOut_ok s₂ hab hm₂
  have hc₃ : Consts s₃ := hc₂.congr fun w _ _ _ _ => by rw [v₃]
  have a₂ : s₂.gpr a = spreadW l := by rw [g₂ a ha5, g₁ a ha5 ha10, hl]
  -- The S-boxes' outputs.
  have hy : ∀ l' < 8, (s₂.gpr .x5).extractLsb' (8 * l') 8 = sTable (I l').toNat := by
    intro l' hl'
    rw [y₂ l' hl', hc₁.tab _ (I l').isLt]
  have hI : ∀ i < 8, (I (laneOf i)).toNat = 2 ^ 6 * boxTable i + (chunk r (K.setWidth 48) i).toNat := by
    intro i hi
    have hL := laneOf_lt i hi
    simp only [I]
    rw [i₀ _ hL, hK, hr, index_byte K r hL, boxOf_laneOf i hi, BitVec.toNat_ofNat]
    have := (chunk r (K.setWidth 48) i).isLt
    have := tableOf_lt i hi
    omega
  refine ⟨s₃, ?_, ?_, ?_, fun g hg => ?_, hc₃, hm₃, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁]⟩
  · rw [round, runBlock_cat_some (runBlock_cat_some h₁ h₂) h₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [a₃ p hp, a₂, getLsbD_spreadW _ hp, getLsbD_spreadW _ hp]
    have hj := xSrc_rot_lt p hp
    cases hx : xBit p
    · have : ySrc p = none := by simp [ySrc, hx]
      rw [this]; simp
    · rw [ySrc_eq hx, BitVec.getLsbD_xor, Bool.true_and, Bool.true_and,
        getLsbD_roundFunction r _ hj]
      dsimp only
      have hu := pSrc_lt _ hj
      have hi : 7 - pSrc ((xSrc p + 32 - rot) % 32) / 4 < 8 := by omega
      have hq : pSrc ((xSrc p + 32 - rot) % 32) % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [y_bit I sTable hy hi (posOf_lt _ hi _ hq), hI _ hi,
        sTable_bit _ hi _ (chunk r (K.setWidth 48) _).isLt _ hq, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, Bool.xor_comm]
  · rw [k₃ .x10 (by simp [pKept]), g₂ .x10 (by decide), x10₁]
  · have hg' : g ∈ b :: pKept := by
      simp only [pKept, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
      rcases hg with h | h | h | h | h | h | h | h <;> simp [h]
    have h5 : g ≠ .x5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> first | exact hb5 | decide
    have h10 : g ≠ .x10 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> first | exact hb10 | decide
    rw [k₃ g hg', g₂ g h5, g₁ g h5 h10]

end VG.Proof.CmacTripleDes.AArch64
