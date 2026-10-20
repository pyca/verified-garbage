module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Batch
public import VerifiedGarbage.Proof.Ed25519.Canonical64
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Step
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # The inversion's start and end on AArch64

`fold` and `freeze` reduce four words modulo `p` (`fold_ok`, `freeze_ok`),
`storeConst` stores a constant (`storeConst_ok`); `init` sets up the
invariant before the first batch (`init_ok`), and `finish` leaves `±u` modulo
`p`, by the sign of `f` (`finish_ok`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64 VG.Spec.X25519
open VG.Proof.Mont.AArch64 (KeepRegs Keeps.regs)
open VG.Proof.X25519.AArch64 (exec_movz)
open VG.Impl.Ed25519.AArch64 (ld st loads stores const64 offset)
open VG.Impl.Ed25519.AArch64.Divstep (F G U V DSAVE v0 storeConst fold freeze init finish)

variable {large : Bool}

/-- The four words in `x2`–`x5`. -/
abbrev r4 (s : State) : Nat := val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)

theorem fold_ok (s : State) (hz : s.gpr .x12 = 0) (h19 : s.gpr .x6 = 19)
    (hl : s.gpr .x7 = 0x7fffffffffffffff) :
    WP isa (.block fold) s fun t =>
      r4 t % P = r4 s % P ∧ r4 t < 2 ^ 255 + 19 ∧ Keeps [.x2, .x3, .x4, .x5, .x8] s t := by
  have hm (x : Word) : ((x >>> 63) * 19).toNat = 19 * (x.toNat / 2 ^ 63) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (19 : Word).toNat = 19 from rfl, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  apply WP.of_runBlock
  simp only [fold, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := fold_top (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
    (s.gpr .x5 &&& 0x7fffffffffffffff) ((s.gpr .x5 >>> 63) * 19) (hm _) (and_low63 _)
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem cand_ok (s : State) (hz : s.gpr .x12 = 0) (h19 : s.gpr .x6 = 19)
    (hl : s.gpr .x7 = 0x7fffffffffffffff) (hx : r4 s < 2 ^ 255 + 19) :
    WP isa (.block [.adds .x .x8 .x2 .x6, .adcs .x .x9 .x3 .x12, .adcs .x .x10 .x4 .x12,
        .adc .x .x11 .x5 .x12, .lsr .x .x13 .x11 63, .logic .and .x .x11 .x11 .x7,
        .sub .x .x13 .x12 .x13]) s fun t =>
      t.gpr .x13 = mask (decide (P ≤ r4 s)) ∧
      (P ≤ r4 s → val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) = r4 s - P) ∧
      Keeps [.x8, .x9, .x10, .x11, .x13] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := add19_top (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) hx
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `x2`–`x5` replaced by `y₀`–`y₃` where the mask `x13` is set. -/
theorem sel_ok (s : State) {sw : Bool} (hm : s.gpr .x13 = mask sw) (y0 y1 y2 y3 : Reg)
    (hy : ([y0, y1, y2, y3, .x2, .x3, .x4, .x5, .x13] : List Reg).Nodup) :
    WP isa (.block ([(Reg.x2, y0), (.x3, y1), (.x4, y2), (.x5, y3)].flatMap fun (x, y) =>
        [.logic .eor .x y y x, .logic .and .x y y .x13, .logic .eor .x x x y])) s fun t =>
      r4 t = (if sw then val4 (s.gpr y0) (s.gpr y1) (s.gpr y2) (s.gpr y3) else r4 s) ∧
      Keeps [.x2, .x3, .x4, .x5, y0, y1, y2, y3] s t := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨⟨a1, a2', a3', a2, a3, a4, a5, a13⟩, ⟨b2', b3', b2, b3, b4, b5, b13⟩, ⟨c3', c2, c3, c4, c5, c13⟩,
    ⟨d2, d3, d4, d5, d13⟩, -⟩ := hy
  apply WP.of_runBlock
  simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.append_nil, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', r4, b2, c2, c3, d2, d3, d4, Ne.symm a1, Ne.symm a2', Ne.symm a3',
    Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm a13, Ne.symm b2', Ne.symm b3',
    Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm b13, Ne.symm c3', Ne.symm c2,
    Ne.symm c3, Ne.symm c4, Ne.symm c5, Ne.symm c13, Ne.symm d2, Ne.symm d3, Ne.symm d4,
    Ne.symm d5, Ne.symm d13, hm, xor_sel']
  refine ⟨by cases sw <;> rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h2, h3, h4, h5, h0, h1, h2', h3'⟩ := hr
  simp only [RegUpd.gpr_write, h2, h3, h4, h5, h0, h1, h2', h3', ite_false]

theorem freeze_ok (s : State) (hz : s.gpr .x12 = 0) (h19 : s.gpr .x6 = 19)
    (hl : s.gpr .x7 = 0x7fffffffffffffff) (hx : r4 s < 2 ^ 255 + 19) :
    WP isa (.block freeze) s fun t =>
      r4 t = r4 s % P ∧ Keeps [.x2, .x3, .x4, .x5, .x8, .x9, .x10, .x11, .x13] s t := by
  rw [freeze, WP.block_append_iff]
  refine WP.mono (cand_ok s hz h19 hl hx) fun a ⟨a13, av, ka⟩ => ?_
  refine WP.mono (sel_ok a a13 .x8 .x9 .x10 .x11 (by decide)) fun t ⟨tv, kt⟩ => ?_
  have e : r4 a = r4 s := by
    simp only [r4]; rw [ka.gpr _ (by decide), ka.gpr _ (by decide), ka.gpr _ (by decide),
      ka.gpr _ (by decide)]
  refine ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [tv, e]
  by_cases h : P ≤ r4 s
  · simp only [decide_eq_true h, ite_true]
    rw [av h]
    simp only [P] at h hx ⊢
    omega
  · simp only [decide_eq_false h, Bool.false_eq_true, ite_false]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- `[o] = v` (four words), through `x2`. -/
theorem storeConst_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat}
    (ho : FieldRange o large) (v : Nat) (hv : v < 2 ^ 256) :
    WP isa (.block (storeConst o v)) s fun t =>
      fe t.mem base o = v ∧ Outside base o 32 s.mem t.mem ∧ KeepRegs [.x2] s t := by
  have _hcap := workSize_le large
  obtain ⟨h8, ho⟩ := ho
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 8 * j) = BitVec.ofNat 64 (v >>> (64 * j))) ∧
    Outside base o 32 s.mem t.mem ∧ KeepRegs [.x2] s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tw, tO, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩) fun t ⟨tw, tO, tk⟩ => ⟨?_, tO, tk⟩
  · have ts := scr_of hs tk (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (const64_ok t .x2 _) fun a ⟨a2, ka⟩ => ?_
    have as := ts.of_keeps ka (by decide)
    refine WP.mono (st_ok as (d := o + 8 * n) (by omega) (by omega) .x2) fun b ⟨mb, kb⟩ => ?_
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · by_cases h : j = n
      · subst h; rw [mb, word_writeW_self, a2]
      · rw [mb, (writeW_outside a.mem base (a.gpr .x2) (d := o + 8 * n) (by omega)).word (by omega)
          (by omega), ka.mem]
        exact tw j (by omega)
    · rw [mb, ka.mem]
      exact tO.trans ((writeW_outside _ base _ (by omega)).mono (by omega) (by omega))
    · exact (tk.trans (Keeps.regs ka)).trans (kb.mono (by simp))
  · have w0 := tw 0 (by decide); have w1 := tw 1 (by decide)
    have w2 := tw 2 (by decide); have w3 := tw 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3
    simp only [show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl, show 64 * 2 = 128 from rfl,
      show 64 * 3 = 192 from rfl] at w2 w3
    simp only [AArch64.fe, val4]
    rw [w0, w1, w2, w3]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega

theorem v0_spec : (2 ^ 590 * (v0 : Int)) % (P : Int) = 1 := by decide +kernel

theorem movz_ok (s : State) (d : Reg) (imm : BitVec 16) :
    WP isa (.block [.movz .x d imm 0]) s fun t => t.gpr d = imm.setWidth 64 ∧ Keeps [d] s t :=
  WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ⟨RegUpd.gpr_write_self _ _ _ _,
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
      rfl, rfl, rfl, rfl⟩⟩⟩

/-- `d = n`. -/
theorem mov_ok (s : State) (d n : Reg) :
    WP isa (.block [.addImm .x d n 0]) s fun t => t.gpr d = s.gpr n ∧ Keeps [d] s t :=
  WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 0) (by decide), WP.block_nil
    ⟨by rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]; simp only [State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero],
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩

theorem start_ok (s : State) :
    WP isa (.block [.addImm .x .x19 .x1 0, .movz .x .x12 0 0, .movz .x .x6 19 0]) s fun t =>
      t.gpr .x19 = s.gpr .x1 ∧ t.gpr .x12 = 0 ∧ t.gpr .x6 = 19 ∧ Keeps [.x6, .x12, .x19] s t := by
  change WP isa (.block (([.addImm .x .x19 .x1 0] : List Instr) ++ (([.movz .x .x12 0 0] : List Instr) ++
    ([.movz .x .x6 19 0] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (mov_ok s .x19 .x1) fun a ⟨a19, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok a .x12 0) fun b ⟨b12, kb⟩ => ?_
  refine WP.mono (movz_ok b .x6 19) fun t ⟨t6, kt⟩ => ?_
  refine ⟨by rw [kt.gpr _ (by decide), kb.gpr _ (by decide), a19],
    by rw [kt.gpr _ (by decide), b12]; rfl, by rw [t6]; rfl, ?_⟩
  exact ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))

theorem last_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block [.movz .x .x1 1 0, st .x1 DSAVE, .movz .x .x20 10 0]) s fun t =>
      t.mem = s.mem.writeW (off base DSAVE) (1 : Word) ∧
      t.gpr .x20 = BitVec.ofNat 64 10 ∧ KeepRegs [.x1, .x20] s t := by
  have _hmin := workSize_ge large
  change WP isa (.block (([.movz .x .x1 1 0] : List Instr) ++ (([st .x1 DSAVE] : List Instr) ++
    ([.movz .x .x20 10 0] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok s .x1 1) fun a ⟨a1, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st_ok hsa (by decide) (by simp only [DSAVE]; omega) .x1) fun b ⟨mb, kb⟩ => ?_
  refine WP.mono (movz_ok b .x20 10) fun t ⟨t20, kt⟩ => ?_
  refine ⟨by rw [kt.mem, mb, a1, ka.mem]; rfl, by rw [t20]; rfl, ?_⟩
  exact (((Keeps.regs ka).mono (by decide)).trans (kb.mono (by simp))).trans
    ((Keeps.regs kt).mono (by decide))

theorem dsI_init (x : Nat) : dsI x 0 = (1, (P : Int), (x : Int)) := rfl

theorem sv_small {X : Nat} (h : X < 2 ^ 255) : sv X = X := by simp only [sv, h, ↓reduceIte]

/-- The invariant before the first batch, for `x = [slot 2] mod p`. -/
theorem init_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block init) s fun t =>
      RInv (fe s.mem base 128 % P) 0 (word t.mem base DSAVE) (fe t.mem base F) (fe t.mem base G)
        (fe t.mem base U) (fe t.mem base V) ∧
      t.gpr .x20 = BitVec.ofNat 64 10 ∧
      t.gpr .x19 = s.gpr .x1 ∧ Outside base 192 312 s.mem t.mem ∧ KeepRegs (.x19 :: batchRegs) s t := by
  have _hmin := workSize_ge large
  have _hcap := workSize_le large
  simp only [init, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (start_ok s) fun a ⟨a19, a12, a6, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok a .x7 0x7fffffffffffffff) fun b ⟨b7, kb⟩ => ?_
  have hsb := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hsb (o := offset 2) ⟨by decide, by simp only [offset]; omega⟩ (by decide))
    fun c ⟨c2, c3, c4, c5, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok c (by rw [kc.gpr _ (by decide), kb.gpr _ (by decide), a12])
    (by rw [kc.gpr _ (by decide), kb.gpr _ (by decide), a6]) (by rw [kc.gpr _ (by decide), b7]))
    fun d ⟨dv, db, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok d (by rw [kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a12])
    (by rw [kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a6])
    (by rw [kd.gpr _ (by decide), kc.gpr _ (by decide), b7]) db) fun e ⟨ev, ke⟩ => ?_
  have hse := hsd.of_keeps ke (by decide)
  have z12 : e.gpr .x12 = 0 := by
    rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a12]
  -- `x = [slot 2] mod p` in `x2`–`x5`
  have oc : Outside base 488 0 s.mem c.mem := by
    rw [kc.mem, kb.mem, ka.mem]; exact Outside.refl _ _ _ _
  have ex : r4 e = fe s.mem base 128 % P := by
    rw [ev, dv]
    refine congrArg (· % P) ?_
    simp only [r4]
    rw [c2, c3, c4, c5, ← oc.fe (d := 128) (by decide) (by decide), kc.mem]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hse (o := G) ⟨by decide, by simp only [G]; omega⟩ .x2 .x3 .x4 .x5)
    fun f hf => ?_
  subst hf
  have hsf : Scr { e with mem := st4 e.mem base G (e.gpr .x2) (e.gpr .x3) (e.gpr .x4) (e.gpr .x5) }
    base large := hse.setMem _
  rw [WP.block_append_iff]
  refine WP.mono (storeConst_ok hsf (o := F) ⟨by decide, by simp only [F]; omega⟩ P (by decide))
    fun g ⟨gF, og, kg⟩ => ?_
  have hsg := scr_of hsf kg (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hsg (o := U) ⟨by decide, by simp only [U]; omega⟩ .x12 .x12 .x12 .x12)
    fun h hh => ?_
  subst hh
  have g12 : g.gpr .x12 = 0 := by rw [kg.gpr _ (by decide)]; exact z12
  rw [WP.block_append_iff]
  refine WP.mono (storeConst_ok (hsg.setMem _) (o := V) ⟨by decide, by simp only [V]; omega⟩ v0
    (by decide)) fun i ⟨iV, oi, ki⟩ => ?_
  have hsi := scr_of (hsg.setMem _) ki (by decide)
  refine WP.mono (last_ok hsi) fun t ⟨mt, t20, kt⟩ => ?_
  -- the memory at the end
  have oh : Outside base U 32 g.mem (st4 g.mem base U (g.gpr .x12) (g.gpr .x12) (g.gpr .x12)
      (g.gpr .x12)) := st4_outside _ _ (by decide) _ _ _ _
  have of : Outside base G 32 e.mem (st4 e.mem base G (e.gpr .x2) (e.gpr .x3) (e.gpr .x4)
      (e.gpr .x5)) := st4_outside _ _ (by decide) _ _ _ _
  have o1 : Outside base DSAVE 8 i.mem (i.mem.writeW (off base DSAVE) (1 : Word)) :=
    writeW_outside _ _ _ (by decide)
  have o2 : Outside base 496 8 (i.mem.writeW (off base DSAVE) (1 : Word)) t.mem := by
    rw [mt]; exact Outside.refl _ _ _ _
  have fF : fe t.mem base F = P := by
    rw [o2.fe (by decide) (by decide), o1.fe (by decide) (by decide), oi.fe (by decide) (by decide)]
    exact (oh.fe (by decide) (by decide)).trans gF
  have fG : fe t.mem base G = fe s.mem base 128 % P := by
    rw [o2.fe (by decide) (by decide), o1.fe (by decide) (by decide), oi.fe (by decide) (by decide),
      oh.fe (by decide) (by decide), og.fe (by decide) (by decide), fe_st4 _ _ (by decide)]
    exact ex
  have fU : fe t.mem base U = 0 := by
    rw [o2.fe (by decide) (by decide), o1.fe (by decide) (by decide), oi.fe (by decide) (by decide),
      fe_st4 _ _ (by decide), g12]
    rfl
  have fV : fe t.mem base V = v0 := by
    rw [o2.fe (by decide) (by decide), o1.fe (by decide) (by decide)]; exact iV
  have wD : word t.mem base DSAVE = 1 := by
    rw [o2.word (by decide) (by decide), word_writeW_self]
  have hx : fe s.mem base 128 % P < P := Nat.mod_lt _ (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, t20, ?_, ?_, ?_⟩
  · rw [wD, dsI_init]; rfl
  · rw [fF, dsI_init, sv_small (by decide)]
  · rw [fG, dsI_init, sv_small (by simp only [P] at hx ⊢; omega)]
  · rw [fF]; decide
  · rw [fG]; simp only [P] at hx ⊢; omega
  · rw [fU]; decide
  · rw [fV]; decide
  · rw [fU, dsI_init]
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero]
    simp only [Int.ModEq, Int.emod_self, Int.zero_emod]
  · rw [fV, dsI_init]
    simp only [Nat.mul_zero, pow_zero, one_mul]
    have k := (Int.ModEq.mul_left ((fe s.mem base 128 % P : Nat) : Int)
      (show (2 ^ 590 * (v0 : Int)) ≡ 1 [ZMOD P] from v0_spec.trans (by decide))).symm
    rw [mul_one, ← mul_assoc] at k
    exact k
  · intro _
    rw [fU]
    exact Int.ModEq.refl _
  · exact (kt.gpr _ (by decide)).trans ((ki.gpr _ (by decide)).trans ((kg.gpr _ (by decide)).trans
      ((ke.gpr _ (by decide)).trans ((kd.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans
        ((kb.gpr _ (by decide)).trans a19))))))
  · have oa : Outside base 192 312 s.mem c.mem := oc.mono (by decide) (by decide)
    rw [← kd.mem, ← ke.mem] at oa
    exact ((((oa.trans (of.mono (by decide) (by decide))).trans (og.mono (by decide) (by decide))).trans
      (oh.mono (by decide) (by decide))).trans (oi.mono (by decide) (by decide))).trans
      ((o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide)))
  · have kf : KeepRegs (.x19 :: batchRegs) e
        { e with mem := st4 e.mem base G (e.gpr .x2) (e.gpr .x3) (e.gpr .x4) (e.gpr .x5) } :=
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have kh : KeepRegs (.x19 :: batchRegs) g
        { g with mem := st4 g.mem base U (g.gpr .x12) (g.gpr .x12) (g.gpr .x12) (g.gpr .x12) } :=
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    exact ((((((((Keeps.regs ka).mono (by decide)).trans ((Keeps.regs kb).mono (by decide))).trans
      ((Keeps.regs kc).mono (by decide))).trans ((Keeps.regs kd).mono (by decide))).trans
      ((Keeps.regs ke).mono (by decide))).trans (kf.trans (kg.mono (by decide)))).trans
      (kh.trans (ki.mono (by decide)))).trans (kt.mono (by decide))

/-- `2p - u` (`2p = 2²⁵⁶ - 38`) into `x8`, `x9`, `x11`, `x10`. -/
theorem neg_ok (s : State) (h9 : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 64 - 38))
    (h10 : s.gpr .x10 = BitVec.allOnes 64) (hu : r4 s ≤ 2 ^ 256 - 38) :
    WP isa (.block [.subs .x .x8 .x9 .x2, .sbcs .x .x9 .x10 .x3, .sbcs .x .x11 .x10 .x4,
        .sbc .x .x10 .x10 .x5]) s fun t =>
      val4 (t.gpr .x8) (t.gpr .x9) (t.gpr .x11) (t.gpr .x10) = 2 ^ 256 - 38 - r4 s ∧
      Keeps [.x8, .x9, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h9, h10, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  have h := sub4_value (BitVec.ofNat 64 (2 ^ 64 - 38)) (BitVec.allOnes 64) (BitVec.allOnes 64)
    (BitVec.allOnes 64) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) true
  have hl := val4_lt (addCarry (BitVec.ofNat 64 (2 ^ 64 - 38)) (~~~s.gpr .x2) true)
    (addCarry (BitVec.allOnes 64) (~~~s.gpr .x3)
      (carryOut (BitVec.ofNat 64 (2 ^ 64 - 38)) (~~~s.gpr .x2) true))
    (addCarry (BitVec.allOnes 64) (~~~s.gpr .x4) (carryOut (BitVec.allOnes 64) (~~~s.gpr .x3)
      (carryOut (BitVec.ofNat 64 (2 ^ 64 - 38)) (~~~s.gpr .x2) true)))
    (addCarry (BitVec.allOnes 64) (~~~s.gpr .x5) (carryOut (BitVec.allOnes 64) (~~~s.gpr .x4)
      (carryOut (BitVec.allOnes 64) (~~~s.gpr .x3)
        (carryOut (BitVec.ofNat 64 (2 ^ 64 - 38)) (~~~s.gpr .x2) true))))
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at h hl ⊢
    have e : val4 (BitVec.ofNat 64 (2 ^ 64 - 38)) (BitVec.allOnes 64) (BitVec.allOnes 64)
      (BitVec.allOnes 64) = 2 ^ 256 - 38 := by decide
    rw [e] at h
    simp only [r4] at hu ⊢
    have key : ∀ (b : Bool) (W R : Nat), W + R + (1 - true.toNat) = 2 ^ 256 - 38 + 2 ^ 256 * (1 - b.toNat) →
        W < 2 ^ 256 → R ≤ 2 ^ 256 - 38 → W = 2 ^ 256 - 38 - R := by
      intro b W R h1 h2 h3; cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] at h1 <;> omega
    exact key _ _ _ h hl hu
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The mask of `f`'s sign into `x13`. -/
theorem sgn_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x12 = 0) :
    WP isa (.block [ld .x13 (F + 24), .lsr .x .x13 .x13 63, .sub .x .x13 .x12 .x13]) s fun t =>
      t.gpr .x13 = mask (decide (2 ^ 255 ≤ fe s.mem base F)) ∧ Keeps [.x13] s t := by
  have _hmin := workSize_ge large
  change WP isa (.block (([ld .x13 (F + 24)] : List Instr) ++
    ([.lsr .x .x13 .x13 63, .sub .x .x13 .x12 .x13] : List Instr))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (by decide) (by simp only [F]; omega) .x13) fun a ⟨a13, ka⟩ => ?_
  have az : a.gpr .x12 = 0 := (ka.gpr _ (by decide)).trans hz
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, VG.Proof.X25519.AArch64.exec_lsr
    (by decide : 63 < 64), VG.Proof.X25519.AArch64.exec_sub_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, az, a13]
    rw [mask_eq]
    have l0 := (word s.mem base F).isLt
    have l1 := (word s.mem base (F + 8)).isLt
    have l2 := (word s.mem base (F + 16)).isLt
    have l3 := (word s.mem base (F + 24)).isLt
    simp only [maskN, mask, BitVec.msb_eq_decide, AArch64.fe, val4]
    congr 1
    apply propext
    simp only [decide_eq_true_eq]
    omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
    exact ka.gpr r (by simpa using hr)

/-- `[slot 15] ≡ ±u` (mod `p`), `-` if `f < 0`; `x1` back. -/
theorem finish_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block finish) s fun t =>
      ((fe t.mem base 544 : Nat) : Int) % P =
        (if 2 ^ 255 ≤ fe s.mem base F then -(fe s.mem base U : Int) else fe s.mem base U) % P ∧
      t.gpr .x1 = s.gpr .x19 ∧ Outside base 544 32 s.mem t.mem ∧
      KeepRegs batchRegs s t := by
  have _hmin := workSize_ge large
  have _hcap := workSize_le large
  simp only [finish, List.append_assoc]
  change WP isa (.block (([.movz .x .x12 0 0] : List Instr) ++ ([.movz .x .x6 19 0] ++ _))) s _
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok s .x12 0) fun a ⟨a12, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok a .x6 19) fun b ⟨b6, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b .x7 0x7fffffffffffffff) fun c ⟨c7, kc⟩ => ?_
  have hsc := ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)).of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hsc (o := U) ⟨by decide, by simp only [U]; omega⟩ (by decide))
    fun d ⟨d2, d3, d4, d5, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  have z12 : d.gpr .x12 = 0 := by
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a12]; rfl
  have z6 : d.gpr .x6 = 19 := by rw [kd.gpr _ (by decide), kc.gpr _ (by decide), b6]; rfl
  have z7 : d.gpr .x7 = 0x7fffffffffffffff := by rw [kd.gpr _ (by decide), c7]
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok d z12 z6 z7) fun e ⟨ev, eb, ke⟩ => ?_
  have hse := hsd.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok e .x9 (BitVec.ofNat 64 (2 ^ 64 - 38))) fun f ⟨f9, kf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok f .x10 (BitVec.allOnes 64)) fun g ⟨g10, kg⟩ => ?_
  have hsg := (hse.of_keeps kf (by decide)).of_keeps kg (by decide)
  have rg : r4 g = r4 e := by
    simp only [r4]
    rw [kg.gpr _ (by decide), kg.gpr _ (by decide), kg.gpr _ (by decide), kg.gpr _ (by decide),
      kf.gpr _ (by decide), kf.gpr _ (by decide), kf.gpr _ (by decide), kf.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (neg_ok g (by rw [kg.gpr _ (by decide), f9]) g10
    (by rw [rg]; omega)) fun h ⟨hv, kh⟩ => ?_
  have hsh := hsg.of_keeps kh (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sgn_ok hsh (by rw [kh.gpr _ (by decide), kg.gpr _ (by decide), kf.gpr _ (by decide),
    ke.gpr _ (by decide), z12])) fun i ⟨i13, ki⟩ => ?_
  have hsi := hsh.of_keeps ki (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok i i13 .x8 .x9 .x11 .x10 (by decide)) fun j ⟨jv, kj⟩ => ?_
  have hsj := hsi.of_keeps kj (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hsj (o := offset 15) ⟨by decide, by simp only [offset]; omega⟩
    .x2 .x3 .x4 .x5) fun k hk => ?_
  subst hk
  refine WP.mono (mov_ok _ .x1 .x19) fun t ⟨t1, kt⟩ => ?_
  -- the memory
  have mh : h.mem = s.mem := by
    rw [kh.mem, kg.mem, kf.mem, ke.mem, kd.mem, kc.mem, kb.mem, ka.mem]
  have mi : i.mem = s.mem := ki.mem.trans mh
  have mj : j.mem = s.mem := kj.mem.trans mi
  have ok : Outside base 544 32 j.mem (st4 j.mem base 544 (j.gpr .x2) (j.gpr .x3) (j.gpr .x4)
      (j.gpr .x5)) := st4_outside _ _ (by decide) _ _ _ _
  have ot : Outside base 544 32 s.mem t.mem := by rw [kt.mem, ← mj]; exact ok
  refine ⟨?_, ?_, ot, ?_⟩
  · rw [kt.mem]
    show ((fe (st4 j.mem base 544 (j.gpr .x2) (j.gpr .x3) (j.gpr .x4) (j.gpr .x5)) base 544 : Nat) : Int) % P = _
    rw [fe_st4 _ _ (by decide), show val4 (j.gpr .x2) (j.gpr .x3) (j.gpr .x4) (j.gpr .x5) = r4 j from rfl,
      jv]
    have hu : r4 d = fe s.mem base U := by
      simp only [r4]; rw [d2, d3, d4, d5, kc.mem, kb.mem, ka.mem]
    have ri : r4 i = r4 e := by
      simp only [r4]
      rw [ki.gpr _ (by decide), ki.gpr _ (by decide), ki.gpr _ (by decide), ki.gpr _ (by decide),
        kh.gpr _ (by decide), kh.gpr _ (by decide), kh.gpr _ (by decide), kh.gpr _ (by decide)]
      exact rg
    have vi : val4 (i.gpr .x8) (i.gpr .x9) (i.gpr .x11) (i.gpr .x10) = 2 ^ 256 - 38 - r4 e := by
      rw [ki.gpr _ (by decide), ki.gpr _ (by decide), ki.gpr _ (by decide), ki.gpr _ (by decide), hv, rg]
    rw [ri, vi, mh]
    rw [hu] at ev
    generalize r4 e = W at ev eb
    generalize fe s.mem base U = X at ev
    have hP : (P : Int) = 2 ^ 255 - 19 := P_val
    simp only [P] at ev
    rw [hP]
    by_cases hc : 2 ^ 255 ≤ fe s.mem base F
    · simp only [hc, decide_true, ite_true]
      omega
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      omega
  · exact t1.trans ((kj.gpr .x19 (by decide)).trans
      ((ki.gpr .x19 (by decide)).trans
      ((kh.gpr .x19 (by decide)).trans
      ((kg.gpr .x19 (by decide)).trans
      ((kf.gpr .x19 (by decide)).trans
      ((ke.gpr .x19 (by decide)).trans
      ((kd.gpr .x19 (by decide)).trans
      ((kc.gpr .x19 (by decide)).trans
      ((kb.gpr .x19 (by decide)).trans
      (ka.gpr .x19 (by decide)))))))))))
  · exact ((((((((((Keeps.regs ka).mono (by decide)).trans ((Keeps.regs kb).mono (by decide))).trans
      ((Keeps.regs kc).mono (by decide))).trans ((Keeps.regs kd).mono (by decide))).trans
      ((Keeps.regs ke).mono (by decide))).trans ((Keeps.regs kf).mono (by decide))).trans
      ((Keeps.regs kg).mono (by decide))).trans ((Keeps.regs kh).mono (by decide))).trans
      ((Keeps.regs ki).mono (by decide))).trans
      (((Keeps.regs kj).mono (by decide)).trans ((⟨fun _ _ => rfl, rfl, rfl, rfl⟩ : KeepRegs batchRegs j
        { j with mem := st4 j.mem base 544 (j.gpr .x2) (j.gpr .x3) (j.gpr .x4) (j.gpr .x5) }).trans
        ((Keeps.regs kt).mono (by decide))))

end VG.Proof.Ed25519.AArch64.Inv
