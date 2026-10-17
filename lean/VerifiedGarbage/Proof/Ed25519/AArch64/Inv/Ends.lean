module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Batch
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Ed25519.Canonical64
public import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
open VG.Impl.Ed25519.AArch64.Divstep (F G U V DSAVE CNT X1SAVE v0 storeConst fold freeze init finish)

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

theorem start_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block [st .x1 X1SAVE, .movz .x .x12 0 0, .movz .x .x6 19 0]) s fun t =>
      t.mem = s.mem.writeW (off base X1SAVE) (s.gpr .x1) ∧ t.gpr .x12 = 0 ∧ t.gpr .x6 = 19 ∧
        KeepRegs [.x6, .x12] s t := by
  have _hmin := workSize_ge large
  change WP isa (.block (([st .x1 X1SAVE] : List Instr) ++ (([.movz .x .x12 0 0] : List Instr) ++
    ([.movz .x .x6 19 0] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (st_ok hs (by decide) (by simp only [X1SAVE]; omega) .x1) fun a ⟨ma, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok a .x12 0) fun b ⟨b12, kb⟩ => ?_
  refine WP.mono (movz_ok b .x6 19) fun t ⟨t6, kt⟩ => ?_
  refine ⟨by rw [kt.mem, kb.mem, ma], by rw [kt.gpr _ (by decide), b12]; rfl, by rw [t6]; rfl, ?_⟩
  exact ((ka.mono (by simp)).trans ((Keeps.regs kb).mono (by decide))).trans
    ((Keeps.regs kt).mono (by decide))

theorem last_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block [.movz .x .x1 1 0, st .x1 DSAVE, .movz .x .x19 10 0, st .x19 CNT]) s fun t =>
      t.mem = (s.mem.writeW (off base DSAVE) (1 : Word)).writeW (off base CNT) (BitVec.ofNat 64 10) ∧
      t.gpr .x19 = BitVec.ofNat 64 10 ∧ KeepRegs [.x1, .x19] s t := by
  have _hmin := workSize_ge large
  change WP isa (.block (([.movz .x .x1 1 0] : List Instr) ++ (([st .x1 DSAVE] : List Instr) ++
    (([.movz .x .x19 10 0] : List Instr) ++ ([st .x19 CNT] : List Instr))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok s .x1 1) fun a ⟨a1, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st_ok hsa (by decide) (by simp only [DSAVE]; omega) .x1) fun b ⟨mb, kb⟩ => ?_
  have hsb := scr_of hsa kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movz_ok b .x19 10) fun c ⟨c19, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  refine WP.mono (st_ok hsc (by decide) (by simp only [CNT]; omega) .x19) fun t ⟨mt, kt⟩ => ?_
  refine ⟨by rw [mt, c19, kc.mem, mb, a1, ka.mem]; rfl,
    by rw [kt.gpr _ (by simp), c19]; rfl, ?_⟩
  exact ((((Keeps.regs ka).mono (by decide)).trans (kb.mono (by simp))).trans
    ((Keeps.regs kc).mono (by decide))).trans (kt.mono (by simp))

theorem dsI_init (x : Nat) : dsI x 0 = (1, (P : Int), (x : Int)) := rfl

theorem sv_small {X : Nat} (h : X < 2 ^ 255) : sv X = X := by simp only [sv, h, ↓reduceIte]

/-- The invariant before the first batch, for `x = [slot 2] mod p`. -/
theorem init_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block init) s fun t =>
      RInv (fe s.mem base 128 % P) 0 (word t.mem base DSAVE) (fe t.mem base F) (fe t.mem base G)
        (fe t.mem base U) (fe t.mem base V) ∧
      word t.mem base CNT = BitVec.ofNat 64 10 ∧ t.gpr .x19 = BitVec.ofNat 64 10 ∧
      word t.mem base X1SAVE = s.gpr .x1 ∧ Outside base 192 312 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  have _hmin := workSize_ge large
  have _hcap := workSize_le large
  simp only [init, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (start_ok hs) fun a ⟨ma, a12, a6, ka⟩ => ?_
  have hsa := scr_of hs ka (by decide)
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
  have mc : c.mem = s.mem.writeW (off base X1SAVE) (s.gpr .x1) := by rw [kc.mem, kb.mem, ma]
  have oc : Outside base X1SAVE 8 s.mem c.mem := by
    rw [mc]; exact writeW_outside _ _ _ (by decide)
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
  refine WP.mono (last_ok hsi) fun t ⟨mt, t19, kt⟩ => ?_
  -- the memory at the end
  have oh : Outside base U 32 g.mem (st4 g.mem base U (g.gpr .x12) (g.gpr .x12) (g.gpr .x12)
      (g.gpr .x12)) := st4_outside _ _ (by decide) _ _ _ _
  have of : Outside base G 32 e.mem (st4 e.mem base G (e.gpr .x2) (e.gpr .x3) (e.gpr .x4)
      (e.gpr .x5)) := st4_outside _ _ (by decide) _ _ _ _
  have o1 : Outside base DSAVE 8 i.mem (i.mem.writeW (off base DSAVE) (1 : Word)) :=
    writeW_outside _ _ _ (by decide)
  have o2 : Outside base CNT 8 (i.mem.writeW (off base DSAVE) (1 : Word)) t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by decide)
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, t19, ?_, ?_, ?_⟩
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
  · rw [mt, word_writeW_self]
  · rw [o2.word (by decide) (by decide), o1.word (by decide) (by decide), oi.word (by decide) (by decide),
      oh.word (by decide) (by decide), og.word (by decide) (by decide), of.word (by decide) (by decide),
      ke.mem, kd.mem, mc, word_writeW_self]
  · have oa : Outside base 192 312 s.mem c.mem := oc.mono (by decide) (by decide)
    rw [← kd.mem, ← ke.mem] at oa
    exact ((((oa.trans (of.mono (by decide) (by decide))).trans (og.mono (by decide) (by decide))).trans
      (oh.mono (by decide) (by decide))).trans (oi.mono (by decide) (by decide))).trans
      ((o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide)))
  · have kf : KeepRegs batchRegs e
        { e with mem := st4 e.mem base G (e.gpr .x2) (e.gpr .x3) (e.gpr .x4) (e.gpr .x5) } :=
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have kh : KeepRegs batchRegs g
        { g with mem := st4 g.mem base U (g.gpr .x12) (g.gpr .x12) (g.gpr .x12) (g.gpr .x12) } :=
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    exact (((((((ka.mono (by decide)).trans ((Keeps.regs kb).mono (by decide))).trans
      ((Keeps.regs kc).mono (by decide))).trans ((Keeps.regs kd).mono (by decide))).trans
      ((Keeps.regs ke).mono (by decide))).trans (kf.trans (kg.mono (by decide)))).trans
      (kh.trans (ki.mono (by decide)))).trans (kt.mono (by decide))

end VG.Proof.Ed25519.AArch64.Inv
