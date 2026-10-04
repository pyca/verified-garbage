import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

/-!
# ECDH on AArch64: reading and checking the peer's key

As on x86-64 (`Proof/Ecdh/X86_64/Peer.lean`).

## The checks

Each check ands a mask into the flag, as the signature's checks do
(`Proof/Ecdsa/AArch64/Flags.lean`): the peer's first byte is `04`
(`checkLead_ok`), a number is below `p` (`checkLtP_ok`) and a number is
zero (`checkZero_ok`). A register is zero iff it is below 1
(`isZero_ok`).
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem movz_ok (s : State) (r : Reg) (v : BitVec 16) :
    WP isa (.block [.movz .x r v 0]) s fun s' => s'.gpr r = v.setWidth 64 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by simp, fun r' hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x2` is all ones iff `x1 = 0`, with `x7 = 0`, through `x5` and `x16`. -/
theorem isZero_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block Impl.Ecdh.AArch64.Cfg.isZero) s fun s' =>
      s'.gpr .x2 = mask (s.gpr .x1 = 0) ∧ Keeps [.x2, .x5, .x16] s s' := by
  rw [Impl.Ecdh.AArch64.Cfg.isZero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz_ok s .x5 1) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₁ .x16 .x1 .x5 true (c := true) rfl) fun s₂ ⟨_, c₂, k₂⟩ => ?_
  refine WP.mono (sbcMask2_ok s₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]))
    fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))⟩
  rw [e₃, c₂, not_carryOut, e₁, k₁.gpr .x1 (by decide)]
  have h1 : ((1 : BitVec 16).setWidth 64).toNat = 1 := rfl
  simp only [h1, Bool.not_true, Bool.toNat_false, Nat.add_zero, Nat.lt_one_iff, decide_eq_true_eq]
  simp only [mask]
  congr 1
  exact propext ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩

/-- The mask `x2` of the byte at `q = x6` being `04`. -/
theorem lead_ok {s : State} {q : Addr} (hq : s.gpr .x6 = q) (hin : InRegions (s.rd ++ s.wr) q 1) :
    WP isa (.block ([zero7, .ldrb .x1 .x6 0, .movz .x .x5 4 0, .logic .eor .x .x1 .x1 .x5] ++
      Impl.Ecdh.AArch64.Cfg.isZero)) s fun s' =>
      s'.gpr .x2 = mask (s.mem q = 4) ∧ Keeps [.x1, .x2, .x5, .x7, .x16] s s' := by
  have ha : s.gpr .x6 + BitVec.ofNat 64 0 = q := by rw [hq]; exact BitVec.add_zero _
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [zero7, .ldrb .x1 .x6 0, .movz .x .x5 4 0,
      .logic .eor .x .x1 .x1 .x5]) s (fun s₁ =>
      s₁.gpr .x1 = (s.mem q).setWidth 64 ^^^ 4 ∧ s₁.gpr .x7 = 0 ∧ Keeps [.x1, .x5, .x7] s s₁) by
    apply WP.of_runBlock
    simp only [zero7, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, Nat.mod_one,
      show 0 < 4096 * 1 by decide, show 16 * 0 < Size.x.bits by decide, and_self, ite_true,
      Option.bind_some, State.load, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
      BitVec.setWidth_eq, reduceCtorEq, ite_false, ha, hin, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨by rw [read1_zext]; rfl, by rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]) fun s₁ ⟨e₁, z₁, k₁⟩ => ?_
  refine WP.mono (isZero_ok s₁ z₁) fun s₂ ⟨e₂, k₂⟩ =>
    ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [e₂, e₁]
  have key : ∀ b : Byte, (b.setWidth 64 ^^^ 4 = 0) = (b = 4) := by decide
  simp only [mask, key]

/-! ## Below `p` -/

theorem ltP_eq (c : Cfg) (a : Nat) :
    Impl.Ecdh.AArch64.Cfg.ltP c a =
      zero7 :: ((List.range c.n).flatMap (ltStep a (c.sl MP)) ++ ([.sbc .x .x2 .x7 .x7] : List Instr)) :=
  rfl

/-- The mask `x2` of `[a] < p`. -/
theorem ltP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) (ha8 : a % 8 = 0)
    (hm8 : c.sl MP % 8 = 0) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.ltP c a)) s fun s' =>
      s'.gpr .x2 = mask (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      Keeps [.x1, .x2, .x7, .x16] s s' := by
  obtain ⟨k, hk⟩ : ∃ k, c.n = k + 1 := ⟨c.n - 1, by omega⟩
  rw [ltP_eq, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  rw [WP.block_append_iff, hk]
  rw [hk] at ha hm
  refine WP.mono (ltSteps_ok (hs.of_keeps k₀ (by decide)) ha8 hm8 k ha hm) fun s₁ ⟨c₁, k₁⟩ => ?_
  refine WP.mono (sbcMask2_ok s₁ (by rw [k₁.gpr _ (by decide), z₀])) fun s₂ ⟨e₂, k₂⟩ =>
    ⟨?_, ((k₀.mono (by sub_regs)).trans (k₁.mono (by sub_regs))).trans (k₂.mono (by sub_regs))⟩
  rw [e₂, c₁, k₀.mem]
  simp only [mask, decide_eq_true_eq]

/-- `checkLtP a`: the flag `&=` the mask of `[a] < [MP]`. -/
theorem checkLtP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size)
    (ha8 : a % 8 = 0) (hm8 : c.sl MP % 8 = 0) (hf8 : c.sl FLAG % 8 = 0) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.checkLtP c a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        mask (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      KeepRegs [.x1, .x2, .x7, .x16] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Impl.Ecdh.AArch64.Cfg.checkLtP, WP.block_append_iff]
  refine WP.mono (ltP_ok c hs hn ha hm ha8 hm8) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok c (hs.of_keeps k₁ (by decide)) hf hf8) fun s₂ ⟨e₂, k₂, O₂⟩ =>
    ⟨by rw [e₂, e₁, k₁.mem], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
      by rw [← k₁.mem]; exact O₂⟩

/-- `checkLead`: the flag `&=` the mask of the byte at `q = x6` being `04`. -/
theorem checkLead_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {q : Addr} (hq : s.gpr .x6 = q) (hin : InRegions (s.rd ++ s.wr) q 1) (hf : c.sl FLAG + 8 ≤ size)
    (hf8 : c.sl FLAG % 8 = 0) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.checkLead c)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (s.mem q = 4) ∧
      KeepRegs [.x1, .x2, .x5, .x7, .x16] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Impl.Ecdh.AArch64.Cfg.checkLead, WP.block_append_iff]
  refine WP.mono (lead_ok hq hin) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok c (hs.of_keeps k₁ (by decide)) hf hf8) fun s₂ ⟨e₂, k₂, O₂⟩ =>
    ⟨by rw [e₂, e₁, k₁.mem], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
      by rw [← k₁.mem]; exact O₂⟩

/-! ## Zero -/

/-- The mask `x2` of `[a] = 0`. -/
theorem zero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (ha8 : a % 8 = 0) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.zero c a)) s fun s' =>
      s'.gpr .x2 = mask (wordsVal s.mem base a c.n = 0) ∧ Keeps [.x1, .x2, .x5, .x7, .x16] s s' := by
  rw [Impl.Ecdh.AArch64.Cfg.zero, List.append_assoc, WP.block_append_iff, ← List.singleton_append,
    WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  refine WP.mono (ld_ok hs₀ (d := a) (by omega) ha8 .x1) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ ha8 (c.n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.mem, k₀.mem] at e₂
  have hz : s₂.gpr .x1 = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), z₀]
  refine WP.mono (isZero_ok s₂ hz₂) fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ?_⟩
  · rw [e₃]
    simp only [mask, hz]
  · exact (((k₀.mono (by sub_regs)).trans (k₁.mono (by sub_regs))).trans (k₂.mono (by sub_regs))).trans
      (k₃.mono (by sub_regs))

/-- `checkZero a`: the flag `&=` the mask of `[a] = 0`. -/
theorem checkZero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size) (ha8 : a % 8 = 0)
    (hf8 : c.sl FLAG % 8 = 0) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.checkZero c a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (wordsVal s.mem base a c.n = 0) ∧
      KeepRegs [.x1, .x2, .x5, .x7, .x16] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Impl.Ecdh.AArch64.Cfg.checkZero, WP.block_append_iff]
  refine WP.mono (zero_ok c hs hn ha ha8) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok c (hs.of_keeps k₁ (by decide)) hf hf8) fun s₂ ⟨e₂, k₂, O₂⟩ =>
    ⟨by rw [e₂, e₁, k₁.mem], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
      by rw [← k₁.mem]; exact O₂⟩

end VG.Proof.Ecdh.AArch64

/-!
## Reading the peer's key

`peer` stores `R² mod p` and `b R mod p`, reads the peer's `y` into its
slot, and ands into the flag the masks of the peer's first byte being `04`,
`x < p` and `y < p` (`peer_ok`). It writes only those slots and the flag,
in the working space, which the peer's key is apart from.
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdh.AArch64 (QY R2P BP)

variable {c : Cfg}

/-- `x2 = x6 + k`. -/
theorem ptr_ok (s : State) {k : Nat} (hk : k < 4096) :
    WP isa (.block [.addImm .x .x2 .x6 k]) s
      fun s' => s'.gpr .x2 = s.gpr .x6 + BitVec.ofNat 64 k ∧ Keeps [.x2] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, hk, ite_true,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem peer_eq (c : Cfg) : Impl.Ecdh.AArch64.Cfg.peer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++ (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (([.addImm .x .x2 .x6 (1 + 8 * c.n)] : List Instr) ++
    (loadBE c.n (c.sl QY) .x2 ++ (Impl.Ecdh.AArch64.Cfg.checkLead c ++
    (Impl.Ecdh.AArch64.Cfg.checkLtP c (c.sl E) ++ Impl.Ecdh.AArch64.Cfg.checkLtP c (c.sl QY)))))) := by
  simp only [Impl.Ecdh.AArch64.Cfg.peer, Impl.Ecdh.AArch64.Cfg.consts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-- A slot apart from the one an operation wrote keeps its number. -/
theorem sv_out {base : Addr} {m m' : Mem} {j : Nat} (h : Outside base (c.sl j) (8 * c.n) m m')
    (h7 : c.n < 7) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45) (hij : i ≠ j) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  have := sl_le c h7 hi
  exact h.wordsVal (sl_apart c hij) (by omega)

/-- The constants, the peer's `y` and the checks of its first byte, `x` and `y`. -/
theorem peer_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {q : Addr}
    (hq : s.gpr .x6 = q) (hin : (⟨q, 1 + 16 * c.n⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q, 1 + 16 * c.n⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.peer c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.x1, .x2, .x5, .x7, .x16] s s' ∧
      Unch base (slW c [R2P, BP, QY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' QY = ofBytes (Spec.Ecdsa.bytesAt s.mem (q + BitVec.ofNat 64 (1 + 8 * c.n)) (8 * c.n)) ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (s.mem q = 4) &&&
        mask (sv c base s E < c.C.p) &&& mask (sv c base s' QY < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  rw [peer_eq, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hR2 (sl_mod8 c R2P) (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ hB (sl_mod8 c BP) (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ptr_ok s₂ (k := 1 + 8 * c.n) (by omega)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hq₂ : s₂.gpr .x6 = q := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hq]
  have hq₃ : s₃.gpr .x6 = q := by rw [k₃.gpr _ (by decide), hq₂]
  have hrw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by
    rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]
  rw [hq₂] at e₃
  -- `y`
  rw [WP.block_append_iff]
  refine WP.mono (loadBE_ok hs₃ (src := .x2) (by decide) hY (sl_mod8 c QY) (by omega) (fun e he => ⟨_, by rw [hrw₃]; exact hin, by
      rw [e₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.contains_base q (by omega) (by omega)⟩)
    (by rw [e₃]; exact (hd.sub_left (Offset.sub_base q (by omega))).sub_right (Offset.sub_base base hY)))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have O₄' : Outside base (c.sl QY) (8 * c.n) s₂.mem s₄.mem := k₃.mem ▸ O₄
  have hq₄ : s₄.gpr .x6 = q := by rw [k₄.gpr _ (by decide), hq₃]
  have hrw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [k₄.rd, k₄.wr, hrw₃]
  -- What the stores so far keep: everything apart from the working space.
  have W₄ : Outside base 0 size s.mem s₄.mem :=
    ((O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.zero_le _) (by omega))).trans
      (O₄'.mono (Nat.zero_le _) (by omega))
  have hq0 : s₄.mem q = s.mem q := by
    have := keep_of_disjoint' W₄ hd (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- the first byte
  rw [WP.block_append_iff]
  refine WP.mono (checkLead_ok c hs₄ hq₄ ⟨_, by rw [hrw₄]; exact hin, by
      have := Offset.contains_base q (d := 0) (n := 1) (k := 1 + 16 * c.n) (by omega) (by omega)
      rwa [BitVec.add_zero] at this⟩ hF (sl_mod8 c FLAG)) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- `x < p`
  rw [WP.block_append_iff]
  refine WP.mono (checkLtP_ok c hs₅ h0 hE hM hF (sl_mod8 c E) (sl_mod8 c MP) (sl_mod8 c FLAG)) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- `y < p`
  refine WP.mono (checkLtP_ok c hs₆ h0 hY hM hF (sl_mod8 c QY) (sl_mod8 c MP) (sl_mod8 c FLAG)) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  -- The slots.
  have v₄ : ∀ {i}, i < 45 → i ≠ R2P → i ≠ BP → i ≠ QY →
      wordsVal s₄.mem base (c.sl i) c.n = wordsVal s.mem base (c.sl i) c.n :=
    fun hi h₁ h₂ h₃ => by
      rw [sv_out O₄' h7 hn hi h₃, sv_out O₂ h7 hn hi h₂, sv_out O₁ h7 hn hi h₁]
  have v₇ : ∀ {i}, i < 45 → i ≠ FLAG →
      wordsVal s₇.mem base (c.sl i) c.n = wordsVal s₄.mem base (c.sl i) c.n := fun hi hf =>
    ((sv_flag O₇ h0 h7 hn hi hf).trans (sv_flag O₆ h0 h7 hn hi hf)).trans (sv_flag O₅ h0 h7 hn hi hf)
  have flag₄ : word s₄.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) := by
    have hap : ∀ {j}, j < 45 → j ≠ FLAG → c.sl FLAG + 8 ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl FLAG :=
      fun hj hjf => by have := sl_apart c (Ne.symm hjf) (i := FLAG); omega
    rw [O₄'.word (hap (j := QY) (by decide) (by decide)) (by omega),
      O₂.word (hap (j := BP) (by decide) (by decide)) (by omega),
      O₁.word (hap (j := R2P) (by decide) (by decide)) (by omega)]
  refine ⟨hs₆.of_keepRegs k₇ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((k₁.trans k₂).mono (by sub_regs)).trans ((Keeps.regs k₃).mono (by sub_regs))).trans
      ((k₄.mono (by sub_regs)).trans (k₅.trans ((k₆.trans k₇).mono (by sub_regs)))))
  · have U := ((((O₁.unch.trans O₂.unch).trans O₄'.unch).trans O₅.unch).trans
      O₆.unch).trans O₇.unch
    refine U.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.map_cons, List.map_nil, slW] at hw ⊢
    grind
  · show wordsVal s₇.mem _ _ _ = _
    rw [v₇ (i := R2P) (by decide) (by decide), sv_out O₄' h7 hn (by decide) (by decide),
      sv_out O₂ h7 hn (by decide) (by decide), e₁]
  · show wordsVal s₇.mem _ _ _ = _
    rw [v₇ (i := BP) (by decide) (by decide), sv_out O₄' h7 hn (by decide) (by decide), e₂]
  · show wordsVal s₇.mem _ _ _ = _
    rw [v₇ (i := QY) (by decide) (by decide), e₄, e₃, k₃.mem]
    congr 1
    exact bytesAt_keep (O₁.mono (Nat.zero_le _) (by omega) |>.trans (O₂.mono (Nat.zero_le _) (by omega)))
      (hd.sub_left (Offset.sub_base q (by omega))) (by omega) (by omega)
  · have mp₅ : wordsVal s₅.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₅ h0 h7 hn (i := MP) (by decide) (by decide)]
      exact (v₄ (i := MP) (by decide) (by decide) (by decide) (by decide)).trans hmp
    have mp₆ : wordsVal s₆.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₆ h0 h7 hn (i := MP) (by decide) (by decide)]; exact mp₅
    have e₅ : wordsVal s₅.mem base (c.sl E) c.n = sv c base s E := by
      rw [sv_flag O₅ h0 h7 hn (i := E) (by decide) (by decide)]
      exact v₄ (by decide) (by decide) (by decide) (by decide)
    have y₆ : wordsVal s₆.mem base (c.sl QY) c.n = wordsVal s₇.mem base (c.sl QY) c.n :=
      (sv_flag O₇ h0 h7 hn (i := QY) (by decide) (by decide)).symm
    show _ = _ &&& _ &&& mask (wordsVal s.mem base (c.sl E) c.n < c.C.p) &&&
      mask (wordsVal s₇.mem base (c.sl QY) c.n < c.C.p)
    rw [f₇, f₆, f₅, flag₄, hq0, e₅, mp₅, y₆, mp₆]

end VG.Proof.Ecdh.AArch64
