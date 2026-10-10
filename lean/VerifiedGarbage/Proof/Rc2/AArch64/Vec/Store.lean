import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Load
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Storing a group of eight blocks

`scatter_ok`: `tbl` scatters the sets' words back into blocks, blocks `4 h +
2 k` and `4 h + 2 k + 1` into `v(2 h + k)` (`outIndex`). `xorStore_ok`: each
XORed with the ciphertext block before it and stored in place.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- Byte `j` of a block with words `r` (`Spec.Rc2.encodeBlock`). -/
def encByte (r : Spec.Rc2.State) (j : Nat) : BitVec 8 :=
  ((r.getD (j / 2) 0) >>> (8 * (j % 2))).setWidth 8

theorem encodeBlock_getElem (r : Spec.Rc2.State) {j : Nat} (hj : j < 8) :
    (Spec.Rc2.encodeBlock r)[j] = encByte r j := by
  simp [Spec.Rc2.encodeBlock, encByte]

theorem exec_tbl4 (s : State) (d n m : VReg) :
    exec (.vop (.tblN false 4 d n m)) s = some (s.setV d (ofVBytes fun e =>
      if (vbyte (s.v m) e).toNat < 16 * 4 then tableByte s.v n (vbyte (s.v m) e).toNat else 0)) :=
  rfl

/-- The low two bytes of a lane, from its low 16 bits. -/
theorem vbyte_lw (x : BitVec 128) (b : Nat) {c : Nat} (hc : c < 2) :
    vbyte x (4 * b + c) = ((lw x b) >>> (8 * c)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, lw, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and]
  simp [show 8 * c + t < 16 by omega_arith, show 8 * c + t < 32 by omega_arith,
    show 8 * (4 * b + c) + t = 32 * b + (8 * c + t) by omega_arith]

theorem outIndex_byte (k : Nat) (hk : k < 2) {e : Nat} (he : e < 16) :
    (vbyte (outIndex k) e).toNat = 16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2 := by
  rw [outIndex, vbyte_ofVBytes _ he, BitVec.toNat_ofNat]
  omega_arith

theorem repeat_wreg : ∀ h < 2, ∀ w < 4, Nat.repeat VReg.succ w (wreg h 0) = wreg h w := by
  decide

/-- Byte `e` of `tbl` of set `h` at `outIndex k`: byte `e % 8` of block `4 h + 2 k + e / 8`. -/
theorem scatter_byte {v : VReg → BitVec 128} {h k : Nat} (hh : h < 2) (hk : k < 2)
    (hix : v .v4 = outIndex k) {R : Nat → Spec.Rc2.State}
    (hw : ∀ i < 4, ∀ b < 4, lw (v (wreg h i)) b = (R (4 * h + b)).getD i 0) {e : Nat} (he : e < 16) :
    vbyte (ofVBytes fun e =>
      if (vbyte (v .v4) e).toNat < 16 * 4 then tableByte v (wreg h 0) (vbyte (v .v4) e).toNat else 0) e =
      encByte (R (4 * h + 2 * k + e / 8)) (e % 8) := by
  rw [vbyte_ofVBytes _ he, hix, outIndex_byte k hk he,
    ite_eq_left (show 16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2 < 16 * 4 by omega_arith), tableByte,
    show (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2) / 16 = e % 8 / 2 by omega_arith,
    show (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2) % 16 = 4 * (2 * k + e / 8) + e % 2 by omega_arith,
    repeat_wreg h hh _ (by omega_arith), vbyte_lw _ _ (by omega_arith), hw _ (by omega_arith) _ (by omega_arith), encByte,
    show 4 * h + (2 * k + e / 8) = 4 * h + 2 * k + e / 8 by omega_arith,
    show e % 8 % 2 = e % 2 by omega_arith]

/-- The scattering: the blocks into `v0`–`v3`. -/
def scatterCode : List Instr :=
  const128 .v4 (outIndex 0) ++
  [.vop (.tblN false 4 .v0 (wreg 0 0) .v4), .vop (.tblN false 4 .v2 (wreg 1 0) .v4)] ++
  const128 .v4 (outIndex 1) ++
  [.vop (.tblN false 4 .v1 (wreg 0 0) .v4), .vop (.tblN false 4 .v3 (wreg 1 0) .v4)]

/-- The XOR with the ciphertext blocks, and the stores. -/
def xorCode : List Instr :=
  [.ldr .x .x9 .x1 0, .vop (.ins .d2 .v4 0 .x11), .vop (.ins .d2 .v4 1 .x9),
   .addImm .x .x12 .x1 8, .ldrq .v5 .x12 0,
   .vop (.logic .eor .v0 .v0 .v4), .vop (.logic .eor .v1 .v1 .v5),
   .ldrq .v4 .x12 16, .ldrq .v5 .x12 32,
   .vop (.logic .eor .v2 .v2 .v4), .vop (.logic .eor .v3 .v3 .v5),
   .ldr .x .x11 .x1 56,
   .strq .v0 .x1 0, .strq .v1 .x1 16, .strq .v2 .x1 32, .strq .v3 .x1 48]

theorem storeGroup_eq : storeGroup = scatterCode ++ xorCode := by
  simp only [storeGroup, scatterCode, xorCode, List.append_assoc, List.cons_append, List.nil_append]

/-- Byte `e` of `v0`–`v3` after the scattering: byte `16 c + e` of the eight blocks. -/
def Scattered (v : VReg → BitVec 128) (R : Nat → Spec.Rc2.State) : Prop :=
  ∀ e < 16, vbyte (v .v0) e = encByte (R (e / 8)) (e % 8) ∧
    vbyte (v .v1) e = encByte (R (2 + e / 8)) (e % 8) ∧
    vbyte (v .v2) e = encByte (R (4 + e / 8)) (e % 8) ∧
    vbyte (v .v3) e = encByte (R (6 + e / 8)) (e % 8)

theorem scatter_ok (t : State) {R : Nat → Spec.Rc2.State} (hS : Sets t R) :
    WP isa (.block scatterCode) t fun t' => Scattered t'.v R ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → t'.v w = t.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  rw [scatterCode, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const128_ok t .v4 (outIndex 0)) fun a ⟨a4, av, ag, am, ard, awr, asp⟩ => ?_
  let c₁ := a.setV .v0 (ofVBytes fun e => if (vbyte (a.v .v4) e).toNat < 16 * 4 then
    tableByte a.v (wreg 0 0) (vbyte (a.v .v4) e).toNat else 0)
  let c₂ := c₁.setV .v2 (ofVBytes fun e => if (vbyte (c₁.v .v4) e).toNat < 16 * 4 then
    tableByte c₁.v (wreg 1 0) (vbyte (c₁.v .v4) e).toNat else 0)
  refine WP.of_runBlock ⟨c₂, by
    rw [runBlock_cons, exec_tbl4, runStep_some, runBlock_cons, exec_tbl4, runStep_some,
      runBlock_nil], ?_⟩
  refine WP.mono (const128_ok c₂ .v4 (outIndex 1)) fun b ⟨b4, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  let d₁ := b.setV .v1 (ofVBytes fun e => if (vbyte (b.v .v4) e).toNat < 16 * 4 then
    tableByte b.v (wreg 0 0) (vbyte (b.v .v4) e).toNat else 0)
  let d₂ := d₁.setV .v3 (ofVBytes fun e => if (vbyte (d₁.v .v4) e).toNat < 16 * 4 then
    tableByte d₁.v (wreg 1 0) (vbyte (d₁.v .v4) e).toNat else 0)
  refine WP.of_runBlock ⟨d₂, by
    rw [runBlock_cons, exec_tbl4, runStep_some, runBlock_cons, exec_tbl4, runStep_some,
      runBlock_nil], ?_⟩
  -- The sets, kept until the end.
  have ws : ∀ h < 2, ∀ i < 4, a.v (wreg h i) = t.v (wreg h i) ∧ c₁.v (wreg h i) = t.v (wreg h i) ∧
      b.v (wreg h i) = t.v (wreg h i) ∧ d₁.v (wreg h i) = t.v (wreg h i) := by
    intro h hh i hi
    have wn := wreg_ne h i hh
    have e₁ : a.v (wreg h i) = t.v (wreg h i) := av _ wn.2.2.2.2.1
    have e₂ : c₁.v (wreg h i) = t.v (wreg h i) := by
      simp only [c₁, v_setV_of_ne _ _ wn.1]; exact e₁
    have e₃ : b.v (wreg h i) = t.v (wreg h i) := by
      rw [bv _ wn.2.2.2.2.1]; simp only [c₂, v_setV_of_ne _ _ wn.2.2.1]; exact e₂
    refine ⟨e₁, e₂, e₃, ?_⟩
    simp only [d₁, v_setV_of_ne _ _ wn.2.1]; exact e₃
  have hw : ∀ (f : VReg → BitVec 128), (∀ h < 2, ∀ i < 4, f (wreg h i) = t.v (wreg h i)) →
      ∀ h < 2, ∀ i < 4, ∀ b < 4, lw (f (wreg h i)) b = (R (4 * h + b)).getD i 0 :=
    fun f hf h hh i hi b hb => by rw [hf h hh i hi]; exact hS h hh i hi b hb
  have c4 : c₁.v .v4 = outIndex 0 := by simp only [c₁, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v0)]; exact a4
  have d4 : d₁.v .v4 = outIndex 1 := by simp only [d₁, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1)]; exact b4
  refine ⟨fun e he => ⟨?_, ?_, ?_, ?_⟩, fun w h0 h1 h2 h3 h4 => ?_, fun g h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · have : d₂.v .v0 = c₁.v .v0 := by
      simp only [d₂, d₁, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
      rw [bv _ (by decide)]; simp only [c₂, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2)]
    rw [this, show c₁.v .v0 = _ from v_setV_self _ _ _,
      scatter_byte (h := 0) (k := 0) (by decide) (by decide) a4
        (hw a.v (fun h hh i hi => (ws h hh i hi).1) 0 (by decide)) he,
      show 4 * 0 + 2 * 0 + e / 8 = e / 8 by omega_arith]
  · rw [show d₂.v .v1 = d₁.v .v1 from v_setV_of_ne _ _ (by decide),
      show d₁.v .v1 = _ from v_setV_self _ _ _,
      scatter_byte (h := 0) (k := 1) (by decide) (by decide) b4
        (hw b.v (fun h hh i hi => (ws h hh i hi).2.2.1) 0 (by decide)) he]
  · have : d₂.v .v2 = c₂.v .v2 := by
      simp only [d₂, d₁, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v1)]
      exact bv _ (by decide)
    rw [this, show c₂.v .v2 = _ from v_setV_self _ _ _,
      scatter_byte (h := 1) (k := 0) (by decide) (by decide) c4
        (hw c₁.v (fun h hh i hi => (ws h hh i hi).2.1) 1 (by decide)) he]
  · rw [show d₂.v .v3 = _ from v_setV_self _ _ _,
      scatter_byte (h := 1) (k := 1) (by decide) (by decide) d4
        (hw d₁.v (fun h hh i hi => (ws h hh i hi).2.2.2) 1 (by decide)) he]
  · simp only [d₂, d₁, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h1]
    rw [bv _ h4]
    simp only [c₂, c₁, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h0]
    exact av _ h4
  · simp only [d₂, d₁, gpr_setV]; rw [bg g h6 h7]; simp only [c₂, c₁, gpr_setV]; exact ag g h6 h7
  · simp only [d₂, d₁, mem_setV]; rw [bm]; simp only [c₂, c₁, mem_setV]; exact am
  · simp only [d₂, d₁, rd_setV]; rw [brd]; simp only [c₂, c₁, rd_setV]; exact ard
  · simp only [d₂, d₁, wr_setV]; rw [bwr]; simp only [c₂, c₁, wr_setV]; exact awr
  · simp only [d₂, d₁, sp_setV]; rw [bsp]; simp only [c₂, c₁, sp_setV]; exact asp

theorem exec_addImmx (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp [exec, State.read, h]

theorem exec_strq (s : State) (t : VReg) (n : Reg) (off : Nat) (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.store, h,
    Option.bind_some]

/-- A 16-byte write at offset `d`, read at offset `j`. -/
theorem write16_at (m : Mem) (q : Addr) {d j : Nat} (hd : d + 16 ≤ 64) (hj : j < 64)
    (v : BitVec (8 * 16)) :
    (m.write (q + BitVec.ofNat 64 d) 16 v) (q + BitVec.ofNat 64 j) =
      if d ≤ j ∧ j < d + 16 then vbyte v (j - d) else m (q + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.add_sub_add_left]
  by_cases h : d ≤ j ∧ j < d + 16
  · rw [Offset.ofNat_sub_ofNat h.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    simp only [show j - d < 16 by omega_arith, h, and_self, ite_true]
    rfl
  · have : ¬ (BitVec.ofNat 64 j - BitVec.ofNat 64 d).toNat < 16 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    simp only [this, h, ite_false]

theorem write4_at (m : Mem) (q : Addr) (V0 V1 V2 V3 : BitVec (8 * 16)) {o : Nat} (ho : o < 64) :
    ((((m.write (q + BitVec.ofNat 64 0) 16 V0).write (q + BitVec.ofNat 64 16) 16 V1).write
      (q + BitVec.ofNat 64 32) 16 V2).write (q + BitVec.ofNat 64 48) 16 V3) (q + BitVec.ofNat 64 o) =
      vbyte (if o < 16 then V0 else if o < 32 then V1 else if o < 48 then V2 else V3) (o % 16) := by
  rw [write16_at _ _ (by decide) ho, write16_at _ _ (by decide) ho, write16_at _ _ (by decide) ho,
    write16_at _ _ (by decide) ho]
  rcases (by omega_arith : o < 16 ∨ (16 ≤ o ∧ o < 32) ∨ (32 ≤ o ∧ o < 48) ∨ 48 ≤ o) with h | h | h | h <;>
    simp (disch := omega_arith) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega_arith)

theorem vbyte_ofVDwords (a b : BitVec 64) {e : Nat} (he : e < 16) :
    vbyte (ofVDwords a b) e =
      if e < 8 then a.extractLsb' (8 * e) 8 else b.extractLsb' (8 * (e - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, ofVDwords, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : e < 8
  · simp only [h, ite_true, show 8 * e + t < 64 by omega_arith, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 8 * e + t < 64 by omega_arith, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and, show 8 * e + t - 64 = 8 * (e - 8) + t by omega_arith]

/-- The ciphertext byte before byte `o` of the group: the chaining value's
in the first block. -/
def prevByte (X : BitVec 64) (m : Mem) (q : Addr) (o : Nat) : BitVec 8 :=
  if o < 8 then X.extractLsb' (8 * o) 8 else m (q + BitVec.ofNat 64 (o - 8))

theorem xorStore_ok (t : State) {R : Nat → Spec.Rc2.State} (hsc : Scattered t.v R)
    (hrd : InRegions (t.rd ++ t.wr) (t.gpr .x1) 64) (hwr : InRegions t.wr (t.gpr .x1) 64) :
    ∃ t', runBlock isa xorCode t = some t' ∧
      (∀ o < 64, t'.mem (t.gpr .x1 + BitVec.ofNat 64 o) =
        encByte (R (o / 8)) (o % 8) ^^^ prevByte (t.gpr .x11) t.mem (t.gpr .x1) o) ∧
      Frame [⟨t.gpr .x1, 64⟩] t.mem t'.mem ∧
      t'.gpr .x11 = t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 56) 64 ∧
      (∀ g, g ≠ .x9 → g ≠ .x11 → g ≠ .x12 → t'.gpr g = t.gpr g) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 → t'.v w = t.v w) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  let q := t.gpr .x1
  let M := t.mem
  let X := t.gpr .x11
  have rd : ∀ off, off + 16 ≤ 64 → InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 off) 16 :=
    fun off h => CallLay.inRegions_sub hrd h (by decide)
  let d₁ := t.write .x .x9 (t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 0) 64)
  let d₂ := d₁.setV .v4 (setLane (d₁.v .v4) 64 0 (d₁.gpr .x11))
  let d₃ := d₂.setV .v4 (setLane (d₂.v .v4) 64 1 (d₂.gpr .x9))
  let d₄ := d₃.write .x .x12 (d₃.gpr .x1 + BitVec.ofNat 64 8)
  let d₅ := d₄.setV .v5 (d₄.mem.read (d₄.gpr .x12 + BitVec.ofNat 64 0) 16)
  let d₆ := d₅.setV .v0 (d₅.v .v0 ^^^ d₅.v .v4)
  let d₇ := d₆.setV .v1 (d₆.v .v1 ^^^ d₆.v .v5)
  let d₈ := d₇.setV .v4 (d₇.mem.read (d₇.gpr .x12 + BitVec.ofNat 64 16) 16)
  let d₉ := d₈.setV .v5 (d₈.mem.read (d₈.gpr .x12 + BitVec.ofNat 64 32) 16)
  let d₁₀ := d₉.setV .v2 (d₉.v .v2 ^^^ d₉.v .v4)
  let d₁₁ := d₁₀.setV .v3 (d₁₀.v .v3 ^^^ d₁₀.v .v5)
  let d₁₂ := d₁₁.write .x .x11 (d₁₁.mem.readW (d₁₁.gpr .x1 + BitVec.ofNat 64 56) 64)
  let d₁₃ : State := { d₁₂ with mem := d₁₂.mem.write (d₁₂.gpr .x1 + BitVec.ofNat 64 0) 16 (d₁₂.v .v0) }
  let d₁₄ : State := { d₁₃ with mem := d₁₃.mem.write (d₁₃.gpr .x1 + BitVec.ofNat 64 16) 16 (d₁₃.v .v1) }
  let d₁₅ : State := { d₁₄ with mem := d₁₄.mem.write (d₁₄.gpr .x1 + BitVec.ofNat 64 32) 16 (d₁₄.v .v2) }
  let d₁₆ : State := { d₁₅ with mem := d₁₅.mem.write (d₁₅.gpr .x1 + BitVec.ofNat 64 48) 16 (d₁₅.v .v3) }
  -- The general registers along the way.
  have x1₄ : d₄.gpr .x1 = q := by
    simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x12), gpr_setV,
      gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x9)]; rfl
  have x12₄ : d₄.gpr .x12 = q + BitVec.ofNat 64 8 := by
    simp only [d₄, gpr_write_self, BitVec.setWidth_eq]
    rw [show d₃.gpr .x1 = d₄.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₄]
  have x1₁₂ : d₁₂.gpr .x1 = q := by
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x11),
      gpr_setV]; exact x1₄
  have x12₇ : d₇.gpr .x12 = q + BitVec.ofNat 64 8 := by
    simp only [d₇, d₆, d₅, gpr_setV]; exact x12₄
  have e₁ : exec (.ldr .x .x9 .x1 0) t = some d₁ :=
    exec_ldr_x ⟨by decide, by decide⟩ (CallLay.inRegions_sub hrd (by decide : 0 + 8 ≤ 64) (by decide))
  have e₄ : exec (.addImm .x .x12 .x1 8) d₃ = some d₄ := exec_addImmx _ _ _ (by decide)
  have e₅ : exec (.ldrq .v5 .x12 0) d₄ = some d₅ := exec_ldrq' d₄ _ _ 0 ⟨by decide, by decide⟩
    (by rw [x12₄, Offset.add_add]; exact rd _ (by decide))
  have e₈ : exec (.ldrq .v4 .x12 16) d₇ = some d₈ := exec_ldrq' d₇ _ _ 16 ⟨by decide, by decide⟩
    (by rw [x12₇, Offset.add_add]; exact rd _ (by decide))
  have e₉ : exec (.ldrq .v5 .x12 32) d₈ = some d₉ := exec_ldrq' d₈ _ _ 32 ⟨by decide, by decide⟩
    (by rw [show d₈.gpr .x12 = d₇.gpr .x12 from rfl, x12₇, Offset.add_add]; exact rd _ (by decide))
  have e₁₂ : exec (.ldr .x .x11 .x1 56) d₁₁ = some d₁₂ := exec_ldr_x ⟨by decide, by decide⟩
    (by
      rw [show d₁₁.gpr .x1 = d₁₂.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₁₂]
      exact CallLay.inRegions_sub hrd (by decide : 56 + 8 ≤ 64) (by decide))
  have wr : ∀ off, off + 16 ≤ 64 → InRegions d₁₂.wr (d₁₂.gpr .x1 + BitVec.ofNat 64 off) 16 :=
    fun off h => by rw [x1₁₂]; exact CallLay.inRegions_sub hwr h (by decide)
  have e₁₃ : exec (.strq .v0 .x1 0) d₁₂ = some d₁₃ := exec_strq _ _ _ 0 ⟨by decide, by decide⟩ (wr 0 (by decide))
  have e₁₄ : exec (.strq .v1 .x1 16) d₁₃ = some d₁₄ := exec_strq _ _ _ 16 ⟨by decide, by decide⟩ (wr 16 (by decide))
  have e₁₅ : exec (.strq .v2 .x1 32) d₁₄ = some d₁₅ := exec_strq _ _ _ 32 ⟨by decide, by decide⟩ (wr 32 (by decide))
  have e₁₆ : exec (.strq .v3 .x1 48) d₁₅ = some d₁₆ := exec_strq _ _ _ 48 ⟨by decide, by decide⟩ (wr 48 (by decide))
  have run : runBlock isa xorCode t = some d₁₆ := by
    rw [xorCode, runBlock_cons, e₁, runStep_some, runBlock_cons, exec_insd _ _ _ (by decide),
      runStep_some, runBlock_cons, exec_insd _ _ _ (by decide), runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, exec_eorv, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_cons, e₉,
      runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, e₁₂, runStep_some, runBlock_cons, e₁₃, runStep_some, runBlock_cons, e₁₄,
      runStep_some, runBlock_cons, e₁₅, runStep_some, runBlock_cons, e₁₆, runStep_some, runBlock_nil]
  -- The values stored.
  have V0 : d₁₂.v .v0 = t.v .v0 ^^^ ofVDwords X (M.readW (q + BitVec.ofNat 64 0) 64) := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq,
      setLane_two] <;> rfl
  have V1 : d₁₂.v .v1 = t.v .v1 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 0) 16 := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  have V2 : d₁₂.v .v2 = t.v .v2 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 16) 16 := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  have V3 : d₁₂.v .v3 = t.v .v3 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 32) 16 := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  have mem : d₁₆.mem = (((M.write (q + BitVec.ofNat 64 0) 16 (d₁₂.v .v0)).write
      (q + BitVec.ofNat 64 16) 16 (d₁₂.v .v1)).write (q + BitVec.ofNat 64 32) 16 (d₁₂.v .v2)).write
      (q + BitVec.ofNat 64 48) 16 (d₁₂.v .v3) := by
    simp only [d₁₆, d₁₅, d₁₄, d₁₃, x1₁₂]
    rfl
  refine ⟨d₁₆, run, fun o ho => ?_, ?_, ?_, fun g h9 h11 h12 => ?_, fun w h0 h1 h2 h3 h4 h5 => ?_,
    rfl, rfl, rfl⟩
  · rw [mem, write4_at _ _ _ _ _ _ ho, prevByte]
    rcases (by omega_arith : o < 16 ∨ (16 ≤ o ∧ o < 32) ∨ (32 ≤ o ∧ o < 48) ∨ 48 ≤ o) with h | h | h | h <;>
      simp (disch := omega_arith) only [ite_eq_left, ite_eq_right]
    · rw [V0, vbyte_xor, (hsc _ (by omega_arith)).1, vbyte_ofVDwords _ _ (by omega_arith),
        show o % 16 = o by omega_arith]
      by_cases h8 : o < 8
      · simp only [h8, ite_true] <;> rfl
      · simp only [h8, ite_false]
        rw [read64_byte _ _ _ (by omega_arith), Offset.add_add, show 0 + (o - 8) = o - 8 by omega_arith]
    · rw [V1, vbyte_xor, (hsc _ (by omega_arith)).2.1, vbyte_read _ _ (by omega_arith), Offset.add_add,
        Offset.add_add, show o / 8 = 2 + o % 16 / 8 by omega_arith, show o % 8 = o % 16 % 8 by omega_arith,
        show 8 + (0 + o % 16) = o - 8 by omega_arith]
    · rw [V2, vbyte_xor, (hsc _ (by omega_arith)).2.2.1, vbyte_read _ _ (by omega_arith), Offset.add_add,
        Offset.add_add, show o / 8 = 4 + o % 16 / 8 by omega_arith, show o % 8 = o % 16 % 8 by omega_arith,
        show 8 + (16 + o % 16) = o - 8 by omega_arith]
    · rw [V3, vbyte_xor, (hsc _ (by omega_arith)).2.2.2, vbyte_read _ _ (by omega_arith), Offset.add_add,
        Offset.add_add, show o / 8 = 6 + o % 16 / 8 by omega_arith, show o % 8 = o % 16 % 8 by omega_arith,
        show 8 + (32 + o % 16) = o - 8 by omega_arith]
  · rw [mem]
    have c : ∀ d, d + 16 ≤ 64 → (⟨q, 64⟩ : Region).Contains (q + BitVec.ofNat 64 d) 16 :=
      fun d h => Offset.contains_base q h (by omega_arith)
    exact (((((Frame.refl _ M).write (List.mem_singleton_self _) _ (c 0 (by decide))).write
      (List.mem_singleton_self _) _ (c 16 (by decide))).write (List.mem_singleton_self _) _
      (c 32 (by decide))).write (List.mem_singleton_self _) _ (c 48 (by decide)))
  · show d₁₂.gpr .x11 = _
    simp only [d₁₂, gpr_write_self, BitVec.setWidth_eq]
    rw [show d₁₁.gpr .x1 = d₁₂.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₁₂]
    rfl
  · show d₁₂.gpr g = t.gpr g
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ h11, gpr_setV,
      gpr_write_of_ne _ _ _ h12, gpr_write_of_ne _ _ _ h9]
  · show d₁₂.v w = t.v w
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ h0,
      v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h4,
      v_setV_of_ne _ _ h5]

end VG.Proof.Rc2.AArch64.Vec
