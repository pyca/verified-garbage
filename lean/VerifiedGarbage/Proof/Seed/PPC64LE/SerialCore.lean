module

public import VerifiedGarbage.Proof.Seed.PPC64LE.SerialSbox
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorBytes
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Seed.G
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModeCore
public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Proof.Modes.PPC64LE.Wide
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap

/-!
# The single-block SEED core on PPC64LE

* `gA_run`, `gB_run`, `gFn_run`: `G` (`Serial.gFn`): the S-boxes of the
  word's bytes through the AES S-box (`s0_affine`, `s1_affine`), then the
  masks and the XOR of each byte's images (`Proof.Seed.getLsbD_g`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.Serial

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.PPC64LE.Bytes
open VG.Impl.Seed.PPC64LE.Serial
open VG.Spec.Seed (Direction)

/-! ## Bytes -/

theorem gbyte_mask {k : Nat} (hk : k < 4) : gbyte 0x0f0f0f0f k = 0x0f := by
  rcases k with _ | _ | _ | _ | k
  all_goals first | decide | omega

/-- The high nibble of each byte of the low word, by the word's shift right
by 4, masked. -/
theorem gbyte_lsr4 (x : BitVec 64) {k : Nat} (hk : k < 4) :
    gbyte ((x.setWidth 32 >>> 4).setWidth 64 &&& 0x0f0f0f0f) k = gbyte x k >>> 4 := by
  rw [gbyte_and, gbyte_mask hk]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rcases k with _ | _ | _ | _ | k <;> rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | omega | simp

theorem vbyte_and' (a b : BitVec 128) (i : Nat) : vbyte (a &&& b) i = vbyte a i &&& vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hj, decide_true, Bool.true_and]

/-- `vsldoi` of a register with itself rotates its bytes. -/
theorem vbyte_sldoi (v : BitVec 128) {sh i : Nat} (hsh : sh < 16) (hi : i < 16) :
    vbyte (((v ++ v) <<< (8 * sh)).extractLsb' 128 128) i = vbyte v ((i + sh) % 16) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hj,
    decide_true, Bool.true_and]
  by_cases h : i + sh < 16
  · rw [Nat.mod_eq_of_lt h]
    simp only [show 128 + (8 * (15 - i) + j) < 128 + 128 by omega, show ¬ 128 + (8 * (15 - i) + j) < 8 * sh by omega,
      show ¬ 128 + (8 * (15 - i) + j) - 8 * sh < 128 by omega, decide_true, decide_false, Bool.not_false,
      Bool.true_and, ite_false, show 8 * (15 - i) + j < 128 by omega]
    exact congrArg v.getLsbD (by omega)
  · rw [show (i + sh) % 16 = i + sh - 16 by omega]
    simp only [show 128 + (8 * (15 - i) + j) < 128 + 128 by omega, show ¬ 128 + (8 * (15 - i) + j) < 8 * sh by omega,
      show 128 + (8 * (15 - i) + j) - 8 * sh < 128 by omega, decide_true, decide_false, Bool.not_false,
      Bool.true_and, ite_true, show 8 * (15 - i) + j < 128 by omega]
    exact congrArg v.getLsbD (by omega)

theorem exec_vsldoi8 {s : State} {d n m : VReg} :
    exec (.vop (.sldoi d n m 8)) s = some (s.writeV d (((s.vpr n ++ s.vpr m) <<< (8 * 8)).extractLsb' 128 128)) :=
  rfl

theorem exec_vsldoi4 {s : State} {d n m : VReg} :
    exec (.vop (.sldoi d n m 4)) s = some (s.writeV d (((s.vpr n ++ s.vpr m) <<< (8 * 4)).extractLsb' 128 128)) :=
  rfl

theorem exec_vand {s : State} {d n m : VReg} :
    exec (.vop (.logic .and d n m)) s = some (s.writeV d (s.vpr n &&& s.vpr m)) := rfl

theorem exec_and {s : State} {d n m : Reg} :
    exec (.logic .and d n m) s = some (s.write d (s.gpr n &&& s.gpr m)) := rfl

/-- A lookup by `vperm` in one of two tables, the choice in bit 4 of the
index (`sel`, `0` or `0x10`), its low bits a nibble. -/
theorem lookup_sel {T U c : BitVec 128} {t u : Vector Byte 16} (hT : TabOk T t) (hU : TabOk U u)
    {i : Nat} (hi : i < 16) {y sel : Byte} (hy : y.toNat < 16) (hc : vbyte c i = y ||| sel)
    (hs : sel = 0 ∨ sel = 0x10) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte c i).toNat % 32
      if j < 16 then vbyte T j else vbyte U (j - 16)) i =
      if sel = 0x10 then u.getD y.toNat 0 else t.getD y.toNat 0 := by
  rcases hs with rfl | rfl
  · have e : (vbyte c i).toNat = y.toNat := by rw [hc]; simp
    rw [vperm_byte2 hT hU hi (by omega), e]; simp [hy]
  · have e : (vbyte c i).toNat = y.toNat + 16 := by rw [hc, toNat_or_16 hy]
    rw [vperm_byte2 hT hU hi (by omega), e]
    simp only [show ¬(y.toNat + 16 < 16) by omega, ite_false, Nat.add_sub_cancel, ite_true]

/-! ## The constants -/

/-- What the core keeps in registers: the tables in `treg 0 … 8` and the
mask in `r12`. -/
structure Consts (s : State) : Prop where
  tab : ∀ k < 9, TabOk (s.vpr (treg k)) (tables.getD k inLo)
  nib : s.gpr .r12 = 0x0f0f0f0f

theorem treg_ne : ∀ k < 9, treg k ≠ .v0 ∧ treg k ≠ .v1 := by decide

theorem Consts.of_eq {s t : State} (h : Consts s) (hv : ∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v)
    (hg : t.gpr .r12 = s.gpr .r12) : Consts t :=
  ⟨fun k hk => by rw [hv _ (treg_ne k hk).1 (treg_ne k hk).2]; exact h.tab k hk, by rw [hg]; exact h.nib⟩

/-- The tables, by register. -/
theorem Consts.t {s : State} (h : Consts s) :
    TabOk (s.vpr .v8) inLo ∧ TabOk (s.vpr .v9) inHi ∧ TabOk (s.vpr .v10) out0Lo ∧ TabOk (s.vpr .v11) out1Lo ∧
    TabOk (s.vpr .v12) out0Hi ∧ TabOk (s.vpr .v13) out1Hi ∧ TabOk (s.vpr .v14) selOut ∧
    TabOk (s.vpr .v15) bidx ∧ TabOk (s.vpr .v16) mask :=
  ⟨h.tab 0 (by decide), h.tab 1 (by decide), h.tab 2 (by decide), h.tab 3 (by decide), h.tab 4 (by decide),
    h.tab 5 (by decide), h.tab 6 (by decide), h.tab 7 (by decide), h.tab 8 (by decide)⟩

theorem selOut_eq {k : Nat} (hk : k < 4) : selOut.getD (7 - k) 0 = if k = 1 ∨ k = 3 then 0x10 else 0 := by
  rcases k with _ | _ | _ | _ | k
  all_goals first | decide | omega

theorem sel_cases (p : Prop) [Decidable p] : ((if p then 0x10 else 0 : Byte) = 0 ∨ (if p then 0x10 else 0 : Byte) = 0x10) := by
  by_cases h : p <;> simp [h]

theorem sel_iff (p : Prop) [Decidable p] : ((if p then 0x10 else 0 : Byte) = 0x10) ↔ p := by
  by_cases h : p <;> simp [h]

theorem bidx_eq : ∀ i < 16, (bidx.getD i 0).toNat = 7 - i / 4 := by decide

/-! ## G -/

/-- `G`'s first half: the AES S-box of `A_in` of the bytes of `x`'s low word. -/
def gA (x : Reg) : List Instr :=
  nibbles x ++
  [.mtvsrd .v0 .r0, .mtvsrd .v1 .r11,
   .vop (.perm .v0 .v8 .v8 .v0), .vop (.perm .v1 .v9 .v9 .v1), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.sbox .v0 .v0), .mfvsrd x .v0]

/-- `G`'s second half: the output maps, the masks and the sums. -/
def gB (x : Reg) : List Instr :=
  nibbles x ++
  [.mtvsrd .v0 .r0, .mtvsrd .v1 .r11,
   .vop (.logic .or .v0 .v0 .v14), .vop (.logic .or .v1 .v1 .v14),
   .vop (.perm .v0 .v10 .v11 .v0), .vop (.perm .v1 .v12 .v13 .v1), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.perm .v0 .v0 .v0 .v15), .vop (.logic .and .v0 .v0 .v16),
   .vop (.sldoi .v1 .v0 .v0 8), .vop (.logic .xor .v0 .v0 .v1),
   .vop (.sldoi .v1 .v0 .v0 4), .vop (.logic .xor .v0 .v0 .v1), .mfvsrd x .v0]

theorem gFn_eq (x : Reg) : gFn x = gA x ++ gB x := by
  simp only [gFn, gA, gB, List.append_assoc, List.cons_append, List.nil_append]

theorem gA_run (s : State) (hc : Consts s) {x : Reg} (hx : x ≠ .r0 ∧ x ≠ .r11 ∧ x ≠ .r12) :
    ∃ t, runBlock isa (gA x) s = some t ∧
      (∀ k < 4, gbyte (t.gpr x) k = Spec.Aes.sbox (aff inLo inHi (gbyte (s.gpr x) k))) ∧
      (∀ r, r ≠ x → r ≠ .r0 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have T := hc.t
  let a := s.write .r0 (s.gpr x &&& s.gpr .r12)
  let b := a.write .r11 (((a.gpr x).setWidth 32 >>> 4).setWidth 64)
  let c := b.write .r11 (b.gpr .r11 &&& b.gpr .r12)
  let d : State := { c.writeV .v0 (c.gpr .r0 ++ c.unknowns 0) with unknowns := fun i => c.unknowns (i + 1) }
  let e : State := { d.writeV .v1 (d.gpr .r11 ++ d.unknowns 0) with unknowns := fun i => d.unknowns (i + 1) }
  let f := e.writeV .v0 (ofVBytes fun i =>
      let j := (vbyte (e.vpr .v0) i).toNat % 32
      if j < 16 then vbyte (e.vpr .v8) j else vbyte (e.vpr .v8) (j - 16))
  let g := f.writeV .v1 (ofVBytes fun i =>
      let j := (vbyte (f.vpr .v1) i).toNat % 32
      if j < 16 then vbyte (f.vpr .v9) j else vbyte (f.vpr .v9) (j - 16))
  let h := g.writeV .v0 (g.vpr .v0 ^^^ g.vpr .v1)
  let l := h.writeV .v0 (ofVBytes fun i => VectorCrypto.aesSbox (vbyte (h.vpr .v0) i))
  let t := l.write x (vdword (l.vpr .v0) 0)
  have ax : a.gpr x = s.gpr x := gpr_write_of_ne _ _ hx.1
  refine ⟨t, ?_, fun k hk => ?_, fun r hrx h0 h11 => ?_, fun v h0 h1 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [gA, nibbles, List.cons_append, List.nil_append, runBlock_cons, exec_and,
      exec_lsr_w (by decide : 4 < 32), exec_mtvsrd, exec_vperm, exec_vxor, exec_vsbox, exec_mfvsrd,
      runStep_some, runBlock_nil]
    rfl
  · have c0 : c.gpr .r0 = s.gpr x &&& s.gpr .r12 := rfl
    have c11 : c.gpr .r11 = ((a.gpr x).setWidth 32 >>> 4).setWidth 64 &&& s.gpr .r12 := rfl
    rw [ax, hc.nib] at c11
    rw [hc.nib] at c0
    have e0 : vbyte (e.vpr .v0) (7 - k) = gbyte (s.gpr x) k &&& 0x0f := by
      show vbyte (c.gpr .r0 ++ c.unknowns 0) (7 - k) = _
      rw [vbyte_append _ _ (by omega), c0, gbyte_and, gbyte_mask hk]
    have f1 : vbyte (f.vpr .v1) (7 - k) = gbyte (s.gpr x) k >>> 4 := by
      show vbyte (c.gpr .r11 ++ d.unknowns 0) (7 - k) = _
      rw [vbyte_append _ _ (by omega), c11, gbyte_lsr4 _ hk]
    have e8 : TabOk (e.vpr .v8) inLo := T.1
    have f9 : TabOk (f.vpr .v9) inHi := T.2.1
    have gv0 : g.vpr .v0 = ofVBytes fun i =>
        let j := (vbyte (e.vpr .v0) i).toNat % 32
        if j < 16 then vbyte (e.vpr .v8) j else vbyte (e.vpr .v8) (j - 16) := rfl
    have gv1 : g.vpr .v1 = ofVBytes fun i =>
        let j := (vbyte (f.vpr .v1) i).toNat % 32
        if j < 16 then vbyte (f.vpr .v9) j else vbyte (f.vpr .v9) (j - 16) := vpr_writeV_self _ _ _
    have hv : vbyte (h.vpr .v0) (7 - k) = aff inLo inHi (gbyte (s.gpr x) k) := by
      rw [show h.vpr .v0 = g.vpr .v0 ^^^ g.vpr .v1 from vpr_writeV_self _ _ _, vbyte_xor', gv0, gv1,
        vperm_byte e8 (by omega) (by rw [e0]; exact toNat_and_0f _),
        vperm_byte f9 (by omega) (by rw [f1]; exact toNat_shr4 _), e0, f1]
      rfl
    have lv0 : l.vpr .v0 = ofVBytes fun i => VectorCrypto.aesSbox (vbyte (h.vpr .v0) i) := vpr_writeV_self _ _ _
    rw [show t.gpr x = vdword (l.vpr .v0) 0 from gpr_write_self _ _ _, gbyte_vdword _ (by omega), lv0,
      vbyte_packed _ (by omega), hv, Proof.Aes.Vector.sbox_eq]
  · rw [gpr_write_of_ne _ _ hrx, show l.gpr r = c.gpr r from rfl, gpr_write_of_ne _ _ h11,
      gpr_write_of_ne _ _ h11, gpr_write_of_ne _ _ h0]
  · change (h.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (g.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (f.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (e.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (d.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (c.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    rfl

/-- The output map of byte `a`: `S2`'s for `X1` and `X3`, `S1`'s otherwise. -/
def outB (y : BitVec 64) (a : Nat) : Byte :=
  if a = 1 ∨ a = 3 then aff out1Lo out1Hi (gbyte y a) else aff out0Lo out0Hi (gbyte y a)

theorem gB_run (s : State) (hc : Consts s) {x : Reg} (hx : x ≠ .r0 ∧ x ≠ .r11 ∧ x ≠ .r12) :
    ∃ t, runBlock isa (gB x) s = some t ∧
      (∀ k < 4, gbyte (t.gpr x) k =
        ((outB (s.gpr x) 1 &&& mask.getD (7 - k) 0) ^^^ (outB (s.gpr x) 3 &&& mask.getD (15 - k) 0)) ^^^
          ((outB (s.gpr x) 2 &&& mask.getD (11 - k) 0) ^^^ (outB (s.gpr x) 0 &&& mask.getD (3 - k) 0))) ∧
      (∀ r, r ≠ x → r ≠ .r0 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  have T := hc.t
  let y := s.gpr x
  let a := s.write .r0 (s.gpr x &&& s.gpr .r12)
  let b := a.write .r11 (((a.gpr x).setWidth 32 >>> 4).setWidth 64)
  let c := b.write .r11 (b.gpr .r11 &&& b.gpr .r12)
  let d : State := { c.writeV .v0 (c.gpr .r0 ++ c.unknowns 0) with unknowns := fun i => c.unknowns (i + 1) }
  let e : State := { d.writeV .v1 (d.gpr .r11 ++ d.unknowns 0) with unknowns := fun i => d.unknowns (i + 1) }
  let f := e.writeV .v0 (e.vpr .v0 ||| e.vpr .v14)
  let g := f.writeV .v1 (f.vpr .v1 ||| f.vpr .v14)
  let h := g.writeV .v0 (ofVBytes fun i =>
      let j := (vbyte (g.vpr .v0) i).toNat % 32
      if j < 16 then vbyte (g.vpr .v10) j else vbyte (g.vpr .v11) (j - 16))
  let i := h.writeV .v1 (ofVBytes fun i =>
      let j := (vbyte (h.vpr .v1) i).toNat % 32
      if j < 16 then vbyte (h.vpr .v12) j else vbyte (h.vpr .v13) (j - 16))
  let j := i.writeV .v0 (i.vpr .v0 ^^^ i.vpr .v1)
  let l := j.writeV .v0 (ofVBytes fun i =>
      let j' := (vbyte (j.vpr .v15) i).toNat % 32
      if j' < 16 then vbyte (j.vpr .v0) j' else vbyte (j.vpr .v0) (j' - 16))
  let n := l.writeV .v0 (l.vpr .v0 &&& l.vpr .v16)
  let o := n.writeV .v1 (((n.vpr .v0 ++ n.vpr .v0) <<< (8 * 8)).extractLsb' 128 128)
  let q := o.writeV .v0 (o.vpr .v0 ^^^ o.vpr .v1)
  let u := q.writeV .v1 (((q.vpr .v0 ++ q.vpr .v0) <<< (8 * 4)).extractLsb' 128 128)
  let w := u.writeV .v0 (u.vpr .v0 ^^^ u.vpr .v1)
  let t := w.write x (vdword (w.vpr .v0) 0)
  have ax : a.gpr x = s.gpr x := gpr_write_of_ne _ _ hx.1
  refine ⟨t, ?_, fun k hk => ?_, fun r hrx h0 h11 => ?_, fun v h0 h1 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [gB, nibbles, List.cons_append, List.nil_append, runBlock_cons, exec_and,
      exec_lsr_w (by decide : 4 < 32), exec_mtvsrd, exec_vor, exec_vperm, exec_vxor, exec_vand, exec_vsldoi8,
      exec_vsldoi4, exec_mfvsrd, runStep_some, runBlock_nil]
    rfl
  · have c0 : c.gpr .r0 = y &&& 0x0f0f0f0f := by rw [← hc.nib]; rfl
    have c11 : c.gpr .r11 = ((y.setWidth 32 >>> 4).setWidth 64) &&& 0x0f0f0f0f := by
      rw [← hc.nib, show y = a.gpr x from ax.symm]; rfl
    have hJ : ∀ a < 4, vbyte (j.vpr .v0) (7 - a) = outB y a := fun a ha => by
      have hsel := selOut_eq ha
      have hL : vbyte (g.vpr .v0) (7 - a) = (gbyte y a &&& 0x0f) ||| selOut.getD (7 - a) 0 := by
        show vbyte ((c.gpr .r0 ++ c.unknowns 0) ||| s.vpr .v14) (7 - a) = _
        rw [vbyte_or', vbyte_append _ _ (by omega), c0, gbyte_and, gbyte_mask ha, T.2.2.2.2.2.2.1 (7 - a) (by omega)]
      have hH : vbyte (h.vpr .v1) (7 - a) = (gbyte y a >>> 4) ||| selOut.getD (7 - a) 0 := by
        show vbyte ((c.gpr .r11 ++ d.unknowns 0) ||| s.vpr .v14) (7 - a) = _
        rw [vbyte_or', vbyte_append _ _ (by omega), c11, gbyte_lsr4 _ ha, T.2.2.2.2.2.2.1 (7 - a) (by omega)]
      rw [hsel] at hL hH
      have hv0 : h.vpr .v0 = ofVBytes fun i =>
          let j := (vbyte (g.vpr .v0) i).toNat % 32
          if j < 16 then vbyte (s.vpr .v10) j else vbyte (s.vpr .v11) (j - 16) := vpr_writeV_self _ _ _
      have iv1 : i.vpr .v1 = ofVBytes fun i =>
          let j := (vbyte (h.vpr .v1) i).toNat % 32
          if j < 16 then vbyte (s.vpr .v12) j else vbyte (s.vpr .v13) (j - 16) := vpr_writeV_self _ _ _
      have l0 := lookup_sel T.2.2.1 T.2.2.2.1 (by omega : 7 - a < 16) (toNat_and_0f _) hL (sel_cases _)
      have l1 := lookup_sel T.2.2.2.2.1 T.2.2.2.2.2.1 (by omega : 7 - a < 16) (toNat_shr4 _) hH (sel_cases _)
      rw [show j.vpr .v0 = i.vpr .v0 ^^^ i.vpr .v1 from vpr_writeV_self _ _ _, vbyte_xor',
        show i.vpr .v0 = h.vpr .v0 from vpr_writeV_of_ne _ _ (by decide), hv0, iv1, l0, l1]
      simp only [sel_iff, outB, aff]
      split <;> rfl
    have hl : ∀ p < 16, vbyte (l.vpr .v0) p = vbyte (j.vpr .v0) (7 - p / 4) := fun p hp => by
      have hb : (vbyte (j.vpr .v15) p).toNat % 32 = 7 - p / 4 := by
        rw [show j.vpr .v15 = s.vpr .v15 from rfl, T.2.2.2.2.2.2.2.1 p hp, bidx_eq p hp]; omega
      rw [show l.vpr .v0 = _ from vpr_writeV_self _ _ _, vbyte_packed _ hp]
      simp only [hb, show 7 - p / 4 < 16 by omega, ite_true]
    have hn : ∀ p < 16, vbyte (n.vpr .v0) p = vbyte (j.vpr .v0) (7 - p / 4) &&& mask.getD p 0 := fun p hp => by
      rw [show n.vpr .v0 = l.vpr .v0 &&& l.vpr .v16 from vpr_writeV_self _ _ _, vbyte_and', hl p hp,
        show l.vpr .v16 = s.vpr .v16 from rfl, T.2.2.2.2.2.2.2.2 p hp]
    have hq : ∀ p < 16, vbyte (q.vpr .v0) p = vbyte (n.vpr .v0) p ^^^ vbyte (n.vpr .v0) ((p + 8) % 16) :=
      fun p hp => by
        rw [show q.vpr .v0 = o.vpr .v0 ^^^ o.vpr .v1 from vpr_writeV_self _ _ _, vbyte_xor',
          show o.vpr .v0 = n.vpr .v0 from vpr_writeV_of_ne _ _ (by decide),
          show o.vpr .v1 = _ from vpr_writeV_self _ _ _, vbyte_sldoi _ (by decide) hp]
    have hw : vbyte (w.vpr .v0) (7 - k) = vbyte (q.vpr .v0) (7 - k) ^^^ vbyte (q.vpr .v0) (11 - k) := by
      rw [show w.vpr .v0 = u.vpr .v0 ^^^ u.vpr .v1 from vpr_writeV_self _ _ _, vbyte_xor',
        show u.vpr .v0 = q.vpr .v0 from vpr_writeV_of_ne _ _ (by decide),
        show u.vpr .v1 = _ from vpr_writeV_self _ _ _, vbyte_sldoi _ (by decide) (by omega),
        show (7 - k + 4) % 16 = 11 - k by omega]
    rw [show t.gpr x = vdword (w.vpr .v0) 0 from gpr_write_self _ _ _, gbyte_vdword _ (by omega), hw,
      hq _ (by omega), hq _ (by omega), show (7 - k + 8) % 16 = 15 - k by omega,
      show (11 - k + 8) % 16 = 3 - k by omega, hn _ (by omega), hn _ (by omega), hn _ (by omega),
      hn _ (by omega), show (7 - k) / 4 = 1 by omega, show (15 - k) / 4 = 3 by omega,
      show (11 - k) / 4 = 2 by omega, show (3 - k) / 4 = 0 by omega, hJ 1 (by decide), hJ 3 (by decide),
      hJ 2 (by decide), hJ 0 (by decide)]
  · rw [gpr_write_of_ne _ _ hrx, show w.gpr r = c.gpr r from rfl, gpr_write_of_ne _ _ h11,
      gpr_write_of_ne _ _ h11, gpr_write_of_ne _ _ h0]
  · change (u.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (q.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (o.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (n.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (l.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (j.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (i.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (h.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (g.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (f.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (e.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    change (d.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h1]
    change (c.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV_of_ne _ _ h0]
    rfl

theorem byteOf_gbyte (X : BitVec 64) {a : Nat} (ha : a < 4) : Proof.Seed.byteOf (X.setWidth 32) a = gbyte X a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [Proof.Seed.getLsbD_byteOf _ hi]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 8 * a + i < 32 by omega]

theorem outB_eq {X y : BitVec 64} (hy : ∀ k < 4, gbyte y k = Spec.Aes.sbox (aff inLo inHi (gbyte X k)))
    {a : Nat} (ha : a < 4) : outB y a = Proof.Seed.sOf a (Proof.Seed.byteOf (X.setWidth 32) a) := by
  rw [byteOf_gbyte _ ha, outB, hy a ha]
  rcases a with _ | _ | _ | _ | a
  · simp only [Proof.Seed.sOf, Proof.Seed.sTable, s0_affine]; rfl
  · simp only [Proof.Seed.sOf, Proof.Seed.sTable, s1_affine]; rfl
  · simp only [Proof.Seed.sOf, Proof.Seed.sTable, s0_affine]; rfl
  · simp only [Proof.Seed.sOf, Proof.Seed.sTable, s1_affine]; rfl
  · omega

theorem mask_eqs : ∀ k < 4, mask.getD (7 - k) 0 = Proof.Seed.maskOf ((1 + k) % 4) ∧
    mask.getD (15 - k) 0 = Proof.Seed.maskOf ((3 + k) % 4) ∧ mask.getD (11 - k) 0 = Proof.Seed.maskOf ((2 + k) % 4) ∧
    mask.getD (3 - k) 0 = Proof.Seed.maskOf ((0 + k) % 4) := by decide

theorem xor_shuffle (b0 b1 b2 b3 : Bool) : ((b1 ^^ b3) ^^ (b2 ^^ b0)) = (b0 ^^ b1 ^^ b2 ^^ b3) := by
  revert b0 b1 b2 b3; decide

/-- `x := G(x)`, on `x`'s low word. -/
theorem gFn_run (s : State) (hc : Consts s) {x : Reg} (hx : x ≠ .r0 ∧ x ≠ .r11 ∧ x ≠ .r12) :
    ∃ t, runBlock isa (gFn x) s = some t ∧
      (t.gpr x).setWidth 32 = Spec.Seed.g ((s.gpr x).setWidth 32) ∧
      (∀ r, r ≠ x → r ≠ .r0 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, ab, ag, av, am, ard, awr, asp, asy⟩ := gA_run s hc hx
  have ac : Consts a := hc.of_eq av (ag _ (fun h => hx.2.2 h.symm) (by decide) (by decide))
  obtain ⟨b, be, bb, bg, bv, bm, brd, bwr, bsp, bsy⟩ := gB_run a ac hx
  refine ⟨b, ?_, ?_, fun r hrx h0 h11 => (bg r hrx h0 h11).trans (ag r hrx h0 h11),
    fun v h0 h1 => (bv v h0 h1).trans (av v h0 h1), bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp,
    bsy.trans asy⟩
  · rw [gFn_eq, VG.Interleave.runBlock_append, ae, Option.bind_some, be]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    obtain ⟨k, tb, hk, htb, rfl⟩ : ∃ k tb, k < 4 ∧ tb < 8 ∧ i = 8 * k + tb :=
      ⟨i / 8, i % 8, by omega, by omega, by omega⟩
    rw [Proof.Seed.getLsbD_g _ hk htb]
    have e : ((b.gpr x).setWidth 32).getLsbD (8 * k + tb) = (gbyte (b.gpr x) k).getLsbD tb := by
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, htb, decide_true, Bool.true_and]
    have m := mask_eqs k hk
    rw [e, bb k hk, m.1, m.2.1, m.2.2.1, m.2.2.2, outB_eq ab (by decide : 0 < 4), outB_eq ab (by decide : 1 < 4),
      outB_eq ab (by decide : 2 < 4), outB_eq ab (by decide : 3 < 4)]
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, Proof.Seed.xor4]
    exact xor_shuffle _ _ _ _

/-! ## A round -/

/-- A register's low word. -/
abbrev lo (s : State) (r : Reg) : BitVec 32 := (s.gpr r).setWidth 32

/-- What the round's steps keep: the tables, memory and regions. -/
structure Keeps (s t : State) : Prop where
  v : ∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  syms : t.syms = s.syms

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun v h0 h1 => (h'.v v h0 h1).trans (h.v v h0 h1), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.sp.trans h.sp, h'.syms.trans h.syms⟩

theorem Keeps.write (s : State) (r : Reg) (x : BitVec 64) : Keeps s (s.write r x) :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.consts {s t : State} (h : Keeps s t) (hc : Consts s) (h12 : t.gpr .r12 = s.gpr .r12) : Consts t :=
  hc.of_eq h.v h12

theorem gFn_run' (s : State) (hc : Consts s) {x : Reg} (hx : x ≠ .r0 ∧ x ≠ .r11 ∧ x ≠ .r12) :
    ∃ t, runBlock isa (gFn x) s = some t ∧ lo t x = Spec.Seed.g (lo s x) ∧
      (∀ r, r ≠ x → r ≠ .r0 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ Keeps s t := by
  obtain ⟨t, e, h, g, v, m, rd, wr, sp, sy⟩ := gFn_run s hc hx
  exact ⟨t, e, h, g, ⟨v, m, rd, wr, sp, sy⟩⟩

theorem step_add {s : State} {d n m : Reg} :
    runBlock isa ([.add d n m] : List Instr) s = some (s.write d (s.gpr n + s.gpr m)) := by
  rw [runBlock_cons, exec_add, runStep_some, runBlock_nil]

/-- The registers of a round's halves. -/
def Halves (p0 p1 q0 q1 : Reg) : Prop :=
  (p0, p1, q0, q1) = (.r4, .r6, .r7, .r8) ∨ (p0, p1, q0, q1) = (.r7, .r8, .r4, .r6)

theorem Halves.ne {p0 p1 q0 q1 : Reg} (h : Halves p0 p1 q0 q1) :
    (∀ r ∈ [p0, p1, q0, q1], r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12) ∧
      p0 ≠ p1 ∧ q0 ≠ p0 ∧ q0 ≠ p1 ∧ q1 ≠ p0 ∧ q1 ≠ p1 := by
  rcases h with h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> decide

/-- `L ^= F(K_j, R)`. -/
theorem fRound_run {s : State} (hc : Consts s) {p0 p1 q0 q1 : Reg} (hh : Halves p0 p1 q0 q1) {j : Nat}
    (hj : 8 * j + 4 < 2 ^ 15)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * j)) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * j + 4)) 4) :
    ∃ t, runBlock isa (fRound p0 p1 q0 q1 j) s = some t ∧
      lo t p0 = lo s p0 ^^^ (Spec.Seed.f (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j)) 32)
        (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j + 4)) 32) (lo s q0) (lo s q1)).1 ∧
      lo t p1 = lo s p1 ^^^ (Spec.Seed.f (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j)) 32)
        (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j + 4)) 32) (lo s q0) (lo s q1)).2 ∧
      (∀ r, r ≠ p0 → r ≠ p1 → r ≠ .r0 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      Keeps s t := by
  obtain ⟨hne, h01, hq00, hq01, hq10, hq11⟩ := hh.ne
  have nq0 := hne q0 (by simp)
  have nq1 := hne q1 (by simp)
  have np0 := hne p0 (by simp)
  have np1 := hne p1 (by simp)
  let K0 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j)) 32
  let K1 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j + 4)) 32
  let Q0 := lo s q0
  let Q1 := lo s q1
  -- The round key and `R`.
  let a1 := s.write .r9 (K0.setWidth 64)
  let a2 := a1.write .r10 (K1.setWidth 64)
  let a3 := a2.write .r9 (a2.gpr .r9 ^^^ a2.gpr q0)
  let a4 := a3.write .r10 (a3.gpr .r10 ^^^ a3.gpr q1)
  let s1 := a4.write .r10 (a4.gpr .r9 ^^^ a4.gpr .r10)
  have a13 : a1.gpr .r3 = s.gpr .r3 := gpr_write_of_ne _ _ (by decide)
  have e1 : runBlock isa ([.load .w .r9 .r3 (8 * j), .load .w .r10 .r3 (8 * j + 4), .logic .xor .r9 .r9 q0,
      .logic .xor .r10 .r10 q1, .logic .xor .r10 .r9 .r10] : List Instr) s = some s1 := by
    rw [runBlock_cons, exec_load_w (by decide) (by omega) hk0, runStep_some, runBlock_cons,
      exec_load_w (by decide) (by omega) (by rw [a13]; exact hk1), runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    rfl
  have s1g : ∀ r, r ≠ .r9 → r ≠ .r10 → s1.gpr r = s.gpr r := fun r h9 h10 => by
    rw [gpr_write_of_ne _ _ h10, gpr_write_of_ne _ _ h10, gpr_write_of_ne _ _ h9, gpr_write_of_ne _ _ h10,
      gpr_write_of_ne _ _ h9]
  have hA : lo s1 .r9 = K0 ^^^ Q0 := by
    show ((a2.gpr .r9 ^^^ a2.gpr q0)).setWidth 32 = _
    rw [BitVec.setWidth_xor, gpr_write_of_ne _ _ (by decide), gpr_write_self, lo32_ext,
      gpr_write_of_ne _ _ nq0.2.2.2.1, gpr_write_of_ne _ _ nq0.2.2.1]
  have hB : lo s1 .r10 = (K0 ^^^ Q0) ^^^ (K1 ^^^ Q1) := by
    show ((a4.gpr .r9 ^^^ (a3.gpr .r10 ^^^ a3.gpr q1))).setWidth 32 = _
    rw [BitVec.setWidth_xor, BitVec.setWidth_xor, show a4.gpr .r9 = a3.gpr .r9 from gpr_write_of_ne _ _ (by decide),
      show (a3.gpr .r9).setWidth 32 = lo s1 .r9 from rfl, hA,
      show a3.gpr .r10 = a2.gpr .r10 from gpr_write_of_ne _ _ (by decide), gpr_write_self, lo32_ext,
      gpr_write_of_ne _ _ nq1.2.2.1, gpr_write_of_ne _ _ nq1.2.2.2.1, gpr_write_of_ne _ _ nq1.2.2.1]
  have k1 : Keeps s s1 := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  have c1 : Consts s1 := k1.consts hc (s1g _ (by decide) (by decide))
  -- `C = G(A ^ B)`, `D = G(C + A)`, `E = G(D + C)`.
  obtain ⟨t1, et1, ht1, gt1, kt1⟩ := gFn_run' s1 c1 (x := .r10) (by decide)
  let s2 := t1.write .r9 (t1.gpr .r10 + t1.gpr .r9)
  have c2 : Consts s2 := (kt1.trans (Keeps.write _ _ _)).consts c1
    ((gpr_write_of_ne _ _ (by decide)).trans (gt1 _ (by decide) (by decide) (by decide)))
  obtain ⟨t2, et2, ht2, gt2, kt2⟩ := gFn_run' s2 c2 (x := .r9) (by decide)
  let s3 := t2.write .r10 (t2.gpr .r9 + t2.gpr .r10)
  have c3 : Consts s3 := (kt2.trans (Keeps.write _ _ _)).consts c2
    ((gpr_write_of_ne _ _ (by decide)).trans (gt2 _ (by decide) (by decide) (by decide)))
  obtain ⟨t3, et3, ht3, gt3, kt3⟩ := gFn_run' s3 c3 (x := .r10) (by decide)
  let s4 := t3.write .r9 (t3.gpr .r10 + t3.gpr .r9)
  let s5 := s4.write p0 (s4.gpr p0 ^^^ s4.gpr .r9)
  let t := s5.write p1 (s5.gpr p1 ^^^ s5.gpr .r10)
  have keep : ∀ r, r ≠ .r0 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s4.gpr r = s.gpr r := fun r h0 h9 h10 h11 => by
    rw [gpr_write_of_ne _ _ h9, gt3 r h10 h0 h11, gpr_write_of_ne _ _ h10, gt2 r h9 h0 h11, gpr_write_of_ne _ _ h9,
      gt1 r h10 h0 h11, s1g r h9 h10]
  have hC : lo t1 .r10 = Spec.Seed.g ((K0 ^^^ Q0) ^^^ (K1 ^^^ Q1)) := by rw [ht1, hB]
  have hA1 : lo t1 .r9 = K0 ^^^ Q0 := by
    simp only [lo] at *
    rw [show t1.gpr .r9 = s1.gpr .r9 from gt1 _ (by decide) (by decide) (by decide)]; exact hA
  have hD : lo t2 .r9 = Spec.Seed.g (lo t1 .r10 + (K0 ^^^ Q0)) := by
    simp only [lo] at *
    rw [ht2, show s2.gpr .r9 = t1.gpr .r10 + t1.gpr .r9 from gpr_write_self _ _ _, lo32_add, hA1]
  have hC2 : lo t2 .r10 = lo t1 .r10 := by
    simp only [lo] at *
    rw [show t2.gpr .r10 = s2.gpr .r10 from gt2 _ (by decide) (by decide) (by decide),
      show s2.gpr .r10 = t1.gpr .r10 from gpr_write_of_ne _ _ (by decide)]
  have hE : lo t3 .r10 = Spec.Seed.g (lo t2 .r9 + lo t1 .r10) := by
    simp only [lo] at *
    rw [ht3, show s3.gpr .r10 = t2.gpr .r9 + t2.gpr .r10 from gpr_write_self _ _ _, lo32_add]
    exact congrArg (fun z => Spec.Seed.g (lo t2 .r9 + z)) hC2
  have hD3 : lo t3 .r9 = lo t2 .r9 := by
    simp only [lo] at *
    rw [show t3.gpr .r9 = s3.gpr .r9 from gt3 _ (by decide) (by decide) (by decide),
      show s3.gpr .r9 = t2.gpr .r9 from gpr_write_of_ne _ _ (by decide)]
  have h4 : lo s4 .r9 = lo t3 .r10 + lo t2 .r9 := by
    simp only [lo] at *
    rw [show s4.gpr .r9 = t3.gpr .r10 + t3.gpr .r9 from gpr_write_self _ _ _, lo32_add]
    exact congrArg (lo t3 .r10 + ·) hD3
  have h4' : lo s4 .r10 = lo t3 .r10 := by
    simp only [lo] at *
    rw [show s4.gpr .r10 = t3.gpr .r10 from gpr_write_of_ne _ _ (by decide)]
  have hf : Spec.Seed.f K0 K1 Q0 Q1 = (lo t3 .r10 + lo t2 .r9, lo t3 .r10) := by
    rw [hE, hD, hC, BitVec.xor_comm K0 Q0, BitVec.xor_comm K1 Q1]
    rfl
  refine ⟨t, ?_, ?_, ?_, fun r hr0 hr1 h0 h9 h10 h11 => ?_, ?_⟩
  · rw [fRound, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append]
    rw [e1, Option.bind_some, et1, Option.bind_some, step_add, Option.bind_some, et2, Option.bind_some, step_add,
      Option.bind_some, et3, Option.bind_some, runBlock_cons, exec_add, runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
  · rw [hf]
    show ((t.gpr p0)).setWidth 32 = _
    rw [gpr_write_of_ne _ _ h01, gpr_write_self, BitVec.setWidth_xor, keep _ np0.1 np0.2.2.1 np0.2.2.2.1 np0.2.2.2.2.1]
    exact congrArg (lo s p0 ^^^ ·) h4
  · rw [hf]
    show ((t.gpr p1)).setWidth 32 = _
    rw [gpr_write_self, BitVec.setWidth_xor, gpr_write_of_ne _ _ (Ne.symm h01),
      keep _ np1.1 np1.2.2.1 np1.2.2.2.1 np1.2.2.2.2.1, gpr_write_of_ne _ _ (Ne.symm np0.2.2.2.1)]
    exact congrArg (lo s p1 ^^^ ·) h4'
  · rw [gpr_write_of_ne _ _ hr1, gpr_write_of_ne _ _ hr0, keep r h0 h9 h10 h11]
  · exact k1.trans (kt1.trans ((Keeps.write _ _ _).trans (kt2.trans ((Keeps.write _ _ _).trans
      (kt3.trans ((Keeps.write _ _ _).trans ((Keeps.write _ _ _).trans (Keeps.write _ _ _))))))))

/-- The halves `(L0, L1, R0, R1)` before round `j`: in `r4`, `r6` and `r7`,
`r8` before an even round, the other way before an odd one. -/
def regQ (s : State) (j : Nat) : Proof.Seed.Quad :=
  if j % 2 = 0 then (lo s .r4, lo s .r6, lo s .r7, lo s .r8) else (lo s .r7, lo s .r8, lo s .r4, lo s .r6)

/-- Round `j`'s key, from the schedule at `r3`. -/
def keyAt (s : State) (j : Nat) : BitVec 32 × BitVec 32 :=
  (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j)) 32, s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * j + 4)) 32)

/-- The registers the rounds write. -/
def written : List Reg := [.r0, .r4, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The schedule is readable. -/
def KeyIn (s : State) : Prop := ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4

theorem keyIdx_lt (dir : Direction) {j : Nat} (hj : j < 16) : keyIdx dir j < 16 := by
  cases dir <;> simp only [keyIdx] <;> omega

theorem round_run (dir : Direction) {s : State} (hc : Consts s) {j : Nat} (hj : j < 16) (hk : KeyIn s) :
    ∃ t, runBlock isa (round dir j) s = some t ∧
      regQ t (j + 1) = Spec.Seed.round (keyAt s (keyIdx dir j)) (regQ s j) ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧ Keeps s t := by
  have hkj := keyIdx_lt dir hj
  have hk0 := hk (2 * keyIdx dir j) (by omega)
  have hk1 := hk (2 * keyIdx dir j + 1) (by omega)
  rw [show 4 * (2 * keyIdx dir j) = 8 * keyIdx dir j by omega] at hk0
  rw [show 4 * (2 * keyIdx dir j + 1) = 8 * keyIdx dir j + 4 by omega] at hk1
  unfold round
  split
  · rename_i he
    obtain ⟨t, e, h0, h1, g, k⟩ := fRound_run hc (.inl rfl) (by omega) hk0 hk1
    refine ⟨t, e, ?_, fun r hr => g r (fun h => hr (by simp [written, h])) (fun h => hr (by simp [written, h]))
      (fun h => hr (by simp [written, h])) (fun h => hr (by simp [written, h])) (fun h => hr (by simp [written, h]))
      (fun h => hr (by simp [written, h])), k⟩
    have h7 : t.gpr .r7 = s.gpr .r7 := g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h8 : t.gpr .r8 = s.gpr .r8 := g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [regQ, he, show ¬ (j + 1) % 2 = 0 by omega, ite_true, ite_false, Spec.Seed.round, keyAt, h0, h1]
    simp only [lo, h7, h8]
  · rename_i he
    obtain ⟨t, e, h0, h1, g, k⟩ := fRound_run hc (.inr rfl) (by omega) hk0 hk1
    refine ⟨t, e, ?_, fun r hr => g r (fun h => hr (by simp [written, h])) (fun h => hr (by simp [written, h]))
      (fun h => hr (by simp [written, h])) (fun h => hr (by simp [written, h])) (fun h => hr (by simp [written, h]))
      (fun h => hr (by simp [written, h])), k⟩
    have h4 : t.gpr .r4 = s.gpr .r4 := g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h6 : t.gpr .r6 = s.gpr .r6 := g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [regQ, he, show (j + 1) % 2 = 0 by omega, ite_true, ite_false, Spec.Seed.round, keyAt, h0, h1]
    simp only [lo, h4, h6]

theorem KeyIn.of_eq {s t : State} (h : KeyIn s) (h3 : t.gpr .r3 = s.gpr .r3) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : KeyIn t := fun i hi => by rw [h3, hrd, hwr]; exact h i hi

theorem rounds_run (dir : Direction) (s : State) (n : Nat) (hn : n ≤ 16) (hc : Consts s) (hk : KeyIn s) :
    ∃ t, runBlock isa ((List.range n).flatMap (round dir)) s = some t ∧
      regQ t n = Proof.Seed.roundsN (fun j => keyAt s (keyIdx dir j)) n (regQ s 0) ∧ Consts t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧ Keeps s t := by
  induction n with
  | zero => exact ⟨s, rfl, rfl, hc, fun _ _ => rfl, ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    obtain ⟨a, ae, aq, ac, ag, ak⟩ := ih (by omega)
    have a3 : a.gpr .r3 = s.gpr .r3 := ag _ (by decide)
    obtain ⟨b, be, bq, bg, bk⟩ := round_run dir ac (j := n) (by omega) (hk.of_eq a3 ak.rd ak.wr)
    refine ⟨b, ?_, ?_, bk.consts ac (bg _ (by decide)), fun r hr => (bg r hr).trans (ag r hr), ak.trans bk⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · rw [bq, Proof.Seed.roundsN_succ, aq, show keyAt a (keyIdx dir n) = keyAt s (keyIdx dir n) by
        rw [keyAt, keyAt, ak.mem, a3]]

open VG.Impl.Modes.PPC64LE (sb)
open VG.Impl.Seed.PPC64LE (bufSlot)
open VG.Proof.Modes.PPC64LE (ScrIn coreRegion blkRegion blkAddr Layout CoreSpec kept KeptBut)
open VG.Spec.Aes (bytesAt)

/-! ## The tables -/

/-- Table `k` as `lxvd2xTbl` loads it. -/
abbrev tval (k : Nat) : BitVec 128 := tableWords.getD (2 * k) 0 ++ tableWords.getD (2 * k + 1) 0

theorem tval_ok : ∀ k < 9, TabOk (tval k) (tables.getD k inLo) := by
  intro k hk; intro j hj; revert j; revert k; decide

theorem tableWords_length : tableWords.length = 18 := rfl

theorem treg_inj : ∀ a < 9, ∀ b < 9, treg a = treg b → a = b := by decide

/-- After loading the tables `0 … n - 1`. -/
theorem loadT_run (s : State) (n : Nat) (hn : n ≤ 9) (h10 : s.gpr .r10 = s.syms tableSym) :
    ∃ t, runBlock isa ((List.range n).flatMap fun k =>
        [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) s = some t ∧
      (∀ k < n, t.vpr (treg k) = tval k) ∧
      (∀ v, (∀ k < n, v ≠ treg k) → t.vpr v = s.vpr v) ∧
      (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, av, avo, ag, am, ard, awr, asp, asy⟩ := ih (by omega)
    let b := a.write .r11 (BitVec.ofNat 64 (16 * n))
    let c := b.writeV (treg n) (tval n)
    have hb10 : b.gpr .r10 = b.syms tableSym := by
      rw [show b.syms = s.syms from asy, gpr_write_of_ne _ _ (by decide), ag _ (by decide), h10]
    have hb11 : (b.gpr .r11).toNat = 16 * n := by
      rw [gpr_write_self, BitVec.toNat_ofNat]; omega
    have hc : exec (.lxvd2xTbl (treg n) .r10 .r11 tableSym tableWords) b = some c := by
      have e1 : 16 * n / 8 = 2 * n := by omega
      have e2 : 16 * n % 8 = 0 := by omega
      have e3 : 2 * n + 2 ≤ 18 := by omega
      have e4 : (Reg.r10 ≠ .r0) := by decide
      simp only [exec, hb10, hb11, e1, e2, e3, e4, tableWords_length, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte]
      rfl
    refine ⟨c, ?_, fun k hk => ?_, fun v hv => ?_, fun r hr => ?_, am, ard, awr, asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons, exec_li (by omega), runStep_some,
        runBlock_cons, hc, runStep_some, runBlock_nil]
    · rw [vpr_writeV]
      by_cases e : k = n
      · subst e; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd (treg_inj k (by omega) n (by omega) h) e)]
        exact av k (by omega)
    · rw [vpr_writeV, ite_eq_right_iff.mpr (fun h => absurd h (hv n (by omega)))]
      exact avo v fun k hk => hv k (by omega)
    · exact (gpr_write_of_ne _ _ hr).trans (ag r hr)

theorem mask_eq : ((0x0f0f : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0x0f0f : BitVec 16).setWidth 64 =
    (0x0f0f0f0f : BitVec 64) := by decide

theorem loadTables_run (s : State) :
    ∃ t, runBlock isa loadTables s = some t ∧ Consts t ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a : State := { s.write .r10 (s.syms tableSym) with lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) }
  have a10 : a.gpr .r10 = a.syms tableSym := by
    show (s.write .r10 (s.syms tableSym)).gpr .r10 = s.syms tableSym; exact gpr_write_self _ _ _
  obtain ⟨b, be, bv, _, bg, bm, brd, bwr, bsp, bsy⟩ := loadT_run a 9 (by decide) a10
  let c := b.write .r12 (((0x0f0f : BitVec 16) ++ (0 : BitVec 16)).signExtend 64)
  let d := c.write .r12 (c.gpr .r12 ||| (0x0f0f : BitVec 16).setWidth 64)
  refine ⟨d, ?_, ⟨fun k hk => ?_, ?_⟩, fun r h10 h11 h12 => ?_, bm, brd, bwr, bsp, bsy⟩
  · rw [loadTables, List.cons_append, runBlock_cons]
    simp only [exec, ne_eq, show ¬(Reg.r10 = .r0) by decide, not_false_eq_true, ↓reduceIte]
    rw [runStep_some, VG.Interleave.runBlock_append, be, Option.bind_some, runBlock_cons, exec_lis, runStep_some,
      runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  · rw [show d.vpr (treg k) = b.vpr (treg k) from rfl, bv k (by omega)]; exact tval_ok k hk
  · rw [gpr_write_self, gpr_write_self, mask_eq]
  · rw [gpr_write_of_ne _ _ h12, gpr_write_of_ne _ _ h12, bg r h11]; exact gpr_write_of_ne _ _ h10

/-! ## The block -/

/-- The registers of the block's words, as loaded. -/
def inReg (i : Nat) : Reg := [Reg.r4, .r6, .r7, .r8].getD i .r4

/-- The registers of the output's words, as stored. -/
def outReg (i : Nat) : Reg := [Reg.r7, .r8, .r4, .r6].getD i .r7

/-- The offset of word `i` of the block. -/
abbrev woff (i : Nat) : Nat := 8 * bufSlot + 4 * i

theorem inReg_ne : ∀ j < 4, inReg j ≠ sb ∧ inReg j ≠ .r0 ∧ inReg j ∈ written := by decide

theorem inReg_inj : ∀ a < 4, ∀ b < 4, inReg a = inReg b → a = b := by decide

theorem outReg_ne : ∀ j < 4, outReg j ≠ sb ∧ outReg j ≠ .r0 := by decide

theorem bufSlot_eq : bufSlot = 136 := rfl

theorem loadBlock_eq : loadBlock = (List.range 4).flatMap fun i =>
    [.li .r0 (woff i), .loadRev .w (inReg i) sb .r0] := by
  simp only [loadBlock, woff, inReg, List.range_succ, List.range_zero, List.flatMap_cons,
    List.flatMap_nil, List.nil_append, List.append_nil, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
  rfl

theorem storeBlock_eq : storeBlock = (List.range 4).flatMap fun i =>
    [.li .r0 (woff i), .storeRev .w (outReg i) sb .r0] := by
  simp only [storeBlock, woff, outReg, List.range_succ, List.range_zero, List.flatMap_cons,
    List.flatMap_nil, List.nil_append, List.append_nil, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
  rfl

theorem loads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hr : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (woff i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.li .r0 (woff i), .loadRev .w (inReg i) sb .r0]) s = some t ∧
      (∀ j < n, lo t (inReg j) = rev32 (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (woff j)) 32)) ∧
      (∀ r, r ≠ .r0 → (∀ j < n, r ≠ inReg j) → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega), fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, av, am, ard, awr, asp, asy⟩ := ih (by omega)
    have ab : a.gpr sb = s.gpr sb := ag _ (by decide) (fun j hj => (inReg_ne j (by omega)).1.symm)
    let b := a.write .r0 (BitVec.ofNat 64 (woff n))
    have bb : b.gpr sb + b.gpr .r0 = s.gpr sb + BitVec.ofNat 64 (woff n) := by
      rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, ab]
    have br : InRegions (b.rd ++ b.wr) (b.gpr sb + b.gpr .r0) 4 := by
      rw [bb]; show InRegions (a.rd ++ a.wr) _ 4; rw [ard, awr]; exact hr n (by omega)
    let c := b.write (inReg n) ((rev32 (b.mem.readW (b.gpr sb + b.gpr .r0) 32)).setWidth 64)
    have hw := inReg_ne n (by omega)
    refine ⟨c, ?_, fun j hj => ?_, fun r h0 hr' => ?_, av, am, ard, awr, asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons,
        exec_li (by rw [woff, bufSlot_eq]; omega), runStep_some, runBlock_cons,
        exec_loadRev_w (by decide) br, runStep_some, runBlock_nil]
    · by_cases h : j = n
      · subst j
        rw [lo, show c.gpr (inReg n) = _ from gpr_write_self _ _ _, bb, lo32_ext]
        show rev32 (a.mem.readW _ 32) = _
        rw [am]
      · rw [lo, gpr_write_of_ne _ _ (fun e => h (inReg_inj j (by omega) n (by omega) e)),
          gpr_write_of_ne _ _ (inReg_ne j (by omega)).2.1]
        exact aw j (by omega)
    · rw [gpr_write_of_ne _ _ (hr' n (by omega)), gpr_write_of_ne _ _ h0]
      exact ag r h0 fun j hj => hr' j (by omega)

theorem frame_write_word (m : Mem) (p : Addr) (v : BitVec 32) : Frame [⟨p, 4⟩] m (m.writeW p v) := by
  intro x hx
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right (fun h => hx _ List.mem_cons_self h)

theorem stores_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hw : ∀ i < 4, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (woff i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.li .r0 (woff i), .storeRev .w (outReg i) sb .r0]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr sb + BitVec.ofNat 64 (woff j)) 32 = rev32 (lo s (outReg j))) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr sb + BitVec.ofNat 64 (8 * bufSlot), 16⟩] s.mem t.mem ∧
      t.vpr = s.vpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, af, av, ard, awr, asp, asy⟩ := ih (by omega)
    have ab : a.gpr sb = s.gpr sb := ag _ (by decide)
    let b := a.write .r0 (BitVec.ofNat 64 (woff n))
    have bb : b.gpr sb + b.gpr .r0 = s.gpr sb + BitVec.ofNat 64 (woff n) := by
      rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, ab]
    have br : InRegions b.wr (b.gpr sb + b.gpr .r0) 4 := by
      rw [bb]; show InRegions a.wr _ 4; rw [awr]; exact hw n (by omega)
    have bv : b.gpr (outReg n) = s.gpr (outReg n) :=
      (gpr_write_of_ne _ _ (outReg_ne n (by omega)).2).trans (ag _ (outReg_ne n (by omega)).2)
    let m' := b.mem.writeW (s.gpr sb + BitVec.ofNat 64 (woff n)) (rev32 (lo s (outReg n)))
    let c : State := { b with mem := m' }
    have bf : Frame [⟨s.gpr sb + BitVec.ofNat 64 (woff n), 4⟩] a.mem c.mem := frame_write_word _ _ _
    refine ⟨c, ?_, fun j hj => ?_, fun r h0 => (gpr_write_of_ne _ _ h0).trans (ag r h0), ?_, av, ard, awr,
      asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons,
        exec_li (by rw [woff, bufSlot_eq]; omega), runStep_some, runBlock_cons,
        exec_storeRev_w (by decide) br, runStep_some, runBlock_nil, bb, bv]
    · by_cases h : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr sb) (by rw [woff, woff, bufSlot_eq]; omega)
            (by rw [woff, bufSlot_eq]; omega) (by rw [woff, bufSlot_eq]; omega)) (by decide)]
        exact aw j (by omega)
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [woff, ← VG.Offset.add_add (s.gpr sb) (8 * bufSlot) (4 * n)]
      exact VG.Offset.sub_base _ (by omega : 4 * n + 4 ≤ 16)

/-- The block of the stored words `z 0 … z 3`, big-endian. -/
theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = rev32 (z i)) :
    bytesAt m p 16 = (Vector.ofFn fun i : Fin 16 => (z (i.val / 4) >>> (8 * (3 - i.val % 4))).setWidth 8).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i hi _
  have hi16 : i < 16 := by simpa [bytesAt] using hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, Vector.getElem_toList, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have b := Mem.readW_byte m (p + BitVec.ofNat 64 (4 * (i / 4))) (i := i % 4) (by omega)
  rw [VG.Offset.add_add, show 4 * (i / 4) + i % 4 = i by omega, h (i / 4) (by omega)] at b
  rw [b, BitVec.getLsbD_extractLsb']
  simp only [hj, decide_true, Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  change (byteRev32 (z (i / 4))).getLsbD (8 * (i % 4) + j) = _
  rw [byteRev32_getLsbD _ (by omega)]
  congr 1; omega

/-! ## The core -/

open VG.Proof.Seed.PPC64LE.Mode (KeyArgs Ready keyR)

theorem kept_ne : ∀ r ∈ kept, r ∉ written ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ sb := by decide

theorem dirCipher_bytes (dir : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    Proof.Seed.dirCipher dir k (bytesAt m p 16) =
      (Spec.Seed.crypt (fun j => Spec.Seed.roundKey k (keyIdx dir j)) (Spec.Seed.blockAt m p)).toList := by
  have e : (Vector.ofFn fun i : Fin 16 => (Spec.Seed.blockAt m p).toList.getD i.val 0) = Spec.Seed.blockAt m p := by
    apply Vector.ext; intro i hi; simp
  cases dir <;> simp only [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, Proof.Seed.bytesAt_eq, e,
    Spec.Seed.encryptBlock, Spec.Seed.decryptBlock, keyIdx]

/-- The core in the direction `dir` on the first block of the buffer of the
blocks function's core on `g ≥ 1` blocks, whose key it keeps ready. -/
theorem crypt_ok (dir : Direction) {g : Nat} (hg : 1 ≤ g) {s : State} {B : Addr} {ws : List Region}
    {k : Spec.Seed.Schedule} (hB : s.gpr sb = B) (hs : ScrIn s B (bufSlot + 2 * g + 6)) (hk : Ready g s B ws k) :
    WP isa (core dir).crypt s fun t => t.gpr sb = B ∧ (∀ r ∈ kept, t.gpr r = s.gpr r) ∧ Ready g t B ws k ∧
      Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem t.mem ∧
      bytesAt t.mem (B + BitVec.ofNat 64 (8 * bufSlot)) 16 =
        Proof.Seed.dirCipher dir k (bytesAt s.mem (B + BitVec.ofNat 64 (8 * bufSlot)) 16) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hwr : (⟨B, 8 * (bufSlot + 2 * g + 6)⟩ : Region) ∈ s.wr := hs.wr
  obtain ⟨⟨hsched, hin, _⟩, _⟩ := id hk
  change WP isa (.block (loadTables ++ loadBlock ++ rounds dir ++ storeBlock)) s _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨a, ae, ac, ag, am, ard, awr, _, _⟩ := loadTables_run s
  refine WP.of_runBlock ⟨a, ae, ?_⟩
  have ab : a.gpr sb = B := (ag _ (by decide) (by decide) (by decide)).trans hB
  have ar : ∀ i < 4, InRegions (a.rd ++ a.wr) (a.gpr sb + BitVec.ofNat 64 (woff i)) 4 := fun i hi => by
    rw [ard, awr, ab]
    exact ⟨_, List.mem_append_right _ hwr, VG.Offset.contains_base B
      (by rw [woff, bufSlot_eq]; omega) (by rw [woff, bufSlot_eq]; omega)⟩
  obtain ⟨b, be, bw, bg, bv, bm, brd, bwr, _, _⟩ := loads_run a 4 (by decide) ar
  have be' : runBlock isa loadBlock a = some b := by rw [loadBlock_eq]; exact be
  refine WP.of_runBlock ⟨b, be', ?_⟩
  have bnot : ∀ r, r ≠ .r0 → r ∉ written → b.gpr r = a.gpr r := fun r h0 hw =>
    bg r h0 fun j hj he => hw (he ▸ (inReg_ne j hj).2.2)
  have bc : Consts b := ac.of_eq (fun v _ _ => by rw [bv]) (bnot _ (by decide) (by decide))
  have b3 : b.gpr .r3 = s.gpr .r3 := by
    rw [bnot _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)]
  have bmem : b.mem = s.mem := bm.trans am
  have bk : KeyIn b := fun i hi => by
    rw [brd, ard, b3]
    exact ⟨_, List.mem_append_left _ hin, VG.Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨d, de, dq, _, dg, dk⟩ := rounds_run dir b 16 (by decide) bc bk
  refine WP.of_runBlock ⟨d, de, ?_⟩
  have dbase : d.gpr sb = B := by
    rw [dg _ (by decide), bnot _ (by decide) (by decide), ab]
  have dmem : d.mem = s.mem := dk.mem.trans bmem
  let A := B + BitVec.ofNat 64 (8 * bufSlot)
  have initial : regQ b 0 = Proof.Seed.decodeQ (Spec.Seed.blockAt s.mem A) := by
    rw [Proof.Seed.decodeQ_blockAt]
    have w : ∀ i < 4, lo b (inReg i) = byteRev32 (s.mem.readW (A + BitVec.ofNat 64 (4 * i)) 32) := fun i hi => by
      rw [bw i hi, am, ab, woff, ← VG.Offset.add_add B (8 * bufSlot) (4 * i)]; rfl
    simp only [regQ, Nat.zero_mod, ite_true]
    rw [show lo b .r4 = lo b (inReg 0) from rfl, show lo b .r6 = lo b (inReg 1) from rfl,
      show lo b .r7 = lo b (inReg 2) from rfl, show lo b .r8 = lo b (inReg 3) from rfl, w 0 (by decide),
      w 1 (by decide), w 2 (by decide), w 3 (by decide)]
  have hkey : ∀ j < 16, keyAt b (keyIdx dir j) = Spec.Seed.roundKey k (keyIdx dir j) := fun j hj => by
    rw [keyAt, ← hsched, Proof.Seed.roundKey_readW _ _ (keyIdx_lt dir hj), bmem, b3,
      show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, VG.Offset.add_add]
  let q := Proof.Seed.roundsN (fun j => Spec.Seed.roundKey k (keyIdx dir j)) 16
    (Proof.Seed.decodeQ (Spec.Seed.blockAt s.mem A))
  have dq' : regQ d 16 = q := by
    rw [dq, initial]; exact Proof.Seed.roundsN_congr 16 _ hkey
  have dr : ∀ i < 4, InRegions d.wr (d.gpr sb + BitVec.ofNat 64 (woff i)) 4 := fun i hi => by
    rw [dk.wr, bwr, awr, dbase]
    exact ⟨_, hwr, VG.Offset.contains_base B
      (by rw [woff, bufSlot_eq]; omega) (by rw [woff, bufSlot_eq]; omega)⟩
  obtain ⟨e, ee, ew, eg, ef, _, erd, ewr, _, _⟩ := stores_run d 4 (by decide) dr
  have ee' : runBlock isa storeBlock d = some e := by rw [storeBlock_eq]; exact ee
  refine WP.of_runBlock ⟨e, ee', ?_⟩
  have keptE : ∀ r ∈ kept, e.gpr r = s.gpr r := fun r hr => by
    have h := kept_ne r hr
    rw [eg r h.2.2.2.2.1, dg r h.1, bnot r h.2.2.2.2.1 h.1, ag r h.2.1 h.2.2.1 h.2.2.2.1]
  have frame : Frame [⟨B, 8 * (bufSlot + 2)⟩] s.mem e.mem := by
    rw [← dmem]
    refine ef.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨_, List.mem_cons_self, ?_⟩
    rw [dbase]
    exact VG.Offset.sub_base B (by show 8 * bufSlot + 16 ≤ 8 * (bufSlot + 2); omega)
  have hq : q = (lo d .r4, lo d .r6, lo d .r7, lo d .r8) := by rw [← dq']; rfl
  have output : bytesAt e.mem A 16 = (Proof.Seed.encodeSwapped q).toList := by
    rw [stored_bytes (z := fun i => lo d (outReg i)) fun i hi => by
      rw [VG.Offset.add_add, ← dbase, show 8 * bufSlot + 4 * i = woff i from rfl, ew i hi], hq]
    congr 1
  refine ⟨(eg _ (by decide)).trans dbase, keptE,
    VG.Proof.Seed.PPC64LE.Mode.ready_core hk (keptE .r3 (by decide)) (by rw [erd, dk.rd, brd, ard])
      (frame.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst r; exact Region.sub_prefix (by omega)⟩),
    frame, ?_, ?_, ?_⟩
  · rw [output, dirCipher_bytes, Proof.Seed.crypt_eq]
  · rw [erd, dk.rd, brd, ard]
  · rw [ewr, dk.wr, bwr, awr]

theorem blkAddr_zero (c : Impl.Modes.PPC64LE.Core) (hb : c.buf = bufSlot) (B : Addr) :
    blkAddr c B 0 = B + BitVec.ofNat 64 (8 * bufSlot) := by
  show B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 (4 * c.bw * 0) = _
  rw [hb, VG.Offset.add_add, Nat.mul_zero, Nat.add_zero]

/-- The single-block core meets what the modes need. -/
def coreSpec (dir : Direction) : CoreSpec (core dir) where
  Key := Spec.Seed.Schedule
  cipher := Proof.Seed.dirCipher dir
  KeyArgs := KeyArgs
  Ready := Ready 1
  cipher_len _ _ := by cases dir <;> simp [Proof.Seed.dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, core]
  layout := ⟨Nat.one_pos, .inr rfl, by simp only [core]; omega, by simp only [core]; omega,
    by simp only [core, bufSlot]; omega⟩
  keyArgs_congr h e r _ _ f := VG.Proof.Seed.PPC64LE.Mode.keyArgs_congr h e.r3 r f
  ready_frame h e r _ _ f hs _ := VG.Proof.Seed.PPC64LE.Mode.ready_frame h e.r3 r f hs
  prepare_wp {s B rs k} hB _ hm hk :=
    WP.of_runBlock ⟨s, rfl, ⟨hk, hk.2.2 _ hm⟩, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp {s B ws k} hB hs hR := WP.mono (crypt_ok dir (g := 1) (Nat.le_refl 1) hB hs hR)
    fun _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, fun j hj => by
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      rw [blkAddr_zero _ rfl]; exact h5, h6, h7⟩

/-- The core enciphers the first block of the buffer of the blocks function's
core on sixteen blocks, for the blocks CBC and CFB decryption leave after
their groups (`Core.seq2With`). -/
theorem oneOk (dir : Direction) :
    Proof.Modes.PPC64LE.OneOk (VG.Proof.Seed.PPC64LE.Mode.wideCoreSpec dir) (core dir).crypt :=
  fun hB hS hR => WP.mono (crypt_ok dir (g := 16) (by decide) hB hS hR)
    fun _ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3,
      h4.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst r; exact Region.sub_prefix (by show _ ≤ 8 * (bufSlot + 2 * 16); omega)⟩,
      by rw [blkAddr_zero _ rfl]; exact h5, h6, h7⟩

end VG.Proof.Seed.PPC64LE.Serial
