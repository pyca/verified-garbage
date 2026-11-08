module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.SerialSbox
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModeCore
public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.PPC64LE.Core
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import all Init.Data.Nat.Bitwise.Basic

/-!
# The single-block SM4 core on PPC64LE

`coreSpec`: the single-block core (`Impl.Sm4.PPC64LE.Serial.core`) meets
what the modes need of a core (`Proof.Modes.PPC64LE.CoreSpec`), with the
key the schedule at `r3`, read in place (`KeyArgs`, apart from the core's
slots and the mode's regions), and its cipher `Spec.Sm4.cipher`.

* `affine_run`: the nibble-table lookups of an affine map (`Serial.affine`)
  put, in bytes `4 … 7` of `v0`, the map (`aff`) of the bytes of `r9`'s low
  word. `tau_run`: SM4's S-box layer (`Serial.tau`), from `sbox_affine`.
* `linear_run`, `round_run` and `rounds_run`: the linear map, a round, and
  the 32.
* `crypt_wp`: the tables to `v12`–`v15` (`loadTables_run`), the block's
  big-endian words (`loads_run`), the 32 rounds, and the words back in
  reverse order (`stores_run`) encipher the block of the buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.Serial

open VG VG.PPC64LE VG.PPC64LE.RegUpd
open VG.Impl.Sm4.PPC64LE.Serial

/-! ## Bytes -/

/-- Byte `k` of a doubleword, from the least significant. -/
abbrev gbyte (x : BitVec 64) (k : Nat) : BitVec 8 := x.extractLsb' (8 * k) 8

theorem gbyte_and (x y : BitVec 64) (k : Nat) : gbyte (x &&& y) k = gbyte x k &&& gbyte y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]

theorem gbyte_xor (x y : BitVec 64) (k : Nat) : gbyte (x ^^^ y) k = gbyte x k ^^^ gbyte y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

/-- The mask `0x0f0f0f0f` has `0x0f` in each byte of its low word. -/
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

/-- The register's doubleword `x`, moved to the high doubleword of a vector
register: its byte `k` is the vector's byte `7 - k`. -/
theorem vbyte_append (x u : BitVec 64) {k : Nat} (hk : k < 8) : vbyte (x ++ u) (7 - k) = gbyte x k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  split
  · omega
  · congr 1; omega

theorem gbyte_vdword (v : BitVec 128) {k : Nat} (hk : k < 8) : gbyte (vdword v 0) k = vbyte v (7 - k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [show 64 * (1 - 0) + (8 * k + i) = 8 * (15 - (7 - k)) + i by omega]
  simp only [show 8 * k + i < 64 by omega, decide_true, Bool.true_and]

theorem toNat_and_0f (b : BitVec 8) : (b &&& 0x0f).toNat < 16 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem toNat_shr4 (b : BitVec 8) : (b >>> 4).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight]; have := b.isLt
  rw [Nat.shiftRight_eq_div_pow]; omega

/-! ## Vector instructions -/

theorem vbyte_xor' (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

theorem exec_mtvsrd {s : State} {d : VReg} {n : Reg} :
    exec (.mtvsrd d n) s = some { s.writeV d (s.gpr n ++ s.unknowns 0) with
      unknowns := fun i => s.unknowns (i + 1) } := rfl

theorem exec_mfvsrd {s : State} {d : Reg} {n : VReg} :
    exec (.mfvsrd d n) s = some (s.write d (vdword (s.vpr n) 0)) := rfl

theorem exec_vperm {s : State} {d n m c : VReg} :
    exec (.vop (.perm d n m c)) s = some (s.writeV d (ofVBytes fun i =>
      let j := (vbyte (s.vpr c) i).toNat % 32
      if j < 16 then vbyte (s.vpr n) j else vbyte (s.vpr m) (j - 16))) := rfl

theorem exec_vxor {s : State} {d n m : VReg} :
    exec (.vop (.logic .xor d n m)) s = some (s.writeV d (s.vpr n ^^^ s.vpr m)) := rfl

theorem exec_vsbox {s : State} {d n : VReg} :
    exec (.vop (.sbox d n)) s =
      some (s.writeV d (ofVBytes fun i => VectorCrypto.aesSbox (vbyte (s.vpr n) i))) := rfl

theorem vpr_writeV (s : State) (d : VReg) (v : BitVec 128) (d' : VReg) :
    (s.writeV d v).vpr d' = if d' = d then v else s.vpr d' := rfl

/-- A table of sixteen bytes, in a vector register. -/
def TabOk (v : BitVec 128) (t : Vector Byte 16) : Prop := ∀ j < 16, vbyte v j = t.getD j 0

/-- A table lookup by `vperm` of a byte below 16. -/
theorem vperm_byte {T c : BitVec 128} {t : Vector Byte 16} (hT : TabOk T t) {i : Nat} (hi : i < 16)
    (hc : (vbyte c i).toNat < 16) :
    vbyte (ofVBytes fun i =>
      let j := (vbyte c i).toNat % 32
      if j < 16 then vbyte T j else vbyte T (j - 16)) i = t.getD (vbyte c i).toNat 0 := by
  rw [vbyte_packed _ hi]
  have hm : (vbyte c i).toNat % 32 = (vbyte c i).toNat := Nat.mod_eq_of_lt (by omega)
  simp only [hm, hc, ite_true]
  exact hT _ hc

/-! ## The affine maps -/

/-- What the core keeps in registers: the four tables in `v12`–`v15` and the
mask in `r12`. -/
structure Consts (s : State) : Prop where
  inLo : TabOk (s.vpr (treg 0)) inLo
  inHi : TabOk (s.vpr (treg 1)) inHi
  outLo : TabOk (s.vpr (treg 2)) outLo
  outHi : TabOk (s.vpr (treg 3)) outHi
  mask : s.gpr .r12 = 0x0f0f0f0f

theorem Consts.of_eq {s t : State} (h : Consts s) (hv : ∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v)
    (hg : t.gpr .r12 = s.gpr .r12) : Consts t := by
  have e : ∀ k < 4, t.vpr (treg k) = s.vpr (treg k) := fun k hk => by
    rcases k with _ | _ | _ | _ | k
    all_goals first | omega | exact hv _ (by decide) (by decide)
  exact ⟨by rw [e 0 (by decide)]; exact h.inLo, by rw [e 1 (by decide)]; exact h.inHi,
    by rw [e 2 (by decide)]; exact h.outLo, by rw [e 3 (by decide)]; exact h.outHi, by rw [hg]; exact h.mask⟩

/-- The registers `affine` writes are not the tables. -/
theorem treg_ne (k : Nat) : treg k ≠ .v0 ∧ treg k ≠ .v1 := by
  rcases k with _ | _ | _ | _ | k <;> simp [treg]

theorem affine_run (s : State) {lo hi : VReg} {tl th : Vector Byte 16} (hlo : TabOk (s.vpr lo) tl)
    (hhi : TabOk (s.vpr hi) th) (hl : lo ≠ .v0 ∧ lo ≠ .v1) (hh : hi ≠ .v0 ∧ hi ≠ .v1)
    (hm : s.gpr .r12 = 0x0f0f0f0f) :
    ∃ t, runBlock isa (affine lo hi) s = some t ∧
      (∀ k < 4, vbyte (t.vpr .v0) (7 - k) = aff tl th (gbyte (s.gpr .r9) k)) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a := s.write .r10 (s.gpr .r9 &&& s.gpr .r12)
  let b := a.write .r11 (((a.gpr .r9).setWidth 32 >>> 4).setWidth 64)
  let c := b.write .r11 (b.gpr .r11 &&& b.gpr .r12)
  let d : State := { c.writeV .v0 (c.gpr .r10 ++ c.unknowns 0) with unknowns := fun i => c.unknowns (i + 1) }
  let e : State := { d.writeV .v1 (d.gpr .r11 ++ d.unknowns 0) with unknowns := fun i => d.unknowns (i + 1) }
  let f := e.writeV .v0 (ofVBytes fun i =>
      let j := (vbyte (e.vpr .v0) i).toNat % 32
      if j < 16 then vbyte (e.vpr lo) j else vbyte (e.vpr lo) (j - 16))
  let g := f.writeV .v1 (ofVBytes fun i =>
      let j := (vbyte (f.vpr .v1) i).toNat % 32
      if j < 16 then vbyte (f.vpr hi) j else vbyte (f.vpr hi) (j - 16))
  let h := g.writeV .v0 (g.vpr .v0 ^^^ g.vpr .v1)
  refine ⟨h, ?_, fun k hk => ?_, fun r h10 h11 => ?_, fun v h0 h1 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [affine, runBlock_cons, exec_logic, exec_lsr_w (by decide : 4 < 32), exec_mtvsrd, exec_vperm,
      exec_vxor, runStep_some, runBlock_nil]
    rfl
  · have g9 : a.gpr .r9 = s.gpr .r9 := gpr_write_of_ne _ _ (by decide)
    have r10 : gbyte (h.gpr .r10) k = gbyte (s.gpr .r9) k &&& 0x0f := by
      show gbyte (s.gpr .r9 &&& s.gpr .r12) k = _
      rw [gbyte_and, hm, gbyte_mask hk]
    have r11 : gbyte (h.gpr .r11) k = gbyte (s.gpr .r9) k >>> 4 := by
      show gbyte ((((a.gpr .r9).setWidth 32 >>> 4).setWidth 64) &&& s.gpr .r12) k = _
      rw [g9, hm, gbyte_lsr4 _ hk]
    have v0e : vbyte (e.vpr .v0) (7 - k) = gbyte (s.gpr .r9) k &&& 0x0f := by
      show vbyte (c.gpr .r10 ++ c.unknowns 0) (7 - k) = _
      rw [vbyte_append _ _ (by omega)]; exact r10
    have v1f : vbyte (f.vpr .v1) (7 - k) = gbyte (s.gpr .r9) k >>> 4 := by
      show vbyte (d.gpr .r11 ++ d.unknowns 0) (7 - k) = _
      rw [vbyte_append _ _ (by omega)]; exact r11
    have elo : TabOk (e.vpr lo) tl := by
      show TabOk (if lo = .v1 then _ else if lo = .v0 then _ else s.vpr lo) tl
      simp only [hl.2, hl.1, ite_false]; exact hlo
    have fhi : TabOk (f.vpr hi) th := by
      show TabOk (if hi = .v0 then _ else if hi = .v1 then _ else if hi = .v0 then _ else s.vpr hi) th
      simp only [hh.1, hh.2, ite_false]; exact hhi
    have gv0 : g.vpr .v0 = ofVBytes fun i =>
        let j := (vbyte (e.vpr .v0) i).toNat % 32
        if j < 16 then vbyte (e.vpr lo) j else vbyte (e.vpr lo) (j - 16) := rfl
    have gv1 : g.vpr .v1 = ofVBytes fun i =>
        let j := (vbyte (f.vpr .v1) i).toNat % 32
        if j < 16 then vbyte (f.vpr hi) j else vbyte (f.vpr hi) (j - 16) := rfl
    have hv : h.vpr .v0 = g.vpr .v0 ^^^ g.vpr .v1 := rfl
    rw [hv, vbyte_xor', gv0, gv1, vperm_byte elo (by omega) (by rw [v0e]; exact toNat_and_0f _),
      vperm_byte fhi (by omega) (by rw [v1f]; exact toNat_shr4 _), v0e, v1f]
    rfl
  · change c.gpr r = s.gpr r
    rw [gpr_write_of_ne _ _ h11, gpr_write_of_ne _ _ h11, gpr_write_of_ne _ _ h10]
  · change (g.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    change (f.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h1)]
    change (e.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    change (d.writeV .v1 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h1)]
    change (c.writeV .v0 _).vpr v = s.vpr v
    rw [vpr_writeV, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    rfl

/-! ## The S-box layer -/

/-- A word from its bytes. -/
theorem setWidth_of_gbytes {x : BitVec 64} {y : BitVec 32}
    (h : ∀ k < 4, gbyte x k = y.extractLsb' (8 * k) 8) : x.setWidth 32 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (BitVec.getLsbD · (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and] at e
  rw [show 8 * (i / 8) + i % 8 = i by omega] at e
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]; exact e

theorem bytes4 (a3 a2 a1 a0 : BitVec 8) :
    (a3 ++ a2 ++ a1 ++ a0).extractLsb' 0 8 = a0 ∧ (a3 ++ a2 ++ a1 ++ a0).extractLsb' 8 8 = a1 ∧
    (a3 ++ a2 ++ a1 ++ a0).extractLsb' 16 8 = a2 ∧ (a3 ++ a2 ++ a1 ++ a0).extractLsb' 24 8 = a3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    repeat' split
    all_goals first | omega | (congr 1; omega)

/-- Byte `k` of `τ(w)`. -/
theorem tau_byte (w : BitVec 32) {k : Nat} (hk : k < 4) :
    (Spec.Sm4.tau w).extractLsb' (8 * k) 8 = Spec.Sm4.sbox.getD (w.extractLsb' (8 * k) 8).toNat 0 := by
  have e : ∀ j, (w >>> (8 * j)).setWidth 8 = w.extractLsb' (8 * j) 8 := fun j => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_ushiftRight, hi]
  unfold Spec.Sm4.tau
  simp only [e]
  have h := bytes4 (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 3) 8).toNat 0)
    (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 2) 8).toNat 0) (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 1) 8).toNat 0)
    (Spec.Sm4.sbox.getD (w.extractLsb' (8 * 0) 8).toNat 0)
  rcases k with _ | _ | _ | _ | k
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2
  · omega

theorem gbyte_setWidth (x : BitVec 64) {k : Nat} (hk : k < 4) :
    (x.setWidth 32).extractLsb' (8 * k) 8 = gbyte x k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_setWidth, hi]; omega

theorem tau_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa tau s = some t ∧
      (t.gpr .r9).setWidth 32 = Spec.Sm4.tau ((s.gpr .r9).setWidth 32) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  obtain ⟨a, ae, ab, ag, av, am, ard, awr, asp, asy⟩ :=
    affine_run s hc.inLo hc.inHi (treg_ne 0) (treg_ne 1) hc.mask
  let b := a.writeV .v0 (ofVBytes fun i => VectorCrypto.aesSbox (vbyte (a.vpr .v0) i))
  let c := b.write .r9 (vdword (b.vpr .v0) 0)
  have bv : ∀ v, b.vpr v = if v = .v0 then ofVBytes (fun i => VectorCrypto.aesSbox (vbyte (a.vpr .v0) i))
      else a.vpr v := fun v => vpr_writeV _ _ _ _
  have cv : ∀ v, c.vpr v = b.vpr v := fun _ => rfl
  have cc : Consts c := hc.of_eq (fun v h0 h1 => by
      rw [cv, bv, ite_eq_right_iff.mpr (fun e => absurd e h0)]; exact av v h0 h1)
    ((gpr_write_of_ne _ _ (by decide)).trans (ag _ (by decide) (by decide)))
  have cb : ∀ k < 4, gbyte (c.gpr .r9) k =
      VectorCrypto.aesSbox (aff inLo inHi (gbyte (s.gpr .r9) k)) := fun k hk => by
    rw [show c.gpr .r9 = vdword (b.vpr .v0) 0 from gpr_write_self _ _ _, gbyte_vdword _ (by omega), bv]
    simp only [↓reduceIte]
    rw [vbyte_packed _ (by omega), ab k hk]
  obtain ⟨d, de, db, dg, dv, dm, drd, dwr, dsp, dsy⟩ :=
    affine_run c cc.outLo cc.outHi (treg_ne 2) (treg_ne 3) cc.mask
  let e := d.write .r9 (vdword (d.vpr .v0) 0)
  refine ⟨e, ?_, ?_, fun r h9 h10 h11 => ?_, fun v h0 h1 => ?_, dm.trans am, drd.trans ard, dwr.trans awr,
    dsp.trans asp, dsy.trans asy⟩
  · have hb : runBlock isa ([.vop (.sbox .v0 .v0), .mfvsrd .r9 .v0] : List Instr) a = some c := by
      rw [runBlock_cons, exec_vsbox, runStep_some, runBlock_cons, exec_mfvsrd, runStep_some, runBlock_nil]
    have hd : runBlock isa ([.mfvsrd .r9 .v0] : List Instr) d = some e := by
      rw [runBlock_cons, exec_mfvsrd, runStep_some, runBlock_nil]
    rw [tau, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, ae,
      Option.bind_some, hb, Option.bind_some, de, Option.bind_some, hd]
  · refine setWidth_of_gbytes fun k hk => ?_
    rw [tau_byte _ hk, gbyte_setWidth _ hk]
    rw [show e.gpr .r9 = vdword (d.vpr .v0) 0 from gpr_write_self _ _ _, gbyte_vdword _ (by omega), db k hk,
      cb k hk, Proof.Aes.Vector.sbox_eq, sbox_affine]
  · rw [gpr_write_of_ne _ _ h9, dg r h10 h11, gpr_write_of_ne _ _ h9]
    exact ag r h10 h11
  · rw [show e.vpr v = d.vpr v from rfl, dv v h0 h1, cv, bv, ite_eq_right_iff.mpr (fun e => absurd e h0)]
    exact av v h0 h1

/-! ## The linear map -/

theorem rotate_complement (x : BitVec 32) (r : Nat) (hr : 0 < r) (hr' : r < 32) :
    x.rotateRight (32 - r) = x.rotateLeft r := by
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hr',
    Nat.mod_eq_of_lt (show 32 - r < 32 by omega), Nat.sub_sub_self (by omega : r ≤ 32)]
  exact BitVec.or_comm _ _

theorem linear_eq (x : BitVec 32) :
    x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 ^^^ x.rotateRight 8 =
      Spec.Sm4.linear x := by
  rw [show 30 = 32 - 2 by rfl, rotate_complement x 2 (by decide) (by decide),
    show 22 = 32 - 10 by rfl, rotate_complement x 10 (by decide) (by decide),
    show 14 = 32 - 18 by rfl, rotate_complement x 18 (by decide) (by decide),
    show 8 = 32 - 24 by rfl, rotate_complement x 24 (by decide) (by decide)]
  rfl

theorem setWidth_rot (x : BitVec 32) (k : Nat) : ((x.rotateRight k).setWidth 64).setWidth 32 = x.rotateRight k := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

theorem linear_run (s : State) :
    ∃ t, runBlock isa linear s = some t ∧
      (t.gpr .r11).setWidth 32 = Spec.Sm4.linear ((s.gpr .r9).setWidth 32) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let x := (s.gpr .r9).setWidth 32
  let a1 := s.write .r10 ((x.rotateRight 30).setWidth 64)
  let a2 := a1.write .r11 (a1.gpr .r9 ^^^ a1.gpr .r10)
  let b1 := a2.write .r10 (((a2.gpr .r9).setWidth 32 |>.rotateRight 22).setWidth 64)
  let b2 := b1.write .r11 (b1.gpr .r11 ^^^ b1.gpr .r10)
  let c1 := b2.write .r10 (((b2.gpr .r9).setWidth 32 |>.rotateRight 14).setWidth 64)
  let c2 := c1.write .r11 (c1.gpr .r11 ^^^ c1.gpr .r10)
  let d1 := c2.write .r10 (((c2.gpr .r9).setWidth 32 |>.rotateRight 8).setWidth 64)
  let d2 := d1.write .r11 (d1.gpr .r11 ^^^ d1.gpr .r10)
  refine ⟨d2, ?_, ?_, fun r h10 h11 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [linear, runBlock_cons, exec_logic, exec_rotr_w (by decide : 30 < 32),
      exec_rotr_w (by decide : 22 < 32), exec_rotr_w (by decide : 14 < 32), exec_rotr_w (by decide : 8 < 32),
      runStep_some, runBlock_nil]
    rfl
  · have e1 : a1.gpr .r9 = s.gpr .r9 := gpr_write_of_ne _ _ (by decide)
    have e2 : a2.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e1
    have e3 : b1.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e2
    have e4 : b2.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e3
    have e5 : c1.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e4
    have e6 : c2.gpr .r9 = s.gpr .r9 := (gpr_write_of_ne _ _ (by decide)).trans e5
    have f2 : (a2.gpr .r11).setWidth 32 = x ^^^ x.rotateRight 30 := by
      rw [show a2.gpr .r11 = a1.gpr .r9 ^^^ a1.gpr .r10 from gpr_write_self _ _ _, e1,
        show a1.gpr .r10 = _ from gpr_write_self _ _ _, BitVec.setWidth_xor, setWidth_rot]
    have f4 : (b2.gpr .r11).setWidth 32 = x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 := by
      rw [show b2.gpr .r11 = b1.gpr .r11 ^^^ b1.gpr .r10 from gpr_write_self _ _ _,
        show b1.gpr .r11 = a2.gpr .r11 from gpr_write_of_ne _ _ (by decide),
        show b1.gpr .r10 = _ from gpr_write_self _ _ _, e2, BitVec.setWidth_xor, setWidth_rot, f2]
    have f6 : (c2.gpr .r11).setWidth 32 = x ^^^ x.rotateRight 30 ^^^ x.rotateRight 22 ^^^ x.rotateRight 14 := by
      rw [show c2.gpr .r11 = c1.gpr .r11 ^^^ c1.gpr .r10 from gpr_write_self _ _ _,
        show c1.gpr .r11 = b2.gpr .r11 from gpr_write_of_ne _ _ (by decide),
        show c1.gpr .r10 = _ from gpr_write_self _ _ _, e4, BitVec.setWidth_xor, setWidth_rot, f4]
    rw [show d2.gpr .r11 = d1.gpr .r11 ^^^ d1.gpr .r10 from gpr_write_self _ _ _,
      show d1.gpr .r11 = c2.gpr .r11 from gpr_write_of_ne _ _ (by decide),
      show d1.gpr .r10 = _ from gpr_write_self _ _ _, e6, BitVec.setWidth_xor, setWidth_rot, f6, ← linear_eq]
  · simp only [d2, d1, c2, c1, b2, b1, a2, a1, gpr_write_of_ne _ _ h10, gpr_write_of_ne _ _ h11]

/-! ## A round -/

/-- The block's words, in `wordReg 0 … 3`. -/
def words (s : State) (w : Nat) : BitVec 32 := (s.gpr (wordReg w)).setWidth 32

theorem wordReg_ne (j : Nat) : wordReg j ≠ .r9 ∧ wordReg j ≠ .r10 ∧ wordReg j ≠ .r11 ∧ wordReg j ≠ .r12 ∧
    wordReg j ≠ .r3 ∧ wordReg j ≠ .r0 := by
  have h := Nat.mod_lt j (by decide : 4 > 0)
  unfold wordReg
  generalize j % 4 = k at h
  rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem wordReg_inj : ∀ a < 4, ∀ b < 4, wordReg a = wordReg b → a = b := by decide

theorem wordReg_mod (j : Nat) : wordReg (j % 4) = wordReg j := by simp [wordReg]

/-- The round key `i` from the schedule at `r3`. -/
def rkey (s : State) (i : Nat) : BitVec 32 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 32

theorem round_run {s : State} {i : Nat} (hi : i < 32) (hc : Consts s)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa (round i) s = some t ∧
      (∀ w < 4, words t w = Proof.Sm4.sround .enc (rkey s i) (i % 4) (words s) w) ∧
      Consts t ∧
      (∀ r, r ≠ wordReg i → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let q1 := wordReg (i + 1)
  let q2 := wordReg (i + 2)
  let q3 := wordReg (i + 3)
  let ra := wordReg i
  let a := s.write .r9 ((rkey s i).setWidth 64)
  let b := a.write .r9 (a.gpr .r9 ^^^ a.gpr q1)
  let c := b.write .r9 (b.gpr .r9 ^^^ b.gpr q2)
  let d := c.write .r9 (c.gpr .r9 ^^^ c.gpr q3)
  have hm : runBlock isa ([.load .w .r9 .r3 (4 * i), .logic .xor .r9 .r9 q1, .logic .xor .r9 .r9 q2,
      .logic .xor .r9 .r9 q3] : List Instr) s = some d := by
    rw [runBlock_cons, exec_load_w (by decide) (by omega) hr, runStep_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    rfl
  have dg : ∀ r, r ≠ .r9 → d.gpr r = s.gpr r := fun r h => by
    rw [gpr_write_of_ne _ _ h, gpr_write_of_ne _ _ h, gpr_write_of_ne _ _ h, gpr_write_of_ne _ _ h]
  have ag : ∀ r, r ≠ .r9 → a.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have bg : ∀ r, r ≠ .r9 → b.gpr r = s.gpr r := fun r h => (gpr_write_of_ne _ _ h).trans (ag r h)
  have cg : ∀ r, r ≠ .r9 → c.gpr r = s.gpr r := fun r h => (gpr_write_of_ne _ _ h).trans (bg r h)
  have d9 : (d.gpr .r9).setWidth 32 = rkey s i ^^^ words s (i + 1) ^^^ words s (i + 2) ^^^ words s (i + 3) := by
    rw [show d.gpr .r9 = c.gpr .r9 ^^^ c.gpr q3 from gpr_write_self _ _ _,
      show c.gpr .r9 = b.gpr .r9 ^^^ b.gpr q2 from gpr_write_self _ _ _,
      show b.gpr .r9 = a.gpr .r9 ^^^ a.gpr q1 from gpr_write_self _ _ _,
      show a.gpr .r9 = _ from gpr_write_self _ _ _, cg _ (wordReg_ne _).1, bg _ (wordReg_ne _).1,
      ag _ (wordReg_ne _).1, BitVec.setWidth_xor, BitVec.setWidth_xor, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rfl
  have dc : Consts d := hc.of_eq (fun _ _ _ => rfl) (dg _ (by decide))
  obtain ⟨e, ee, e9, eg, ev, em, erd, ewr, esp, esy⟩ := tau_run d dc
  obtain ⟨f, fe, f11, fg, fv, fm, frd, fwr, fsp, fsy⟩ := linear_run e
  let t := f.write ra (f.gpr ra ^^^ f.gpr .r11)
  have tg : ∀ r, r ≠ ra → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r := fun r ha h9 h10 h11 => by
    rw [gpr_write_of_ne _ _ ha, fg r h10 h11, eg r h9 h10 h11, dg r h9]
  have tv : ∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v := fun v h0 h1 => by
    rw [show t.vpr v = f.vpr v from rfl, fv, ev v h0 h1]; rfl
  refine ⟨t, ?_, fun w hw => ?_, hc.of_eq tv (tg _ (wordReg_ne i).2.2.2.1.symm (by decide) (by decide) (by decide)), tg, tv,
    fm.trans (em.trans rfl), frd.trans (erd.trans rfl), fwr.trans (ewr.trans rfl), fsp.trans (esp.trans rfl),
    fsy.trans (esy.trans rfl)⟩
  · rw [round, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, hm,
      Option.bind_some, ee, Option.bind_some, fe, Option.bind_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_nil]
  · by_cases h : w = i % 4
    · subst w
      have ha := wordReg_ne i
      rw [words, wordReg_mod, show t.gpr ra = f.gpr ra ^^^ f.gpr .r11 from gpr_write_self _ _ _,
        fg _ ha.2.1 ha.2.2.1, eg _ ha.1 ha.2.1 ha.2.2.1, dg _ ha.1, BitVec.setWidth_xor, f11, e9, d9]
      have e : ∀ k, wordReg (i % 4 + k) = wordReg (i + k) := fun k => by
        rw [← wordReg_mod (i % 4 + k), ← wordReg_mod (i + k), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      simp only [Proof.Sm4.sround, ite_true, Impl.Sm4.Lin.t_enc, words, wordReg_mod, e, Spec.Sm4.t]
      ac_rfl
    · have hreg : wordReg w ≠ ra := fun e => h (wordReg_inj w hw _ (Nat.mod_lt _ (by decide))
        (e.trans (wordReg_mod i).symm))
      have hn := wordReg_ne w
      rw [words, tg _ hreg hn.1 hn.2.1 hn.2.2.1]
      simp only [Proof.Sm4.sround, h, ite_false, words]

/-! ## The rounds -/

open VG.Proof.Sm4 (sround quads)

/-- The first `n` rounds, in place. -/
def steps (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) : Nat → BitVec 32 :=
  (List.range n).foldl (fun z i => sround .enc (K i) (i % 4) z) x

theorem steps_succ (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) :
    steps K (n + 1) x = sround .enc (K n) (n % 4) (steps K n x) := by
  simp only [steps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sround_congr (k : BitVec 32) {a w : Nat} {x y : Nat → BitVec 32}
    (ha : a < 4) (h : ∀ j < 4, x j = y j) (hw : w < 4) :
    sround .enc k a x w = sround .enc k a y w := by
  unfold sround
  split
  · rw [h a ha, h _ (Nat.mod_lt _ (by decide)), h _ (Nat.mod_lt _ (by decide)), h _ (Nat.mod_lt _ (by decide))]
  · exact h w hw

theorem steps_quads (K : Nat → BitVec 32) (x : Nat → BitVec 32) (n : Nat) :
    steps K (4 * n) x = quads .enc K n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [steps, Proof.Sm4.range_four, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change sround .enc (K (4 * n + 3)) ((4 * n + 3) % 4)
      (sround .enc (K (4 * n + 2)) ((4 * n + 2) % 4)
        (sround .enc (K (4 * n + 1)) ((4 * n + 1) % 4)
          (sround .enc (K (4 * n)) ((4 * n) % 4) (steps K (4 * n) x)))) = _
    rw [ih, show (4 * n) % 4 = 0 by omega, show (4 * n + 1) % 4 = 1 by omega,
      show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 3) % 4 = 3 by omega]
    rfl

/-- The registers the rounds write. -/
def written : List Reg := [.r4, .r6, .r7, .r8, .r9, .r10, .r11]

theorem wordReg_mem (j : Nat) : wordReg j ∈ written := by
  have h := Nat.mod_lt j (by decide : 4 > 0)
  unfold wordReg
  generalize j % 4 = k at h
  rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem rounds_run (s : State) (n : Nat) (hn : n ≤ 32) (hc : Consts s)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap round) s = some t ∧
      (∀ w < 4, words t w = steps (rkey s) n (words s) w) ∧
      Consts t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ .v0 → v ≠ .v1 → t.vpr v = s.vpr v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ _ => rfl, hc, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ac, ag, av, am, ard, awr, asp, asy⟩ := ih (by omega)
    have ab : a.gpr .r3 = s.gpr .r3 := ag _ (by decide)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .r3 + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [ard, awr, ab]; exact hr n (by omega)
    obtain ⟨b, be, bw, bc, bg, bv, bm, brd, bwr, bsp, bsy⟩ := round_run (by omega) ac ar
    refine ⟨b, ?_, fun w hw => ?_, bc, fun r hr => ?_, fun v h0 h1 => (bv v h0 h1).trans (av v h0 h1),
      bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp, bsy.trans asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · rw [bw w hw, steps_succ, show rkey a n = rkey s n by rw [rkey, rkey, am, ab]]
      exact sround_congr _ (Nat.mod_lt _ (by decide)) aw hw
    · have hreg : r ≠ wordReg n := fun he => hr (he ▸ wordReg_mem n)
      have h9 : r ≠ .r9 := fun he => hr (by simp [written, he])
      have h10 : r ≠ .r10 := fun he => hr (by simp [written, he])
      have h11 : r ≠ .r11 := fun he => hr (by simp [written, he])
      exact (bg r hreg h9 h10 h11).trans (ag r hr)

open VG.Impl.Modes.PPC64LE (sb)
open VG.Impl.Sm4.PPC64LE (tailSlot slots)
open VG.Proof.Modes.PPC64LE (ScrIn coreRegion blkRegion blkAddr Layout CoreSpec kept KeptBut)
open VG.Spec.Aes (bytesAt)
/-! ## The tables -/

/-- Table `k` as `lxvd2xTbl` loads it. -/
abbrev tval (k : Nat) : BitVec 128 := tableWords.getD (2 * k) 0 ++ tableWords.getD (2 * k + 1) 0

theorem tval_ok : TabOk (tval 0) inLo ∧ TabOk (tval 1) inHi ∧ TabOk (tval 2) outLo ∧ TabOk (tval 3) outHi := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro j hj; revert j; decide)

theorem tableWords_length : tableWords.length = 8 := rfl

theorem treg_inj : ∀ a < 4, ∀ b < 4, treg a = treg b → a = b := by decide

/-- After loading the tables `0 … n - 1`. -/
theorem loadT_run (s : State) (n : Nat) (hn : n ≤ 4) (h10 : s.gpr .r10 = s.syms tableSym) :
    ∃ t, runBlock isa ((List.range n).flatMap fun k =>
        [.li .r11 (16 * k), .lxvd2xTbl (treg k) .r10 .r11 tableSym tableWords]) s = some t ∧
      (∀ k < n, t.vpr (treg k) = tval k) ∧
      (∀ v, (∀ k < n, v ≠ treg k) → t.vpr v = s.vpr v) ∧
      (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms ∧ t.lr = s.lr ∧
      t.unknowns = s.unknowns := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, av, avo, ag, am, ard, awr, asp, asy, alr, aun⟩ := ih (by omega)
    let b := a.write .r11 (BitVec.ofNat 64 (16 * n))
    let c := b.writeV (treg n) (tval n)
    have hb10 : b.gpr .r10 = b.syms tableSym := by
      rw [show b.syms = s.syms from asy, gpr_write_of_ne _ _ (by decide), ag _ (by decide), h10]
    have hb11 : (b.gpr .r11).toNat = 16 * n := by
      rw [gpr_write_self, BitVec.toNat_ofNat]; omega
    have hc : exec (.lxvd2xTbl (treg n) .r10 .r11 tableSym tableWords) b = some c := by
      have e1 : 16 * n / 8 = 2 * n := by omega
      have e2 : 16 * n % 8 = 0 := by omega
      have e3 : 2 * n + 2 ≤ 8 := by omega
      have e4 : (Reg.r10 ≠ .r0) := by decide
      simp only [exec, hb10, hb11, e1, e2, e3, e4, tableWords_length, ne_eq, not_false_eq_true, and_self,
        ↓reduceIte]
      rfl
    refine ⟨c, ?_, fun k hk => ?_, fun v hv => ?_, fun r hr => ?_, am, ard, awr, asp, asy, alr, aun⟩
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
      (∀ v, v ≠ .v12 → v ≠ .v13 → v ≠ .v14 → v ≠ .v15 → t.vpr v = s.vpr v) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  let a : State := { s.write .r10 (s.syms tableSym) with lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) }
  have a10 : a.gpr .r10 = a.syms tableSym := by
    show (s.write .r10 (s.syms tableSym)).gpr .r10 = s.syms tableSym; exact gpr_write_self _ _ _
  obtain ⟨b, be, bv, bvo, bg, bm, brd, bwr, bsp, bsy, _, _⟩ := loadT_run a 4 (by decide) a10
  let c := b.write .r12 (((0x0f0f : BitVec 16) ++ (0 : BitVec 16)).signExtend 64)
  let d := c.write .r12 (c.gpr .r12 ||| (0x0f0f : BitVec 16).setWidth 64)
  have dv : ∀ v, d.vpr v = b.vpr v := fun _ => rfl
  have dg : ∀ r, r ≠ .r12 → d.gpr r = b.gpr r := fun r h => (gpr_write_of_ne _ _ h).trans (gpr_write_of_ne _ _ h)
  have ok := tval_ok
  refine ⟨d, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, fun v h12 h13 h14 h15 => ?_, fun r h10 h11 h12 => ?_, bm, brd, bwr, bsp, bsy⟩
  · rw [loadTables, List.cons_append, runBlock_cons]
    simp only [exec, ne_eq, show ¬(Reg.r10 = .r0) by decide, not_false_eq_true, ↓reduceIte]
    rw [runStep_some, VG.Interleave.runBlock_append, be, Option.bind_some, runBlock_cons, exec_lis, runStep_some,
      runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  · rw [dv, bv 0 (by decide)]; exact ok.1
  · rw [dv, bv 1 (by decide)]; exact ok.2.1
  · rw [dv, bv 2 (by decide)]; exact ok.2.2.1
  · rw [dv, bv 3 (by decide)]; exact ok.2.2.2
  · rw [gpr_write_self, gpr_write_self, mask_eq]
  · rw [dv, bvo v fun k hk => ?_]
    · rfl
    · rcases k with _ | _ | _ | _ | k
      all_goals first | omega | (intro e; subst e; contradiction)
  · rw [dg r h12, bg r h11]
    exact gpr_write_of_ne _ _ h10

/-! ## The block -/

theorem readBE_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    rev32 (m.readW (p + BitVec.ofNat 64 (4 * i)) 32) = Spec.Sm4.wordAt (Spec.Sm4.blockAt m p) (4 * i) := by
  rw [rev32_readW, Spec.Sm4.wordAt]
  rw [Proof.Sm4.blockAt_getD _ _ (by omega), Proof.Sm4.blockAt_getD _ _ (by omega),
    Proof.Sm4.blockAt_getD _ _ (by omega), Proof.Sm4.blockAt_getD _ _ (by omega)]
  have add1 (j : Nat) : p + BitVec.ofNat 64 (j + 1) = p + BitVec.ofNat 64 j + 1 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  simp only [show 4 * i + 2 = (4 * i + 1) + 1 by omega, show 4 * i + 3 = ((4 * i + 1) + 1) + 1 by omega, add1]

theorem wordReg_ne_sb (j : Nat) : wordReg j ≠ sb ∧ wordReg j ≠ .r0 := by
  have h := Nat.mod_lt j (by decide : 4 > 0)
  unfold wordReg
  generalize j % 4 = k at h
  rcases k with _ | _ | _ | _ | k <;> first | omega | decide

/-- The offset of word `i` of the block. -/
abbrev woff (i : Nat) : Nat := 8 * tailSlot + 4 * i

theorem loads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hr : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (woff i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap fun i =>
        [.li .r0 (woff i), .loadRev .w (wordReg i) sb .r0]) s = some t ∧
      (∀ j < n, words t j = rev32 (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (woff j)) 32)) ∧
      (∀ r, r ≠ .r0 → (∀ j < n, r ≠ wordReg j) → t.gpr r = s.gpr r) ∧
      t.vpr = s.vpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega), fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, av, am, ard, awr, asp, asy⟩ := ih (by omega)
    have ab : a.gpr sb = s.gpr sb := ag _ (by decide) (fun j _ => (wordReg_ne_sb j).1.symm)
    let b := a.write .r0 (BitVec.ofNat 64 (woff n))
    have bb : b.gpr sb + b.gpr .r0 = s.gpr sb + BitVec.ofNat 64 (woff n) := by
      rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, ab]
    have br : InRegions (b.rd ++ b.wr) (b.gpr sb + b.gpr .r0) 4 := by
      rw [bb]; show InRegions (a.rd ++ a.wr) _ 4; rw [ard, awr]; exact hr n (by omega)
    let c := b.write (wordReg n) ((rev32 (b.mem.readW (b.gpr sb + b.gpr .r0) 32)).setWidth 64)
    have hw := wordReg_ne_sb n
    refine ⟨c, ?_, fun j hj => ?_, fun r h0 hr' => ?_, av, am, ard, awr, asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons,
        exec_li (by rw [woff, tailSlot_eq]; omega), runStep_some, runBlock_cons,
        exec_loadRev_w (by decide) br, runStep_some, runBlock_nil]
    · by_cases h : j = n
      · subst j
        rw [words, show c.gpr (wordReg n) = _ from gpr_write_self _ _ _, bb,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        show rev32 (a.mem.readW _ 32) = _
        rw [am]
      · rw [words, gpr_write_of_ne _ _ (fun e => h (wordReg_inj j (by omega) n (by omega) e)),
          gpr_write_of_ne _ _ (wordReg_ne_sb j).2]
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
        [.li .r0 (woff i), .storeRev .w (wordReg (3 - i)) sb .r0]) s = some t ∧
      (∀ j < n, t.mem.readW (s.gpr sb + BitVec.ofNat 64 (woff j)) 32 = rev32 (words s (3 - j))) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr sb + BitVec.ofNat 64 (8 * tailSlot), 16⟩] s.mem t.mem ∧
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
    have bv : b.gpr (wordReg (3 - n)) = s.gpr (wordReg (3 - n)) :=
      (gpr_write_of_ne _ _ (wordReg_ne_sb _).2).trans (ag _ (wordReg_ne_sb _).2)
    let m' := b.mem.writeW (s.gpr sb + BitVec.ofNat 64 (woff n)) (rev32 (words s (3 - n)))
    let c : State := { b with mem := m' }
    have bf : Frame [⟨s.gpr sb + BitVec.ofNat 64 (woff n), 4⟩] a.mem c.mem := frame_write_word _ _ _
    refine ⟨c, ?_, fun j hj => ?_, fun r h0 => (gpr_write_of_ne _ _ h0).trans (ag r h0), ?_, av, ard, awr,
      asp, asy⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons,
        exec_li (by rw [woff, tailSlot_eq]; omega), runStep_some, runBlock_cons,
        exec_storeRev_w (by decide) br, runStep_some, runBlock_nil, bb, bv]
      rfl
    · by_cases h : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [bf.readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr sb) (by rw [woff, woff, tailSlot_eq]; omega)
            (by rw [woff, tailSlot_eq]; omega) (by rw [woff, tailSlot_eq]; omega)) (by decide)]
        exact aw j (by omega)
    · refine af.trans (bf.sub (fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst r
      refine ⟨_, List.mem_cons_self, ?_⟩
      rw [woff, ← VG.Offset.add_add (s.gpr sb) (8 * tailSlot) (4 * n)]
      exact VG.Offset.sub_base _ (by omega : 4 * n + 4 ≤ 16)

theorem stored_bytes {m : Mem} {p : Addr} {z : Nat → BitVec 32}
    (h : ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = rev32 (z (3 - i))) :
    bytesAt m p 16 = (Proof.Sm4.outBlock z).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i hi _
  have hi16 : i < 16 := by simpa [bytesAt] using hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, Vector.getElem_toList]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have b := Mem.readW_byte m (p + BitVec.ofNat 64 (4 * (i / 4))) (i := i % 4) (by omega)
  rw [VG.Offset.add_add, show 4 * (i / 4) + i % 4 = i by omega, h (i / 4) (by omega)] at b
  rw [b, BitVec.getLsbD_extractLsb', Proof.Sm4.getLsbD_outBlock' z hi16 hj]
  simp only [hj, decide_true, Bool.true_and]
  change (byteRev32 (z (3 - i / 4))).getLsbD (8 * (i % 4) + j) = _
  rw [byteRev32_getLsbD _ (by omega)]
  congr 1 <;> omega

/-- Bit `i` of a little-endian 32-bit word is bit `i % 8` of its byte `i / 8`. -/
theorem getLsbD_readW32' (m : Mem) (a : Addr) {i : Nat} (hi : i < 32) :
    (m.readW a 32).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega

theorem schedule_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 32) :
    m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = (Spec.Sm4.scheduleAt m p).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [Proof.Aes.getD_eq _ hi, getLsbD_readW32' m _ hj, VG.Offset.add_add]
  have h := Proof.Sm4.getLsbD_scheduleAt m p (i := i) (c := j / 8) (j := j % 8) hi (by omega) (by omega)
  rw [show 8 * (j / 8) + j % 8 = j by omega] at h
  rw [h]

theorem steps_congr (K L : Nat → BitVec 32) (n : Nat) (x y : Nat → BitVec 32)
    (hk : ∀ i < n, K i = L i) (hx : ∀ j < 4, x j = y j) :
    ∀ w < 4, steps K n x w = steps L n y w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    intro w hw
    rw [steps_succ, steps_succ, hk n (by omega)]
    exact sround_congr _ (Nat.mod_lt _ (by decide)) (ih (fun i hi => hk i (by omega))) hw

/-! ## The key, in place -/

/-- The key is ready: the schedule at `r3`, apart from the core's slots and
the regions `ws`. -/
def Ready (s : State) (B : Addr) (ws : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  Proof.Sm4.PPC64LE.KeyArgs s (coreRegion core B :: ws) k

/-- The schedule survives a frame within its regions. -/
theorem keyArgs_frame {s s' : State} {rs rs' : List Region} {k : Spec.Sm4.Schedule}
    (h : Proof.Sm4.PPC64LE.KeyArgs s rs k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd)
    (hf : Frame rs' s.mem s'.mem) (hs : ∀ r ∈ rs', ∃ r' ∈ rs, Region.Sub r r') :
    Proof.Sm4.PPC64LE.KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [e, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  refine (Proof.Sm4.scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 128⟩) (fun r hr => ?_)
    (by show 128 ≤ 2 ^ 64; omega) hi).symm
  obtain ⟨r', hr', hsub⟩ := hs r hr
  exact (hdis r' hr').sub_right hsub

theorem kept_ne : ∀ r ∈ kept, r ≠ .r0 ∧ r ∉ written ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧ r ≠ sb := by decide

/-! ## The block -/

theorem crypt_wp {s : State} {B : Addr} {ws : List Region} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B core.total) (hk : Ready s B ws k) :
    WP isa core.crypt s fun t => t.gpr sb = B ∧ (∀ r ∈ kept, t.gpr r = s.gpr r) ∧ Ready t B ws k ∧
      Frame [coreRegion core B] s.mem t.mem ∧
      (∀ j < core.G, bytesAt t.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Sm4.cipher k (bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hfB : B.toNat + 8 * (slots + 6) ≤ 2 ^ 64 := hs.fit
  have hwr : (⟨B, 8 * (slots + 6)⟩ : Region) ∈ s.wr := hs.wr
  have hk' := hk
  obtain ⟨p, hp, hsched, hin, hfit, _⟩ := hk'
  change WP isa (.block (loadTables ++ loadBlock ++ rounds ++ storeBlock)) s _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨a, ae, ac, _, ag, am, ard, awr, _, _⟩ := loadTables_run s
  refine WP.of_runBlock ⟨a, ae, ?_⟩
  have ab : a.gpr sb = B := (ag _ (by decide) (by decide) (by decide)).trans hB
  have ar : ∀ i < 4, InRegions (a.rd ++ a.wr) (a.gpr sb + BitVec.ofNat 64 (woff i)) 4 := fun i hi => by
    rw [ard, awr, ab]
    exact ⟨_, List.mem_append_right _ hwr, VG.Offset.contains_base B
      (by rw [woff, tailSlot_eq, slots_eq]; omega) (by rw [woff, tailSlot_eq]; omega)⟩
  obtain ⟨b, be, bw, bg, bv, bm, brd, bwr, _, _⟩ := loads_run a 4 (by decide) ar
  refine WP.of_runBlock ⟨b, be, ?_⟩
  have bc : Consts b := ac.of_eq (fun v _ _ => by rw [bv]) (bg _ (by decide) (fun j _ => (wordReg_ne j).2.2.2.1.symm))
  have b3 : b.gpr .r3 = p := by
    rw [bg _ (by decide) (fun j _ => (wordReg_ne j).2.2.2.2.1.symm), ag _ (by decide) (by decide) (by decide), hp]
  have bmem : b.mem = s.mem := bm.trans am
  have br : ∀ i < 32, InRegions (b.rd ++ b.wr) (b.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := fun i hi => by
    rw [brd, ard, b3]
    exact ⟨_, List.mem_append_left _ hin, VG.Offset.contains_base p (by omega) (by omega)⟩
  obtain ⟨d, de, dw, _, dg, _, dm, drd, dwr, _, _⟩ := rounds_run b 32 (by decide) bc br
  refine WP.of_runBlock ⟨d, de, ?_⟩
  have dbase : d.gpr sb = B := by
    rw [dg _ (by decide), bg _ (by decide) (fun j _ => (wordReg_ne_sb j).1.symm), ab]
  have dmem : d.mem = s.mem := dm.trans bmem
  let A := B + BitVec.ofNat 64 (8 * tailSlot)
  let init := Proof.Sm4.ofBlock (Spec.Sm4.blockAt s.mem A)
  let z := Proof.Sm4.quads .enc (fun i => k.getD i 0) 8 init
  have initial : ∀ w < 4, words b w = init w := fun w hw => by
    rw [bw w hw, am, ab, woff, ← VG.Offset.add_add B (8 * tailSlot) (4 * w), readBE_word _ _ w hw]
    rfl
  have dwords : ∀ w < 4, words d w = z w := fun w hw => by
    rw [dw w hw, steps_congr (rkey b) (fun i => k.getD i 0) 32 (words b) init
      (fun i hi => by rw [rkey, bmem, b3, hsched, schedule_readW _ _ i hi]) initial w hw]
    change steps (fun i => k.getD i 0) (4 * 8) init w = z w
    rw [steps_quads]
  have dr : ∀ i < 4, InRegions d.wr (d.gpr sb + BitVec.ofNat 64 (woff i)) 4 := fun i hi => by
    rw [dwr, bwr, awr, dbase]
    exact ⟨_, hwr, VG.Offset.contains_base B
      (by rw [woff, tailSlot_eq, slots_eq]; omega) (by rw [woff, tailSlot_eq]; omega)⟩
  obtain ⟨e, ee, ew, eg, ef, _, erd, ewr, _, _⟩ := stores_run d 4 (by decide) dr
  refine WP.of_runBlock ⟨e, ee, ?_⟩
  have keptE : ∀ r ∈ kept, e.gpr r = s.gpr r := fun r hr => by
    have h := kept_ne r hr
    rw [eg r h.1, dg r h.2.1, bg r h.1 (fun j _ he => h.2.1 (he ▸ wordReg_mem j)), ag r h.2.2.1 h.2.2.2.1 h.2.2.2.2.1]
  have frame : Frame [coreRegion core B] s.mem e.mem := by
    rw [← dmem]
    refine ef.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨_, List.mem_cons_self, ?_⟩
    rw [dbase]
    exact VG.Offset.sub_base B (by rw [tailSlot_eq]; show 768 + 16 ≤ 8 * slots; rw [slots_eq]; omega)
  have output : bytesAt e.mem A 16 = (Proof.Sm4.outBlock z).toList := by
    apply stored_bytes
    intro i hi
    rw [VG.Offset.add_add, ← dbase, show 8 * tailSlot + 4 * i = woff i from rfl, ew i hi, dwords (3 - i) (by omega)]
  refine ⟨(eg _ (by decide)).trans dbase, keptE, keyArgs_frame hk (keptE .r3 (by decide)) ?_ frame
    (fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self, fun _ h => h⟩),
    frame, fun j hj => ?_, ?_, ?_⟩
  · rw [erd, drd, brd, ard]
  · have hj0 : j = 0 := by have : j < 1 := hj; omega
    subst hj0
    have ha : blkAddr core B 0 = A := by
      show B + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (4 * 4 * 0) = A
      rw [VG.Offset.add_add, Nat.mul_zero, Nat.add_zero]
    show bytesAt e.mem (blkAddr core B 0) 16 = Spec.Sm4.cipher k (bytesAt s.mem (blkAddr core B 0) 16)
    rw [ha, output, Proof.Sm4.cipher_bytes]
  · rw [erd, drd, brd, ard]
  · rw [ewr, dwr, bwr, awr]

/-! ## The core -/

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule}
    (_hs : ScrIn s B core.total) (hR : (⟨B, 8 * core.total⟩ : Region) ∈ rs)
    (hk : Proof.Sm4.PPC64LE.KeyArgs s rs k) (hB : s.gpr sb = B) :
    WP isa core.prepare s fun s' => Ready s' B rs k ∧ s'.gpr sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [coreRegion core B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.of_runBlock ⟨s, rfl, ?_, hB, fun _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
  obtain ⟨p, hp, hk', hin, hfit, hdis⟩ := hk
  refine ⟨p, hp, hk', hin, hfit, fun r hr => ?_⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact (hdis _ hR).sub_right (Region.sub_prefix (by show 8 * slots ≤ 8 * (slots + 6); omega))
  · exact hdis r hr

theorem ready_frame {s s' : State} {B : Addr} {ws : List Region} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready s B ws k) (e : s'.gpr .r3 = s.gpr .r3) (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ ws, Region.Sub r r')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) :
    Ready s' B ws k := keyArgs_frame h e hrd hf fun r hr => by
  rcases hd r hr with _ | h'
  · obtain ⟨r', hr', hs'⟩ := hsub r hr
    exact ⟨r', List.mem_cons_of_mem _ hr', hs'⟩
  · have hb : Region.Sub (blkRegion core B) (coreRegion core B) :=
      VG.Offset.sub_base B (by show 8 * tailSlot + 4 * 4 * 1 ≤ 8 * slots; rw [tailSlot_eq, slots_eq]; omega)
    exact ⟨_, List.mem_cons_self, fun x hx => hb x (h' x hx)⟩

/-- The single-block core meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Spec.Sm4.Schedule
  cipher := Spec.Sm4.cipher
  KeyArgs := Proof.Sm4.PPC64LE.KeyArgs
  Ready := Ready
  cipher_len _ _ := by show _ = 16; simp [Spec.Sm4.cipher]
  layout := ⟨by decide, .inr rfl, by decide, by decide, by decide⟩
  keyArgs_congr h e hrd hwr _ hf := Proof.Sm4.PPC64LE.keyArgs_congr h e.r3 hrd hwr hf
  ready_frame h e hrd _ _ hf hsub hd := ready_frame h e.r3 hrd hf hsub hd
  prepare_wp hB hs hR hk := prepare_wp hs hR hk hB
  crypt_wp hB hs hR := crypt_wp hB hs hR

end VG.Proof.Sm4.PPC64LE.Serial
