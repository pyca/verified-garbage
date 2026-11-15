module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
meta import VerifiedGarbage.Proof.Framework.AArch64.Tbl
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: it needs the lemmas of the AES extension's proofs (`Aese/`), which import `Blocks.lean`.

/-!
# AES on AArch64: one block by table lookups

`OneBlock.core` is FIPS 197's cipher on the state in `v0` (`core_ok`):
ShiftRows by `tbl` is `aesShiftRows` (`tbl_shiftRows`), `select` on the
S-box in the table registers is `aesMapBytes aesSbox` (`subShift_run`), and
`mix` is `aesMixColumns` (`mix_bytes`: the columns are the 32-bit lanes, and
their rotations by one and two bytes are `ushr` with `sli` and `rev32`),
which `Proof/Aes/Vector.lean` relates to the specification's rounds.

`vg_aes_encrypt_blocks` (`encryptBlocksN`) runs it for one block and the
bitsliced code otherwise (`encryptBlocksN_correct`), against the contract of
the bitsliced code, `blocksAArch64`.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.OneBlock

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Aes.AArch64 VG.Impl.Aes.AArch64.OneBlock
open VG.Proof.Aes.Vector (st KeyIs rnds rnds_zero rnds_succ cipher_eq eor_st aese_st aesmc_st keyIs_readW
  vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns ext_vbyte)
open VG.Spec.Aes (roundKey cipher addRoundKey bytesAt)

/-! ## ShiftRows -/

theorem shiftIdx_byte : ∀ i < 16, (vbyte shiftIdx i).toNat = i % 4 + 4 * ((i / 4 + i % 4) % 4) := by
  decide +kernel

/-- `tbl` of the state by `shiftIdx` is ShiftRows. -/
theorem tbl_shiftRows (x : BitVec 128) :
    (ofVBytes fun i =>
      let idx := (vbyte shiftIdx i).toNat
      if idx < 16 then vbyte x idx else 0) = aesShiftRows x := by
  apply ext_vbyte
  intro i hi
  rw [vbyte_ofVBytes _ hi, vbyte_shiftRows _ hi]
  simp only [shiftIdx_byte i hi]
  rw [ite_eq_left (by omega_arith)]

/-! ## MixColumns -/

/-- `2 • b` in GF(2⁸), as `mix` computes it. -/
def xt (b : BitVec 8) : BitVec 8 := b <<< 1 ^^^ (b.sshiftRight 7 &&& 0x1b)

theorem mul2_eq : ∀ b : BitVec 8, aesMul 0x02 b = xt b := by decide +kernel
theorem mul3_eq : ∀ b : BitVec 8, aesMul 0x03 b = xt b ^^^ b := by decide +kernel
theorem mul1_eq : ∀ b : BitVec 8, aesMul 0x01 b = b := by decide +kernel

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_b16 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 16) : vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) := by
  simp only [VArr.map2]
  exact vbyte_ofVBytes _ he

theorem vbyte_rev32h (x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VRevOp.rev32h.eval x) e = vbyte x (4 * (e / 4) + (e % 4 + 2) % 4) := by
  simp only [VRevOp.eval]
  exact vbyte_ofVBytes _ he

/-- A byte of a vector, in its 32-bit lane. -/
theorem vbyte_vword (v : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte v e = (vword v (e / 4)).extractLsb' (8 * (e % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte, vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show 8 * (e % 4) + i < 32 by omega_arith]
  exact congrArg v.getLsbD (by omega_arith)

/-- `ushr` by 8 and `sli` by 24 of a 32-bit lane rotate it right by a byte. -/
theorem ror8_byte (a w : BitVec 32) : ∀ k < 4,
    (VShiftOp.sli.eval 24 32 (VShiftOp.ushr.eval 8 32 a w) w).extractLsb' (8 * k) 8 =
      w.extractLsb' (8 * ((k + 1) % 4)) 8 := by
  intro k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [VShiftOp.eval, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, hi,
    decide_true, Bool.true_and]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · simp [show i < 24 by omega_arith, show i < 32 by omega_arith]
  · simp [show 8 + i < 24 by omega_arith, show 8 + i < 32 by omega_arith]
    exact congrArg w.getLsbD (by omega_arith)
  · simp [show 16 + i < 24 by omega_arith, show 16 + i < 32 by omega_arith]
    exact congrArg w.getLsbD (by omega_arith)
  · have h32 : w.getLsbD (8 + (24 + i)) = false := BitVec.getLsbD_of_ge _ _ (by omega_arith)
    simp only [show ¬ 24 + i < 24 by omega_arith, show 24 + i < 32 by omega_arith, decide_true, decide_false,
      Bool.not_false, Bool.and_true, Bool.true_and, Bool.false_and, h32, Bool.false_or]
    exact congrArg w.getLsbD (by omega_arith)

/-- A byte of the rotation of the 32-bit lanes by a byte. -/
theorem vbyte_ror8 (d z : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VArr.s4.map2 (fun w a b => VShiftOp.sli.eval 24 w a b)
      (VArr.s4.map2 (fun w a b => VShiftOp.ushr.eval 8 w a b) d z) z) e =
      vbyte z (4 * (e / 4) + (e % 4 + 1) % 4) := by
  have h4 : e / 4 < 4 := by omega_arith
  rw [vbyte_vword _ he, vword_map2 _ _ _ h4, vword_map2 _ _ _ h4, ror8_byte _ _ _ (by omega_arith),
    vbyte_vword _ (show 4 * (e / 4) + (e % 4 + 1) % 4 < 16 by omega_arith),
    show (4 * (e / 4) + (e % 4 + 1) % 4) / 4 = e / 4 by omega_arith,
    show (4 * (e / 4) + (e % 4 + 1) % 4) % 4 = (e % 4 + 1) % 4 by omega_arith]

/-- `2 • x ⊕ rot₂ x`, as `mix` computes it in `v2` (`d₁` and `d₂` are what
`v1` and `v2` held). -/
def mixY (d₁ d₂ x : BitVec 128) : BitVec 128 :=
  VArr.b16.map2 (fun w a b => VShiftOp.shl.eval 1 w a b) d₂ x ^^^
    (VArr.b16.map2 (fun w a b => VShiftOp.sshr.eval 7 w a b) d₁ x &&& bc 0x1b) ^^^ VRevOp.rev32h.eval x

theorem vbyte_mixY (d₁ d₂ x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (mixY d₁ d₂ x) e = xt (vbyte x e) ^^^ vbyte x (4 * (e / 4) + (e % 4 + 2) % 4) := by
  rw [mixY, vbyte_xor, vbyte_xor, vbyte_and, vbyte_b16 _ _ _ he, vbyte_b16 _ _ _ he, vbyte_bc _ he,
    vbyte_rev32h _ he]
  rfl

/-- `mix`'s result in `v0`. -/
def mixV (d₁ d₂ x : BitVec 128) : BitVec 128 :=
  VArr.s4.map2 (fun w a b => VShiftOp.sli.eval 24 w a b)
    (VArr.s4.map2 (fun w a b => VShiftOp.ushr.eval 8 w a b) (VRevOp.rev32h.eval x) (x ^^^ mixY d₁ d₂ x))
    (x ^^^ mixY d₁ d₂ x) ^^^ mixY d₁ d₂ x

/-- `mix` is MixColumns. -/
theorem mixV_eq (d₁ d₂ x : BitVec 128) : mixV d₁ d₂ x = aesMixColumns x := by
  apply ext_vbyte
  intro e he
  have h1 : 4 * (e / 4) + (e % 4 + 1) % 4 < 16 := by omega_arith
  rw [mixV, vbyte_xor, vbyte_ror8 _ _ he, vbyte_xor, vbyte_mixY _ _ _ h1, vbyte_mixY _ _ _ he,
    vbyte_mixColumns _ he, mul2_eq, mul3_eq, mul1_eq, mul1_eq,
    show 4 * ((4 * (e / 4) + (e % 4 + 1) % 4) / 4) + ((4 * (e / 4) + (e % 4 + 1) % 4) % 4 + 2) % 4 =
      (e % 4 + 3) % 4 + 4 * (e / 4) by omega_arith,
    show 4 * (e / 4) + (e % 4 + 1) % 4 = (e % 4 + 1) % 4 + 4 * (e / 4) by omega_arith,
    show 4 * (e / 4) + (e % 4 + 2) % 4 = (e % 4 + 2) % 4 + 4 * (e / 4) by omega_arith,
    show (e % 4 + 0) % 4 + 4 * (e / 4) = e by omega_arith]
  ac_rfl

/-! ## The tables and constants -/

/-- What `setup` leaves in the vector registers. -/
structure Consts (s : State) : Prop where
  tab : ∀ k < 256, tbyte s.v k = aesSbox (BitVec.ofNat 8 k)
  v4 : s.v .v4 = shiftIdx
  v5 : s.v .v5 = bc 0x80
  v6 : s.v .v6 = bc 0x40
  v7 : s.v .v7 = bc 0x1b

theorem Consts.of_v {s t : State} (h : Consts s)
    (hv : ∀ r, r ∉ [VReg.v0, .v1, .v2, .v3] → t.v r = s.v r) : Consts t :=
  ⟨fun k hk => by
      rw [tbyte_congr' (fun a ha => hv _ (by
        have hn := treg_ne a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩)) k hk]
      exact h.tab k hk,
    (hv _ (by decide)).trans h.v4, (hv _ (by decide)).trans h.v5, (hv _ (by decide)).trans h.v6,
    (hv _ (by decide)).trans h.v7⟩

/-- The three constant bytes, through `x6`. -/
theorem consts_run (s : State) :
    ∃ t, runBlock isa [.movz .w .x6 0x80 0, .vop (.dup .b16 .v5 .x6), .movz .w .x6 0x40 0,
        .vop (.dup .b16 .v6 .x6), .movz .w .x6 0x1b 0, .vop (.dup .b16 .v7 .x6)] s = some t ∧
      t.v .v5 = bc 0x80 ∧ t.v .v6 = bc 0x40 ∧ t.v .v7 = bc 0x1b ∧
      (∀ v, v ≠ .v5 → v ≠ .v6 → v ≠ .v7 → t.v v = s.v v) ∧ (∀ r, r ≠ .x6 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let a := s.write .w .x6 0x80
  let b := a.setV .v5 (bc 0x80)
  let c := b.write .w .x6 0x40
  let d := c.setV .v6 (bc 0x40)
  let e := d.write .w .x6 0x1b
  let f := e.setV .v7 (bc 0x1b)
  refine ⟨f, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [f, e, d, c, b, a, State.setV, State.write]
  · simp [f, e, d, c, b, a, State.setV, State.write]
  · simp [f, State.setV]
  · intro v h5 h6 h7
    simp only [f, e, d, c, b, a, v_write, v_setV_of_ne _ _ h5, v_setV_of_ne _ _ h6, v_setV_of_ne _ _ h7]
  · intro r hr
    simp only [f, e, d, c, b, a, gpr_setV, gpr_write_of_ne _ _ _ hr]

/-- `setup`: the tables and constants, through `x6` and `x7`. -/
theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧ t.v .v0 = s.v .v0 ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  unfold setup
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadTable_ok s _) fun a ⟨atab, av, ag, am, ard, awr, asp⟩ => ?_
  refine WP.mono (const128_ok a .v4 shiftIdx) fun b ⟨b4, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  obtain ⟨t, ht, t5, t6, t7, tv, tg, tm, trd, twr, tsp⟩ := consts_run b
  refine WP.of_runBlock ⟨t, ht, ⟨fun k hk => ?_, ?_, t5, t6, t7⟩, ?_, fun g h6 h7 => ?_, tm.trans (bm.trans am),
    trd.trans (brd.trans ard), twr.trans (bwr.trans awr), tsp.trans (bsp.trans asp)⟩
  · rw [tbyte_congr' (fun r hr => by
      have hn := treg_ne8 r hr
      rw [tv _ hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2, bv _ hn.2.2.2.2.1]) k hk]
    exact atab k hk
  · rw [tv _ (by decide) (by decide) (by decide)]; exact b4
  · rw [tv _ (by decide) (by decide) (by decide), bv _ (by decide),
      av _ (fun r hr => (treg_ne8 r hr).1.symm)]
  · rw [tg _ h6, bg _ h6 h7, ag _ h6 h7]

/-! ## SubBytes and ShiftRows, and MixColumns -/

/-- `subShift`: ShiftRows, then SubBytes. -/
theorem subShift_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa subShift s = some t ∧ t.v .v0 = aesMapBytes aesSbox (aesShiftRows (s.v .v0)) ∧
      VOnly [.v0, .v1, .v2, .v3] s t := by
  let a := s.setV .v0 (ofVBytes fun i =>
    let idx := (vbyte (s.v .v4) i).toNat
    if idx < 16 then vbyte (s.v .v0) idx else 0)
  let b := a.setV .v1 (a.v .v0 ^^^ a.v .v6)
  let c := b.setV .v2 (b.v .v0 ^^^ b.v .v5)
  let d := c.setV .v3 (c.v .v1 ^^^ c.v .v5)
  have od : VOnly [.v0, .v1, .v2, .v3] s d :=
    (((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)).trans
      (VOnly.setV c (by simp) _)
  have h0 : d.v .v0 = aesShiftRows (s.v .v0) := by
    simp only [d, c, b, a, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
      v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), v_setV_self,
      hc.v4]
    exact tbl_shiftRows _
  have h1 : d.v .v1 = d.v .v0 ^^^ bc 0x40 := by simp [d, c, b, a, State.setV, hc.v6]
  have h2 : d.v .v2 = d.v .v0 ^^^ bc 0x80 := by simp [d, c, b, a, State.setV, hc.v5]
  have h3 : d.v .v3 = d.v .v0 ^^^ bc 0x40 ^^^ bc 0x80 := by simp [d, c, b, a, State.setV, hc.v5, hc.v6]
  have hd : runBlock isa [.vop (.tbl .v0 .v0 .v4), .vop (.logic .eor .v1 .v0 .v6),
      .vop (.logic .eor .v2 .v0 .v5), .vop (.logic .eor .v3 .v1 .v5)] s = some d := rfl
  obtain ⟨t, ht, hb, ot⟩ := select_full_run (s := d) (fun e => vbyte (d.v .v0) e) (fun _ _ => rfl)
    (fun e he => by rw [h1, vbyte_xor, vbyte_bc _ he])
    (fun e he => by rw [h2, vbyte_xor, vbyte_bc _ he])
    (fun e he => by rw [h3, vbyte_xor, vbyte_xor, vbyte_bc _ he, vbyte_bc _ he, BitVec.xor_assoc]; rfl)
  refine ⟨t, runBlock_cat_some hd ht, ?_, od.trans ot⟩
  apply ext_vbyte
  intro e he
  have hk : (vbyte (d.v .v0) e).toNat < 256 := (vbyte (d.v .v0) e).isLt
  rw [hb e he, vbyte_mapBytes _ _ he, ← h0,
    tbyte_congr (fun r a b c dd _ _ => od.2 r (by simp [a, b, c, dd])) _ hk, hc.tab _ hk, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- `mix`: MixColumns. -/
theorem mix_run (s : State) (h7 : s.v .v7 = bc 0x1b) :
    ∃ t, runBlock isa mix s = some t ∧ t.v .v0 = aesMixColumns (s.v .v0) ∧
      VOnly [.v0, .v1, .v2, .v3] s t := by
  let a := s.setV .v1 (VArr.b16.map2 (fun w a b => VShiftOp.sshr.eval 7 w a b) (s.v .v1) (s.v .v0))
  let b := a.setV .v2 (VArr.b16.map2 (fun w a b => VShiftOp.shl.eval 1 w a b) (a.v .v2) (a.v .v0))
  let c := b.setV .v1 (b.v .v1 &&& b.v .v7)
  let d := c.setV .v2 (c.v .v2 ^^^ c.v .v1)
  let e := d.setV .v1 (VRevOp.rev32h.eval (d.v .v0))
  let f := e.setV .v2 (e.v .v2 ^^^ e.v .v1)
  let g := f.setV .v0 (f.v .v0 ^^^ f.v .v2)
  let h := g.setV .v1 (VArr.s4.map2 (fun w a b => VShiftOp.ushr.eval 8 w a b) (g.v .v1) (g.v .v0))
  let i := h.setV .v1 (VArr.s4.map2 (fun w a b => VShiftOp.sli.eval 24 w a b) (h.v .v1) (h.v .v0))
  let t := i.setV .v0 (i.v .v1 ^^^ i.v .v2)
  have hv : t.v .v0 = mixV (s.v .v1) (s.v .v2) (s.v .v0) := by
    simp only [t, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, h7, mixV, mixY]
  refine ⟨t, rfl, by rw [hv, mixV_eq], ?_⟩
  exact (((((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
    (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
    (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans
    (VOnly.setV h (by simp) _)).trans (VOnly.setV i (by simp) _)

end VG.Proof.Aes.AArch64.OneBlock
