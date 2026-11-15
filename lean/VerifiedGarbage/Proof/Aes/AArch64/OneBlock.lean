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
`mix` is `aesMixColumns` (`mixV_eq`: the columns are the 32-bit lanes, and
their rotations by one and two bytes are `ushr` with `sli` and `rev32`),
which `Proof/Aes/Vector.lean` relates to the specification's rounds.

`vg_aes_encrypt_blocks` (`encryptBlocksN`) runs it for one block and the
bitsliced code otherwise (`encryptBlocksN_correct`), against the contract of
the bitsliced code, `blocksAArch64`; so does `vg_aes_ctr32` (`ctr32N`,
`ctr32N_correct`, against `ctr32AArch64`), on the counter block, whose
`inc₃₂` it writes back (`ctrOneLoad_ok`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.OneBlock

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Aes.AArch64 VG.Impl.Aes.AArch64.OneBlock
open VG.Proof.Aes.Vector (st KeyIs rnds rnds_zero rnds_succ cipher_eq eor_st aesmc_st keyIs_readW
  vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns ext_vbyte st_ext getD_st getD_shiftRows getD_subBytes
  getD_ofFn vbyte_readW)
open VG.Spec.Aes (roundKey cipher addRoundKey bytesAt subBytes shiftRows mixColumns)

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

/-! ## The rounds -/

theorem VOnly.sp {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.sp = s.sp := by
  rw [h.1]

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp [State.read, Size.bits]

theorem ofNat_bne_zero {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = true := by
  rw [bne_iff_ne]
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h'
  have h'' : k = 0 := h'
  omega_using [h0, h'']

theorem ofNat_sub_one {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) :=
  BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h

/-- ShiftRows and SubBytes, in either order. -/
theorem shiftSub_st (v : BitVec 128) :
    st (aesMapBytes aesSbox (aesShiftRows v)) = shiftRows (subBytes (st v)) := by
  apply st_ext
  intro i hi
  have hs : i % 4 + 4 * ((i / 4 + i % 4) % 4) < 16 := by omega_arith
  rw [getD_st _ hi, getD_shiftRows _ hi, getD_subBytes _ hs, getD_st _ hs, vbyte_mapBytes _ _ hi,
    vbyte_shiftRows _ hi]
  exact congrFun VG.Proof.Aes.Vector.sbox_eq _

/-- A round key from the schedule, XORed into the state. -/
theorem keyEor_run (s : State) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 16) :
    ∃ t, runBlock isa [.ldrq .v1 .x0 off, .vop (.logic .eor .v0 .v0 .v1)] s = some t ∧
      t.v .v0 = s.v .v0 ^^^ s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 128 ∧
      VOnly [.v0, .v1, .v2, .v3] s t := by
  let a := s.setV .v1 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 128)
  let b := a.setV .v0 (a.v .v0 ^^^ a.v .v1)
  refine ⟨b, by rw [runBlock_cons, Aese.exec_ldrq ho hin, runStep_some, runBlock_cons, exec_eorv, runStep_some,
    runBlock_nil], ?_, (VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)⟩
  simp only [b, a, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]

/-- After `j` full rounds from the state `x`, with the key schedule at `K`:
the state in `v0`, `x0` at round key `j`, and `R − 1 − j` in `x1`. -/
structure RInv (s₀ : State) (K : Addr) (R : Nat) (w : List Byte) (x : Spec.Aes.State) (j : Nat)
    (s : State) : Prop where
  consts : Consts s
  x0 : s.gpr .x0 = K + BitVec.ofNat 64 (16 * j)
  x1 : s.gpr .x1 = BitVec.ofNat 64 (R - 1 - j)
  st : st (s.v .v0) = rnds w x j
  gpr : ∀ r, r ≠ .x0 → r ≠ .x1 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- A full round. -/
theorem round_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) {j : Nat} (hj : j + 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x j s) :
    WP isa (.block round) s (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (j + 1)) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨a, ha, a0, oa⟩ := subShift_run s hI.consts
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  obtain ⟨b, hb, b0, ob⟩ := mix_run a (hI.consts.of_v oa.2).v7
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  let c := b.write .x .x0 (b.read .x .x0 + BitVec.ofNat 64 16)
  rw [WP.block_cons_iff]
  refine ⟨c, exec_addImm_x (imm := 16) (by decide), ?_⟩
  have c0 : c.gpr .x0 = K + BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show c.gpr .x0 = b.gpr .x0 + BitVec.ofNat 64 16 by simp [c, State.write, read_x], ob.gpr, oa.gpr,
      hI.x0, BitVec.add_assoc, ← BitVec.ofNat_add]
    rfl
  have crd : c.rd = s₀.rd := ob.rd.trans (oa.rd.trans hI.rd)
  have cmem : c.mem = s₀.mem := ob.mem.trans (oa.mem.trans hI.mem)
  obtain ⟨t, ht, t0, ot⟩ := keyEor_run c (off := 0) (by decide) ⟨_, List.mem_append_left _ (by rw [crd]; exact hK),
    by rw [c0, BitVec.add_zero]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  rw [show ([.ldrq .v1 .x0 0, .vop (.logic .eor .v0 .v0 .v1), .subImm .x .x1 .x1 1] : List Instr) =
    [.ldrq .v1 .x0 0, .vop (.logic .eor .v0 .v0 .v1)] ++ [.subImm .x .x1 .x1 1] from rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨t, ht, ?_⟩
  let f := t.write .x .x1 (t.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨f, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hk : KeyIs (c.mem.readW (c.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt s₀.mem K (16 * (R + 1))) (j + 1)) := by
    rw [c0, BitVec.add_zero, cmem]
    exact keyIs_readW s₀.mem K (by omega_arith)
  have tx1 : t.gpr .x1 = BitVec.ofNat 64 (R - 1 - j) := by
    rw [ot.gpr, show c.gpr .x1 = b.gpr .x1 by simp [c, State.write], ob.gpr, oa.gpr]; exact hI.x1
  refine ⟨hI.consts.of_v fun r hr => (ot.2 r hr).trans ((ob.2 r hr).trans (oa.2 r hr)), ?_, ?_, ?_,
    fun r h0 h1 => ?_, ot.mem.trans cmem, ot.rd.trans crd, ot.wr.trans (ob.wr.trans (oa.wr.trans hI.wr)),
    (VOnly.sp ot).trans ((VOnly.sp ob).trans ((VOnly.sp oa).trans hI.sp))⟩
  · rw [show f.gpr .x0 = t.gpr .x0 by simp [f, State.write], ot.gpr]; exact c0
  · rw [show f.gpr .x1 = t.gpr .x1 - BitVec.ofNat 64 1 by simp [f, State.write, read_x], tx1,
      ofNat_sub_one (by omega_arith), Nat.sub_sub]
  · rw [show f.v .v0 = t.v .v0 from rfl, t0, show c.v .v0 = b.v .v0 from rfl, b0, a0, eor_st hk, aesmc_st,
      shiftSub_st, hI.st, rnds_succ]
  · rw [show f.gpr r = t.gpr r by simp [f, State.write, h1], ot.gpr,
      show c.gpr r = b.gpr r by simp [c, State.write, h0], ob.gpr, oa.gpr]
    exact hI.gpr r h0 h1

/-- The full rounds: `R − 1` of them. -/
theorem loop_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State} (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x 0 s) :
    WP isa (.loop (.block round) (.nonzero .x .x1)) s
      (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (R - 1)) := by
  refine WP.loop (M := isa) (fun n t => ∃ j, n = R - 1 - j ∧ j + 2 ≤ R ∧
    RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x j t) ?_ (R - 1) s ⟨0, rfl, hR2, hI⟩
  rintro n t ⟨j, hn, hj, hI⟩
  refine WP.mono (round_ok hK hR hj hI) fun t' hI' => ?_
  have he : isa.eval (.nonzero .x .x1) t' = some (BitVec.ofNat 64 (R - 1 - (j + 1)) != 0) := by
    simp [AArch64.eval, State.read, hI'.x1]
  rcases Nat.lt_or_ge (j + 2) R with h | h
  · exact .inr ⟨by rw [he, ofNat_bne_zero (by omega_arith) (by omega_arith)], R - 1 - (j + 1), by omega_arith,
      j + 1, rfl, h, hI'⟩
  · have e : j + 1 = R - 1 := by omega_arith
    refine .inl ⟨by rw [he, show R - 1 - (j + 1) = 0 by omega_arith]; rfl, ?_⟩
    rw [← e]; exact hI'

/-- The last round. -/
theorem last_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (R - 1) s) :
    WP isa (.block (subShift ++ ([.ldrq .v1 .x0 16, .vop (.logic .eor .v0 .v0 .v1)] : List Instr))) s fun t =>
      st (t.v .v0) = cipher R (bytesAt s₀.mem K (16 * (R + 1))) x ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → t.gpr r = s₀.gpr r) ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      t.sp = s₀.sp := by
  rw [WP.block_append_iff]
  obtain ⟨a, ha, a0, oa⟩ := subShift_run s hI.consts
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  have ea : a.gpr .x0 + BitVec.ofNat 64 16 = K + BitVec.ofNat 64 (16 * R) := by
    rw [oa.gpr, hI.x0, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * (R - 1) + 16 = 16 * R by omega_arith]
  have amem : a.mem = s₀.mem := oa.mem.trans hI.mem
  obtain ⟨t, ht, t0, ot⟩ := keyEor_run a (off := 16) (by decide)
    ⟨_, List.mem_append_left _ (by rw [oa.rd, hI.rd]; exact hK),
      by rw [ea]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨t, ht, ?_, fun r h0 h1 => ?_, ot.mem.trans amem, ot.rd.trans (oa.rd.trans hI.rd),
    ot.wr.trans (oa.wr.trans hI.wr), (VOnly.sp ot).trans ((VOnly.sp oa).trans hI.sp)⟩
  · have hk : KeyIs (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 16) 128)
        (roundKey (bytesAt s₀.mem K (16 * (R + 1))) R) := by
      rw [ea, amem]
      exact keyIs_readW s₀.mem K (by omega_arith)
    rw [t0, a0, eor_st hk, shiftSub_st, hI.st]
    rfl
  · rw [ot.gpr, oa.gpr]; exact hI.gpr r h0 h1

/-- `core` is the cipher, on the state in `v0`, with the schedule at `x0`
and the rounds in `x1`. -/
theorem core_ok {s : State} {K : Addr} {R : Nat} (hK : (⟨K, 240⟩ : Region) ∈ s.rd) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa core s fun t =>
      st (t.v .v0) = cipher R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp := by
  have hR14 : R ≤ 14 := by omega_arith
  have hR2 : 2 ≤ R := by omega_arith
  unfold core
  refine WP.seq (WP.mono (setup_ok s) fun a ⟨ac, a0, ag, am, ard, awr, asp⟩ => ?_)
  have ax0 : a.gpr .x0 = K := (ag _ (by decide) (by decide)).trans h0
  have hKa : (⟨K, 240⟩ : Region) ∈ a.rd := by rw [ard]; exact hK
  unfold rounds
  refine WP.seq ?_
  rw [show ([.ldrq .v1 .x0 0, .vop (.logic .eor .v0 .v0 .v1), .subImm .x .x1 .x1 1] : List Instr) =
    [.ldrq .v1 .x0 0, .vop (.logic .eor .v0 .v0 .v1)] ++ [.subImm .x .x1 .x1 1] from rfl, WP.block_append_iff]
  obtain ⟨b, hb, b0, ob⟩ := keyEor_run a (off := 0) (by decide) ⟨_, List.mem_append_left _ hKa,
    by rw [ax0]; exact Offset.contains_base K (by decide) (by decide)⟩
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  let c := b.write .x .x1 (b.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨c, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hk : KeyIs (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt a.mem K (16 * (R + 1))) 0) := by
    have h := keyIs_readW a.mem K (L := 16 * (R + 1)) (j := 0) (by omega_arith)
    rw [Nat.mul_zero] at h
    rw [ax0]
    exact h
  have hI : RInv a K R (bytesAt a.mem K (16 * (R + 1))) (st (a.v .v0)) 0 c := by
    refine ⟨ac.of_v ob.2, ?_, ?_, ?_, fun r h0 h1 => ?_, ob.mem, ob.rd, ob.wr, (VOnly.sp ob :)⟩
    · rw [show c.gpr .x0 = b.gpr .x0 by simp [c, State.write], ob.gpr, ax0]
      exact (BitVec.add_zero K).symm
    · rw [show c.gpr .x1 = b.gpr .x1 - BitVec.ofNat 64 1 by simp [c, State.write, read_x], ob.gpr,
        ag _ (by decide) (by decide), h1, ofNat_sub_one (by omega_arith)]
      rfl
    · rw [show c.v .v0 = b.v .v0 from rfl, b0, eor_st hk, rnds_zero]
    · rw [show c.gpr r = b.gpr r by simp [c, State.write, h1], ob.gpr]
  refine WP.seq (WP.mono (loop_ok hKa hR14 hR2 hI) fun d hd => ?_)
  refine WP.mono (last_ok hKa hR14 hR2 hd) fun t ⟨tst, tg, tm, trd, twr, tsp⟩ => ?_
  refine ⟨by rw [tst, am, a0], fun r h0 h1 h6 h7 => (tg r h0 h1).trans (ag r h6 h7), tm.trans am,
    trd.trans ard, twr.trans awr, tsp.trans asp⟩

/-! ## `vg_aes_encrypt_blocks` -/

/-- The registers the bitsliced code saves are none of those `encryptOne`
writes. -/
theorem sreg_ne : ∀ i < 10, sreg i ≠ .x0 ∧ sreg i ≠ .x1 ∧ sreg i ≠ .x6 ∧ sreg i ≠ .x7 := by decide

/-- One block, encrypted in place. -/
theorem encryptOne_ok {s : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s)
    (h3 : (s.gpr .x3).toNat = 1) :
    WP isa encryptOne s fun s' =>
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' := by
  obtain ⟨hrd, hwr, -, -, -, -, hR⟩ := hp
  have hwD : (⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [h3] at hwD
  have hrS : (⟨s.gpr .x0, 240⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  unfold encryptOne
  -- The block.
  refine WP.seq ?_
  let a := s.setV .v0 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128)
  rw [WP.block_cons_iff]
  refine ⟨a, Aese.exec_ldrq (off := 0) (by decide)
    ⟨_, List.mem_append_right _ hwD, Offset.contains_base (s.gpr .x2) (d := 0) (by decide) (by decide)⟩,
    WP.block_nil ?_⟩
  -- The cipher.
  have a1 : a.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    show s.gpr .x1 = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (core_ok (s := a) (K := s.gpr .x0) (R := (s.gpr .x1).toNat) hrS rfl a1 hR)
    fun b ⟨bst, bg, bm, brd, bwr, bsp⟩ => ?_)
  -- The block, back.
  have b2 : b.gpr .x2 = s.gpr .x2 := bg _ (by decide) (by decide) (by decide) (by decide)
  have bm' : b.mem = s.mem := bm
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_strq (off := 0) (by decide) ⟨_, by rw [bwr]; exact hwD,
    by rw [b2]; exact Offset.contains_base (s.gpr .x2) (d := 0) (by decide) (by decide)⟩,
    WP.block_nil ⟨fun r h0 h1 h6 h7 => bg r h0 h1 h6 h7, ?_⟩⟩
  have hE := (Aese.ecbInv_write (m₀ := s.mem) (m := b.mem) (D := s.gpr .x2) (n := 1) (k := 0)
    (F := ecbOut cipher s.mem (s.gpr .x2) (s.gpr .x1).toNat
      (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))) (v := b.v .v0) (by decide) (by decide)
    (fun i hi => by rw [ite_eq_right (by omega_arith), bm']) (fun t ht => by
      rw [← getD_st _ ht, bst, show a.v .v0 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 from rfl,
        Aese.st_readW]
      rfl)).1
  show Spec.Aes.statesAt (b.mem.write (b.gpr .x2 + BitVec.ofNat 64 0) 16 (b.v .v0)) (s.gpr .x2)
      (s.gpr .x3).toNat = _
  rw [h3, b2]
  refine (statesAt_of_ecbInv hE).trans ?_
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

/-- `encryptBlocksN`: one block by the tables, any other number of blocks
bitsliced. -/
theorem encryptBlocksN_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₀) :
    WP isa encryptBlocksN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s₀ s' := by
  unfold encryptBlocksN
  let s₁ := s₀.write .x .x6 (s₀.read .x .x3 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, State.write, hr]
  refine WP.ite (s₀.gpr .x3 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x3 : s₀.gpr .x3 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x3) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h3 : (s₁.gpr .x3).toNat = 1 := by
      show (s₀.gpr .x3).toNat = 1
      rw [x3]; rfl
    refine WP.mono (encryptOne_ok hp₁ h3) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, hpost⟩
    have hn := sreg_ne i hi
    rw [hg _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact g₁ _ hn.2.2.1
  · exact WP.mono (correct_blocks encrypt4_cryptOk hp₁) fun s' ⟨hsv, hpost⟩ =>
      ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), hpost⟩

theorem encryptBlocksN_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocksN s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (encryptBlocksN_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_arith)
  · exact h₁ 1 (by omega_arith)
  · exact h₁ 2 (by omega_arith)
  · exact h₁ 3 (by omega_arith)
  · exact h₁ 4 (by omega_arith)
  · exact h₁ 5 (by omega_arith)
  · exact h₁ 6 (by omega_arith)
  · exact h₁ 7 (by omega_arith)
  · exact h₁ 8 (by omega_arith)
  · exact h₁ 9 (by omega_arith)
  · exact h₃ _ (by simp)

theorem encryptBlocksN_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub encryptBlocksN := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocksN_verified :
    Verified AArch64.target encryptBlocksN (Proof.Aes.encryptBlocksRoundsContract AArch64.abi) :=
  Verified.of_correct encryptBlocksN_correct encryptBlocksN_ct (by
    sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [blocksSat] using blocksSat)

/-! ## `vg_aes_ctr32` -/

/-- The counter block, as an AES state. -/
theorem st_ctr (m : Mem) (p : Addr) :
    st (m.readW (p + BitVec.ofNat 64 0) 128) = ctrState (Spec.Gcm.blockAt m p) 0 := by
  apply st_ext; intro j hj
  rw [getD_st _ hj, ctrState, getD_ofFn hj, vbyte_readW _ _ hj, BitVec.add_zero]
  exact (toBytes_blockAt m p hj).symm

/-- `ctrOneLoad`: the counter block in `v0`, and its last four bytes, as a
big-endian integer, plus one, written back. -/
theorem ctrOneLoad_ok (s : State) (hc : (⟨s.gpr .x2, 16⟩ : Region) ∈ s.wr) :
    WP isa (.block ctrOneLoad) s fun a =>
      a.v .v0 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 ∧
      a.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 12)
        (rev32 (rev32 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 1)) ∧
      (∀ r, r ≠ .x6 → a.gpr r = s.gpr r) ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.sp = s.sp := by
  have hc' := List.mem_append_right s.rd hc
  rw [ctrOneLoad, WP.block_cons_iff]
  refine ⟨_, Aese.exec_ldrq (off := 0) (by decide)
    (in_off (off := 0) (n := 16) hc' (by omega_arith) (by omega_arith)), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldr_w (off := 12) (by decide)
    (in_off (off := 12) (n := 4) hc' (by omega_arith) (by omega_arith)), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_addImm_w (imm := 1) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_w (off := 12) (by decide)
    (in_off (off := 12) (n := 4) hc (by omega_arith) (by omega_arith)), WP.block_nil ?_⟩
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [State.setV, State.write, State.read, sw_32]
  · simp [State.setV, State.write, hr]

/-- One block of the counter mode: the counter block encrypted, XORed into
the block of the data, and the counter block incremented. -/
theorem ctr32One_ok {s : State} (hp : Proof.Aes.ctr32AArch64.pre s) (h4 : (s.gpr .x4).toNat = 1) :
    WP isa ctr32One s fun s' =>
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨hrd, hwr, dSC, -, -, dCD, -, -, -, hR⟩ := hp
  rw [h4] at hwr dCD
  have hC : (⟨s.gpr .x2, 16⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hD : (⟨s.gpr .x3, 16 * 1⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hS : (⟨s.gpr .x0, 240⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  unfold ctr32One
  refine WP.seq (WP.mono (ctrOneLoad_ok s hC) fun a ⟨av, am, ag, ard, awr, asp⟩ => ?_)
  -- Only the counter block is written.
  have fa : Frame [⟨s.gpr .x2, 16⟩] s.mem a.mem := by
    rw [am]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (c_off (s.gpr .x2) (off := 12) (by omega_arith) (by omega_arith))
  have hw : bytesAt a.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)) =
      bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)) := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => fa.bytes (R := ⟨s.gpr .x0, 240⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dSC) (show (240 : Nat) ≤ 2 ^ 64 by decide)
      (show i < 240 by have := List.mem_range.mp hi; omega_using [this, hR])
  have fD : ∀ i < 16 * 1, a.mem (s.gpr .x3 + BitVec.ofNat 64 i) = s.mem (s.gpr .x3 + BitVec.ofNat 64 i) :=
    fun i hi => fa.bytes (R := ⟨s.gpr .x3, 16 * 1⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dCD.symm) (show (16 * 1 : Nat) ≤ 2 ^ 64 by decide) hi
  -- The cipher.
  have a1 : a.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [ag _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (core_ok (s := a) (K := s.gpr .x0) (R := (s.gpr .x1).toNat)
    (by rw [ard]; exact hS) (ag _ (by decide)) a1 hR) fun b ⟨bst, bg, bm, brd, bwr, bsp⟩ => ?_)
  have b3 : b.gpr .x3 = s.gpr .x3 :=
    (bg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  have bwD : (⟨s.gpr .x3, 16 * 1⟩ : Region) ∈ b.wr := by rw [bwr, awr]; exact hD
  have hin : (⟨s.gpr .x3, 16 * 1⟩ : Region).Contains (b.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [b3]; exact Offset.contains_base (s.gpr .x3) (d := 0) (by decide) (by decide)
  -- The data.
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_ldrq (off := 0) (by decide) ⟨_, List.mem_append_right _ bwD, hin⟩, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_strq (off := 0) (by decide) ⟨_, bwD, hin⟩, WP.block_nil ?_⟩
  refine ⟨fun r h0 h1 h6 h7 => (bg r h0 h1 h6 h7).trans (ag r h6), ?_⟩
  show Spec.Gcm.blocksAt (b.mem.write (b.gpr .x3 + BitVec.ofNat 64 0) 16
        (b.v .v0 ^^^ b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)) (s.gpr .x3) (s.gpr .x4).toNat = _ ∧
      Spec.Gcm.blockAt (b.mem.write (b.gpr .x3 + BitVec.ofNat 64 0) 16
        (b.v .v0 ^^^ b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)) (s.gpr .x2) = _
  rw [h4, b3, bm]
  have hst := dataInvM_store1 (m₀ := s.mem) (m := a.mem) (D := s.gpr .x3) (O := s.gpr .x3) (n := 1) (k := 0)
    (ks := keyStream (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
      (Spec.Gcm.blockAt s.mem (s.gpr .x2)))
    (v := b.v .v0 ^^^ a.mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 128) (by decide) (by decide)
    (fun i hi => by rw [ite_eq_right (by omega_arith)]; exact fD i hi)
    (fun t ht => by
      rw [Nat.mul_zero, Nat.zero_add, keyStream, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, vbyte_xor,
        vbyte_readW _ _ ht, BitVec.add_zero, fD t (by omega_using [ht]), ← getD_st _ ht, bst, hw, av,
        st_ctr])
  rw [Nat.mul_zero] at hst
  obtain ⟨hd, hf⟩ := hst
  refine ⟨ctr32_of_dataInvM hd, ctr_after (n := 1) fun k hk => ?_⟩
  rw [show (BitVec.ofNat 64 1).setWidth 32 = BitVec.ofNat 32 1 by decide]
  refine (hf.bytes (R := ⟨s.gpr .x2, 16⟩) (by simp only [List.mem_singleton, forall_eq]; exact dCD)
    (show (16 : Nat) ≤ 2 ^ 64 by decide) hk).trans ?_
  show a.mem (s.gpr .x2 + BitVec.ofNat 64 k) = _
  rw [am, writeW_apply, off_toNat (s.gpr .x2) (by omega_using [hk]) (by decide)]
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega_using [h]),
      ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_using [h]), ite_eq_left h]
  · rw [ite_eq_left (show 12 ≤ k by omega_using [h]),
      ite_eq_left (show k - 12 < 32 / 8 by omega_using [h, hk]), ite_eq_right h, BitVec.setWidth_eq]

/-- `ctr32N`: one block by the tables, any other number of blocks
bitsliced. -/
theorem ctr32N_wp {s₀ : State} (hp : Proof.Aes.ctr32AArch64.pre s₀) :
    WP isa ctr32N s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.ctr32AArch64.post s₀ s' := by
  unfold ctr32N
  let s₁ := s₀.write .x .x6 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : Proof.Aes.ctr32AArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, State.write, hr]
  refine WP.ite (s₀.gpr .x4 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x4 : s₀.gpr .x4 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x4) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h4 : (s₁.gpr .x4).toNat = 1 := by
      show (s₀.gpr .x4).toNat = 1
      rw [x4]; rfl
    refine WP.mono (ctr32One_ok hp₁ h4) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, hpost⟩
    have hn := sreg_ne i hi
    rw [hg _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact g₁ _ hn.2.2.1
  · exact WP.mono (correct (cpre_of hp₁)) fun s' ⟨hsv, _, hpost⟩ =>
      ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), hpost⟩

theorem ctr32N_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa ctr32N s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (ctr32N_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_arith)
  · exact h₁ 1 (by omega_arith)
  · exact h₁ 2 (by omega_arith)
  · exact h₁ 3 (by omega_arith)
  · exact h₁ 4 (by omega_arith)
  · exact h₁ 5 (by omega_arith)
  · exact h₁ 6 (by omega_arith)
  · exact h₁ 7 (by omega_arith)
  · exact h₁ 8 (by omega_arith)
  · exact h₁ 9 (by omega_arith)
  · exact h₃ _ (by simp)

theorem ctr32N_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub ctr32N := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.AArch64.OneBlock
