module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecMac
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Decrypt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecLay
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `RsaPkcs1Enc.AArch64.DecMsg`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: IRPRF's messages

The message of block `i` of IRPRF, `I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)`,
written at `scratch + sMsg` (`msgCL_ok` for `CL`, `msgAM_ok` for `AM`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

theorem add_ofNat_inj (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a = p + BitVec.ofNat 64 b) ↔ a = b :=
  ⟨fun e => Classical.byContradiction fun h => Offset.add_ofNat_ne p ha hb h e, fun e => e ▸ rfl⟩

theorem byte_imm (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 16 v) <<< 0)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.shiftLeft_zero, BitVec.toNat_ofNat]
  omega_using []

theorem byte_reg (x : Nat) : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem ascii_length : Spec.RsaPkcs1Enc.ascii "length" = [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68] := by decide

theorem ascii_message : Spec.RsaPkcs1Enc.ascii "message" = [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65] := by
  decide

theorem bytes10 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 10 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9)] :=
  rfl

theorem msgCL_ok {t : State} {B : Addr} {i : Nat} (h9 : t.gpr .x9 = B) (h11 : t.gpr .x11 = BitVec.ofNat 64 i)
    (hi : i < 256) (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes lengthLabel clLen)) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.v = t.v ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧ Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 10 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2 := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  have w4 := hw 4 (by decide)
  have w5 := hw 5 (by decide)
  have w6 := hw 6 (by decide)
  have w7 := hw 7 (by decide)
  have w8 := hw 8 (by decide)
  have w9 := hw 9 (by decide)
  apply WP.of_runBlock
  simp only [msgBytes, lengthLabel, clLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.read, State.store, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceLT, Nat.reduceAdd, and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false, h9, h11, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, ?_, ?_⟩
  · simp only [mem_ne hr (by decide : Reg.x10 ∉ preserved), ite_false]
  · repeat (first
      | exact Frame.refl _ _
      | refine Frame.write ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide)))
  · rw [bytes10]
    simp only [Bytes.write1_apply, add_ofNat_inj, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
      ite_false, byte_imm, byte_reg, Proof.RsaPkcs1Enc.i2osp_two, ascii_length, Nat.div_eq_of_lt hi]
    rfl

theorem bytes11 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 11 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9),
    m (B + BitVec.ofNat 64 10)] :=
  rfl

theorem am_lo (K : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 32 (K <<< 3)) = BitVec.ofNat 8 (8 * K.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

theorem am_hi (K : BitVec 64) (hK : K.toNat ≤ 1024) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (K <<< 3 >>> 8)) = BitVec.ofNat 8 (8 * K.toNat / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem msgAM_ok {t : State} {B : Addr} {i : Nat} {K : BitVec 64} (h9 : t.gpr .x9 = B)
    (h11 : t.gpr .x11 = BitVec.ofNat 64 i) (h12 : t.gpr .x12 = K) (hi : i < 256) (hK : K.toNat ≤ 1024)
    (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes messageLabel amLen)) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      u.v = t.v ∧ (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧ Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 11 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * K.toNat) 2 := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  have w4 := hw 4 (by decide)
  have w5 := hw 5 (by decide)
  have w6 := hw 6 (by decide)
  have w7 := hw 7 (by decide)
  have w8 := hw 8 (by decide)
  have w9 := hw 9 (by decide)
  have w10 := hw 10 (by decide)
  apply WP.of_runBlock
  simp only [msgBytes, messageLabel, amLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.read, State.store, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod,
    Nat.reduceLT, Nat.reduceAdd, and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write,
    reduceCtorEq, ite_false, h9, h11, h12, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, ?_, ?_⟩
  · simp only [mem_ne hr (by decide : Reg.x10 ∉ preserved), ite_false]
  · repeat (first
      | exact Frame.refl _ _
      | refine Frame.write ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide)))
  · rw [bytes11]
    simp only [Bytes.write1_apply, add_ofNat_inj, Nat.reducePow, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
      ite_false, byte_imm, byte_reg, am_lo, am_hi K hK, Proof.RsaPkcs1Enc.i2osp_two, ascii_message,
      Nat.div_eq_of_lt hi]
    rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end

/-! ### `RsaPkcs1Enc.AArch64.DecPrf`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: a block of IRPRF

The blocks of `prfBody` that set registers and the counter, and one block of
IRPRF (`prfBody_ok`): `HMAC(KDK, I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2))` to
`scratch + dst + 32 i`, the counter `i` in its slot advanced.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

theorem imm16 {n : Nat} (hn : n < 65536) : BitVec.setWidth 64 (BitVec.ofNat 16 n) <<< 0 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem prfHead_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block (scr .x9 sMsg ++ ([.ldrSp .x11 oI, .ldrSp .x12 oK] : List Instr))) t fun u => Same t u ∧
      u.gpr .x9 = slot t Q oScr + BitVec.ofNat 64 sMsg ∧ u.gpr .x11 = slot t Q oI ∧ u.gpr .x12 = slot t Q oK := by
  obtain h184 := h 184 (by decide)
  obtain h200 := h 200 (by decide)
  obtain h136 := h 136 (by decide)
  apply WP.of_runBlock
  simp only [scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oI, oK, sMsg, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184, h200, h136]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl⟩

theorem prfUpdArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) {n : Nat} (hn : n < 65536) :
    WP isa (.block (prfUpdArgs n)) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = BitVec.ofNat 64 64 ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sMsg ∧
      u.gpr .x3 = BitVec.ofNat 64 n ∧ u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  obtain h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [prfUpdArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, sSt, sMsg, sWork, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    imm16 hn, rfl⟩

theorem prfFinArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) {n dst : Nat} (hn : 64 + n < 65536)
    (hd : dst < 4096) :
    WP isa (.block (prfFinArgs n dst)) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oScr + BitVec.ofNat 64 sOuter ∧ u.gpr .x2 = BitVec.ofNat 64 (64 + n) ∧
      u.gpr .x3 = (slot t Q oI <<< 5) + (slot t Q oScr + BitVec.ofNat 64 dst) ∧
      u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  obtain h184 := h 184 (by decide)
  obtain h200 := h 200 (by decide)
  apply WP.of_runBlock
  simp only [prfFinArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oI, sSt, sOuter, sWork, hd, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h184, h200]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl,
    imm16 hn, rfl, rfl⟩

/-- Same, but memory: the regions, the stack pointer, the vector registers and the callee-saved ones. -/
structure SameR (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  cs : ∀ r ∈ preserved, u.gpr r = t.gpr r

theorem incrCL_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : InRegions t.wr (Q + BitVec.ofNat 64 200) 8) :
    WP isa (.block (incr [.movz .x .x12 8 0])) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oI) (slot t Q oI + 1) ∧
      u.gpr .x12 = BitVec.ofNat 64 8 - (slot t Q oI + 1) := by
  obtain h200 := h 200 (by decide)
  apply WP.of_runBlock
  simp only [incr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul,
    Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oI, BitVec.add_zero, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq, ite_false, h200, hw]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl⟩

theorem incrAM_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : InRegions t.wr (Q + BitVec.ofNat 64 200) 8) :
    WP isa (.block (incr [.ldrSp .x12 oNB])) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oI) (slot t Q oI + 1) ∧
      u.gpr .x12 = slot t Q oNB - (slot t Q oI + 1) := by
  obtain h200 := h 200 (by decide)
  obtain h208 := h 208 (by decide)
  obtain e : (t.mem.writeW (Q + BitVec.ofNat 64 200) (slot t Q oI + 1)).readW (Q + BitVec.ofNat 64 208) 64 =
      slot t Q oNB :=
    Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  apply WP.of_runBlock
  simp only [incr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul,
    Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oI, oNB, BitVec.add_zero, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq, ite_false, h200, h208, hw]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl,
    congrArg (fun x => x - (slot t Q 200 + 1)) e⟩

/-! ## A block -/

section
variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- After block `i` of IRPRF from `t`: the block `blk` at `scratch + o`, the counter advanced, the blocks
left in `x12` (from `C`), and every other range of `scratch` from 1040 on as in `t`. -/
structure PrfStep (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (nbv : BitVec 64) (o : Nat) (blk : List Byte) (C : BitVec 64) (i : Nat) (t w : State) :
    Prop where
  post : Post L g vv m₀ R EM w
  ctr : slot w L.Q oI = BitVec.ofNat 64 (i + 1)
  nb : slot w L.Q oNB = nbv
  out : Spec.Rsa.bytesAt w.mem (scA L o) 32 = blk
  x12 : w.gpr .x12 = C - BitVec.ofNat 64 (i + 1)
  keep : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes → (a + l ≤ o ∨ o + 32 ≤ a) →
    Spec.Rsa.bytesAt w.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l

theorem shl5 (i dst : Nat) (scr : Addr) :
    (BitVec.ofNat 64 i <<< 5) + (scr + BitVec.ofNat 64 dst) = scr + BitVec.ofNat 64 (dst + 32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem prfBody_ok (hL : L.Ok) (hP : 16 ≤ L.P) {label : List Nat} {len count : List Instr} {dst : Nat}
    {t : State} {i : Nat} {kd text : List Byte} {nbv C : BitVec 64} (hc : Post L g vv m₀ R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd) (hctr : slot t L.Q oI = BitVec.ofNat 64 i)
    (hnb : slot t L.Q oNB = nbv) (hi : i < 256) (hd1 : 1040 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes)
    (hdst : dst < 4096) (hn : label.length + 4 ≤ 16) (htl : text.length = label.length + 4)
    (hmsg : ∀ u, Post L g vv m₀ R EM u → u.gpr .x9 = scA L sMsg → u.gpr .x11 = BitVec.ofNat 64 i →
      u.gpr .x12 = L.k → WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧
        Frame [⟨scA L sMsg, 16⟩] u.mem w.mem ∧ Spec.Rsa.bytesAt w.mem (scA L sMsg) (label.length + 4) = text)
    (hcount : ∀ u, Post L g vv m₀ R EM u → slot u L.Q oNB = nbv → WP isa (.block (incr count)) u fun w =>
      SameR u w ∧ w.mem = u.mem.writeW (L.Q + BitVec.ofNat 64 oI) (slot u L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u L.Q oI + 1)) :
    WP isa (prfBody (HH v) label len dst count) t
      (PrfStep L g vv m₀ R EM nbv (dst + 32 * i) (Spec.Hmac.hmac Spec.Hmac.sha256 kd text) C i t) := by
  have hs := hL.s8192
  have hnQ := hL.nQ
  -- The message.
  refine WP.seq (WP.mono (prfHead_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x9, x11, x12⟩ => ?_)
  obtain hc₁ := hc.same S₁
  simp only [hc.ctx.kept.scr, hc.ctx.kept.k] at x9 x12
  rw [hctr] at x11
  refine WP.seq (WP.mono (hmsg t₁ hc₁ x9 x11 x12) fun t₂ ⟨R₂, F₂, hm₂⟩ => ?_)
  obtain msgSafe : ∀ r ∈ [(⟨scA L sMsg, 16⟩ : Region)], Safe L r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))
  obtain hc₂ := hc₁.step hL R₂.rd R₂.wr R₂.sp (fun r _ => by rw [R₂.v]) (fun r hr _ => R₂.cs r hr) F₂ msgSafe
  obtain k₂ : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₂.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := fun a l h₁ h₂ => by
    rw [bytes_keep F₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scD hL (.inr (by unfold sMsg; omega_arith)) h₂ (by decide))
      (by unfold scrBytes at h₂; omega_arith), S₁.mem]
  obtain sl₂ : ∀ d, d + 8 ≤ frameBytes → slot t₂ L.Q d = slot t L.Q d := fun d hd => by
    show t₂.mem.readW _ 64 = t.mem.readW _ 64
    rw [F₂.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hL.stk_buf (by unfold frameBytes at hd; omega_arith) (.inr (.inr (sub_trans (scSub (by decide))
        hL.sc_sub)))) (by decide), S₁.mem]
  -- HMAC's `init` with `KDK`.
  refine mac_init hL hP hc₂ (key := sKDK) (by decide) (by decide) fun u hu => ?_
  obtain hkd₂ : Spec.Rsa.bytesAt t₂.mem (scA L sKDK) 32 = kd := by rw [k₂ _ _ (by decide) (by decide), hkd]
  rw [hkd₂] at hu
  obtain hk0 := blockKey_length (key := kd) (by rw [← hkd]; simp [Spec.Rsa.bytesAt])
  -- `update` with the message.
  refine WP.seq (WP.mono (prfUpdArgs_ok hu.post.ctx.sp hu.post.slots (n := label.length + 4) (by omega_arith))
    fun t₄ ⟨S₄, y0, y1, y2, y3, y4⟩ => ?_)
  obtain hc₄ := hu.post.same S₄
  simp only [hu.post.ctx.kept.scr] at y0 y2 y4
  obtain hmsg₄ : Spec.Rsa.bytesAt t₄.mem (scA L sMsg) (label.length + 4) = text := by
    rw [S₄.mem, hu.keep.scr _ _ (by decide) (by unfold sMsg scrBytes; omega_arith) (.inr (Nat.zero_le _)), hm₂]
  refine WP.seq (WP.mono (mac_upd hL hP hc₄ (n := label.length + 4) y0 y1 y2 (by rw [y3, BitVec.toNat_ofNat]; omega_arith) y4
    (Covers.right (scCov hL hc₄.ctx (by unfold sMsg scrBytes; omega_arith)))
    (fun a l hal => scD hL (.inr (by unfold sMsg; omega_arith)) (by unfold sMsg scrBytes; omega_arith)
      (by unfold scrBytes; omega_arith))
    (stkD hL hP (by unfold sMsg scrBytes; omega_arith)) hk0 (by rw [S₄.mem]; exact hu.inner)
    (by rw [S₄.mem]; exact hu.outer)) fun t₅ ⟨hc₅, hi₅, ho₅, kp₅⟩ => ?_)
  rw [hmsg₄] at hi₅
  -- HMAC's `finalize` to the block.
  refine WP.seq (WP.mono (prfFinArgs_ok hc₅.ctx.sp hc₅.slots (n := label.length + 4) (dst := dst) (by omega_arith) hdst)
    fun t₆ ⟨S₆, z0, z1, z2, z3, z4⟩ => ?_)
  obtain hc₆ := hc₅.same S₆
  obtain sl₅ : slot t₅ L.Q oI = BitVec.ofNat 64 i := by
    show t₅.mem.readW _ 64 = _
    rw [kp₅.slot _ (Nat.le_refl _) (by decide), S₄.mem, hu.keep.slot _ (Nat.le_refl _) (by decide)]
    exact (sl₂ oI (by decide)).trans hctr
  simp only [hc₅.ctx.kept.scr, sl₅] at z0 z1 z3 z4
  rw [shl5 i dst] at z3
  refine WP.seq (WP.mono (mac_fin hL hP hc₆ (o := dst + 32 * i) (by omega_arith) hd2 hk0 (text := text)
    (by rw [htl]; omega_arith) z0 z1 (by rw [z2, htl]) z3 z4 (by rw [S₆.mem]; exact hi₅)
    (by rw [S₆.mem]; exact ho₅)) fun t₇ ⟨hc₇, hb₇, kp₇⟩ => ?_)
  -- The counter.
  obtain nb₇ : slot t₇ L.Q oNB = nbv := by
    show t₇.mem.readW _ 64 = _
    rw [kp₇.slot _ (by decide) (by decide), S₆.mem, kp₅.slot _ (by decide) (by decide), S₄.mem,
      hu.keep.slot _ (by decide) (by decide)]
    exact (sl₂ oNB (by decide)).trans hnb
  obtain ct₇ : slot t₇ L.Q oI = BitVec.ofNat 64 i := by
    show t₇.mem.readW _ 64 = _
    rw [kp₇.slot _ (Nat.le_refl _) (by decide), S₆.mem]
    exact sl₅
  refine WP.mono (hcount t₇ hc₇ nb₇) fun w ⟨Sw, mw, xw⟩ => ?_
  obtain Fw : Frame [⟨L.Q + BitVec.ofNat 64 oI, 8⟩] t₇.mem w.mem := by
    rw [mw]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hcw := hc₇.step hL Sw.rd Sw.wr Sw.sp (fun r _ => by rw [Sw.v]) (fun r hr _ => Sw.cs r hr) Fw
    fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)
  obtain one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  obtain kw : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt w.mem (scA L a) l = Spec.Rsa.bytesAt t₇.mem (scA L a) l := fun a l h₂ =>
    bytes_keep Fw (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ((hL.stk_buf (d := oI) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub))))).symm)
      (by unfold scrBytes at h₂; omega_arith)
  refine ⟨hcw, ?_, ?_, ?_, ?_, fun a l h₁ h₂ h₃ => ?_⟩
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_self64, ct₇, one]
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact nb₇
  · rw [kw _ _ hd2, hb₇]; rfl
  · rw [xw, ct₇, one]
  · rw [kw _ _ h₂, kp₇.scr _ _ (by omega_arith) h₂ h₃, S₆.mem, kp₅.scr _ _ (by omega_arith) h₂ (.inr (Nat.zero_le _)),
      S₄.mem, hu.keep.scr _ _ (by omega_arith) h₂ (.inr (Nat.zero_le _)), k₂ _ _ h₁ h₂]

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `CL` and `AM`

The loops of IRPRF's blocks (`prfLoop_ok`): `CL = IRPRF(KDK, "length", 256)`
at `scratch + sCL` (`clLoop_ok`) and `AM = IRPRF(KDK, "message", k)` at
`scratch + sAM` (`amLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- After `i` blocks of IRPRF to `scratch + dst` from `t₀`, with the messages `textF`. -/
structure PInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (nbv : BitVec 64) (dst : Nat) (textF : Nat → List Byte) (t₀ : State)
    (i : Nat) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd
  ctr : slot t L.Q oI = BitVec.ofNat 64 i
  nb : slot t L.Q oNB = nbv
  out : ∀ j < i, Spec.Rsa.bytesAt t.mem (scA L (dst + 32 * j)) 32 = Spec.Hmac.hmac Spec.Hmac.sha256 kd (textF j)
  keep : ∀ a l, 1040 ≤ a → a + l ≤ dst → Spec.Rsa.bytesAt t.mem (scA L a) l = Spec.Rsa.bytesAt t₀.mem (scA L a) l

theorem prfLoop_ok (hL : L.Ok) (hP : 16 ≤ L.P) {label : List Nat} {len count : List Instr} {dst N : Nat}
    {kd : List Byte} {nbv C : BitVec 64} {textF : Nat → List Byte} {t₀ : State} (hN0 : 0 < N) (hN : N ≤ 256)
    (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 4096) (hn : label.length + 4 ≤ 16)
    (htl : ∀ i, (textF i).length = label.length + 4)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, ∀ u, Post L g vv m₀ R EM u → u.gpr .x9 = scA L sMsg → u.gpr .x11 = BitVec.ofNat 64 i →
      u.gpr .x12 = L.k → WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧
        Frame [⟨scA L sMsg, 16⟩] u.mem w.mem ∧
        Spec.Rsa.bytesAt w.mem (scA L sMsg) (label.length + 4) = textF i)
    (hcount : ∀ u, Post L g vv m₀ R EM u → slot u L.Q oNB = nbv → WP isa (.block (incr count)) u fun w =>
      SameR u w ∧ w.mem = u.mem.writeW (L.Q + BitVec.ofNat 64 oI) (slot u L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u L.Q oI + 1))
    (h : PInv L g vv m₀ R EM kd nbv dst textF t₀ 0 t₀) :
    WP isa (.loop (prfBody (HH v) label len dst count) (.nonzero .x .x12)) t₀
      (PInv L g vv m₀ R EM kd nbv dst textF t₀ N) := by
  refine Bytes.count_loop hN0 (PInv L g vv m₀ R EM kd nbv dst textF t₀) (fun i hi u hu => ?_) h
  refine WP.mono (prfBody_ok hL hP hu.post hu.kdk hu.ctr hu.nb (by omega_arith) (by omega_arith) (by omega_arith) hdst hn (htl i)
    (hmsg i hi) hcount) fun w hw => ⟨⟨hw.post, ?_, hw.ctr, hw.nb, fun j hj => ?_, fun a l h₁ h₂ => ?_⟩, ?_⟩
  · rw [hw.keep _ _ (by decide) (by unfold scrBytes at hd2; decide) (.inl (by unfold sKDK; omega_arith)), hu.kdk]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw.keep _ _ (by omega_arith) (by omega_arith) (.inl (by omega_arith)), hu.out j hj]
    · exact hw.out
  · rw [hw.keep _ _ h₁ (by omega_arith) (.inl (by omega_arith)), hu.keep a l h₁ h₂]
  · rw [hw.x12, hC i hi]; exact Bytes.counter_ne hi (by omega_arith)

/-! ## The bytes of the blocks -/

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} (n : Nat) (h : ∀ j < n, f j = g j) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun j hj => h j (by omega_arith)),
      List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.flatMap_nil, h n (by omega_arith)]

theorem bytes_blocks (m : Mem) (o : Nat) : ∀ n, Spec.Rsa.bytesAt m (scA L o) (32 * n) =
    (List.range n).flatMap fun j => Spec.Rsa.bytesAt m (scA L (o + 32 * j)) 32
  | 0 => rfl
  | n + 1 => by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega_arith, Enc.bytesAt_add, bytes_blocks m o n, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Enc.add_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ## The counters -/

theorem clInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : ∀ d, 200 ≤ d → d + 8 ≤ 224 → InRegions t.wr (Q + BitVec.ofNat 64 d) 8) :
    WP isa (.block clInit) t fun u => SameR t u ∧
      u.mem = (t.mem.writeW (Q + BitVec.ofNat 64 oI) (0 : BitVec 64)).writeW (Q + BitVec.ofNat 64 oNB)
        (((t.mem.writeW (Q + BitVec.ofNat 64 oI) (0 : BitVec 64)).readW (Q + BitVec.ofNat 64 oK) 64 + 31) >>> 5) := by
  obtain h136 := h 136 (by decide)
  obtain w200 := hw 200 (by decide) (by decide)
  obtain w208 := hw 208 (by decide) (by decide)
  apply WP.of_runBlock
  simp only [clInit, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.load, State.store,
    Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp,
    oI, oK, oNB, BitVec.add_zero, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq,
    ite_false, h136, w200, w208]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

theorem amInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (hw : InRegions t.wr (Q + BitVec.ofNat 64 200) 8) :
    WP isa (.block [.addSp .x9 0, .movz .x .x10 0 0, .str .x .x10 .x9 oI]) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oI) (0 : BitVec 64) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.store,
    Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp,
    oI, BitVec.add_zero, Option.bind_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq,
    ite_false, hw]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

/-! ## The loops -/

theorem irprf_bytes {m : Mem} {kd label : List Byte} {length dst N : Nat} (hN : N = (length + 31) / 32)
    (hout : ∀ j < N, Spec.Rsa.bytesAt m (scA L (dst + 32 * j)) 32 = Proof.RsaPkcs1Enc.prfBlock kd label length j)
    (hl : length ≤ 32 * N) :
    Spec.Rsa.bytesAt m (scA L dst) length = Spec.RsaPkcs1Enc.irprf kd label length := by
  rw [Proof.RsaPkcs1Enc.irprf_eq, ← hN, ← flatMap_range_congr N hout, ← bytes_blocks, ← bytesAt_take _ _ hl]

theorem nb_eq {k : BitVec 64} (hk : k.toNat ≤ 1024) : (k + 31) >>> 5 = BitVec.ofNat 64 ((k.toNat + 31) / 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (31 : BitVec 64).toNat = 31 from rfl]
  omega_arith

/-- `CL` after its loop. -/
structure CLR (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd
  nb : slot t L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32)
  cl : Spec.Rsa.bytesAt t.mem (scA L sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- A byte of the message buffer is writable. -/
theorem Post.msgW (hL : L.Ok) {t : State} (hc : Post L g vv m₀ R EM t) :
    ∀ d < 16, InRegions t.wr (scA L sMsg + BitVec.ofNat 64 d) 1 := fun d hd => by
  rw [Enc.add_add]
  exact (scCov hL hc.ctx (a := sMsg + d) (n := 1) (by unfold sMsg scrBytes; omega_arith)) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- After `clInit`: the counter zero, the number of `AM`'s blocks in its slot, and `scratch` as before. -/
theorem clStart_ok (hL : L.Ok) {t : State} (hc : Post L g vv m₀ R EM t) :
    WP isa (.block clInit) t fun t₁ => Post L g vv m₀ R EM t₁ ∧ slot t₁ L.Q oI = BitVec.ofNat 64 0 ∧
      slot t₁ L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32) ∧ ∀ a l, a + l ≤ scrBytes →
        Spec.Rsa.bytesAt t₁.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := by
  have hk := hL.k1024
  have hnQ := hL.nQ
  refine WP.mono (clInit_ok hc.ctx.sp hc.slots fun d _ h₂ => hc.ctx.inFr (by unfold frameBytes; omega_arith))
    fun t₁ ⟨S₁, m₁⟩ => ?_
  obtain F₁ : Frame [⟨L.Q + BitVec.ofNat 64 oI, 8⟩, ⟨L.Q + BitVec.ofNat 64 oNB, 8⟩] t.mem t₁.mem := by
    rw [m₁]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_cons_self ..) _ ?_)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_ <;> exact Region.contains_self _ _
  obtain hc₁ := hc.step hL S₁.rd S₁.wr S₁.sp (fun r _ => by rw [S₁.v]) (fun r hr _ => S₁.cs r hr) F₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)
    · exact .inr (.inr ⟨oNB, by decide, by show oNB + 8 ≤ frameBytes; decide, rfl⟩)
  obtain kp₁ : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₁.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := fun a l h₂ =>
    bytes_keep F₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_buf (d := oI) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub)))).symm
      · exact (hL.stk_buf (d := oNB) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub)))).symm)
      (by unfold scrBytes at h₂; omega_arith)
  obtain sep : ∀ a b, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 360 → b + 8 ≤ 360 → Mem.Sep (L.Q + BitVec.ofNat 64 a) 8
      (L.Q + BitVec.ofNat 64 b) 8 := fun a b h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
  obtain ct₁ : slot t₁ L.Q oI = BitVec.ofNat 64 0 := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_sep (sep _ _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]; rfl
  obtain nb₁ : slot t₁ L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32) := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_self64, Mem.readW_writeW_sep (sep _ _ (by decide) (by decide) (by decide)) (by decide),
      hc.ctx.kept.k, nb_eq hk]
  exact ⟨hc₁, ct₁, nb₁, kp₁⟩

theorem clLoop_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} {kd : List Byte} (hc : Post L g vv m₀ R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd) :
    WP isa (clLoop (HH v)) t (CLR L g vv m₀ R EM kd) := by
  refine WP.seq (WP.mono (clStart_ok hL hc) fun t₁ ⟨hc₁, ct₁, nb₁, kp₁⟩ => ?_)
  refine WP.mono (prfLoop_ok (v := v) hL hP (label := lengthLabel) (len := clLen) (count := [.movz .x .x12 8 0])
    (dst := sCL) (N := 8) (C := BitVec.ofNat 64 8) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_length, lengthLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_arith))
    (fun i hi u hu x9 x11 x12 => WP.mono (msgCL_ok x9 x11 (by omega_arith) (hu.msgW hL))
      fun w ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e⟩, f, g⟩)
    (fun u hu _ => WP.mono (incrCL_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 200) (by decide)))
      fun w hw => hw)
    ⟨hc₁, by rw [kp₁ _ _ (by decide), hkd], ct₁, nb₁, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.post, h₂.kdk, h₂.nb, ?_⟩
  exact irprf_bytes (N := 8) (by decide) (fun j hj => h₂.out j hj) (by decide)

/-- `AM` after its loop, and `CL` still. -/
structure AMR (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA L sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA L sAM) L.k.toNat =
    Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") L.k.toNat

/-- After `AM`'s counter is zeroed: `scratch` as before. -/
theorem amStart_ok (hL : L.Ok) {t : State} (hc : Post L g vv m₀ R EM t)
    (hnb : slot t L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32)) :
    WP isa (.block [.addSp .x9 0, .movz .x .x10 0 0, .str .x .x10 .x9 oI]) t fun t₁ =>
      Post L g vv m₀ R EM t₁ ∧ slot t₁ L.Q oI = BitVec.ofNat 64 0 ∧
      slot t₁ L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32) ∧ ∀ a l, a + l ≤ scrBytes →
        Spec.Rsa.bytesAt t₁.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := by
  have hnQ := hL.nQ
  refine WP.mono (amInit_ok hc.ctx.sp (hc.ctx.inFr (d := 200) (by decide))) fun t₁ ⟨S₁, m₁⟩ => ?_
  obtain F₁ : Frame [⟨L.Q + BitVec.ofNat 64 oI, 8⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hc₁ := hc.step hL S₁.rd S₁.wr S₁.sp (fun r _ => by rw [S₁.v]) (fun r hr _ => S₁.cs r hr) F₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)
  obtain kp₁ : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₁.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := fun a l h₂ =>
    bytes_keep F₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hL.stk_buf (d := oI) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub)))).symm)
      (by unfold scrBytes at h₂; omega_arith)
  obtain ct₁ : slot t₁ L.Q oI = BitVec.ofNat 64 0 := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_self64]; rfl
  obtain nb₁ : slot t₁ L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32) := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by unfold oNB; omega_arith) (by unfold oI; omega_arith))
      (by decide)]
    exact hnb
  exact ⟨hc₁, ct₁, nb₁, kp₁⟩

theorem amLoop_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} {kd : List Byte} (h : CLR L g vv m₀ R EM kd t) :
    WP isa (amLoop (HH v)) t (AMR L g vv m₀ R EM kd) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  refine WP.seq (WP.mono (amStart_ok hL h.post h.nb) fun t₁ ⟨hc₁, ct₁, nb₁, kp₁⟩ => ?_)
  obtain hN0 : 0 < (L.k.toNat + 31) / 32 := by omega_arith
  refine WP.mono (prfLoop_ok (v := v) hL hP (label := messageLabel) (len := amLen) (count := [.ldrSp .x12 oNB])
    (dst := sAM) (N := (L.k.toNat + 31) / 32) (C := BitVec.ofNat 64 ((L.k.toNat + 31) / 32)) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * L.k.toNat) 2)
    hN0 (by omega_arith) (by decide) (by unfold sAM scrBytes; omega_arith) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_message, messageLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_arith))
    (fun i hi u hu x9 x11 x12 => WP.mono (msgAM_ok x9 x11 x12 (by omega_arith) hk (hu.msgW hL))
      fun w ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e⟩, f, g⟩)
    (fun u hu hnb' => WP.mono (incrAM_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 200) (by decide)))
      fun w ⟨a, b, c⟩ => ⟨a, b, by rw [c, hnb']⟩)
    ⟨hc₁, by rw [kp₁ _ _ (by decide), h.kdk], ct₁, nb₁, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.post, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide), kp₁ _ _ (by decide), h.cl]
  · exact irprf_bytes rfl (fun j hj => h₂.out j hj) (by omega_arith)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
