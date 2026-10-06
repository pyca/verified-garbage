import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: one byte of each loop

What one iteration of each byte loop does, from any state in which its
accesses are permitted, as facts about the state it ends in (`PsStep`,
`MsgStep`, `MaskStep`): the byte it stores, the registers it advances, and
that nothing else changes. The zero test of `PS` is `zmask`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- All ones if a byte of `bs` is zero, zero if none is. -/
def zmask (bs : List Byte) : BitVec 64 := if bs.all (· != 0) then 0 else BitVec.allOnes 64

/-- All ones if `b` is zero. -/
def zbit (b : Byte) : BitVec 64 := if b = 0 then BitVec.allOnes 64 else 0

theorem zmask_nil : zmask [] = 0 := rfl

theorem zmask_snoc (bs : List Byte) (b : Byte) : zmask (bs ++ [b]) = zmask bs ||| zbit b := by
  by_cases hb : b = 0
  · subst hb
    have : ¬ (bs ++ [(0 : Byte)]).all (· != 0) = true := by simp
    simp only [zmask, this, Bool.false_eq_true, ite_false, zbit, ite_true, BitVec.or_allOnes]
  · have : (b != 0) = true := by simpa using hb
    simp only [zmask, List.all_append, List.all_cons, List.all_nil, Bool.and_true, this, zbit, hb, ite_false]
    exact BitVec.or_zero.symm

/-- After one iteration of `psBody`, from `t`. -/
structure PsStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr .x13) 1 (t.mem (t.gpr .x11))
  x11 : u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1
  x12 : u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1
  x13 : u.gpr .x13 = t.gpr .x13 + BitVec.ofNat 64 1
  x14 : u.gpr .x14 = t.gpr .x14 ||| zbit (t.mem (t.gpr .x11))
  other : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x16 → u.gpr r = t.gpr r

theorem borrow_byte (b : Byte) :
    b.setWidth 64 + ~~~(b.setWidth 64) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (b.setWidth 64).toNat + (~~~(1 : BitVec 64)).toNat + 1)).toNat = zbit b := by
  rw [Bytes.borrow, zbit]
  by_cases hb : b = 0
  · simp only [hb, ite_true]; rfl
  · have : ¬ b.setWidth 64 = 0 := fun h => hb ((Bytes.setWidth64_eq_zero b).mp h)
    simp only [hb, ite_false, this]

theorem psBody_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .x13 + BitVec.ofNat 64 0) 1) (h15 : t.gpr .x15 = 1) :
    WP isa (.block psBody) t (PsStep t) := by
  apply WP.of_runBlock
  simp only [psBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, State.addWithCarry, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, RegUpd.c_write, reduceCtorEq, ite_false, hr, hw, h15,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, fun r h10 h11 h12 h13 h14 h16 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, Bytes.read_one, Bytes.byte_rt]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, BitVec.add_zero,
      Bytes.read_one, Bytes.byte64, Bool.toNat_true, borrow_byte]
  · simp only [RegUpd.gpr_write, h10, h11, h12, h13, h14, h16, ite_false]

/-- After one iteration of `msgBody`, from `t`. -/
structure MsgStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr .x13) 1 (t.mem (t.gpr .x6))
  x6 : u.gpr .x6 = t.gpr .x6 + BitVec.ofNat 64 1
  x7 : u.gpr .x7 = t.gpr .x7 - BitVec.ofNat 64 1
  x13 : u.gpr .x13 = t.gpr .x13 + BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x13 → u.gpr r = t.gpr r

theorem msgBody_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x6 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .x13 + BitVec.ofNat 64 0) 1) :
    WP isa (.block msgBody) t (MsgStep t) := by
  apply WP.of_runBlock
  simp only [msgBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hr, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun r h6 h7 h10 h13 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, Bytes.read_one, Bytes.byte_rt]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h6, h7, h10, h13, ite_false]

/-- After one iteration of `maskBody`, from `t`. -/
structure MaskStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = (t.mem.write (t.gpr .x11) 1 (((t.mem (t.gpr .x11)).setWidth 64 &&& ~~~(t.gpr .x14)).setWidth 8)).write
    (t.gpr .x13) 1 ((t.gpr .x15).setWidth 8)
  x11 : u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1
  x12 : u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1
  x13 : u.gpr .x13 = t.gpr .x13 + BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → u.gpr r = t.gpr r

theorem maskBody_ok {t : State} (hr : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 0) 1) (hw' : InRegions t.wr (t.gpr .x13 + BitVec.ofNat 64 0) 1) :
    WP isa (.block maskBody) t (MaskStep t) := by
  apply WP.of_runBlock
  simp only [maskBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hr, hw, hw',
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun r h10 h11 h12 h13 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, Bytes.read_one, Bytes.byte64, Bytes.rotateRight_zero,
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h10, h11, h12, h13, ite_false]

/-- After `sep`, from `t`. -/
structure SepStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = (t.mem.write (t.gpr .x13) 1 0#8).writeW (t.sp + BitVec.ofNat 64 oZ) (t.gpr .x14)
  x13 : u.gpr .x13 = t.gpr .x13 + BitVec.ofNat 64 1
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x13 → u.gpr r = t.gpr r

theorem sep_ok {t : State} (hw : InRegions t.wr (t.gpr .x13 + BitVec.ofNat 64 0) 1)
    (hz : InRegions t.wr (t.sp + BitVec.ofNat 64 0 + BitVec.ofNat 64 oZ) 8) :
    WP isa (.block sep) t (SepStep t) := by
  unfold oZ at hz
  apply WP.of_runBlock
  simp only [sep, oZ, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store,
    State.read, Size.bits, Size.bytes, BitVec.shiftLeft_zero, BitVec.setWidth_eq, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hw, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, fun r h9 h10 h13 => ?_⟩
  · simp only [BitVec.add_zero, write8]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h9, h10, h13, ite_false]

/-- After `callArgs`, from `t`. -/
structure ArgsStep (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  x6 : u.gpr .x6 = t.sp + BitVec.ofNat 64 oEM
  x7 : u.gpr .x7 = t.gpr .x3
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → u.gpr r = t.gpr r

theorem callArgs_ok (t : State) : WP isa (.block callArgs) t (ArgsStep t) := by
  apply WP.of_runBlock
  simp only [callArgs, oEM, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, Nat.reduceLT, ite_true, RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.or_self,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r h6 h7 => by simp only [RegUpd.gpr_write, h6, h7, ite_false]⟩

/-- After `maskArgs`, from `t`. -/
structure MaskArgs (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem
  x0 : u.gpr .x0 = t.gpr .x0 &&& ~~~(t.mem.readW (t.sp + BitVec.ofNat 64 oZ) 64)
  x11 : u.gpr .x11 = t.mem.readW (t.sp + BitVec.ofNat 64 oOut) 64
  x12 : u.gpr .x12 = t.mem.readW (t.sp + BitVec.ofNat 64 oK) 64
  x13 : u.gpr .x13 = t.sp + BitVec.ofNat 64 oEM
  x14 : u.gpr .x14 = t.mem.readW (t.sp + BitVec.ofNat 64 oZ) 64
  x15 : u.gpr .x15 = 0
  other : ∀ r, r ≠ .x0 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → u.gpr r = t.gpr r

theorem maskArgs_ok {t : State} (hz : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 oZ) 8)
    (ho : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 oOut) 8)
    (hk : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 oK) 8) :
    WP isa (.block maskArgs) t (MaskArgs t) := by
  unfold oZ at hz; unfold oOut at ho; unfold oK at hk
  apply WP.of_runBlock
  simp only [maskArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.shiftLeft_zero, BitVec.setWidth_eq, Option.map_some, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write,
    reduceCtorEq, ite_false, hz, ho, hk, read8, oZ, oOut, oK, oEM, Bytes.rotateRight_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r h0 h11 h12 h13 h14 h15 => ?_⟩
  all_goals first
    | simp only [RegUpd.gpr_write, h0, h11, h12, h13, h14, h15, ite_false]
    | (simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; done)
    | (simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
