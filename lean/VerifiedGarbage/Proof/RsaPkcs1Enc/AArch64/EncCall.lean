module

public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Encrypt
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `RsaPkcs1Enc.AArch64.EncLoops`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.EncStep`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: one byte of each loop

What one iteration of each byte loop does, from any state in which its
accesses are permitted, as facts about the state it ends in (`PsStep`,
`MsgStep`, `MaskStep`): the byte it stores, the registers it advances, and
that nothing else changes. The zero test of `PS` is `zmask`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- All ones if a byte of `bs` is zero, zero if none is. -/
def zmask (bs : List Byte) : BitVec 64 := if bs.all (· != 0) then 0 else BitVec.allOnes 64

/-- All ones if `b` is zero. -/
def zbit (b : Byte) : BitVec 64 := if b = 0 then BitVec.allOnes 64 else 0

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

end

end

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the copies of `PS` and `M`

`psLoop` copies the padding string `PS` to `EM` after its first two bytes,
collecting in `x14` whether any byte is zero (`zmask`); `msgCopy` copies the
message after the separator. Both keep `Ctx`, since they write only `EM`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- The argument registers hold the arguments on entry. -/
structure Args (g : Reg → BitVec 64) (t : State) : Prop where
  x0 : t.gpr .x0 = g .x0
  x1 : t.gpr .x1 = g .x1
  x2 : t.gpr .x2 = g .x2
  x3 : t.gpr .x3 = g .x3
  x4 : t.gpr .x4 = g .x4
  x5 : t.gpr .x5 = g .x5
  x6 : t.gpr .x6 = g .x6
  x7 : t.gpr .x7 = g .x7

theorem Args.of {g : Reg → BitVec 64} {t u : State} (h : Args g t)
    (hk : ∀ r, r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] → u.gpr r = t.gpr r) : Args g u :=
  ⟨(hk _ (by simp)).trans h.x0, (hk _ (by simp)).trans h.x1, (hk _ (by simp)).trans h.x2,
    (hk _ (by simp)).trans h.x3, (hk _ (by simp)).trans h.x4, (hk _ (by simp)).trans h.x5,
    (hk _ (by simp)).trans h.x6, (hk _ (by simp)).trans h.x7⟩

theorem mem_ne {l : List Reg} {r d : Reg} (hr : r ∈ l) (hd : d ∉ l) : r ≠ d := fun e => hd (e ▸ hr)

theorem bytesAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Rsa.bytesAt m p (j + 1) = Spec.Rsa.bytesAt m p j ++ [m (p + BitVec.ofNat 64 j)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ]

theorem add_one (p : Addr) (j : Nat) : p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) :=
  add_add p j 1

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
  (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

omit hL in
/-- A byte of a buffer the function never writes, as on entry. -/
theorem byte_ro {R : Region} (hO : R.Disjoint L.OUT) (hS : R.Disjoint L.SCR) (hK : R.Disjoint L.STK)
    (hb : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  hc.frame.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hO, hS, hK]) hb hi

theorem ps_byte {i : Nat} (hi : i < L.pl.toNat) :
    t.mem (L.ps + BitVec.ofNat 64 i) = m₀ (L.ps + BitVec.ofNat 64 i) :=
  hc.byte_ro (R := L.PS) hL.oP.symm hL.pS hL.kP.symm (Nat.le_of_lt L.pl.isLt) hi

theorem msg_byte {i : Nat} (hi : i < L.ml.toNat) :
    t.mem (L.msg + BitVec.ofNat 64 i) = m₀ (L.msg + BitVec.ofNat 64 i) :=
  hc.byte_ro (R := L.MSG) hL.oM.symm hL.mS hL.kM.symm (Nat.le_of_lt L.ml.isLt) hi

/-- A byte of `PS` may be read. -/
theorem in_ps {i : Nat} (hi : i < L.pl.toNat) :
    InRegions (t.rd ++ t.wr) (L.ps + BitVec.ofNat 64 i + BitVec.ofNat 64 0) 1 :=
  ⟨L.PS, by rw [hc.rd, hc.wr]; simp,
    by rw [add_add, Nat.add_zero]; exact Offset.contains_base _ (by omega_arith) (by have := hL.bP; omega_arith)⟩

theorem in_msg {i : Nat} (hi : i < L.ml.toNat) :
    InRegions (t.rd ++ t.wr) (L.msg + BitVec.ofNat 64 i + BitVec.ofNat 64 0) 1 :=
  ⟨L.MSG, by rw [hc.rd, hc.wr]; simp,
    by rw [add_add, Nat.add_zero]; exact Offset.contains_base _ (by omega_arith) (by have := hL.bM; omega_arith)⟩

omit hL in
/-- A byte of the inner frame may be written. -/
theorem in_fr {d : Nat} (hd : d + 1 ≤ frameBytes) :
    InRegions t.wr (L.Q + BitVec.ofNat 64 d + BitVec.ofNat 64 0) 1 := by
  rw [add_add, Nat.add_zero]; exact hc.inFr hd

end Ctx

namespace Lay.Ok

variable {L : Lay} (hL : L.Ok)
include hL

theorem pl_le : L.pl.toNat + 3 ≤ L.k.toNat := by have := hL.plk; have := hL.mlk; omega_arith
theorem pl8 : 8 ≤ L.pl.toNat := by have := hL.plk; have := hL.mlk; omega_arith
theorem em_len : L.pl.toNat + L.ml.toNat + 3 = L.k.toNat := by have := hL.plk; have := hL.mlk; omega_arith

end Lay.Ok

/-- After `j` bytes of `PS`. -/
structure PsInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (j : Nat) (t : State) :
    Prop where
  ctx : Ctx L g vv m₀ t
  args : Args g t
  x11 : t.gpr .x11 = L.ps + BitVec.ofNat 64 j
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.pl.toNat - j)
  x13 : t.gpr .x13 = L.Q + BitVec.ofNat 64 (oEM + 2 + j)
  x14 : t.gpr .x14 = zmask (Spec.Rsa.bytesAt m₀ L.ps j)
  x15 : t.gpr .x15 = 1
  b0 : t.mem (L.Q + BitVec.ofNat 64 oEM) = 0
  b1 : t.mem (L.Q + BitVec.ofNat 64 (oEM + 1)) = 2
  ps : ∀ i < j, t.mem (L.Q + BitVec.ofNat 64 (oEM + 2 + i)) = m₀ (L.ps + BitVec.ofNat 64 i)

theorem psLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : PsInv L g vv m₀ 0 t) : WP isa psLoop t (PsInv L g vv m₀ L.pl.toNat) := by
  have hnQ := hL.nQ
  have hpl := hL.pl_le
  have hk := hL.k1024
  refine Bytes.count_loop (by have := hL.pl8; omega_arith) (PsInv L g vv m₀) (fun j hj u hu => ?_) h
  have hc := hu.ctx
  refine WP.mono (psBody_ok (by rw [hu.x11]; exact hc.in_ps hL hj)
    (by rw [hu.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega_arith)) hu.x15) fun w hw => ?_
  obtain hne : ∀ d, d < oEM + 2 + j → L.Q + BitVec.ofNat 64 d ≠ L.Q + BitVec.ofNat 64 (oEM + 2 + j) :=
    fun d hd => Offset.add_ofNat_ne _ (by unfold oEM at hd; omega_arith) (by unfold oEM; omega_arith) (by omega_arith)
  obtain hmem : w.mem = u.mem.write (L.Q + BitVec.ofNat 64 (oEM + 2 + j)) 1 (m₀ (L.ps + BitVec.ofNat 64 j)) := by
    rw [hw.mem, hu.x13, hu.x11, hc.ps_byte hL hj]
  obtain hf : Frame [⟨L.Q + BitVec.ofNat 64 (oEM + 2 + j), 1⟩] u.mem w.mem := by
    rw [hmem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.pl.toNat - (j + 1)) := by
    rw [hw.x12, hu.x12, Bytes.counter_step hj L.pl.isLt]
  refine ⟨⟨?_, ?_, ?_, hx12, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · refine hc.store hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => hw.other r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))
      (mem_ne hr (by decide))) hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨oEM + 2 + j, by unfold oEM; omega_arith, by show oEM + 2 + j + 1 ≤ 1072; unfold oEM; omega_arith, rfl⟩
  · exact hu.args.of fun r hr => hw.other r (mem_ne hr (by decide)) (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))
  · rw [hw.x11, hu.x11, add_one]
  · rw [hw.x13, hu.x13, add_add, Nat.add_assoc]
  · rw [hw.x14, hu.x14, hu.x11, hc.ps_byte hL hj, bytesAt_succ, zmask_snoc]
  · rw [hw.other .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu.x15]
  · rw [hmem, Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega_arith)), hu.b0]
  · rw [hmem, Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega_arith)), hu.b1]
  · rw [hmem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (hne _ (by omega_arith)), hu.ps i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hx12]; exact Bytes.counter_ne hj L.pl.isLt

/-- After the separator and `j` bytes of `M`. -/
structure MsgInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (j : Nat) (t : State) :
    Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = g .x0
  x1 : t.gpr .x1 = g .x1
  x2 : t.gpr .x2 = g .x2
  x3 : t.gpr .x3 = g .x3
  x4 : t.gpr .x4 = g .x4
  x5 : t.gpr .x5 = g .x5
  x6 : t.gpr .x6 = L.msg + BitVec.ofNat 64 j
  x7 : t.gpr .x7 = BitVec.ofNat 64 (L.ml.toNat - j)
  x13 : t.gpr .x13 = L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j)
  b0 : t.mem (L.Q + BitVec.ofNat 64 oEM) = 0
  b1 : t.mem (L.Q + BitVec.ofNat 64 (oEM + 1)) = 2
  ps : ∀ i < L.pl.toNat, t.mem (L.Q + BitVec.ofNat 64 (oEM + 2 + i)) = m₀ (L.ps + BitVec.ofNat 64 i)
  sep : t.mem (L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat)) = 0
  msg : ∀ i < j, t.mem (L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + i)) = m₀ (L.msg + BitVec.ofNat 64 i)
  z : t.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

theorem sep_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hg : L.msg = g .x6 ∧ L.ml = g .x7) (h : PsInv L g vv m₀ L.pl.toNat t) :
    WP isa (.block sep) t (MsgInv L g vv m₀ 0) := by
  have hnQ := hL.nQ
  have hpl := hL.pl_le
  have hk := hL.k1024
  have hc := h.ctx
  refine WP.mono (sep_ok (by rw [h.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega_arith))
    (by rw [hc.sp, add_add]; exact hc.inFr (by decide))) fun w hw => ?_
  obtain hmem : w.mem = (t.mem.write (L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat)) 1 0#8).writeW
      (L.Q + BitVec.ofNat 64 oZ) (zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)) := by
    rw [hw.mem, h.x13, hc.sp, h.x14]
  obtain hf : Frame [⟨L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat), 1⟩, ⟨L.Q + BitVec.ofNat 64 oZ, 8⟩] t.mem w.mem := by
    rw [hmem]
    exact ((Frame.refl _ _).write (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  -- A byte of `EM` before the separator is not in the zero test's slot.
  obtain hz : ∀ d, oEM ≤ d → d + 1 ≤ frameBytes →
      w.mem (L.Q + BitVec.ofNat 64 d) = (t.mem.write (L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat)) 1 0#8)
        (L.Q + BitVec.ofNat 64 d) := fun d h₁ h₂ => by
    rw [hmem]
    exact Bytes.byte_writeW_sep (Offset.sep _ (by unfold oEM oZ at *; omega_arith) (by unfold frameBytes at h₂; omega_arith)
      (by unfold oZ; omega_arith))
  obtain hne : ∀ d, d < oEM + 2 + L.pl.toNat →
      L.Q + BitVec.ofNat 64 d ≠ L.Q + BitVec.ofNat 64 (oEM + 2 + L.pl.toNat) :=
    fun d hd => Offset.add_ofNat_ne _ (by unfold oEM at hd; omega_arith) (by unfold oEM; omega_arith) (by omega_arith)
  have go : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x13 → w.gpr r = t.gpr r := hw.other
  refine ⟨?_, (go .x0 (by decide) (by decide) (by decide)).trans h.args.x0,
    (go .x1 (by decide) (by decide) (by decide)).trans h.args.x1,
    (go .x2 (by decide) (by decide) (by decide)).trans h.args.x2,
    (go .x3 (by decide) (by decide) (by decide)).trans h.args.x3,
    (go .x4 (by decide) (by decide) (by decide)).trans h.args.x4,
    (go .x5 (by decide) (by decide) (by decide)).trans h.args.x5, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_,
    fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
  · refine hc.store hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨oEM + 2 + L.pl.toNat, by unfold oEM; omega_arith, by show oEM + 2 + L.pl.toNat + 1 ≤ 1072; unfold oEM; omega_arith, rfl⟩
    · exact ⟨oZ, by decide, by show oZ + 8 ≤ 1072; decide, rfl⟩
  · rw [go .x6 (by decide) (by decide) (by decide), h.args.x6, ← hg.1, BitVec.add_zero]
  · rw [go .x7 (by decide) (by decide) (by decide), h.args.x7, ← hg.2, Nat.sub_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hw.x13, h.x13, add_add, show oEM + 2 + L.pl.toNat + 1 = oEM + 3 + L.pl.toNat + 0 by omega_arith]
  · rw [hz _ (Nat.le_refl _) (by decide), Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega_arith)), h.b0]
  · rw [hz _ (by unfold oEM; omega_arith) (by decide), Bytes.write1_ne _ _ (hne _ (by unfold oEM; omega_arith)), h.b1]
  · rw [hz _ (by unfold oEM; omega_arith) (by unfold oEM frameBytes; omega_arith), Bytes.write1_ne _ _ (hne _ (by omega_arith)),
      h.ps i hi]
  · rw [hz _ (by unfold oEM; omega_arith) (by unfold oEM frameBytes; omega_arith)]; exact Bytes.write1_self _ _ _
  · rw [hmem, Mem.readW_writeW_self64]

theorem msgLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hm : 0 < L.ml.toNat) (h : MsgInv L g vv m₀ 0 t) : WP isa msgLoop t (MsgInv L g vv m₀ L.ml.toNat) := by
  have hnQ := hL.nQ
  have hem := hL.em_len
  have hk := hL.k1024
  refine Bytes.count_loop hm (MsgInv L g vv m₀) (fun j hj u hu => ?_) h
  have hc := hu.ctx
  refine WP.mono (msgBody_ok (by rw [hu.x6]; exact hc.in_msg hL hj)
    (by rw [hu.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega_arith))) fun w hw => ?_
  obtain hne : ∀ d, d < oEM + 3 + L.pl.toNat + j →
      L.Q + BitVec.ofNat 64 d ≠ L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j) :=
    fun d hd => Offset.add_ofNat_ne _ (by unfold oEM at hd; omega_arith) (by unfold oEM; omega_arith) (by omega_arith)
  obtain hmem : w.mem = u.mem.write (L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j)) 1
      (m₀ (L.msg + BitVec.ofNat 64 j)) := by
    rw [hw.mem, hu.x13, hu.x6, hc.msg_byte hL hj]
  obtain hf : Frame [⟨L.Q + BitVec.ofNat 64 (oEM + 3 + L.pl.toNat + j), 1⟩] u.mem w.mem := by
    rw [hmem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hx7 : w.gpr .x7 = BitVec.ofNat 64 (L.ml.toNat - (j + 1)) := by
    rw [hw.x7, hu.x7, Bytes.counter_step hj L.ml.isLt]
  have go : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x13 → w.gpr r = u.gpr r := hw.other
  -- The bytes below `M`'s, and the zero test's slot, are as they were.
  obtain hlo : ∀ d, d < oEM + 3 + L.pl.toNat + j → w.mem (L.Q + BitVec.ofNat 64 d) = u.mem (L.Q + BitVec.ofNat 64 d) :=
    fun d hd => by rw [hmem, Bytes.write1_ne _ _ (hne d hd)]
  refine ⟨⟨?_, (go .x0 (by decide) (by decide) (by decide) (by decide)).trans hu.x0,
    (go .x1 (by decide) (by decide) (by decide) (by decide)).trans hu.x1,
    (go .x2 (by decide) (by decide) (by decide) (by decide)).trans hu.x2,
    (go .x3 (by decide) (by decide) (by decide) (by decide)).trans hu.x3,
    (go .x4 (by decide) (by decide) (by decide) (by decide)).trans hu.x4,
    (go .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.x5, ?_, hx7, ?_,
    by rw [hlo _ (by unfold oEM; omega_arith)]; exact hu.b0, by rw [hlo _ (by unfold oEM; omega_arith)]; exact hu.b1,
    fun i hi => by rw [hlo _ (by omega_arith)]; exact hu.ps i hi, by rw [hlo _ (by omega_arith)]; exact hu.sep,
    fun i hi => ?_, ?_⟩, ?_⟩
  · refine hc.store hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨oEM + 3 + L.pl.toNat + j, by unfold oEM; omega_arith,
      by show oEM + 3 + L.pl.toNat + j + 1 ≤ 1072; unfold oEM; omega_arith, rfl⟩
  · rw [hw.x6, hu.x6, add_one]
  · rw [hw.x13, hu.x13, add_add, Nat.add_assoc]
  · rw [hmem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Bytes.write1_ne _ _ (hne _ (by omega_arith)), hu.msg i hi]
    · exact Bytes.write1_self _ _ _
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by unfold oZ oEM; omega_arith) (by unfold oZ; omega_arith) (by unfold oEM; omega_arith)) (by decide)]
    exact hu.z
  · rw [hx7]; exact Bytes.counter_ne hj L.ml.isLt

theorem msgCopy_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : MsgInv L g vv m₀ 0 t) : WP isa msgCopy t (MsgInv L g vv m₀ L.ml.toNat) := by
  refine WP.ite (t.gpr .x7 != 0) (Bytes.eval_nonzero t .x7) (fun hb => msgLoop_ok hL ?_ h) (fun hb => ?_)
  · rw [h.x7, Nat.sub_zero] at hb
    rcases Nat.eq_zero_or_pos L.ml.toNat with h0 | h0
    · rw [h0] at hb; exact absurd hb (by decide)
    · exact h0
  · have h0 : L.ml.toNat = 0 := by
      rw [h.x7, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
      have := (bne_eq_false_iff_eq).mp hb
      rw [this]; rfl
    exact WP.block_nil (h0 ▸ h)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc

end

end

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the call

Once `PS` and `M` are copied, the frame holds
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` (`em_bytes`). `callArgs` sets the call's
`input` and `input_len` (`CallReady`); after the call, whatever it wrote to
`out`, `Ctx` holds again (`CalledF`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, add_add]

/-- The bytes at `p`, each given. -/
theorem bytesAt_eq {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (q + BitVec.ofNat 64 i)) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt m' q n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The encoded message in the frame. -/
theorem em_bytes {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : MsgInv L g vv m₀ L.ml.toNat t) :
    Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
      Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat) := by
  rw [← hL.em_len, show L.pl.toNat + L.ml.toNat + 3 = ((2 + L.pl.toNat) + 1) + L.ml.toNat by omega_arith,
    bytesAt_add, bytesAt_add, bytesAt_add, Spec.RsaPkcs1Enc.encode]
  have e2 : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) 2 = [0x00, 0x02] := by
    simp only [Spec.Rsa.bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, add_add, Nat.add_zero, h.b0, h.b1]
  have eP : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 2) L.pl.toNat =
      Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat :=
    bytesAt_eq fun i hi => by rw [add_add, add_add, ← Nat.add_assoc]; exact h.ps i hi
  have eS : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 (2 + L.pl.toNat)) 1 = [0x00] := by
    simp only [Spec.Rsa.bytesAt, List.range_one, List.map_cons, List.map_nil, add_add, Nat.add_zero, ← Nat.add_assoc,
      h.sep]
  have eM : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM + BitVec.ofNat 64 (2 + L.pl.toNat + 1)) L.ml.toNat =
      Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat :=
    bytesAt_eq fun i hi => by
      rw [add_add, add_add, show oEM + (2 + L.pl.toNat + 1 + i) = oEM + 3 + L.pl.toNat + i by omega_arith]
      exact h.msg i hi
  rw [e2, eP, eS, eM]

/-- Before the call. -/
structure CallReady (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.ol
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.Q + BitVec.ofNat 64 oEM
  x7 : t.gpr .x7 = L.k
  em : Spec.Rsa.bytesAt t.mem (L.Q + BitVec.ofNat 64 oEM) L.k.toNat =
    Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)
  z : t.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

/-- The registers on entry are the layout's. -/
def RegsOf (L : Lay) (g : Reg → BitVec 64) : Prop :=
  g .x0 = L.out ∧ g .x1 = L.ol ∧ g .x2 = L.n ∧ g .x3 = L.k ∧ g .x4 = L.e ∧ g .x5 = L.el ∧ g .x6 = L.msg ∧
    g .x7 = L.ml

theorem callArgs_inv {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hg : RegsOf L g) (h : MsgInv L g vv m₀ L.ml.toNat t) :
    WP isa (.block callArgs) t (CallReady L g vv m₀) :=
  WP.mono (callArgs_ok t) fun w hw => by
    have go : ∀ r, r ≠ .x6 → r ≠ .x7 → w.gpr r = t.gpr r := hw.other
    refine ⟨h.ctx.regs hw.rd hw.wr hw.sp hw.mem hw.v fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [go .x0 (by decide) (by decide), h.x0, hg.1]
    · rw [go .x1 (by decide) (by decide), h.x1, hg.2.1]
    · rw [go .x2 (by decide) (by decide), h.x2, hg.2.2.1]
    · rw [go .x3 (by decide) (by decide), h.x3, hg.2.2.2.1]
    · rw [go .x4 (by decide) (by decide), h.x4, hg.2.2.2.2.1]
    · rw [go .x5 (by decide) (by decide), h.x5, hg.2.2.2.2.2.1]
    · rw [hw.x6, h.ctx.sp]
    · rw [hw.x7, h.x3, hg.2.2.2.1]
    · rw [hw.mem]; exact em_bytes hL h
    · rw [hw.mem]; exact h.z

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem stackArg_ce (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (8 * i)) 64 := rfl

/-- After the call, whatever it wrote to `out`. -/
structure CalledF (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t' : State) : Prop where
  ctx : Ctx L g vv m₀ t'
  z : t'.mem.readW (L.Q + BitVec.ofNat 64 oZ) 64 = zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
