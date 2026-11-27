module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
meta import Lean.Elab.Tactic.Omega.Frontend
import VerifiedGarbage.Proof.Framework.InstancePriority

/-! ### `Rsa.AArch64.PrivLay`, which only this module used -/

section

/-! ### `Rsa.AArch64.PrivCtx`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: the contract on the registers

`chkA` states the shared contract (with the stack the frames use,
`stackBytes`) on the registers and the stack (`private_checked_implies`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

/-- The stack below the stack pointer the function uses: a frame of 16 bytes
saving `x30` and one of 3232 bytes; its callees use none. -/
def stackBytes : Nat := 3248

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- `vg_rsa_private_checked(out = x0, out_len = x1, n = x2, n_len = x3,
e = x4, e_len = x5, input = x6, input_len = x7, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`, the last twelve
on the stack, using `stackBytes` bytes of stack. -/
def chkA : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let scr : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 96⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ s.sp.toNat ∧ s.sp.toNat + 96 ≤ 2 ^ 64 ∧
      s.rd = [n, e, inp, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint inp ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .x3).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .x3).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 11).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 12).map (stackArg s₁) = (List.range 12).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

/-- A state meeting `chkA.pre`: a 64-byte modulus and input, a one-byte
`e`, one-byte primes, exponents and `qInv`, and the stack arguments at
`0x10000`. -/
def chkSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1
    | .x6 => 0x4000 | .x7 => 64 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10058 then 0x20
    else bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x43 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x44 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10041 then 0x45 else bif Nat.beq a.toNat 0x10048 then 1
    else bif Nat.beq a.toNat 0x10052 then 0x02 else bif Nat.beq a.toNat 0x10059 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10000, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem private_checked_implies : chkA.Implies (Proof.Rsa.privateCheckedContract abi stackBytes) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA,
      stackBytes, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h3]) hl
    refine ⟨?_, hsp, by simp only [stackArgs_twelve, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11],
      hn, he⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := by
    sig_implies_sat [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA,
      stackBytes, stackArgs_twelve, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using chkSatState

end VG.Proof.Rsa.AArch64

end

end


/-!
# `vg_rsa_private_checked` on AArch64: where everything is

The function's buffers and the `stackBytes` bytes of stack below the stack
pointer, from `B` up (`Lay`): the inner frame (`FR`, from `B`: the stack
arguments of the calls, the slots, `M` at `oM` and `n`'s values at `oPre`),
then the frame holding our return address (`LR`, at `B + frameBytes`). Our
stack arguments are at `B + stackBytes` (`ARGS`). `Lay.Ok` is what the
contract says of them; `Ctx` is what holds between the frames' pushes and
pops.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The arguments, and the lowest byte of the stack used (`sp - stackBytes`
on entry). -/
structure Lay where
  out : Addr
  ol : BitVec 64
  n : Addr
  k : BitVec 64
  e : Addr
  el : BitVec 64
  inp : Addr
  il : BitVec 64
  p : Addr
  pl : BitVec 64
  q : Addr
  ql : BitVec 64
  dp : Addr
  dpl : BitVec 64
  dq : Addr
  dql : BitVec 64
  qi : Addr
  qil : BitVec 64
  scr : Addr
  sl : BitVec 64
  B : Addr
  /-- Further regions the function may read: none for
  `vg_rsa_private_checked`; for `vg_rsa_private_checked_precomputed`, its
  last stack arguments and `pre`. -/
  X : List Region

namespace Lay

variable (L : Lay)

abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
abbrev N : Region := ⟨L.n, L.k.toNat⟩
abbrev E : Region := ⟨L.e, L.el.toNat⟩
abbrev IN : Region := ⟨L.inp, L.il.toNat⟩
abbrev P : Region := ⟨L.p, L.pl.toNat⟩
abbrev Q : Region := ⟨L.q, L.ql.toNat⟩
abbrev DP : Region := ⟨L.dp, L.dpl.toNat⟩
abbrev DQ : Region := ⟨L.dq, L.dql.toNat⟩
abbrev QI : Region := ⟨L.qi, L.qil.toNat⟩
abbrev SC : Region := ⟨L.scr, L.sl.toNat * 8⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 stackBytes, 96⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, stackBytes⟩
/-- The frames: the inner one, and our return address. -/
abbrev FR : Region := ⟨L.B, frameBytes⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 frameBytes, 16⟩

/-- `w = ⌈k / 8⌉`, and the bytes of `n`'s values. -/
abbrev pw : Nat := 2 * ((L.k.toNat + 7) / 8)

/-- `M` and `n`'s values, in the inner frame. -/
abbrev M : Region := ⟨L.B + BitVec.ofNat 64 oM, L.k.toNat⟩
abbrev PRE : Region := ⟨L.B + BitVec.ofNat 64 oPre, L.pw * 8⟩

/-- What the contract says of where the buffers and the stack are, and of
the lengths. -/
structure Ok : Prop where
  on : L.OUT.Disjoint L.N
  oe : L.OUT.Disjoint L.E
  oi : L.OUT.Disjoint L.IN
  op : L.OUT.Disjoint L.P
  oq : L.OUT.Disjoint L.Q
  odp : L.OUT.Disjoint L.DP
  odq : L.OUT.Disjoint L.DQ
  oqi : L.OUT.Disjoint L.QI
  osc : L.OUT.Disjoint L.SC
  oa : L.OUT.Disjoint L.ARGS
  nsc : L.N.Disjoint L.SC
  esc : L.E.Disjoint L.SC
  isc : L.IN.Disjoint L.SC
  psc : L.P.Disjoint L.SC
  qsc : L.Q.Disjoint L.SC
  dpsc : L.DP.Disjoint L.SC
  dqsc : L.DQ.Disjoint L.SC
  qisc : L.QI.Disjoint L.SC
  sca : L.SC.Disjoint L.ARGS
  ko : L.STK.Disjoint L.OUT
  kn : L.STK.Disjoint L.N
  ke : L.STK.Disjoint L.E
  ki : L.STK.Disjoint L.IN
  kp : L.STK.Disjoint L.P
  kq : L.STK.Disjoint L.Q
  kdp : L.STK.Disjoint L.DP
  kdq : L.STK.Disjoint L.DQ
  kqi : L.STK.Disjoint L.QI
  ksc : L.STK.Disjoint L.SC
  bo : L.out.toNat + L.ol.toNat ≤ 2 ^ 64
  bn : L.n.toNat + L.k.toNat ≤ 2 ^ 64
  be : L.e.toNat + L.el.toNat ≤ 2 ^ 64
  bi : L.inp.toNat + L.il.toNat ≤ 2 ^ 64
  bp : L.p.toNat + L.pl.toNat ≤ 2 ^ 64
  bq : L.q.toNat + L.ql.toNat ≤ 2 ^ 64
  bdp : L.dp.toNat + L.dpl.toNat ≤ 2 ^ 64
  bdq : L.dq.toNat + L.dql.toNat ≤ 2 ^ 64
  bqi : L.qi.toNat + L.qil.toNat ≤ 2 ^ 64
  bsc : L.scr.toNat + L.sl.toNat * 8 ≤ 2 ^ 64
  nB : L.B.toNat + 3344 ≤ 2 ^ 64
  klo : 64 ≤ L.k.toNat
  khi : L.k.toNat ≤ 1024
  olk : L.ol.toNat = L.k.toNat
  ilk : L.il.toNat = L.k.toNat
  el1 : 1 ≤ L.el.toNat
  elk : L.el.toNat ≤ L.k.toNat
  pl1 : 1 ≤ L.pl.toNat
  plk : L.pl.toNat < L.k.toNat
  ql1 : 1 ≤ L.ql.toNat
  qlk : L.ql.toNat < L.k.toNat
  dpl : L.dpl.toNat = L.pl.toNat
  qil : L.qil.toNat = L.pl.toNat
  dql : L.dql.toNat = L.ql.toNat
  slk : 16 * L.k.toNat + 32 ≤ L.sl.toNat

end Lay

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    s.sp - BitVec.ofNat 64 stackBytes, []⟩

theorem lay_top (s : State) : (lay s).B + BitVec.ofNat 64 stackBytes = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 stackBytes = stackArgAddr s 0 := by
  simp only [lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : chkA.pre s) : (lay s).Ok := by
  sig_split h
  rename_i hst h96 _ _ on oe oi op oq odp odq oqi osc oa nsc esc isc psc qsc dpsc dqsc qisc sca ko
    kn ke ki kp kq kdp kdq kqi ksc _ bo bn be bi bp bq bdp bdq bqi bsc _ob1 olk ilk el1 elk pl1 plk
    ql1 qlk dpl qil dql
  obtain ⟨klo, khi⟩ := _ob1
  have slk := h
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 96⟩ := by simp only [Lay.ARGS, lay_args]
  have nB : (lay s).B.toNat + 3344 ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp stackBytes]
    unfold stackBytes at hst ⊢
    omega_using [hst, h96]
  exact ⟨on, oe, oi, op, oq, odp, odq, oqi, osc, ea ▸ oa, nsc, esc, isc, psc, qsc, dpsc, dqsc, qisc,
    ea ▸ sca, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ksc, bo, bn, be, bi, bp, bq, bdp, bdq, bqi, bsc, nB,
    klo, khi, olk, ilk, el1, elk, pl1, plk, ql1, qlk, dpl, qil, dql, slk⟩

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.PrivFrame`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: between the frames' pushes and pops

`Ctx` is what holds there: the permissions, `sp = B`, the callee-saved
registers, our return address in its frame, and that memory changed only in
`out`, `scratch` and the stack. `Slots` is the arguments the code keeps in
the inner frame's slots. `entered` is the state the inner frame's body
starts in.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- The state between the frames' pushes and pops: `g` and `vv` are the
registers on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.IN, L.P, L.Q, L.DP, L.DQ, L.QI, L.ARGS] ++ L.X
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SC]
  sp : t.sp = L.B
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  lr : t.mem.readW (L.B + BitVec.ofNat 64 frameBytes) 64 = g .x30
  frame : Frame [L.OUT, L.SC, L.STK] m₀ t.mem

/-- The arguments kept in the inner frame's slots. -/
structure Slots (L : Lay) (m : Mem) : Prop where
  out : m.readW (L.B + BitVec.ofNat 64 oOut) 64 = L.out
  n : m.readW (L.B + BitVec.ofNat 64 oN) 64 = L.n
  k : m.readW (L.B + BitVec.ofNat 64 oK) 64 = L.k
  e : m.readW (L.B + BitVec.ofNat 64 oE) 64 = L.e
  el : m.readW (L.B + BitVec.ofNat 64 oEl) 64 = L.el
  inp : m.readW (L.B + BitVec.ofNat 64 oIn) 64 = L.inp

/-- Slots survive changes to memory that miss them. -/
theorem Slots.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Slots L m) (hf : Frame rs m m')
    (hd : ∀ R ∈ rs, Region.Disjoint ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ R) (_hB : L.B.toNat + 128 ≤ 2 ^ 64) :
    Slots L m' := by
  have k : ∀ d, oOut ≤ d → d + 8 ≤ oOut + 48 →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 oOut, 48⟩)
      (Offset.contains _ h₁ (by simpa [oOut] using h₂) (by simp only [oOut]; omega_using [])) hd (by decide)
  exact ⟨(k oOut (by decide) (by decide)).trans hk.out, (k oN (by decide) (by decide)).trans hk.n,
    (k oK (by decide) (by decide)).trans hk.k, (k oE (by decide) (by decide)).trans hk.e,
    (k oEl (by decide) (by decide)).trans hk.el, (k oIn (by decide) (by decide)).trans hk.inp⟩

theorem Lay.Ok.args_contains {L : Lay} (hL : L.Ok) {j : Nat} (hj : j < 12) :
    L.ARGS.Contains (L.B + BitVec.ofNat 64 (arg j)) 8 := by
  have hnB := hL.nB
  refine Offset.contains _ ?_ ?_ ?_ <;> simp only [arg, stackBytes, frameBytes] <;> omega_arith

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g vv m₀ t)
include hc

/-- A range in the inner frame may be read. -/
theorem inFr (hL : L.Ok) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by have := hL.nB; unfold frameBytes at h; omega_using [h])⟩

/-- A range in the inner frame may be written. -/
theorem inFrW (hL : L.Ok) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h (by have := hL.nB; unfold frameBytes at h; omega_using [h])⟩

/-- Our stack argument `j` may be read. -/
theorem inArgs (hL : L.Ok) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (arg j)) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, hL.args_contains hj⟩

/-- Our stack argument `j`, read in the frames: what it was on entry. -/
theorem argW (hL : L.Ok) {j : Nat} (hj : j < 12) :
    t.mem.readW (L.B + BitVec.ofNat 64 (arg j)) 64 = m₀.readW (L.B + BitVec.ofNat 64 (arg j)) 64 := by
  have hnB := hL.nB
  refine hc.frame.readW (r := L.ARGS) (hL.args_contains hj) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oa.symm
  · exact hL.sca.symm
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by simp only [stackBytes]; omega_using [])

/-- Code that writes only registers other than the callee-saved ones and
the vector registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr, by rw [hm]; exact hc.lr, by rw [hm]; exact hc.frame⟩

/-- Code that also writes the inner frame. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame [L.FR] t.mem t'.mem) : Ctx L g vv m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    rw [hf.readW (r := L.LR) hlr (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (Nat.le_refl _) (by simp only [frameBytes]; omega_using [])) (by decide)]
    exact hc.lr
  · simp only [List.mem_singleton] at hr; subst hr
    have := Offset.sub_base L.B (d := 0) (n := frameBytes) (k := stackBytes) (by decide)
    exact ⟨L.STK, by simp, by simpa using this⟩

end Ctx

/-! ## Entering the frames -/

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (s : State) : (entered s).sp = (lay s).B := by
  show s.sp - 16 - BitVec.ofNat 64 frameBytes = s.sp - BitVec.ofNat 64 stackBytes
  simp only [frameBytes, stackBytes]
  bv_omega

theorem lr_slot (s : State) : s.sp - 16 = (lay s).B + BitVec.ofNat 64 frameBytes := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 stackBytes + BitVec.ofNat 64 frameBytes
  simp only [frameBytes, stackBytes]
  bv_omega

theorem entered_wr (s : State) : (entered s).wr = (lay s).FR :: (lay s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 frameBytes, frameBytes⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 frameBytes = (lay s).B from entered_sp s, lr_slot]

theorem entered_mem (s : State) :
    (entered s).mem = s.mem.writeW ((lay s).B + BitVec.ofNat 64 frameBytes) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot, write8]

theorem arg_slot (s : State) (j : Nat) (hj : j < 12) :
    stackArgAddr s j = (lay s).B + BitVec.ofNat 64 (arg j) := by
  simp only [stackArgAddr, lay, arg, frameBytes, stackBytes]
  have : 8 * j < 2 ^ 64 := by omega_using [hj]
  bv_omega

/-- `Ctx` on entry to the inner frame's body. -/
theorem entered_ctx {s : State} (h : chkA.pre s) : Ctx (lay s) s.gpr s.v s.mem (entered s) := by
  have hL := lay_ok h
  have hnB := hL.nB
  refine ⟨?_, ?_, entered_sp s, fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · simp only [entered_rd]; rw [h.2.2.1, ← lay_args]; rfl
  · rw [entered_wr, h.2.2.2.1]; rfl
  · rw [entered_mem]; exact Mem.readW_writeW_self64 _ _ _
  · rw [entered_mem]
    exact Frame.writeW (Frame.refl _ _) (r := (lay s).STK) (by simp) _
      (Offset.contains_base _ (by simp only [frameBytes, stackBytes]; omega_using []) (by decide))

/-- The layout of a call from `s` that may also read `X`. -/
def layW (s : State) (X : List Region) : Lay := { lay s with X := X }

theorem Lay.Ok.withX {L : Lay} (h : L.Ok) (X : List Region) : ({ L with X := X } : Lay).Ok := { h with }

/-- `Ctx` on entry to the inner frame's body, for a call that may also read
`X`: `chkA` holds of the call reading the rest, `R₀`. -/
theorem entered_ctxW {s : State} {R₀ X : List Region} (h : chkA.pre (s.withRegions R₀ s.wr))
    (hX : s.rd = R₀ ++ X) : Ctx (layW s X) s.gpr s.v s.mem (entered s) := by
  have hL := lay_ok h
  have hnB := hL.nB
  refine ⟨?_, ?_, entered_sp s, fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · simp only [entered_rd]
    rw [hX, show R₀ = (s.withRegions R₀ s.wr).rd from rfl, h.2.2.1,
      show stackArgAddr (s.withRegions R₀ s.wr) 0 = (layW s X).B + BitVec.ofNat 64 stackBytes from
        (lay_args s).symm]
    rfl
  · rw [entered_wr, show s.wr = (s.withRegions R₀ s.wr).wr from rfl, h.2.2.2.1]; rfl
  · rw [entered_mem]; exact Mem.readW_writeW_self64 _ _ _
  · rw [entered_mem]
    exact Frame.writeW (Frame.refl _ _) (r := (lay s).STK) (by simp only [List.mem_cons]; right; right; left; rfl) _
      (Offset.contains_base _ (by simp only [frameBytes, stackBytes]; omega_using []) (by decide))

/-- The stack arguments on entry, at their place above the frames. -/
theorem arg_m₀ {s : State} (j : Nat) (hj : j < 12) :
    s.mem.readW ((lay s).B + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [stackArg, arg_slot s j hj]

/-- Our stack argument `j`, by the layout. -/
def Lay.argv (L : Lay) : Nat → BitVec 64
  | 0 => L.p | 1 => L.pl | 2 => L.q | 3 => L.ql | 4 => L.dp | 5 => L.dpl | 6 => L.dq | 7 => L.dql
  | 8 => L.qi | 9 => L.qil | 10 => L.scr | 11 => L.sl | _ => 0

/-- Our stack arguments, in memory `m` above the frames. -/
def ArgsAt (L : Lay) (m : Mem) : Prop :=
  ∀ j < 12, m.readW (L.B + BitVec.ofNat 64 (arg j)) 64 = L.argv j

theorem argsAt_entry (s : State) : ArgsAt (lay s) s.mem := by
  intro j hj
  rw [arg_m₀ j hj]
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ => rfl

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.PrivCall`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: calls from the frames

`call_ok` runs a call of verified code without frames from a state in which
`Ctx` and `Slots` hold, given regions within ours to read and, to write,
regions within `out`, `scratch` or the inner frame above the slots: they
hold again afterwards.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region :=
  [L.N, L.E, L.IN, L.P, L.Q, L.DP, L.DQ, L.QI, L.ARGS, L.FR, L.OUT, L.SC]

/-- The inner frame above the slots: `M` and `n`'s values. -/
abbrev Lay.HI (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 oM, frameBytes - oM⟩

/-- A region a callee may write. -/
def InW (L : Lay) (r : Region) : Prop := Within r L.OUT ∨ Within r L.SC ∨ Within r L.HI

theorem InW.sub {L : Lay} (hL : L.Ok) {r : Region} (h : InW L r) :
    ∃ R ∈ [L.OUT, L.SC, L.STK], Region.Sub r R := by
  have hnB := hL.nB
  rcases h with h | h | h
  · exact ⟨_, by simp, h.sub⟩
  · exact ⟨_, by simp, h.sub⟩
  · refine ⟨L.STK, by simp, fun a ha => ?_⟩
    exact Offset.sub_base L.B (d := oM) (n := frameBytes - oM) (k := stackBytes) (by decide) a (h.sub a ha)

/-- A region a callee may write misses the slots and our return address. -/
theorem InW.disj {L : Lay} (hL : L.Ok) {r : Region} (h : InW L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ r ∧ Region.Disjoint L.LR r := by
  have hnB := hL.nB
  rcases h with h | h | h
  · have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ L.STK :=
      Offset.sub_base _ (by decide)
    have hs' : Region.Sub L.LR L.STK := Offset.sub_base _ (by decide)
    exact ⟨(hL.ko.sub_left hs).sub_right h.sub, (hL.ko.sub_left hs').sub_right h.sub⟩
  · have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ L.STK :=
      Offset.sub_base _ (by decide)
    have hs' : Region.Sub L.LR L.STK := Offset.sub_base _ (by decide)
    exact ⟨(hL.ksc.sub_left hs).sub_right h.sub, (hL.ksc.sub_left hs').sub_right h.sub⟩
  · exact ⟨(Offset.disjoint L.B (d := oOut) (n := 48) (e := oM) (k := frameBytes - oM) (by decide)
        (by simp only [oOut]; omega_using []) (by simp only [oM, frameBytes]; omega_using [])).sub_right h.sub,
      (Offset.disjoint L.B (d := frameBytes) (n := 16) (e := oM) (k := frameBytes - oM) (by decide)
        (by simp only [frameBytes]; omega_using []) (by simp only [oM, frameBytes]; omega_using [])).sub_right h.sub⟩

theorem covers {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InW L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · obtain ⟨off, hb, hl⟩ := h
      refine ⟨L.FR, by simp, oM + off, ?_, ?_⟩
      · rw [hb, add_add]
      · simp only [oM, frameBytes] at hl ⊢; omega_using [hl]

/-- A call of verified code without frames, given regions within ours to
read, and within `out`, `scratch` or the inner frame above the slots to
write: afterwards `Ctx` and `Slots` hold again, memory changed only within
what it writes, and the callee's postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InW L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g vv m₀ s' → Slots L s'.mem → Frame wr t.mem s'.mem →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callV hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs _ hvs hpost => ?_) hn
  have hnB := hL.nB
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    ?_, hc.frame.trans (Frame.sub hf fun r hr => (hwsub r hr).sub hL)⟩
    (hs.frame hf (fun R hR => ((hwsub R hR).disj hL).1) (by omega_using [hnB])) hf hpost
  have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  rw [hf.readW hlr (fun R hR => ((hwsub R hR).disj hL).2) (by decide)]
  exact hc.lr

end VG.Proof.Rsa.AArch64

end

end

/-! ### `Rsa.AArch64.PrivArgs`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: the arguments of the CRT

`saveSlots` keeps our arguments in the slots (`saveSlots_ok`), `copyArgs`
copies our last ten stack arguments to the bottom of the inner frame as the
CRT's (`copyArgs_ok`, one word at a time), and `crtRegs` sets its arguments
in registers (`crtRegs_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The registers a block writes, other than the callee-saved ones. -/
macro "priv_cs_tac" : tactic => `(tactic| plain_simp_names (
                   intro r hr _
                   revert hr
                   simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
                   rintro (h | h | h | h | h | h | h | h | h | h | h) <;> subst h <;>
                     simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]))

/-- Six words stored in the slots. -/
theorem six_ok (B : Addr) (_hB : B.toNat + 128 ≤ 2 ^ 64) (m : Mem) (a b c d e f : BitVec 64) :
    let m' := (((((m.writeW (B + BitVec.ofNat 64 80) a).writeW (B + BitVec.ofNat 64 88) b).writeW
      (B + BitVec.ofNat 64 96) c).writeW (B + BitVec.ofNat 64 104) d).writeW (B + BitVec.ofNat 64 112) e).writeW
      (B + BitVec.ofNat 64 120) f
    Frame [⟨B + BitVec.ofNat 64 80, 48⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 80) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 88) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 96) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 104) 64 = d ∧ m'.readW (B + BitVec.ofNat 64 112) 64 = e ∧
      m'.readW (B + BitVec.ofNat 64 120) 64 = f := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 128 → y + 8 ≤ 128 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega_arith) (by omega_arith)
  have ct : ∀ x, 80 ≤ x → x + 8 ≤ 128 →
      (⟨B + BitVec.ofNat 64 80, 48⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega_arith) (by omega_arith)
  refine ⟨((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 80 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (ct 88 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (ct 96 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (ct 104 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (ct 112 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (ct 120 (by omega_arith) (by omega_arith)), ?_, ?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 80 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 104 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 96 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 80 88 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 88 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 88 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 88 104 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 88 96 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 96 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 96 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 96 104 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 104 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sep 104 112 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 112 120 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- Our arguments in registers. -/
structure Regs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.inp

theorem saveSlots_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hr : Regs L t) :
    WP isa (.block saveSlots) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Regs L t' ∧
      t'.gpr .x15 = L.B ∧ Frame [⟨L.B + BitVec.ofNat 64 80, 48⟩] t.mem t'.mem := by
  have hnB := hL.nB
  have w := fun d (h : d + 8 ≤ frameBytes) => hc.inFrW hL (d := d) (n := 8) h
  have w80 := w 80 (by decide)
  have w88 := w 88 (by decide)
  have w96 := w 96 (by decide)
  have w104 := w 104 (by decide)
  have w112 := w 112 (by decide)
  have w120 := w 120 (by decide)
  apply WP.of_runBlock
  simp only [saveSlots, oOut, oN, oK, oE, oEl, oIn, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false,
    ite_true, hc.sp, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w80, w88, w96,
    w104, w112, w120, write8, Option.some.injEq, exists_eq_left', BitVec.add_zero]
  obtain ⟨f, k80, k88, k96, k104, k112, k120⟩ := six_ok L.B (by omega_arith) t.mem (t.gpr .x0) (t.gpr .x2)
    (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6)
  refine ⟨hc.store hL rfl rfl (hc.sp.symm ▸ rfl) rfl
    (by priv_cs_tac) (Frame.sub f fun r hr => ?_), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, f⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.FR, by simp, Offset.sub_base _ (by decide)⟩
  all_goals try simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
  exacts [k80.trans hr.x0, k88.trans hr.x2, k96.trans hr.x3, k104.trans hr.x4, k112.trans hr.x5,
    k120.trans hr.x6, hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6]

/-- After copying `j` of the CRT's stack arguments, from `t₀`. -/
structure CopyInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t₀ : State) (j : Nat)
    (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  slots : Slots L t.mem
  regs : Regs L t
  x15 : t.gpr .x15 = L.B
  frame : Frame [⟨L.B, 80⟩] t₀.mem t.mem
  args : ∀ i < j, t.mem.readW (L.B + BitVec.ofNat 64 (8 * i)) 64 = m₀.readW (L.B + BitVec.ofNat 64 (arg (i + 2))) 64

theorem copyArg_ok (hL : L.Ok) {t₀ t : State} {j : Nat} (hj : j < 10) (hI : CopyInv L g vv m₀ t₀ j t) :
    WP isa (.block (copyArg j)) t (CopyInv L g vv m₀ t₀ (j + 1)) := by
  have hnB := hL.nB
  have hc := hI.ctx
  have la := hc.inArgs hL (j := j + 2) (by omega_arith)
  have aw := hc.argW hL (j := j + 2) (by omega_arith)
  have w := hc.inFrW hL (d := 8 * j) (n := 8) (by simp only [frameBytes]; omega_arith)
  apply WP.of_runBlock
  simp only [copyArg, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, hI.x15, la, w, read8, aw, write8, Option.some.injEq, exists_eq_left',
    show 8 * j % 8 = 0 by omega_arith, show 8 * j < 4096 * 8 by omega_arith, show arg (j + 2) % 8 = 0 by
      simp only [arg, frameBytes]; omega_arith, show arg (j + 2) < 32768 by simp only [arg, frameBytes]; omega_arith,
    and_self]
  have hfr : Frame [L.FR] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (8 * j))
      (m₀.readW (L.B + BitVec.ofNat 64 (arg (j + 2))) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by simp only [frameBytes]; omega_arith) (by omega_arith))
  have hf80 : Frame [⟨L.B, 80⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (8 * j))
      (m₀.readW (L.B + BitVec.ofNat 64 (arg (j + 2))) 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) hfr, hI.slots.frame hf80 (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      have := Offset.disjoint_base L.B (d := oOut) (n := 48) (k := 80) (by decide) (by simp only [oOut]; omega_arith)
      exact this) (by omega_arith), ?_, ?_, hI.frame.trans hf80, fun i hi => ?_⟩
  · have r := hI.regs
    exact ⟨r.x0, r.x2, r.x3, r.x4, r.x5, r.x6⟩
  · exact hI.x15
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hI.args i hi
    · exact Mem.readW_writeW_self64 _ _ _

theorem copyArgs_upto (hL : L.Ok) {t₀ : State} :
    ∀ n ≤ 10, ∀ t, CopyInv L g vv m₀ t₀ 0 t →
      WP isa (.block ((List.range n).flatMap copyArg)) t (CopyInv L g vv m₀ t₀ n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, t, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyArgs_upto hL n (by omega_arith) t h) fun t' h' => copyArg_ok hL (by omega_arith) h'

/-- The arguments of the CRT in registers, and on the stack at `B`. -/
structure CrtArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.B + BitVec.ofNat 64 oM
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.inp
  x5 : t.gpr .x5 = L.k
  x6 : t.gpr .x6 = L.p
  x7 : t.gpr .x7 = L.pl
  stk : ∀ i < 10, t.mem.readW (L.B + BitVec.ofNat 64 (8 * i)) 64 = L.argv (i + 2)

theorem crtRegs_ok (hL : L.Ok) {t₀ t : State} (ha : ArgsAt L m₀) (hI : CopyInv L g vv m₀ t₀ 10 t) :
    WP isa (.block crtRegs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ CrtArgs L t' ∧
      Frame [⟨L.B, 80⟩] t₀.mem t'.mem := by
  have hc := hI.ctx
  have l0 := hc.inArgs hL (j := 0) (by omega_arith)
  have l1 := hc.inArgs hL (j := 1) (by omega_arith)
  have a0 := (hc.argW hL (j := 0) (by omega_arith)).trans (ha 0 (by omega_arith))
  have a1 := (hc.argW hL (j := 1) (by omega_arith)).trans (ha 1 (by omega_arith))
  apply WP.of_runBlock
  simp only [crtRegs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, l0, l1, read8, a0, a1,
    Option.some.injEq, exists_eq_left', show arg 0 % 8 = 0 by decide, show arg 0 < 32768 by decide,
    show arg 1 % 8 = 0 by decide, show arg 1 < 32768 by decide, show oM < 4096 by decide, and_self,
    show (0 : Nat) < 4096 by decide]
  have r := hI.regs
  refine ⟨hc.regs rfl rfl rfl rfl rfl (by priv_cs_tac), hI.slots, ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    fun i hi => (hI.args i hi).trans (ha _ (by omega_arith))⟩, hI.frame⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq,
    BitVec.add_zero, r.x2, r.x3, r.x6]

end

end VG.Proof.Rsa.AArch64

end

end

/-!
# `vg_rsa_private_checked` on AArch64: the call of the CRT

From `CrtArgs`, the CRT reads `n`, the input, the private key and its stack
arguments at `B`, and writes `M` and `scratch` (`crt_call`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The regions the CRT reads and writes. -/
abbrev crtRd (L : Lay) : List Region :=
  [L.N, ⟨L.inp, L.k.toNat⟩, L.P, L.Q, L.DP, L.DQ, L.QI, ⟨L.B, 80⟩]
abbrev crtWr (L : Lay) : List Region := [L.M, L.SC]

theorem low_sub (L : Lay) {n : Nat} (h : n ≤ stackBytes) : Region.Sub ⟨L.B, n⟩ L.STK := Region.sub_prefix h

namespace Lay.Ok
variable (hL : L.Ok)
include hL

/-- A range of the stack misses every buffer. -/
theorem stk_sub {r : Region} (h : Region.Sub r L.STK) :
    r.Disjoint L.OUT ∧ r.Disjoint L.N ∧ r.Disjoint L.E ∧ r.Disjoint L.IN ∧ r.Disjoint L.P ∧
      r.Disjoint L.Q ∧ r.Disjoint L.DP ∧ r.Disjoint L.DQ ∧ r.Disjoint L.QI ∧ r.Disjoint L.SC :=
  ⟨hL.ko.sub_left h, hL.kn.sub_left h, hL.ke.sub_left h, hL.ki.sub_left h, hL.kp.sub_left h,
    hL.kq.sub_left h, hL.kdp.sub_left h, hL.kdq.sub_left h, hL.kqi.sub_left h, hL.ksc.sub_left h⟩

theorem M_sub : Region.Sub L.M L.STK := Offset.sub_base _ (by have := hL.khi; simp only [oM, stackBytes]; omega_arith)

theorem PRE_sub : Region.Sub L.PRE L.STK := by
  have := hL.khi
  refine Offset.sub_base _ ?_
  simp only [oPre, stackBytes, Lay.pw]; omega_arith

theorem M_HI : Within L.M L.HI := ⟨0, by simp, by have := hL.khi; simp only [oM, frameBytes]; omega_arith⟩

theorem PRE_HI : Within L.PRE L.HI :=
  ⟨oPre - oM, by rw [add_add]; rfl, by have := hL.khi; simp only [oPre, oM, frameBytes, Lay.pw]; omega_arith⟩

theorem IN_k : Within ⟨L.inp, L.k.toNat⟩ L.IN := within_base _ (by rw [hL.ilk])

end Lay.Ok

theorem crtCall_pre (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (ha : CrtArgs L t) :
    crtA.pre (t.callEntry.withRegions (crtRd L) (crtWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  have hM := hL.stk_sub hL.M_sub
  have hA := hL.stk_sub (low_sub L (n := 80) (by decide))
  have hMA : L.M.Disjoint ⟨L.B, 80⟩ :=
    Offset.disjoint_base _ (by decide) (by simp only [oM]; omega_arith)
  simp only [crtA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, sa 0 (by omega_arith), sa 1 (by omega_arith), sa 2 (by omega_arith), sa 3 (by omega_arith), sa 4 (by omega_arith),
    sa 5 (by omega_arith), sa 6 (by omega_arith), sa 7 (by omega_arith), sa 8 (by omega_arith), sa 9 (by omega_arith), Lay.argv,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  have hdp := hL.dpl
  have hqi := hL.qil
  have hdq := hL.dql
  have hIk : (⟨L.inp, L.k.toNat⟩ : Region).Disjoint L.SC := hL.isc.sub_left hL.IN_k.sub
  obtain ⟨-, hMn, -, hMi, hMp, hMq, hMdp, hMdq, hMqi, hMsc⟩ := hM
  have hMk : BitVec.toNat (L.B + BitVec.ofNat 64 oM) + L.k.toNat ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; simp only [oM]; omega_arith
  exact ⟨by omega_arith, trivial, trivial, hMn, hMi.sub_right hL.IN_k.sub, hMp, hMq, hMdp, hMdq, hMqi, hMsc, hMA,
    hL.nsc, hIk, hL.psc, hL.qsc, hL.dpsc, hL.dqsc, hL.qisc, hA.2.2.2.2.2.2.2.2.2.symm, hMk, hL.bn,
    by have := hL.bi; rw [hL.ilk] at this; exact this, hL.bp, hL.bq, hL.bdp, hL.bdq, hL.bqi, hL.bsc,
    ⟨hL.klo, hL.khi⟩, trivial, trivial, hL.pl1, hL.plk, hL.ql1, hL.qlk, hdp, hqi, hdq, hL.slk⟩

theorem crt_sub (hL : L.Ok) : ∀ r ∈ crtRd L ++ crtWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [crtRd, crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.N, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.IN, by simp, hL.IN_k⟩
  · exact ⟨L.P, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.Q, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.DP, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.DQ, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.QI, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_base _ (by decide)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oM, frameBytes]; omega_arith)⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem crt_wsub (hL : L.Ok) : ∀ r ∈ crtWr L, InW L r := by
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inr hL.M_HI)
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What the CRT writes to `M` and returns, from the memory `m` at the call. -/
abbrev CrtOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  Spec.Rsa.written m' (L.B + BitVec.ofNat 64 oM) L.k.toNat (r.setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt m L.n L.k.toNat) (Spec.Rsa.bytesAt m L.inp L.k.toNat)
      (Spec.Rsa.bytesAt m L.p L.pl.toNat) (Spec.Rsa.bytesAt m L.q L.ql.toNat)
      (Spec.Rsa.bytesAt m L.dp L.pl.toNat) (Spec.Rsa.bytesAt m L.dq L.ql.toNat)
      (Spec.Rsa.bytesAt m L.qi L.pl.toNat))

/-- The call of the CRT `C`, for a call state with `C.K`. -/
theorem crt_call (C : CrtCallee) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : CrtArgs L t) (hK : C.K (t.callEntry.withRegions (crtRd L) (crtWr L))) :
    WP isa (.call C.name C.code) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (crtWr L) t.mem t'.mem ∧ CrtOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL C.ok C.noFrames hc hs ⟨crtCall_pre hL hc ha, hK⟩ (crt_sub hL) (crt_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  have h := hpost
  simp only [crtKA, crtA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x2, ha.x3, ha.x4, ha.x6, ha.x7, sa 0 (by omega_arith), sa 1 (by omega_arith), sa 2 (by omega_arith),
    sa 4 (by omega_arith), sa 6 (by omega_arith), Lay.argv] at h
  exact h

end

end VG.Proof.Rsa.AArch64
