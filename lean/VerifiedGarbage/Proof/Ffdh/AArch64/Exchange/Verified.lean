module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-! ### `Ffdh.AArch64.Exchange.CT`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Exchange.Correct`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Exchange.Stages`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Exchange.Contract`, which only this module used -/

section

/-!
# `vg_ffdh_exchange` on AArch64: the contract the proofs use

`exContract` states `Spec.Ffdh.exchangeContract` on the registers and the
stack: `vg_ffdh_exchange(out = x0, out_len = x1, domain = x2,
domain_len = x3, p_len = x4, x = x5, x_len = x6, peer = x7,
peer_len = [sp], scratch = [sp + 8], scratch_len = [sp + 16])`; the shared
contract implies it (`ex_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip written)

def exPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let dom : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let xr : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let peer : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  s.sp.toNat + 24 ≤ 2 ^ 64 ∧ s.rd = [dom, xr, peer, args] ∧ s.wr = [out, scr] ∧
    out.Disjoint dom ∧ out.Disjoint xr ∧ out.Disjoint peer ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    dom.Disjoint scr ∧ xr.Disjoint scr ∧ peer.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x4).toNat ∧ domainLenValid (s.gpr .x4).toNat (s.gpr .x3).toNat ∧
    (s.gpr .x1).toNat = (s.gpr .x4).toNat ∧ (stackArg s 0).toNat = (s.gpr .x4).toNat ∧ 1 ≤ (s.gpr .x6).toNat ∧
    (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 2).toNat

/-- The domain on entry. -/
abbrev exDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

/-- The peer's value on entry. -/
abbrev exY (s : State) : List Byte := bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat

/-- The scalar on entry. -/
abbrev exX (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

def exPost (s s' : State) : Prop :=
  domainValid (s.gpr .x4).toNat (exDom s) → publicValid ⟨domainOf (s.gpr .x4).toNat (exDom s), os2ip (exY s)⟩ →
    written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
      (exchangeOp (domainOf (s.gpr .x4).toNat (exDom s)) (os2ip (exX s)) (os2ip (exY s)))

/-- What timing may depend on, beyond the arguments. -/
def exLeak (s : State) : List Nat :=
  (exDom s).map (·.toNat) ++ (exY s).map (·.toNat) ++
    [if (exchangeOp (domainOf (s.gpr .x4).toNat (exDom s)) (os2ip (exX s)) (os2ip (exY s))).isSome then 1 else 0]

def exPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 3).map (stackArg s₁) = (List.range 3).map (stackArg s₂) ∧ exLeak s₁ = exLeak s₂

def exContract : Contract isa where
  pre := exPre
  post := exPost
  pub := exPub

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def exSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 128 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x3100 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 64 else if a = 0x6009 then 0x80 else if a = 0x6010 then 0x20
    else if a = 0x6011 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x6000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem ex_implies : exContract.Implies (exchangeContract abi) where
  pre := by
    intro s h
    sig_pre [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [exchangeContract, exchangeSig, abi, argRegs, exContract, exPost, stackArgs_three,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [exchangeContract, exchangeSig, abi, argRegs, exContract, exPub, stackArgs_three, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_three, stackArgs_three, a0, a1, a2], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold exLeak; exact hl
  sat := by
    sig_implies_sat [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three,
      List.append_eq, pLenValid, domainLenValid] [exSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using exSat

end VG.Proof.Ffdh.AArch64.Exchange

end

end


/-!
# `vg_ffdh_exchange` on AArch64: the stages of a run

The public data (`ExP`) are the working space, the lengths, the pointers,
the domain and the peer's value; the scalar's octets are secret. A run from
a state with the public data `p` and the scalar `xb` (`CR p xb`) goes
through the shared stages of the data `p.D xb`, then stores z masked by its
flag and returns the flag, without a branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data. -/
structure ExP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  op : Addr
  xp : Addr
  xl : Nat
  yp : Addr
  yb : List Byte
  sp : Addr

/-- The run's data, with the scalar's octets. -/
def ExP.D (p : ExP) (xb : List Byte) : FD :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom,
    [(VG.Impl.Ffdh.AArch64.Domain.sOut, p.op), (sX, p.xp), (sXl, BitVec.ofNat 64 p.xl), (sY, p.yp)],
    [(p.yp, p.yb), (p.xp, xb)]⟩

/-- A state the contract allows, with the public data `p` and the scalar `xb`. -/
def CR (p : ExP) (xb : List Byte) (s : State) : Prop :=
  exPre s ∧ s.sp = p.sp ∧ stackArg s 1 = p.B ∧ (stackArg s 2).toNat * 8 = p.Z ∧ (s.gpr .x4).toNat = p.k ∧
    (s.gpr .x3).toNat = p.dl ∧ s.gpr .x2 = p.dp ∧ exDom s = p.dom ∧ s.gpr .x0 = p.op ∧ s.gpr .x5 = p.xp ∧
    (s.gpr .x6).toNat = p.xl ∧ s.gpr .x7 = p.yp ∧ exY s = p.yb ∧ exX s = xb

/-- `out`, writable and outside the working space. -/
def Dst (p : ExP) (t : State) : Prop :=
  ∀ j < p.k, InRegions t.wr (p.op + BitVec.ofNat 64 j) 1 ∧ p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 j)

theorem Dst.keep {p : ExP} {t u : State} (h : Dst p t) {rs : List Reg} (k : Keep rs t u) : Dst p u :=
  fun j hj => ⟨by rw [k.wr]; exact (h j hj).1, (h j hj).2⟩

/-- What the code uses of the precondition. -/
structure ExCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .x4).toNat
  k2 : (s.gpr .x4).toNat ≤ 1024
  dl : (s.gpr .x3).toNat = 2 * (s.gpr .x4).toNat ∨ (s.gpr .x3).toNat = 3 * (s.gpr .x4).toNat
  ol : (s.gpr .x1).toNat = (s.gpr .x4).toNat
  yl : (stackArg s 0).toNat = (s.gpr .x4).toNat
  xl1 : 1 ≤ (s.gpr .x6).toNat
  xl2 : (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat
  hZ : 128 * (s.gpr .x4).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  ha1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x2) (exDom s)
  y : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x7) (exY s)
  x : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x5) (exX s)
  out : ∀ j < (s.gpr .x4).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  outs : ∀ j < (s.gpr .x4).toNat, (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem exCtx_of {s : State} (h : exPre s) : ExCtx s := by
  obtain ⟨hsp, hrd, hwr, dOd, dOx, dOy, dOs, dOa, dds, dxs, dys, dsa, wO, wD, wX, wY, wS, ⟨hk1, hk2⟩, hdl, hol,
    hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  refine ⟨hk1, hk2, hdl, hol, hyl, hxl1, hxl2, by omega_arith, hs,
    ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 by
        simp only [stackArgAddr, Nat.mul_zero, Nat.mul_one, BitVec.add_zero]]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dys,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dxs,
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega_arith) (by omega_arith)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega_arith) (by omega_arith))⟩

theorem cr_base (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) : Base (p.D xb) s := by
  have c := exCtx_of h.1
  obtain ⟨B, Z, k, dl, dp, dom, op, xp, xl, yp, yb, sp⟩ := p
  obtain ⟨-, -, hB, hZ, hk, hdl, hdp, hdom, -, hxp, hxl, hyp, hyb, hxb⟩ := h
  unfold ExP.D
  subst hB hZ hk hdl hdp hdom hxp hxl hyp hyb hxb
  have hy := c.y
  have hx := c.x
  refine ⟨c.hs, c.k1, c.k2, c.dl, c.hZ, c.dom, bytesAt_length _ _ _, fun e he => ?_, fun q hq => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hy
    · exact hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [argSlots]

theorem cr_dst (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) : Dst p s := by
  have c := exCtx_of h.1
  obtain ⟨-, -, hB, hZ, hk, -, -, -, hop, -⟩ := h
  intro j hj
  rw [← hk] at hj
  rw [← hB, ← hZ, ← hop]
  exact ⟨c.out j hj, c.outs j hj⟩

/-- The entry's first instruction: the working space's base, the second stack
argument, in `x8`. -/
theorem ldrSp_ok {s : State} {B : Addr} (hB : stackArg s 1 = B) (ha1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    WP isa (.block [.ldrSp .x8 8]) s fun t => (t.gpr .x8 = B ∧ t.mem = s.mem) ∧ Keep [.x8] s t := by
  have ha1' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := ha1
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = B := hB
  exact WP.keep [.x8] (by brun [exec_ldrSp_x' _ (show 8 % 8 = 0 ∧ 8 < 32768 by decide) ha1', hB'])
    (by decide) (by decide) (by decide +kernel)

/-- The entry: the arguments into the header at the working space, whose
base goes in `x0`. -/
theorem exEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 23, InRegions s.wr (off B (8 * i)) 8)
    (ha1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    WP isa (.block Exchange.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * VG.Impl.Ffdh.AArch64.Domain.sOut) = s.gpr .x0 ∧ word t.mem B (8 * sDom) = s.gpr .x2 ∧
      word t.mem B (8 * sDomLen) = s.gpr .x3 ∧ word t.mem B (8 * sK) = s.gpr .x4 ∧
      word t.mem B (8 * sX) = s.gpr .x5 ∧ word t.mem B (8 * sXl) = s.gpr .x6 ∧ word t.mem B (8 * sY) = s.gpr .x7 ∧
      Outside B 0 (8 * 23) s.mem t.mem ∧ Keep [.x0, .x8] s t := by
  have ha1' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := ha1
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = B := hB
  refine WP.mono (WP.keep [.x0, .x8] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = ((((((s.mem.writeW (off B (8 * VG.Impl.Ffdh.AArch64.Domain.sOut)) (s.gpr .x0)).writeW
        (off B (8 * sDom)) (s.gpr .x2)).writeW (off B (8 * sDomLen)) (s.gpr .x3)).writeW (off B (8 * sK))
          (s.gpr .x4)).writeW (off B (8 * sX)) (s.gpr .x5)).writeW (off B (8 * sXl)) (s.gpr .x6)).writeW
            (off B (8 * sY)) (s.gpr .x7)) (by
    unfold Exchange.entry
    brun [Crt.stw, exec_ldrSp_x' _ (show 8 % 8 = 0 ∧ 8 < 32768 by decide) ha1', hB',
      hdr_enc (show VG.Impl.Ffdh.AArch64.Domain.sOut < 32 by decide), hdr_enc (show sDom < 32 by decide),
      hdr_enc (show sDomLen < 32 by decide), hdr_enc (show sK < 32 by decide), hdr_enc (show sX < 32 by decide),
      hdr_enc (show sXl < 32 by decide), hdr_enc (show sY < 32 by decide),
      hw VG.Impl.Ffdh.AArch64.Domain.sOut (by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide), hw sX (by decide), hw sXl (by decide), hw sY (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k⟩
  all_goals try (rw [hm]; simp (disch := decide) only [hdrStore_hdr, word_writeW_self]; done)
  rw [hm]
  intro x hx
  have e : ∀ i, i < 23 → ∀ (m : Mem) (v : BitVec 64), (m.writeW (off B (8 * i)) v) x = m x := fun i hi m v =>
    writeW_outside m B v (d := 8 * i) (by omega_arith) x (by omega_arith)
  rw [e sY (by decide), e sXl (by decide), e sX (by decide), e sK (by decide), e sDomLen (by decide),
    e sDom (by decide), e VG.Impl.Ffdh.AArch64.Domain.sOut (by decide)]

@[simp] theorem ExP.D_B (p : ExP) (xb : List Byte) : (p.D xb).B = p.B := rfl
@[simp] theorem ExP.D_Z (p : ExP) (xb : List Byte) : (p.D xb).Z = p.Z := rfl
@[simp] theorem ExP.D_k (p : ExP) (xb : List Byte) : (p.D xb).k = p.k := rfl
@[simp] theorem ExP.D_dl (p : ExP) (xb : List Byte) : (p.D xb).dl = p.dl := rfl
@[simp] theorem ExP.D_dp (p : ExP) (xb : List Byte) : (p.D xb).dp = p.dp := rfl
@[simp] theorem ExP.D_dom (p : ExP) (xb : List Byte) : (p.D xb).dom = p.dom := rfl

theorem cr_e1 (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) :
    WP isa (.block Exchange.entry) s fun t => (E1 (p.D xb) t ∧ Dst p t) ∧ KX s t := by
  have hb := cr_base p xb s h
  have hd := cr_dst p xb s h
  have c := exCtx_of h.1
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hs : Scr s p.B p.Z := hb.scr
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, -, hop, hxp, hxl, hyp, -⟩ := h
  have hw : ∀ i < 23, InRegions s.wr (off p.B (8 * i)) 8 := fun i hi => hs.st (by omega_arith)
  refine WP.mono (exEntry_ok hB hw c.ha1) fun t ⟨h0, hO, hD, hL, hK, hX, hXl, hY, ho, k⟩ => ?_
  refine ⟨⟨⟨hb.keep (InScr.of_outside ho (show 0 + 8 * 23 ≤ p.Z by omega_arith)) k, h0, ?_⟩, hd.keep k⟩, k.mono (by decide)⟩
  intro q hq
  simp only [FD.hdr, ExP.D, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · show word t.mem p.B (8 * sDomLen) = BitVec.ofNat 64 p.dl; rw [hL, ← hdl, ofNat_toNat64]
  · show word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k; rw [hK, ← hk, ofNat_toNat64]
  · exact hO.trans hop
  · exact hX.trans hxp
  · show word t.mem p.B (8 * sXl) = BitVec.ofNat 64 p.xl; rw [hXl, ← hxl, ofNat_toNat64]
  · exact hY.trans hyp

/-! ## The exponentiation and the flag -/

/-- z. -/
abbrev zv (p : ExP) (xb : List Byte) : Nat := Spec.Rsa.os2ip p.yb ^ Spec.Rsa.os2ip xb % (p.D xb).P

/-- z's flag: `1 < z < p − 1`, as the code compares. -/
abbrev fl (p : ExP) (xb : List Byte) : Prop := 1 < zv p xb ∧ 2 * (zv p xb / 2) + 1 < (p.D xb).P

/-- The lengths of the inputs. -/
def Ok (p : ExP) (xb : List Byte) : Prop := xb.length = p.xl ∧ 1 ≤ p.xl ∧ p.xl ≤ p.k ∧ p.yb.length = p.k

theorem cr_ok {p : ExP} {xb : List Byte} {s : State} (h : CR p xb s) : Ok p xb := by
  have c := exCtx_of h.1
  obtain ⟨-, -, -, -, hk, -, -, -, -, -, hxl, -, hyb, hxb⟩ := h
  refine ⟨by rw [← hxb, ← hxl, bytesAt_length], by rw [← hxl]; exact c.xl1, by rw [← hxl, ← hk]; exact c.xl2,
    by rw [← hyb, bytesAt_length, c.yl, hk]⟩

/-- In the inner workspace. -/
def X1 (p : ExP) (xb : List Byte) (t : State) : Prop := (∃ mi, In (p.D xb) mi t) ∧ Dst p t ∧ Ok p xb

/-- After `R² mod p`. -/
def X2 (p : ExP) (xb : List Byte) (t : State) : Prop := (∃ mi, Md (p.D xb) mi t) ∧ Dst p t ∧ Ok p xb

theorem x1_x2 (M : Mont) (p : ExP) (xb : List Byte) (t : State) (h : X1 p xb t) :
    WP isa (seqs (r2Steps M.mm)) t fun u => X2 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, hd, ho⟩ := h
  exact WP.mono (hI.r2 M) fun u ⟨⟨hu, _⟩, k⟩ => ⟨⟨⟨mi, hu⟩, hd.keep k, ho⟩, k⟩

/-- After `y^x mod p`. -/
def X3 (p : ExP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ wv t.mem (off (p.D xb).B (inner (p.D xb).w)) (slot (p.D xb).w aY) (p.D xb).w = zv p xb) ∧
    Dst p t ∧ Ok p xb

theorem x2_x3 (W : Window) (M : Mont) (S : Selector) (p : ExP) (xb : List Byte) (t : State) (h : X2 p xb t) :
    WP isa (seqs (pow W.code S.code M.mm sY sK sX sXl)) t fun u => X3 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM⟩, hd, ho⟩ := h
  obtain ⟨hxl, hx1, hx2, hyl⟩ := id ho
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hy : Src t p.B p.Z p.yp p.yb := hb.srcs (p.yp, p.yb) (by simp [ExP.D])
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [ExP.D])
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [ExP.D])) (by rw [hyl]; exact hs.get (i := sK) (by simp))
    hy (by rw [hyl]; have := hb.k1; simp; omega_arith) (by rw [hyl]; simp)
    (hs.get (i := sX) (v := p.xp) (by simp [ExP.D])) (by rw [hxl]; exact hs.get (i := sXl) (by simp [ExP.D]))
    hx (by omega_arith) (by have := hb.k2; simp at this; omega_arith)) fun u ⟨hu, hY, _, k⟩ =>
      ⟨⟨⟨mi, hu, hY⟩, hd.keep k, ho⟩, k⟩

/-- `pow`'s public data. -/
abbrev ExP.pw (p : ExP) : PowPub := ⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.yp, p.k,
  p.xp, p.xl⟩

theorem x2_ps0 (p : ExP) (xb : List Byte) (t : State) (h : X2 p xb t) : PS0 sY sK sX sXl p.pw t := by
  obtain ⟨⟨mi, hM⟩, hd, ho⟩ := h
  obtain ⟨hxl, hx1, hx2, hyl⟩ := id ho
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hy : Src t p.B p.Z p.yp p.yb := hb.srcs (p.yp, p.yb) (by simp [ExP.D])
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [ExP.D])
  have := hM.ps0 (bp := sY) (bl := sK) (ep := sX) (el := sXl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [ExP.D])) (by rw [hyl]; exact hs.get (i := sK) (by simp))
    hy (by rw [hyl]; have := hb.k1; simp; omega_arith) (by rw [hyl]; simp)
    (hs.get (i := sX) (v := p.xp) (by simp [ExP.D])) (by rw [hxl]; exact hs.get (i := sXl) (by simp [ExP.D]))
    hx (by omega_arith) (by have := hb.k2; simp at this; omega_arith)
  rw [hyl, hxl] at this
  exact this

/-- After z stored masked by its flag (`OutMask.outMask_ok`). -/
abbrev X6 (p : ExP) (xb : List Byte) (t : State) : Prop := OutMask.O6 (p.D xb) p.op (zv p xb) t

theorem x3_x6 (p : ExP) (xb : List Byte) (t : State) (h : X3 p xb t) :
    WP isa (seqs OutMask.outMask) t fun u => X6 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hY⟩, hd, -⟩ := h
  exact OutMask.outMask_ok ⟨⟨mi, hM.inn, hY⟩, List.mem_cons_self .., hd⟩

/-- The flag returned. -/
def X7 (p : ExP) (xb : List Byte) (t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.i2osp (if fl p xb then zv p xb else 0) p.k ∧
    t.gpr .x0 = bit (fl p xb)

theorem ldF_ok {t : State} {G : Addr} {f : BitVec 64} (h0 : t.gpr .x0 = G) (hF : word t.mem G (8 * sF) = f)
    (hl : InRegions (t.rd ++ t.wr) (off G (8 * sF)) 8) :
    WP isa (.block [ldh .x0 sF]) t fun u => (u.gpr .x0 = f ∧ u.mem = t.mem) ∧ Keep [.x0] t u :=
  WP.keep [.x0] (by brun [h0, hdr_enc (show sF < 32 by decide), hl, hF]) (by decide) (by decide) (by decide +kernel)

theorem x6_x7 (p : ExP) (xb : List Byte) (t : State) (h : X6 p xb t) :
    WP isa (.block [ldh .x0 sF]) t fun u => X7 p xb u ∧ KX t u := by
  obtain ⟨hb, h0, hF, hl⟩ := h
  exact WP.mono (ldF_ok h0 hF hl) fun u ⟨⟨h0', hm⟩, k⟩ => ⟨⟨by rw [hm]; exact hb, h0'⟩, k.mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Exchange

end

end


/-!
# `vg_ffdh_exchange` on AArch64: correctness

From `exContract`'s precondition, `Exchange.code` writes the shared value or
zeros and returns its flag (`ex_correct`), by its stages.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- A step that keeps the caller's registers. -/
theorem kstep {s₀ t : State} {c : Prog isa} {P Q : State → Prop} (hk : KX s₀ t)
    (h : WP isa c t fun u => P u ∧ KX t u) (k : ∀ u, P u → KX s₀ u → Q u) : WP isa c t Q :=
  WP.mono h fun u ⟨hp, k'⟩ => k u hp (keep_trans hk k')

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    Exchange.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (r2Steps M.mm ++
      (pow W.code S.code M.mm sY sK sX sXl ++ (OutMask.outMask ++ ([.block [ldh .x0 sF]] : List (Prog isa)))))) :=
  rfl

/-- The public data of a state. -/
def exOf (s : State) : ExP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .x4).toNat, (s.gpr .x3).toNat, s.gpr .x2, exDom s, s.gpr .x0,
    s.gpr .x5, (s.gpr .x6).toNat, s.gpr .x7, exY s, s.sp⟩

theorem cr_of (s : State) (h : exPre s) : CR (exOf s) (exX s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `vg_ffdh_exchange`. -/
theorem ex_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : exContract.pre s) :
    ∃ t s', Exec isa (Exchange.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      exContract.post s s' := by
  suffices hwp : WP isa (Exchange.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ exContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  have hok := cr_ok hCR
  have hpost : ∀ t : State, exContract.post s t ↔ (domainValid (exOf s).k (exOf s).dom →
      publicValid ⟨domainOf (exOf s).k (exOf s).dom, Spec.Rsa.os2ip (exOf s).yb⟩ →
      Spec.Rsa.written t.mem (exOf s).op (exOf s).k ((t.gpr .x0).setWidth 32)
        (exchangeOp (domainOf (exOf s).k (exOf s).dom) (Spec.Rsa.os2ip (exX s)) (Spec.Rsa.os2ip (exOf s).yb))) := by
    intro t
    show exPost s t ↔ _
    unfold exPost
    rw [show (s.gpr .x1).toNat = (exOf s).k from (exCtx_of h).ol]
    exact Iff.rfl
  simp only [hpost]
  generalize exOf s = p at hCR hok
  generalize exX s = xb at hCR hok
  have hb₀ := cr_base p xb s hCR
  unfold Exchange.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p xb s hCR) fun t₁ ⟨⟨e1, hd₁⟩, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D xb).mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · -- p is not a valid modulus.
    refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨_, k⟩ =>
      ⟨abiPreserved_of_keep (keep_trans k₂ (k.mono (by decide))), fun hv => ?_⟩
    have hm : (p.D xb).mv = false := by cases hm' : (p.D xb).mv <;> simp_all
    have := domainValid_mod hv
    exact absurd this (by show ¬ (p.D xb).mv = true; rw [hm]; decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  have hm := ce_valid ce he
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp [r2Steps]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [r2Steps]) (by simp [pow]) (kstep k₃ (x1_x2 M p xb t₃ ⟨h₃, (cr_dst p xb s hCR).keep k₃,
    hok⟩) fun t₄ h₄ k₄ => ?_)
  refine wp_seqs_append (by simp [pow]) (by simp) (kstep k₄ (x2_x3 W M S p xb t₄ h₄) fun t₅ h₅ k₅ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (kstep k₅ (x3_x6 p xb t₅ h₅) fun t₈ h₈ k₈ => ?_)
  rw [seqs_one]
  refine kstep k₈ (x6_x7 p xb t₈ h₈) fun t ⟨hbytes, h0⟩ k => ⟨abiPreserved_of_keep k, fun hv hpv => ?_⟩
  -- The value written.
  have hp1 := (valid_facts hm hb₀.k1)
  have hlo : 256 ^ (p.k - 1) ≤ (p.D xb).P := by
    have := hm
    unfold FD.mv Spec.Rsa.modulusValid at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hhi : (p.D xb).P < 256 ^ p.k := by
    have := os2ip_lt ((p.D xb).dom.take (p.D xb).k)
    rw [hb₀.plen] at this
    exact this
  have hk := octets_bitLength (by have := hb₀.k1; simp at this; omega_using [this]) hlo hhi
  rw [exchangeOp_eq hpv (by have := hp1.2.1; exact Nat.lt_trans (by decide) this) hk, h0]
  have hP : (domainOf p.k p.dom).p = (p.D xb).P := rfl
  have hfl : fl p xb ↔ (1 < zv p xb ∧ zv p xb < (p.D xb).P - 1) :=
    ⟨fun ⟨a, b⟩ => ⟨a, (lt_pm1 hp1.1 _).mp b⟩, fun ⟨a, b⟩ => ⟨a, (lt_pm1 hp1.1 _).mpr b⟩⟩
  rw [hP]
  by_cases hc : 1 < zv p xb ∧ zv p xb < (p.D xb).P - 1
  · rw [ite_eq_left hc]
    exact ⟨by unfold bit; rw [ite_eq_left (hfl.mpr hc)]; rfl, by rw [hbytes, ite_eq_left (hfl.mpr hc)]⟩
  · rw [ite_eq_right hc]
    exact ⟨by unfold bit; rw [ite_eq_right (mt hfl.mp hc)]; rfl,
      by rw [hbytes, ite_eq_right (mt hfl.mp hc), i2osp_zero']⟩

end VG.Proof.Ffdh.AArch64.Exchange

end

end

/-!
# `vg_ffdh_exchange` on AArch64: constant time

Runs with the same public data (`ExP`: all but the scalar's octets) leak the
same (`ex_constantTime`): the exponentiation is RSA's, constant time in the
exponent, and the shared value is stored masked by its flag, without a
branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (ct_post pins_nil)

/-- A stage of some scalar. -/
def Ex (Φ : ExP → List Byte → State → Prop) (p : ExP) (t : State) : Prop := ∃ xb, Φ p xb t

theorem ex_post {Φ Ψ : ExP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → WP isa c s fun u => Ψ p xb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨xb, h⟩ => WP.mono (hw p xb s h) fun _ h => ⟨xb, h.1⟩

/-- The entry's registers but `x8`. -/
def entryRegs (p : ExP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.op else if r = .x2 then p.dp else if r = .x3 then BitVec.ofNat 64 p.dl else
    if r = .x4 then BitVec.ofNat 64 p.k else if r = .x5 then p.xp else if r = .x6 then BitVec.ofNat 64 p.xl else
      if r = .x7 then p.yp else p.B

theorem cr_regs (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) :
    ∀ r ∈ [Reg.x0, .x2, .x3, .x4, .x5, .x6, .x7], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, -, -, hk, hdl, hdp, -, hop, hxp, hxl, hyp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hop
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hxp
  · rw [← hxl, ofNat_toNat64]
  · exact hyp

/-- After the entry's first instruction. -/
def EA (p : ExP) (xb : List Byte) (t : State) : Prop :=
  (∀ r ∈ [Reg.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x8], t.gpr r = entryRegs p r) ∧
    WP isa (.block (Exchange.entry.drop 1)) t fun u => E1 (p.D xb) u ∧ Dst p u

theorem entry_split : Exchange.entry ++ domHead = ([.ldrSp .x8 8] : List Instr) ++ (Exchange.entry.drop 1 ++ domHead) := rfl

theorem cr_ea (p : ExP) (xb : List Byte) (s : State) (h : CR p xb s) :
    WP isa (.block [.ldrSp .x8 8]) s (EA p xb) := by
  have c := exCtx_of h.1
  have hw := cr_e1 p xb s h
  rw [show Exchange.entry = [.ldrSp .x8 8] ++ Exchange.entry.drop 1 from rfl, WP.block_append_iff] at hw
  refine WP.mono (wp_and (ldrSp_ok h.2.2.1 c.ha1) hw) fun t ⟨⟨⟨h8, _⟩, k⟩, hr⟩ => ⟨fun r hr' => ?_,
    WP.mono hr fun u hu => hu.1⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have hc := cr_regs p xb s h
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [k.gpr _ (by decide)]; exact hc _ (by simp)
    · rw [h8]; rfl

/-- After the entry's first instruction, with the inputs' lengths. -/
def EA' (p : ExP) (xb : List Byte) (t : State) : Prop := EA p xb t ∧ Ok p xb

/-- After the entry. -/
def E1' (p : ExP) (xb : List Byte) (t : State) : Prop := E1 (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- After `domHead`. -/
def CE' (p : ExP) (xb : List Byte) (t : State) : Prop := CE (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- The inner workspace's base. -/
abbrev ExP.g (p : ExP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex CE' p s ∧ isa.eval (.zero .x .x9) s = some false)
      (Exchange.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [r2Steps]) (RelCT.seq (R := Two (Ex X1))
    (two_post (two_map (fun p : ExP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨xb, h⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨xb, h⟩, he⟩ => WP.mono (ce_in _ s h.1 he) fun u ⟨hu, k⟩ =>
        ⟨xb, hu, h.2.1.keep k, h.2.2⟩) ?_)
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [pow]) (RelCT.seq (R := Two (Ex X2))
    (ex_post ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨xb₁, ⟨mi₁, hI₁⟩, _⟩ ⟨xb₂, ⟨mi₂, hI₂⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D xb₁).w by omega_using [ew, this]) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h) (x1_x2 M)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp) (RelCT.seq (R := Two (Ex X3))
    (ex_post (two_map ExP.pw (fun p s ⟨xb, h⟩ => x2_ps0 p xb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (x2_x3 W M S)) ?_)
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (Ex X6))
    (ex_post (two_map (fun p : ExP => ((p.D []).pub, p.op)) (fun p _ ⟨xb, ⟨mi, hM, hY⟩, hd, _⟩ =>
      ⟨p.D xb, zv p xb, rfl, ⟨mi, hM.inn, hY⟩, List.mem_cons_self .., hd⟩)
      (OutMask.outMask_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) x3_x6) ?_)
  rw [seqs_one]
  exact two_taint [.x0] (pins_x0B ExP.g fun _ _ ⟨_, h⟩ => h.2.1) (by taint_decide)

/-- `Exchange.code` leaks the same in runs with the same public data. -/
theorem ex_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex CR)) (Exchange.code W.code S.code M.mm) fun _ _ => True := by
  unfold Exchange.code
  rw [entry_split]
  refine RelCT.seq (R := Two (Ex CE')) (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex EA') []
      (pins_nil _) (by taint_decide) fun p s ⟨xb, h⟩ => WP.mono (cr_ea p xb s h) fun _ h' => ⟨xb, h', cr_ok h⟩)
    (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex E1') [.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x8]
      (pins_of entryRegs fun p s ⟨_, h, _⟩ => h.1) (by taint_decide)
      fun p s ⟨xb, h, ho⟩ => WP.mono h.2 fun _ h' => ⟨xb, h'.1, h'.2, ho⟩)
    (ex_post (two_map (fun p : ExP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h, _⟩ => h.dhp) domHead_ct)
      fun p xb s h => WP.mono (e1_ce _ s h.1) fun u ⟨hu, k⟩ => ⟨⟨hu, h.2.1.keep k, h.2.2⟩, k⟩))))) ?_
  exact two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁, ce_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of a state. -/
theorem cr_pub {s₁ s₂ : State} (h₁ : exPre s₁) (h₂ : exPre s₂) (hp : exPub s₁ s₂) : CR (exOf s₁) (exX s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_three, stackArgs_three] at ha
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨a0, a1, a2⟩ := ha
  unfold exLeak at hl
  have c₁ := exCtx_of h₁
  have c₂ := exCtx_of h₂
  simp only [List.append_assoc] at hl
  obtain ⟨hd, hl'⟩ := List.append_inj hl (by simp [exDom, Spec.Rsa.bytesAt, r3])
  obtain ⟨hy, -⟩ := List.append_inj hl' (by simp [exY, Spec.Rsa.bytesAt, a0])
  refine ⟨h₂, hsp.symm, a1.symm, by rw [← a2]; rfl, by rw [← r4]; rfl, by rw [← r3]; rfl, r2.symm, ?_, r0.symm,
    r5.symm, by rw [← r6]; rfl, r7.symm, ?_, rfl⟩
  · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd).symm
  · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy).symm

/-- `vg_ffdh_exchange` is constant time. -/
theorem ex_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa exContract.pre exContract.pub (Exchange.code W.code S.code M.mm) :=
  RelCT.constantTime ((ex_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨exOf s₁, ⟨exX s₁, cr_of s₁ h₁⟩, ⟨exX s₂, cr_pub h₁ h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Exchange

end

end

/-!
# `vg_ffdh_exchange` on AArch64: verified

Correct (`ex_correct`) and constant time (`ex_constantTime`) against
`exContract`, which the shared contract implies (`ex_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem ex_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.Exchange.code W.code S.code M.mm)
      (Spec.Ffdh.exchangeContract abi) :=
  Verified.of_correct (ex_correct W M S) (ex_constantTime W M S) ex_implies

end VG.Proof.Ffdh.AArch64.Exchange
