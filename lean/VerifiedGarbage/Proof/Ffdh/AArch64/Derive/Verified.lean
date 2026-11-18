module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Derive
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMaskCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRangeCT
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
meta import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Derive
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Out
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.Power
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Ffdh.AArch64.Derive.CT`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Derive.Correct`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Derive.Stages`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Derive.Contract`, which only this module used -/

section

/-!
# `vg_ffdh_derive_public` on AArch64: the contract the proofs use

`dvContract` states `Spec.Ffdh.derivePublicContract` on the registers and
the stack: `vg_ffdh_derive_public(y = x0, y_len = x1, domain = x2,
domain_len = x3, p_len = x4, x = x5, x_len = x6, scratch = x7,
scratch_len = [sp])`; the shared contract implies it (`dv_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip i2osp powMod)

def dvPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let dom : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let xr : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 64 ∧ s.rd = [dom, xr, args] ∧ s.wr = [out, scr] ∧
    out.Disjoint dom ∧ out.Disjoint xr ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    dom.Disjoint scr ∧ xr.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x4).toNat ∧ domainLenValid (s.gpr .x4).toNat (s.gpr .x3).toNat ∧
    (s.gpr .x1).toNat = (s.gpr .x4).toNat ∧ 1 ≤ (s.gpr .x6).toNat ∧ (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 0).toNat

/-- The domain on entry. -/
abbrev dvDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

/-- x on entry. -/
abbrev dvX (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

/-- The parameters. -/
abbrev dvA (s : State) : Parameters := domainOf (s.gpr .x4).toNat (dvDom s)

def dvPost (s s' : State) : Prop :=
  domainValid (s.gpr .x4).toNat (dvDom s) →
    ((s'.gpr .x0).setWidth 32).toNat = keyStatus (dvA s) (os2ip (dvX s)) ∧
      if keyStatus (dvA s) (os2ip (dvX s)) = 1 then
        bytesAt s'.mem (s.gpr .x0) (s.gpr .x4).toNat =
          i2osp (powMod (dvA s).g (os2ip (dvX s)) (dvA s).p) (s.gpr .x4).toNat
      else bytesAt s'.mem (s.gpr .x0) (s.gpr .x4).toNat = List.replicate (s.gpr .x4).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def dvLeak (s : State) : List Nat := (dvDom s).map (·.toNat) ++ [keyStatus (dvA s) (os2ip (dvX s))]

def dvPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 1).map (stackArg s₁) = (List.range 1).map (stackArg s₂) ∧ dvLeak s₁ = dvLeak s₂

def dvContract : Contract isa where
  pre := dvPre
  post := dvPost
  pub := dvPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def dvSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 128 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x8000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 0x20 else if a = 0x6001 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x6000, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem dv_implies : dvContract.Implies (derivePublicContract abi) where
  pre := by
    intro s h
    sig_pre [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPost, stackArgs_one,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPub, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_one, stackArgs_one, a0], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold dvLeak; exact hl
  sat := by
    sig_implies_sat [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] [dvSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using dvSat

end VG.Proof.Ffdh.AArch64.Derive

end

end


/-!
# `vg_ffdh_derive_public` on AArch64: the stages of a run

The public data (`DvP`) are the working space, the lengths, the pointers,
the domain, and whether x is in range; x's octets are secret. A run from a
state with the public data `p` and the scalar `xb` (`CR p xb`) goes through
the shared stages of the data `p.D xb`: x's range (`ScalarRange`), then, for
x in range, `y = g^x mod p` and its masked store (`OutMask`); otherwise
zeros to y.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data. -/
structure DvP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  op : Addr
  xp : Addr
  xl : Nat
  /-- Whether x is in range. -/
  pv : Bool
  sp : Addr

/-- The run's data, with x's octets. -/
def DvP.D (p : DvP) (xb : List Byte) : FD :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom,
    [(VG.Impl.Ffdh.AArch64.Domain.sOut, p.op), (sX, p.xp), (sXl, BitVec.ofNat 64 p.xl)], [(p.xp, xb)]⟩

@[simp] theorem DvP.D_B (p : DvP) (xb : List Byte) : (p.D xb).B = p.B := rfl
@[simp] theorem DvP.D_Z (p : DvP) (xb : List Byte) : (p.D xb).Z = p.Z := rfl
@[simp] theorem DvP.D_k (p : DvP) (xb : List Byte) : (p.D xb).k = p.k := rfl
@[simp] theorem DvP.D_dl (p : DvP) (xb : List Byte) : (p.D xb).dl = p.dl := rfl
@[simp] theorem DvP.D_dp (p : DvP) (xb : List Byte) : (p.D xb).dp = p.dp := rfl
@[simp] theorem DvP.D_dom (p : DvP) (xb : List Byte) : (p.D xb).dom = p.dom := rfl

/-- The parameters. -/
abbrev DvP.a (p : DvP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom

abbrev X (xb : List Byte) : Nat := Spec.Rsa.os2ip xb

/-- A state the contract allows, with the public data `p` and x's octets `xb`. -/
def CR (p : DvP) (xb : List Byte) (s : State) : Prop :=
  dvPre s ∧ s.sp = p.sp ∧ s.gpr .x7 = p.B ∧ (stackArg s 0).toNat * 8 = p.Z ∧ (s.gpr .x4).toNat = p.k ∧
    (s.gpr .x3).toNat = p.dl ∧ s.gpr .x2 = p.dp ∧ dvDom s = p.dom ∧ s.gpr .x0 = p.op ∧ s.gpr .x5 = p.xp ∧
    (s.gpr .x6).toNat = p.xl ∧ dvX s = xb ∧ p.pv = Spec.Ffdh.privateValid p.a (X xb)

/-- The lengths of the inputs, and whether x is in range. -/
def Ok (p : DvP) (xb : List Byte) : Prop :=
  xb.length = p.xl ∧ 1 ≤ p.xl ∧ p.xl ≤ p.k ∧ p.pv = Spec.Ffdh.privateValid p.a (X xb)

/-- `y`, writable and outside the working space. -/
abbrev Dst (p : DvP) (t : State) : Prop := OutMask.Dst (p.D []) p.op t

/-- What the code uses of the precondition. -/
structure DvCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .x4).toNat
  k2 : (s.gpr .x4).toNat ≤ 1024
  dl : (s.gpr .x3).toNat = 2 * (s.gpr .x4).toNat ∨ (s.gpr .x3).toNat = 3 * (s.gpr .x4).toNat
  ol : (s.gpr .x1).toNat = (s.gpr .x4).toNat
  xl1 : 1 ≤ (s.gpr .x6).toNat
  xl2 : (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat
  hZ : 128 * (s.gpr .x4).toNat + 256 ≤ (stackArg s 0).toNat * 8
  hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8)
  dom : Src s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x2) (dvDom s)
  x : Src s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x5) (dvX s)
  out : ∀ j < (s.gpr .x4).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  outs : ∀ j < (s.gpr .x4).toNat, (stackArg s 0).toNat * 8 ≤ ofs (s.gpr .x7) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem dvCtx_of {s : State} (h : dvPre s) : DvCtx s := by
  obtain ⟨hsp, hrd, hwr, dOd, dOx, dOs, dOa, dds, dxs, dsa, wO, wD, wX, wS, ⟨hk1, hk2⟩, hdl, hol, hxl1, hxl2,
    hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  exact ⟨hk1, hk2, hdl, hol, hxl1, hxl2, by omega_arith, hs, src_of_region (by rw [hrd]; simp) (by omega_arith) dds,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dxs,
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega_arith) (by omega_arith)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega_arith) (by omega_arith))⟩

theorem cr_base (p : DvP) (xb : List Byte) (s : State) (h : CR p xb s) : Base (p.D xb) s := by
  have c := dvCtx_of h.1
  obtain ⟨B, Z, k, dl, dp, dom, op, xp, xl, pv, sp⟩ := p
  obtain ⟨-, -, hB, hZ, hk, hdl, hdp, hdom, -, hxp, hxl, hxb, -⟩ := h
  unfold DvP.D
  subst hB hZ hk hdl hdp hdom hxp hxl hxb
  have hx := c.x
  refine ⟨c.hs, c.k1, c.k2, c.dl, c.hZ, c.dom, bytesAt_length _ _ _, fun e he => ?_, fun q hq => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he]; exact hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [argSlots]

theorem cr_ok {p : DvP} {xb : List Byte} {s : State} (h : CR p xb s) : Ok p xb := by
  have c := dvCtx_of h.1
  obtain ⟨-, -, -, -, hk, -, -, -, -, -, hxl, hxb, hpv⟩ := h
  exact ⟨by rw [← hxb, ← hxl, bytesAt_length], by rw [← hxl]; exact c.xl1, by rw [← hxl, ← hk]; exact c.xl2, hpv⟩

theorem cr_dst (p : DvP) (xb : List Byte) (s : State) (h : CR p xb s) : Dst p s := by
  have c := dvCtx_of h.1
  obtain ⟨-, -, hB, hZ, hk, -, -, -, hop, -⟩ := h
  intro j hj
  simp only [DvP.D_k] at hj
  rw [← hk] at hj
  show InRegions s.wr (p.op + BitVec.ofNat 64 j) 1 ∧ p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 j)
  rw [← hB, ← hZ, ← hop]
  exact ⟨c.out j hj, c.outs j hj⟩

/-- The entry: the arguments into the header at `scratch`. -/
theorem dvEntry_ok {s : State} {B : Addr} (hB : s.gpr .x7 = B) (hw : ∀ i < 23, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block DerivePublic.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * VG.Impl.Ffdh.AArch64.Domain.sOut) = s.gpr .x0 ∧ word t.mem B (8 * sDom) = s.gpr .x2 ∧
      word t.mem B (8 * sDomLen) = s.gpr .x3 ∧ word t.mem B (8 * sK) = s.gpr .x4 ∧
      word t.mem B (8 * sX) = s.gpr .x5 ∧ word t.mem B (8 * sXl) = s.gpr .x6 ∧
      Outside B 0 (8 * 23) s.mem t.mem ∧ Keep [.x0] s t := by
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((((s.mem.writeW (off B (8 * VG.Impl.Ffdh.AArch64.Domain.sOut)) (s.gpr .x0)).writeW
        (off B (8 * sDom)) (s.gpr .x2)).writeW (off B (8 * sDomLen)) (s.gpr .x3)).writeW (off B (8 * sK))
          (s.gpr .x4)).writeW (off B (8 * sX)) (s.gpr .x5)).writeW (off B (8 * sXl)) (s.gpr .x6)) (by
    unfold DerivePublic.entry
    brun [Crt.stw, hB, hdr_enc (show VG.Impl.Ffdh.AArch64.Domain.sOut < 32 by decide),
      hdr_enc (show sDom < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
      hdr_enc (show sK < 32 by decide), hdr_enc (show sX < 32 by decide), hdr_enc (show sXl < 32 by decide),
      hw VG.Impl.Ffdh.AArch64.Domain.sOut (by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide), hw sX (by decide), hw sXl (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k⟩
  all_goals try (rw [hm]; simp (disch := decide) only [hdrStore_hdr, word_writeW_self]; done)
  rw [hm]
  intro x hx
  have e : ∀ i, i < 23 → ∀ (m : Mem) (v : BitVec 64), (m.writeW (off B (8 * i)) v) x = m x := fun i hi m v =>
    writeW_outside m B v (d := 8 * i) (by omega_arith) x (by omega_arith)
  rw [e sXl (by decide), e sX (by decide), e sK (by decide), e sDomLen (by decide), e sDom (by decide),
    e VG.Impl.Ffdh.AArch64.Domain.sOut (by decide)]

/-- The entry's registers. -/
def entryRegs (p : DvP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.op else if r = .x2 then p.dp else if r = .x3 then BitVec.ofNat 64 p.dl else
    if r = .x4 then BitVec.ofNat 64 p.k else if r = .x5 then p.xp else if r = .x6 then BitVec.ofNat 64 p.xl else p.B

theorem cr_regs (p : DvP) (xb : List Byte) (s : State) (h : CR p xb s) :
    ∀ r ∈ [Reg.x0, .x2, .x3, .x4, .x5, .x6, .x7], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, hB, -, hk, hdl, hdp, -, hop, hxp, hxl, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hop
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hxp
  · rw [← hxl, ofNat_toNat64]
  · exact hB

theorem cr_e1 (p : DvP) (xb : List Byte) (s : State) (h : CR p xb s) :
    WP isa (.block DerivePublic.entry) s fun t => (E1 (p.D xb) t ∧ Dst p t) ∧ KX s t := by
  have hb := cr_base p xb s h
  have hd := cr_dst p xb s h
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hs : Scr s p.B p.Z := hb.scr
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, -, hop, hxp, hxl, -⟩ := h
  have hw : ∀ i < 23, InRegions s.wr (off p.B (8 * i)) 8 := fun i hi => hs.st (by omega_arith)
  refine WP.mono (dvEntry_ok hB hw) fun t ⟨h0, hO, hD, hL, hK, hX, hXl, ho, k⟩ => ?_
  refine ⟨⟨⟨hb.keep (InScr.of_outside ho (show 0 + 8 * 23 ≤ p.Z by omega_arith)) k, h0, ?_⟩,
    OutMask.Dst.keep hd k⟩, k.mono (by decide)⟩
  intro q hq
  simp only [FD.hdr, DvP.D, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · show word t.mem p.B (8 * sDomLen) = BitVec.ofNat 64 p.dl; rw [hL, ← hdl, ofNat_toNat64]
  · show word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k; rw [hK, ← hk, ofNat_toNat64]
  · exact hO.trans hop
  · exact hX.trans hxp
  · show word t.mem p.B (8 * sXl) = BitVec.ofNat 64 p.xl; rw [hXl, ← hxl, ofNat_toNat64]

/-! ## x's range -/

/-- In the inner workspace. -/
def V1 (p : DvP) (xb : List Byte) (t : State) : Prop := (∃ mi, In (p.D xb) mi t) ∧ Dst p t ∧ Ok p xb

/-- With x in `aXm`. -/
def V2 (p : DvP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ wv t.mem (ScalarRange.FD.G (p.D xb)) (slot (p.D xb).w aXm) (p.D xb).w = X xb) ∧
    Dst p t ∧ Ok p xb

theorem v1_lpre (p : DvP) (xb : List Byte) (t : State) (h : V1 p xb t) :
    LPre aXm sX sXl ((p.D xb).ld p.xp p.xl) t := by
  obtain ⟨⟨mi, hI⟩, -, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [DvP.D])
  have := hI.lpre (sp := sX) (sl := sXl) (show aXm < 8 by decide) (by decide) (by decide) (hs.get (i := sX) (v := p.xp) (by simp [DvP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [DvP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; exact ho.2.2.1)
  rw [ho.1] at this
  exact this

theorem v1_v2 (p : DvP) (xb : List Byte) (t : State) (h : V1 p xb t) :
    WP isa (seqs (Crt.loadArr aXm sX sXl)) t fun u => V2 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, hd, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [DvP.D])
  exact WP.mono (hI.load (show aXm < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sX) (v := p.xp) (by simp [DvP.D])) (by rw [ho.1]; exact hs.get (i := sXl) (by simp [DvP.D]))
    hx (by rw [ho.1]; exact ho.2.1) (by rw [ho.1]; exact ho.2.2.1)) fun u ⟨⟨hu, hv, _⟩, k⟩ =>
      ⟨⟨⟨mi, hu, hv⟩, OutMask.Dst.keep hd k, ho⟩, k⟩

/-- After the test of x's range. -/
def V3 (p : DvP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ t.gpr .x9 = bit (p.pv = true)) ∧ Dst p t ∧ Ok p xb

/-- x's range test (`ScalarRange.scalarRange_ok`). -/
theorem v2_v3 (p : DvP) (xb : List Byte) (t : State) (h : V2 p xb t) :
    WP isa (seqs CheckPrivate.scalarRange) t fun u => V3 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hx⟩, hd, ho⟩ := h
  refine WP.mono (ScalarRange.scalarRange_ok ⟨mi, hI, hx⟩) fun u ⟨⟨mi', hu, h9⟩, k⟩ =>
    ⟨⟨⟨mi', hu, ?_⟩, OutMask.Dst.keep hd k, ho⟩, k⟩
  rw [h9, ho.2.2.2]; rfl

theorem v3_eval {p : DvP} {xb : List Byte} {t : State} (h : V3 p xb t) :
    isa.eval (.zero .x .x9) t = some (bit (p.pv = true) == 0) := by
  obtain ⟨⟨_, _, h9⟩, _⟩ := h
  rw [eval_zero, h9]

/-! ## x out of range -/

/-- Back in the outer workspace, for the zeros. -/
def V3o (p : DvP) (t : State) : Prop :=
  Scr t p.B p.Z ∧ t.gpr .x0 = p.B ∧ 128 * p.k + 256 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word t.mem p.B (8 * VG.Impl.Ffdh.AArch64.Domain.sOut) = p.op ∧ word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    Dst p t

theorem v3_o (p : DvP) (xb : List Byte) (t : State) (h : V3 p xb t) :
    WP isa (.block [leave]) t fun u => V3o p u ∧ KX t u := by
  obtain ⟨⟨mi, hI, -⟩, hd, -⟩ := h
  refine WP.mono (leave_ok hI.2.1) fun u ⟨⟨h0, hm⟩, k⟩ => ⟨?_, k.mono (by decide)⟩
  have hP := hI.pa hm k h0
  have hb := hP.1
  have hs := hP.2.2.2.2.1
  exact ⟨hb.scr, h0, hb.hZ, hb.k1, hb.k2,
    hs.get (i := VG.Impl.Ffdh.AArch64.Domain.sOut) (v := p.op) (by simp [DvP.D]),
    hs.get (i := sK) (v := BitVec.ofNat 64 (p.D xb).k) (by simp),
    OutMask.Dst.keep hd k⟩

/-- Zeros to y. -/
def V3z (p : DvP) (t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.op p.k = List.replicate p.k 0 ∧ V3o p t

theorem o_z (p : DvP) (t : State) (h : V3o p t) :
    WP isa (Keys.zeroOut VG.Impl.Ffdh.AArch64.Domain.sOut sK) t fun u => V3z p u ∧ KX t u := by
  obtain ⟨hs, h0, hZ, hk1, hk2, hO, hK, hd⟩ := h
  have hn := hs.nowrap
  have eZ : (p.D []).Z = p.Z := rfl
  refine WP.mono (VG.Proof.Rsa.AArch64.zeroOut_ok hs h0 (by omega_using [hZ]) (by decide) (by decide) hO hK (by omega_using [hk1])
    (by omega_using [hk2]) ⟨fun i hi => (hd i hi).1, fun i hi => (hd i hi).2⟩) fun u ⟨hb, hfr, k⟩ => ?_
  have hout := outside_of_frame (fun j hj => (hd j hj).2) hfr
  have e : ∀ i < 32, word u.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hout.word (Or.inl (by omega_using [hZ, eZ, hi])) (by omega_using [hi])
  refine ⟨⟨?_, hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, hZ, hk1, hk2, by rw [e _ (by decide)]; exact hO,
    by rw [e _ (by decide)]; exact hK, OutMask.Dst.keep hd k⟩, k.mono (by decide)⟩
  exact bytesAt_of (by simp) fun i hi => by
    rw [hb i hi]; simp [List.getD_eq_getElem?_getD, hi]

/-! ## x in range -/

/-- In the inner workspace, x in range. -/
def T0 (p : DvP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t) ∧ Dst p t ∧ Ok p xb ∧ p.pv = true

theorem v3_t0 {p : DvP} {xb : List Byte} {t : State} (h : V3 p xb t)
    (he : isa.eval (.zero .x .x9) t = some false) : T0 p xb t := by
  have hpv : p.pv = true := by
    rw [v3_eval h] at he
    by_contra hc
    simp [bit, hc] at he
  obtain ⟨⟨mi, hI, -⟩, hd, ho⟩ := h
  exact ⟨⟨mi, hI⟩, hd, ho, hpv⟩

/-- After `R² mod p`. -/
def T1 (p : DvP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t) ∧ Dst p t ∧ Ok p xb ∧ p.pv = true

theorem t0_t1 (M : Mont) (p : DvP) (xb : List Byte) (t : State) (h : T0 p xb t) :
    WP isa (seqs (r2Steps M.mm)) t fun u => T1 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, hd, ho, hpv⟩ := h
  exact WP.mono (hI.r2 M) fun u ⟨⟨hu, _⟩, k⟩ => ⟨⟨⟨mi, hu⟩, OutMask.Dst.keep hd k, ho, hpv⟩, k⟩

/-- y. -/
abbrev yv (p : DvP) (xb : List Byte) : Nat := (p.D xb).G ^ X xb % (p.D xb).P

/-- `g^x mod p` in `aY`. -/
def T2 (p : DvP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ wv t.mem (ScalarRange.FD.G (p.D xb)) (slot (p.D xb).w aY) (p.D xb).w = yv p xb) ∧
    Dst p t ∧ Ok p xb ∧ p.pv = true

/-- `g^x`'s public data. -/
abbrev DvP.pwG (p : DvP) : PowPub :=
  ⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.dp + BitVec.ofNat 64 p.k, p.k, p.xp, p.xl⟩

theorem t1_pre (p : DvP) (xb : List Byte) (t : State) (h : T1 p xb t) : PS0 sG sK sX sXl p.pwG t := by
  obtain ⟨⟨mi, hM⟩, -, ho, -⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [DvP.D])
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have := hM.ps0 (bp := sG) (bl := sK) (ep := sX) (el := sXl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D xb).dp + BitVec.ofNat 64 (p.D xb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega_arith)
    (by rw [hb.glen]) (hs.get (i := sX) (v := p.xp) (by simp [DvP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [DvP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; have := ho.2.2.1; omega_arith)
  rw [hb.glen, ho.1] at this
  exact this

theorem t1_t2 (W : Window) (M : Mont) (S : Selector) (p : DvP) (xb : List Byte) (t : State) (h : T1 p xb t) :
    WP isa (seqs (pow W.code S.code M.mm sG sK sX sXl)) t fun u => T2 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM⟩, hd, ho, hpv⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [DvP.D])
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D xb).dp + BitVec.ofNat 64 (p.D xb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega_arith)
    (by rw [hb.glen]) (hs.get (i := sX) (v := p.xp) (by simp [DvP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [DvP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; have := ho.2.2.1; omega_arith)) fun u ⟨hu, hY, _, k⟩ =>
      ⟨⟨⟨mi, hu, hY⟩, OutMask.Dst.keep hd k, ho, hpv⟩, k⟩

/-- After y stored masked by its flag (`OutMask.outMask_ok`). -/
def T3 (p : DvP) (xb : List Byte) (t : State) : Prop :=
  OutMask.O6 (p.D xb) p.op (yv p xb) t ∧ Ok p xb ∧ p.pv = true

theorem t2_o3 {p : DvP} {xb : List Byte} {t : State} (h : T2 p xb t) : OutMask.O3 (p.D xb) p.op (yv p xb) t := by
  obtain ⟨⟨mi, hM, hY⟩, hd, -⟩ := h
  exact ⟨⟨mi, hM.inn, hY⟩, List.mem_cons_self .., hd⟩

theorem t2_t3 (p : DvP) (xb : List Byte) (t : State) (h : T2 p xb t) :
    WP isa (seqs OutMask.outMask) t fun u => T3 p xb u ∧ KX t u :=
  WP.mono (OutMask.outMask_ok (t2_o3 h)) fun _ ⟨hu, k⟩ => ⟨⟨hu, h.2.2⟩, k⟩

end VG.Proof.Ffdh.AArch64.Derive

end

end


/-!
# `vg_ffdh_derive_public` on AArch64: correctness

From `dvContract`'s precondition, `DerivePublic.code` returns `keyStatus`
of the imported x and writes y, or zeros (`dv_correct`), by its stages: a
power of the checked generator is in its subgroup (`publicValid_power`), so
y's range is its validity.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

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

/-- The final block. -/
abbrev statusBlk : List Instr := [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]

theorem tail_eq (W : Window) (M : Mont) (S : Selector) :
    DerivePublic.tail W.code S.code M.mm = r2Steps M.mm ++ (pow W.code S.code M.mm sG sK sX sXl ++
      (OutMask.outMask ++ ([.block statusBlk] : List (Prog isa)))) := by
  simp only [DerivePublic.tail, List.append_assoc]
  rfl

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    DerivePublic.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++
      (Crt.loadArr aXm sX sXl ++ (CheckPrivate.scalarRange ++
        ([.ite (.zero .x .x9) DerivePublic.fail (seqs (DerivePublic.tail W.code S.code M.mm))] :
          List (Prog isa))))) := by
  simp only [DerivePublic.main, List.append_assoc]

/-- The public data of a state. -/
def dvOf (s : State) : DvP :=
  ⟨s.gpr .x7, (stackArg s 0).toNat * 8, (s.gpr .x4).toNat, (s.gpr .x3).toNat, s.gpr .x2, dvDom s, s.gpr .x0,
    s.gpr .x5, (s.gpr .x6).toNat, privateValid (dvA s) (Spec.Rsa.os2ip (dvX s)), s.sp⟩

theorem cr_of (s : State) (h : dvPre s) : CR (dvOf s) (dvX s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The postcondition, from the results. -/
theorem dv_post {p : DvP} {xb : List Byte} {s₀ u : State} (hc : CR p xb s₀) (hk : KX s₀ u) {r : Nat}
    (hr : r < 2 ^ 32) (h0 : u.gpr .x0 = BitVec.ofNat 64 r)
    (hv : domainValid p.k p.dom = true → r = keyStatus p.a (X xb) ∧
      if keyStatus p.a (X xb) = 1 then
        Spec.Rsa.bytesAt u.mem p.op p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g (X xb) p.a.p) p.k
      else Spec.Rsa.bytesAt u.mem p.op p.k = List.replicate p.k 0) :
    abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  obtain ⟨-, -, -, -, hk', -, -, hdom, hop, -, -, hxb, -⟩ := hc
  refine ⟨abiPreserved_of_keep hk, fun hd => ?_⟩
  show ((u.gpr .x0).setWidth 32).toNat = keyStatus (dvA s₀) (Spec.Rsa.os2ip (dvX s₀)) ∧ _
  have ha : dvA s₀ = p.a := by simp only [dvA, DvP.a, hk', hdom]
  rw [ha, hxb, hop, hk']
  rw [hk', hdom] at hd
  obtain ⟨hr', hb⟩ := hv hd
  exact ⟨by rw [h0, setWidth32_ofNat hr, hr'], hb⟩

/-- The postcondition after an invalid p. -/
theorem dv_post0 {p : DvP} {xb : List Byte} {s₀ u : State} (hc : CR p xb s₀) (hk : KX s₀ u)
    (hm : (p.D xb).mv = false) : abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  obtain ⟨-, -, -, -, hk', -, -, hdom, -⟩ := hc
  refine ⟨abiPreserved_of_keep hk, fun hd => ?_⟩
  rw [hk', hdom] at hd
  have := domainValid_mod hd
  exact absurd this (by show ¬ (p.D xb).mv = true; rw [hm]; decide)

/-- x out of range: zeros to y, and 2 returned. -/
theorem fail_ok {p : DvP} {xb : List Byte} {s₀ t : State} (hc : CR p xb s₀) (hk : KX s₀ t) (h : V3 p xb t)
    (hpv : p.pv = false) :
    WP isa DerivePublic.fail t fun u => abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  have ho := h.2.2
  unfold DerivePublic.fail
  simp only [seqs]
  refine WP.seq (kstep hk (v3_o p xb t h) fun t₁ h₁ k₁ => ?_)
  refine WP.seq (kstep k₁ (o_z p t₁ h₁) fun t₂ h₂ k₂ => ?_)
  refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨⟨h0, hm⟩, k⟩ =>
    dv_post hc (keep_trans k₂ (k.mono (by decide))) (r := 2) (by decide) h0 fun hdv => ?_
  have hpar : parametersValid p.a = true := by
    unfold domainValid at hdv; simp only [Bool.and_eq_true] at hdv; exact hdv.1
  have hpv' : privateValid p.a (X xb) = false := by rw [← ho.2.2.2]; exact hpv
  rw [KeyScalar.keyStatus_eq hpar, ite_eq_left hpv', hm]
  exact ⟨rfl, h₂.1⟩

/-- x in range: y and its status. -/
theorem tail_ok (W : Window) (M : Mont) (S : Selector) {p : DvP} {xb : List Byte} {s₀ t : State}
    (hc : CR p xb s₀) (hk : KX s₀ t) (h : T0 p xb t) :
    WP isa (seqs (DerivePublic.tail W.code S.code M.mm)) t fun u => abiPreserved s₀ u ∧ dvContract.post s₀ u := by
  have hb₁ := h.1.choose_spec.1
  have hm₁ := h.1.choose_spec.2.2.2.2.2
  rw [tail_eq]
  refine wp_seqs_append (by simp [r2Steps]) (by simp) (kstep hk (t0_t1 M p xb t h) fun t₁ h₁ k₁ => ?_)
  refine wp_seqs_append (by simp [pow]) (by simp) (kstep k₁ (t1_t2 W M S p xb t₁ h₁) fun t₂ h₂ k₂ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (kstep k₂ (t2_t3 p xb t₂ h₂) fun t₃ h₃ k₃ => ?_)
  rw [seqs_one]
  obtain ⟨⟨hy, h0, hF, hl⟩, ho, hpv⟩ := h₃
  refine WP.mono (fBlk_ok h0 hF hl) fun u ⟨⟨h0', hmu⟩, k⟩ =>
    dv_post hc (keep_trans k₃ (k.mono (by decide))) (r := if OutMask.fl (p.D xb) (yv p xb) then 1 else 3)
      (by split <;> decide) (by rw [h0', fin_status]) fun hdv => ?_
  have hpar : parametersValid p.a = true := by
    unfold domainValid at hdv; simp only [Bool.and_eq_true] at hdv; exact hdv.1
  have hpv' : privateValid p.a (X xb) = true := by rw [← ho.2.2.2]; exact hpv
  have hodd := (valid_facts hm₁ hb₁.k1).1
  have hpw := publicValid_power hpar (X xb)
  have ey : p.a.g ^ X xb % p.a.p = yv p xb := rfl
  rw [ey] at hpw
  have hfl : OutMask.fl (p.D xb) (yv p xb) ↔ publicValid ⟨p.a, yv p xb⟩ = true :=
    ⟨fun ⟨a, b⟩ => hpw.mpr ⟨a, (lt_pm1 hodd _).mp b⟩, fun e => ⟨(hpw.mp e).1, (lt_pm1 hodd _).mpr (hpw.mp e).2⟩⟩
  rw [KeyScalar.keyStatus_eq hpar, ite_eq_right (show ¬ privateValid p.a (X xb) = false by rw [hpv']; decide), ey, hmu,
    powMod_eq, ey]
  by_cases hf : OutMask.fl (p.D xb) (yv p xb)
  · rw [ite_eq_left hf] at hy
    rw [ite_eq_left hf, ite_eq_left (hfl.mp hf), ite_eq_left rfl]
    exact ⟨rfl, hy⟩
  · rw [ite_eq_right hf, i2osp_zero'] at hy
    rw [ite_eq_right hf, ite_eq_right (fun e => hf (hfl.mpr e)), ite_eq_right (by decide)]
    exact ⟨rfl, hy⟩

/-- `vg_ffdh_derive_public`. -/
theorem dv_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : dvContract.pre s) :
    ∃ t s', Exec isa (DerivePublic.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      dvContract.post s s' := by
  suffices hwp : WP isa (DerivePublic.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ dvContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  generalize dvOf s = p at hCR
  generalize dvX s = xb at hCR
  have hok := cr_ok hCR
  unfold DerivePublic.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p xb s hCR) fun t₁ ⟨⟨e1, _⟩, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D xb).mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨_, k⟩ => dv_post0 hCR (keep_trans k₂ (k.mono (by decide))) ?_
    cases hm : (p.D xb).mv
    · rfl
    · rw [hm] at hb; exact absurd hb (by decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange])
    (kstep k₃ (v1_v2 p xb t₃ ⟨h₃, OutMask.Dst.keep (cr_dst p xb s hCR) k₃, hok⟩) fun t₄ h₄ k₄ => ?_)
  refine wp_seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (kstep k₄ (v2_v3 p xb t₄ h₄)
    fun t₅ h₅ k₅ => ?_)
  rw [seqs_one]
  refine WP.ite (bit (p.pv = true) == 0) (v3_eval h₅) (fun hb => ?_) (fun hb => ?_)
  · have hpv : p.pv = false := by
      cases hp : p.pv
      · rfl
      · simp [bit, hp] at hb
    exact fail_ok hCR k₅ h₅ hpv
  exact tail_ok W M S hCR k₅ (v3_t0 h₅ (by rw [v3_eval h₅, hb]))

end VG.Proof.Ffdh.AArch64.Derive

end

end

/-!
# `vg_ffdh_derive_public` on AArch64: constant time

Runs with the same public data (`DvP`: all but x's octets, and whether x is
in range) leak the same (`dv_constantTime`): x's range checks run over all
the words (`ScalarRange.scalarRange_ct`), the exponentiation is RSA's,
constant time in the exponent, y is stored masked by its range, without a
branch (`OutMask.outMask_ct`), and the only branch on x is on its range,
which the status gives.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)
open VG.Spec.Ffdh

/-- A stage of some scalar. -/
def Ex (Φ : DvP → List Byte → State → Prop) (p : DvP) (t : State) : Prop := ∃ xb, Φ p xb t

theorem ex_post {Φ Ψ : DvP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → WP isa c s fun u => Ψ p xb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨xb, h⟩ => WP.mono (hw p xb s h) fun _ h => ⟨xb, h.1⟩

theorem ex_post' {Φ Ψ : DvP → List Byte → State → Prop} {c : Prog isa} {P : DvP → State → Prop}
    (hct : RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → P p s → WP isa c s fun u => Ψ p xb u ∧ KX s u) :
    RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨⟨xb, h⟩, hp⟩ => WP.mono (hw p xb s h hp) fun _ h => ⟨xb, h.1⟩

/-- After the entry. -/
def E1' (p : DvP) (xb : List Byte) (t : State) : Prop := E1 (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- After `domHead`. -/
def CE' (p : DvP) (xb : List Byte) (t : State) : Prop := CE (p.D xb) t ∧ Dst p t ∧ Ok p xb

/-- The public part of the run's data. -/
abbrev DvP.pub (p : DvP) : FD := (p.D []).pub

/-- The inner workspace's base. -/
abbrev DvP.g (p : DvP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-- `zeroOut sOut sK`, to y. -/
theorem zo_ct : RelCT isa (Two V3o) (Keys.zeroOut VG.Impl.Ffdh.AArch64.Domain.sOut sK) (Two V3o) := by
  have post : ∀ p t, V3o p t → WP isa (Keys.zeroOut VG.Impl.Ffdh.AArch64.Domain.sOut sK) t (V3o p) :=
    fun p t h => WP.mono (o_z p t h) fun _ h => h.1.2
  unfold Keys.zeroOut
  refine RelCT.seq (R := Two fun p t => (t.gpr .x1 = p.op ∧ t.gpr .x2 = BitVec.ofNat 64 p.k) ∧
      WP isa (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1]) t (V3o p))
    (two_piece [.x0] (pins_x0B DvP.B fun _ _ h => h.2.1) (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨hs, h0, hZ, -, -, hO, hK, -⟩ := id h
    have hn := hs.nowrap
    have hw := post p t h
    unfold Keys.zeroOut at hw
    exact wp_and (zoBlk_ok h0 (by decide) hO hK fun i hi => hs.ld (by omega_using [hZ, hi])) (WP.seq_iff.mp hw)
  · exact two_post (two_taint [.x1, .x2] (pins_of (fun (p : DvP) r => if r = .x1 then p.op else
      BitVec.ofNat 64 p.k) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) (by taint_decide)) fun p t h => h.2

/-- x out of range: zeros to y, and 2 returned. -/
theorem fail_ct :
    RelCT isa (Two fun p s => Ex V3 p s ∧ isa.eval (.zero .x .x9) s = some true) DerivePublic.fail
      fun _ _ => True := by
  unfold DerivePublic.fail
  simp only [seqs]
  refine RelCT.seq (R := Two V3o) (two_piece [.x0] (pins_x0B DvP.g fun (p : DvP) s (h : Ex V3 p s ∧ _) => by
      obtain ⟨⟨_, ⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)
    fun p s ⟨⟨xb, h⟩, _⟩ => WP.mono (v3_o p xb s h) fun _ h => h.1) ?_
  exact RelCT.seq zo_ct (two_taint [] (pins_nil _) (by taint_decide))

/-- x in range: y, masked by its range, and the status. -/
theorem tail_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex V3 p s ∧ isa.eval (.zero .x .x9) s = some false)
      (seqs (DerivePublic.tail W.code S.code M.mm)) fun _ _ => True := by
  rw [tail_eq]
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two (Ex T1))
    (ex_post' ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨⟨xb₁, ⟨mi₁, hI₁, _⟩, _⟩, _⟩
        ⟨⟨xb₂, ⟨mi₂, hI₂, _⟩, _⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D xb₁).w by omega_using [ew, this]) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h)
      fun p xb s h he => t0_t1 M p xb s (v3_t0 h he)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp) (RelCT.seq (R := Two (Ex T2))
    (ex_post (two_map DvP.pwG (fun p s ⟨xb, h⟩ => t1_pre p xb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (t1_t2 W M S)) ?_)
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (Ex T3))
    (ex_post (two_map (fun p : DvP => (p.pub, p.op)) (fun p _ ⟨xb, h⟩ => ⟨p.D xb, yv p xb, rfl, t2_o3 h⟩)
      (OutMask.outMask_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) t2_t3) ?_)
  rw [seqs_one]
  exact two_taint [.x0] (pins_x0B DvP.g fun _ _ ⟨_, h⟩ => h.1.2.1) (by taint_decide)

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex CE' p s ∧ isa.eval (.zero .x .x9) s = some false)
      (DerivePublic.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex V1))
    (two_post (two_map (fun p : DvP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨xb, h⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨xb, h⟩, he⟩ => WP.mono (ce_in _ s h.1 he) fun u ⟨hu, k⟩ =>
        ⟨xb, hu, OutMask.Dst.keep h.2.1 k, h.2.2⟩) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (RelCT.seq
    (R := Two (Ex V2)) (ex_post (two_map (fun p : DvP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8,
      (p.k + 7) / 8⟩, p.xp, p.xl⟩ : BPub)) (fun p s ⟨xb, h⟩ => v1_lpre p xb s h)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) v1_v2) ?_)
  refine RelCT.seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (RelCT.seq (R := Two (Ex V3))
    (ex_post (two_map DvP.pub (fun p _ ⟨xb, ⟨mi, hI, hx⟩, _⟩ => ⟨p.D xb, X xb, rfl, mi, hI, hx⟩)
      (ScalarRange.scalarRange_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) v2_v3) ?_)
  rw [seqs_one]
  exact two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [v3_eval h₁, v3_eval h₂]) fail_ct (tail_ct W M S)

/-- `DerivePublic.code` leaks the same in runs with the same public data. -/
theorem dv_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex CR)) (DerivePublic.code W.code S.code M.mm) fun _ _ => True := by
  unfold DerivePublic.code
  refine RelCT.seq (R := Two (Ex CE')) (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex E1')
      [.x0, .x2, .x3, .x4, .x5, .x6, .x7] (pins_of entryRegs fun p s ⟨xb, h⟩ => cr_regs p xb s h) (by taint_decide)
      fun p s ⟨xb, h⟩ => WP.mono (cr_e1 p xb s h) fun _ h' => ⟨xb, h'.1.1, h'.1.2, cr_ok h⟩)
    (ex_post (two_map (fun p : DvP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h, _⟩ => h.dhp) domHead_ct)
      fun p xb s h => WP.mono (e1_ce _ s h.1) fun u ⟨hu, k⟩ => ⟨⟨hu, OutMask.Dst.keep h.2.1 k, h.2.2⟩, k⟩))) ?_
  exact two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁, ce_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of the second run. -/
theorem cr_pub {s₁ s₂ : State} (h₂ : dvPre s₂) (hp : dvPub s₁ s₂) : CR (dvOf s₁) (dvX s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_one, stackArgs_one] at ha
  simp only [List.cons.injEq, and_true] at ha
  unfold dvLeak at hl
  obtain ⟨hd, hs⟩ := List.append_inj hl (by simp [dvDom, Spec.Rsa.bytesAt, r3])
  have hd' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, hsp.symm, r7.symm, by rw [← ha]; rfl, by rw [← r4]; rfl, by rw [← r3]; rfl, r2.symm, hd'.symm,
    r0.symm, r5.symm, by rw [← r6]; rfl, rfl, ?_⟩
  -- Whether x is in range, from the statuses.
  show privateValid (domainOf (s₁.gpr .x4).toNat (dvDom s₁)) (Spec.Rsa.os2ip (dvX s₁)) =
    privateValid (domainOf (s₁.gpr .x4).toNat (dvDom s₁)) (Spec.Rsa.os2ip (dvX s₂))
  simp only [dvA] at hs
  rw [r4, hd'] at hs ⊢
  unfold keyStatus at hs
  generalize privateValid _ (Spec.Rsa.os2ip (dvX s₁)) = b₁ at hs ⊢
  generalize privateValid _ (Spec.Rsa.os2ip (dvX s₂)) = b₂ at hs ⊢
  cases b₁ <;> cases b₂ <;> simp at hs ⊢ <;> split at hs <;> simp at hs

/-- `vg_ffdh_derive_public` is constant time. -/
theorem dv_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa dvContract.pre dvContract.pub (DerivePublic.code W.code S.code M.mm) :=
  RelCT.constantTime ((dv_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨dvOf s₁, ⟨dvX s₁, cr_of s₁ h₁⟩, ⟨dvX s₂, cr_pub h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Derive

end

end

/-!
# `vg_ffdh_derive_public` on AArch64: verified

Correct (`dv_correct`) and constant time (`dv_constantTime`) against
`dvContract`, which the shared contract implies (`dv_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem dv_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.DerivePublic.code W.code S.code M.mm)
      (Spec.Ffdh.derivePublicContract abi) :=
  Verified.of_correct (dv_correct W M S) (dv_constantTime W M S) dv_implies

end VG.Proof.Ffdh.AArch64.Derive
