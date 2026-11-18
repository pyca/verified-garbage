module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRangeCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.Power
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-! ### `Ffdh.AArch64.CheckPrivate.CT`, which only this module used -/

section

/-! ### `Ffdh.AArch64.CheckPrivate.Correct`, which only this module used -/

section

/-! ### `Ffdh.AArch64.CheckPrivate.Stages`, which only this module used -/

section

/-! ### `Ffdh.AArch64.CheckPrivate.Contract`, which only this module used -/

section

/-!
# `vg_ffdh_check_private` on AArch64: the contract the proofs use

`kpContract` states `Spec.Ffdh.checkPrivateContract` on the registers and
the stack: `vg_ffdh_check_private(domain = x0, domain_len = x1, p_len = x2,
y = x3, y_len = x4, x = x5, x_len = x6, scratch = x7,
scratch_len = [sp])`; the shared contract implies it (`kp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def kpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let y : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let x : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 64 ∧ s.rd = [dom, y, x, args] ∧ s.wr = [scr] ∧
    dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x2).toNat ∧ domainLenValid (s.gpr .x2).toNat (s.gpr .x1).toNat ∧
    (s.gpr .x4).toNat = (s.gpr .x2).toNat ∧ 1 ≤ (s.gpr .x6).toNat ∧ (s.gpr .x6).toNat ≤ (s.gpr .x2).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x2).toNat ≤ (stackArg s 0).toNat

/-- The domain on entry. -/
abbrev kpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat

/-- y on entry. -/
abbrev kpY (s : State) : List Byte := bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat

/-- x on entry. -/
abbrev kpX (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

def kpPost (s s' : State) : Prop :=
  domainValid (s.gpr .x2).toNat (kpDom s) →
    ((s'.gpr .x0).setWidth 32).toNat = privateStatus (domainOf (s.gpr .x2).toNat (kpDom s)) (os2ip (kpY s))
      (os2ip (kpX s))

/-- What timing may depend on, beyond the arguments. -/
def kpLeak (s : State) : List Nat :=
  (kpDom s).map (·.toNat) ++ (kpY s).map (·.toNat) ++
    [privateStatus (domainOf (s.gpr .x2).toNat (kpDom s)) (os2ip (kpY s)) (os2ip (kpX s))]

def kpPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 1).map (stackArg s₁) = (List.range 1).map (stackArg s₂) ∧ kpLeak s₁ = kpLeak s₂

def kpContract : Contract isa where
  pre := kpPre
  post := kpPost
  pub := kpPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def kpSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 64 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x8000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 0x20 else if a = 0x6001 then 0x04 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x6000, 8⟩]
  wr := [⟨0x8000, 1056 * 8⟩]

theorem kp_implies : kpContract.Implies (checkPrivateContract abi) where
  pre := by
    intro s h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPost, stackArgs_one,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPub, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_one, stackArgs_one, a0], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold kpLeak; exact hl
  sat := by
    sig_implies_sat [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] [kpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSat

end VG.Proof.Ffdh.AArch64.CheckPrivate

end

end


/-!
# `vg_ffdh_check_private` on AArch64: the stages of a run

The public data (`KpP`) are the working space, the lengths, the pointers,
the domain, y, and whether x is in range; x's octets are secret. A run from
a state with the public data `p` and the scalar `xb` (`CR p xb`) goes
through the shared stages of the data `p.D xb`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data. -/
structure KpP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  yp : Addr
  yb : List Byte
  xp : Addr
  xl : Nat
  /-- Whether x is in range. -/
  pv : Bool
  sp : Addr

/-- The run's data, with x's octets. -/
def KpP.D (p : KpP) (xb : List Byte) : FD :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, [(sY, p.yp), (sX, p.xp), (sXl, BitVec.ofNat 64 p.xl)],
    [(p.yp, p.yb), (p.xp, xb)]⟩

@[simp] theorem KpP.D_B (p : KpP) (xb : List Byte) : (p.D xb).B = p.B := rfl
@[simp] theorem KpP.D_Z (p : KpP) (xb : List Byte) : (p.D xb).Z = p.Z := rfl
@[simp] theorem KpP.D_k (p : KpP) (xb : List Byte) : (p.D xb).k = p.k := rfl
@[simp] theorem KpP.D_dl (p : KpP) (xb : List Byte) : (p.D xb).dl = p.dl := rfl
@[simp] theorem KpP.D_dp (p : KpP) (xb : List Byte) : (p.D xb).dp = p.dp := rfl
@[simp] theorem KpP.D_dom (p : KpP) (xb : List Byte) : (p.D xb).dom = p.dom := rfl

/-- The parameters. -/
abbrev KpP.a (p : KpP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom

/-- A state the contract allows, with the public data `p` and x's octets `xb`. -/
def CR (p : KpP) (xb : List Byte) (s : State) : Prop :=
  kpPre s ∧ s.sp = p.sp ∧ s.gpr .x7 = p.B ∧ (stackArg s 0).toNat * 8 = p.Z ∧ (s.gpr .x2).toNat = p.k ∧
    (s.gpr .x1).toNat = p.dl ∧ s.gpr .x0 = p.dp ∧ kpDom s = p.dom ∧ s.gpr .x3 = p.yp ∧ kpY s = p.yb ∧
    s.gpr .x5 = p.xp ∧ (s.gpr .x6).toNat = p.xl ∧ kpX s = xb ∧
    p.pv = Spec.Ffdh.privateValid p.a (Spec.Rsa.os2ip xb)

/-- The lengths of the inputs. -/
def Ok (p : KpP) (xb : List Byte) : Prop :=
  xb.length = p.xl ∧ 1 ≤ p.xl ∧ p.xl ≤ p.k ∧ p.yb.length = p.k ∧
    p.pv = Spec.Ffdh.privateValid p.a (Spec.Rsa.os2ip xb)

/-- What the code uses of the precondition. -/
structure KpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .x2).toNat
  k2 : (s.gpr .x2).toNat ≤ 1024
  dl : (s.gpr .x1).toNat = 2 * (s.gpr .x2).toNat ∨ (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat
  yl : (s.gpr .x4).toNat = (s.gpr .x2).toNat
  xl1 : 1 ≤ (s.gpr .x6).toNat
  xl2 : (s.gpr .x6).toNat ≤ (s.gpr .x2).toNat
  hZ : 128 * (s.gpr .x2).toNat + 256 ≤ (stackArg s 0).toNat * 8
  hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8)
  dom : Src s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x0) (kpDom s)
  y : Src s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x3) (kpY s)
  x : Src s (s.gpr .x7) ((stackArg s 0).toNat * 8) (s.gpr .x5) (kpX s)

theorem kpCtx_of {s : State} (h : kpPre s) : KpCtx s := by
  obtain ⟨hsp, hrd, hwr, dds, dys, dxs, dsa, wD, wY, wX, wS, ⟨hk1, hk2⟩, hdl, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (s.gpr .x7) ((stackArg s 0).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  exact ⟨hk1, hk2, hdl, hyl, hxl1, hxl2, by omega_arith, hs, src_of_region (by rw [hrd]; simp) (by omega_arith) dds,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dys, src_of_region (by rw [hrd]; simp) (by omega_arith) dxs⟩

theorem cr_base (p : KpP) (xb : List Byte) (s : State) (h : CR p xb s) : Base (p.D xb) s := by
  have c := kpCtx_of h.1
  obtain ⟨B, Z, k, dl, dp, dom, yp, yb, xp, xl, pv, sp⟩ := p
  obtain ⟨-, -, hB, hZ, hk, hdl, hdp, hdom, hyp, hyb, hxp, hxl, hxb, -⟩ := h
  unfold KpP.D
  subst hB hZ hk hdl hdp hdom hyp hyb hxp hxl hxb
  have hy := c.y
  have hx := c.x
  refine ⟨c.hs, c.k1, c.k2, c.dl, c.hZ, c.dom, bytesAt_length _ _ _, fun e he => ?_, fun q hq => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hy
    · exact hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [argSlots]

theorem cr_ok {p : KpP} {xb : List Byte} {s : State} (h : CR p xb s) : Ok p xb := by
  have c := kpCtx_of h.1
  obtain ⟨-, -, -, -, hk, -, -, -, -, hyb, -, hxl, hxb, hpv⟩ := h
  refine ⟨by rw [← hxb, ← hxl, bytesAt_length], by rw [← hxl]; exact c.xl1, by rw [← hxl, ← hk]; exact c.xl2,
    by rw [← hyb, bytesAt_length, c.yl, hk], hpv⟩

/-- The entry: the arguments into the header at `scratch`. -/
theorem kpEntry_ok {s : State} {B : Addr} (hB : s.gpr .x7 = B) (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block CheckPrivate.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sDom) = s.gpr .x0 ∧ word t.mem B (8 * sDomLen) = s.gpr .x1 ∧
      word t.mem B (8 * sK) = s.gpr .x2 ∧ word t.mem B (8 * sY) = s.gpr .x3 ∧
      word t.mem B (8 * sX) = s.gpr .x5 ∧ word t.mem B (8 * sXl) = s.gpr .x6 ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.x0] s t := by
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((((s.mem.writeW (off B (8 * sDom)) (s.gpr .x0)).writeW (off B (8 * sDomLen)) (s.gpr .x1)).writeW
        (off B (8 * sK)) (s.gpr .x2)).writeW (off B (8 * sY)) (s.gpr .x3)).writeW (off B (8 * sX))
          (s.gpr .x5)).writeW (off B (8 * sXl)) (s.gpr .x6)) (by
    unfold CheckPrivate.entry
    brun [Crt.stw, hB, hdr_enc (show sDom < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
      hdr_enc (show sK < 32 by decide), hdr_enc (show sY < 32 by decide), hdr_enc (show sX < 32 by decide),
      hdr_enc (show sXl < 32 by decide), hw sDom (by decide), hw sDomLen (by decide), hw sK (by decide),
      hw sY (by decide), hw sX (by decide), hw sXl (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k⟩
  all_goals try (rw [hm]; simp (disch := decide) only [hdrStore_hdr, word_writeW_self]; done)
  rw [hm]
  intro x hx
  have e : ∀ i, i < 22 → ∀ (m : Mem) (v : BitVec 64), (m.writeW (off B (8 * i)) v) x = m x := fun i hi m v =>
    writeW_outside m B v (d := 8 * i) (by omega_arith) x (by omega_arith)
  rw [e sXl (by decide), e sX (by decide), e sY (by decide), e sK (by decide), e sDomLen (by decide),
    e sDom (by decide)]

/-- The entry's registers. -/
def entryRegs (p : KpP) (r : Reg) : BitVec 64 :=
  if r = .x0 then p.dp else if r = .x1 then BitVec.ofNat 64 p.dl else if r = .x2 then BitVec.ofNat 64 p.k else
    if r = .x3 then p.yp else if r = .x5 then p.xp else if r = .x6 then BitVec.ofNat 64 p.xl else p.B

theorem cr_regs (p : KpP) (xb : List Byte) (s : State) (h : CR p xb s) :
    ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x5, .x6, .x7], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, hB, -, hk, hdl, hdp, -, hyp, -, hxp, hxl, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hyp
  · exact hxp
  · rw [← hxl, ofNat_toNat64]
  · exact hB

theorem cr_e1 (p : KpP) (xb : List Byte) (s : State) (h : CR p xb s) :
    WP isa (.block CheckPrivate.entry) s fun t => E1 (p.D xb) t ∧ KX s t := by
  have hb := cr_base p xb s h
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hs : Scr s p.B p.Z := hb.scr
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, -, hyp, -, hxp, hxl, -⟩ := h
  have hw : ∀ i < 22, InRegions s.wr (off p.B (8 * i)) 8 := fun i hi => hs.st (by omega_arith)
  refine WP.mono (kpEntry_ok hB hw) fun t ⟨h0, hD, hL, hK, hY, hX, hXl, ho, k⟩ => ?_
  refine ⟨⟨hb.keep (InScr.of_outside ho (show 0 + 8 * 22 ≤ p.Z by omega_arith)) k, h0, ?_⟩, k.mono (by decide)⟩
  intro q hq
  simp only [FD.hdr, KpP.D, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · show word t.mem p.B (8 * sDomLen) = BitVec.ofNat 64 p.dl; rw [hL, ← hdl, ofNat_toNat64]
  · show word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k; rw [hK, ← hk, ofNat_toNat64]
  · exact hY.trans hyp
  · exact hX.trans hxp
  · show word t.mem p.B (8 * sXl) = BitVec.ofNat 64 p.xl; rw [hXl, ← hxl, ofNat_toNat64]

/-! ## x's range -/

abbrev X (xb : List Byte) : Nat := Spec.Rsa.os2ip xb
abbrev KpP.Y (p : KpP) : Nat := Spec.Rsa.os2ip p.yb

/-- The inner workspace's base. -/
abbrev KpP.G (p : KpP) (xb : List Byte) : Addr := off (p.D xb).B (inner (p.D xb).w)

/-- In the inner workspace. -/
def K1 (p : KpP) (xb : List Byte) (t : State) : Prop := (∃ mi, In (p.D xb) mi t) ∧ Ok p xb

/-- With x in `aXm`. -/
def K2 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aXm) (p.D xb).w = X xb) ∧ Ok p xb

theorem k1_lpre (p : KpP) (xb : List Byte) (t : State) (h : K1 p xb t) :
    LPre aXm sX sXl ((p.D xb).ld p.xp xb.length) t := by
  obtain ⟨⟨mi, hI⟩, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [KpP.D])
  exact hI.lpre (show aXm < 8 by decide) (by decide) (by decide) (hs.get (i := sX) (v := p.xp) (by simp [KpP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [KpP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; exact ho.2.2.1)

theorem k1_k2 (p : KpP) (xb : List Byte) (t : State) (h : K1 p xb t) :
    WP isa (seqs (Crt.loadArr aXm sX sXl)) t fun u => K2 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [KpP.D])
  exact WP.mono (hI.load (show aXm < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sX) (v := p.xp) (by simp [KpP.D])) (by rw [ho.1]; exact hs.get (i := sXl) (by simp [KpP.D]))
    hx (by rw [ho.1]; exact ho.2.1) (by rw [ho.1]; exact ho.2.2.1)) fun u ⟨⟨hu, hv, _⟩, k⟩ => ⟨⟨⟨mi, hu, hv⟩, ho⟩, k⟩

/-- After the test of x's range. -/
def K7 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ t.gpr .x9 = bit (p.pv = true)) ∧ Ok p xb

/-- x's range test (`ScalarRange.scalarRange_ok`). -/
theorem k2_k7 (p : KpP) (xb : List Byte) (t : State) (h : K2 p xb t) :
    WP isa (seqs CheckPrivate.scalarRange) t fun u => K7 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hx⟩, ho⟩ := h
  refine WP.mono (ScalarRange.scalarRange_ok ⟨mi, hI, hx⟩) fun u ⟨⟨mi', hu, h9⟩, k⟩ => ⟨⟨⟨mi', hu, ?_⟩, ho⟩, k⟩
  rw [h9, ho.2.2.2.2]; rfl

theorem k7_eval {p : KpP} {xb : List Byte} {t : State} (h : K7 p xb t) :
    isa.eval (.zero .x .x9) t = some (bit (p.pv = true) == 0) := by
  obtain ⟨⟨_, _, h9⟩, _⟩ := h
  rw [eval_zero, h9]

/-! ## y's range and subgroup -/

/-- y's load. -/
theorem _root_.VG.Proof.Ffdh.AArch64.In.loadY {p : KpP} {xb : List Byte} {mi : BitVec 64} {t : State} (hI : In (p.D xb) mi t) (ho : Ok p xb) :
    WP isa (seqs (Crt.loadArr aXm sY sK)) t fun u => (In (p.D xb) mi u ∧
      wv u.mem (p.G xb) (slot (p.D xb).w aXm) (p.D xb).w = p.Y ∧
      Outside (p.G xb) (slot (p.D xb).w aXm) (8 * ((p.D xb).w + 2)) t.mem u.mem) ∧ KX t u := by
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hy : Src t p.B p.Z p.yp p.yb := hb.srcs (p.yp, p.yb) (by simp [KpP.D])
  have := hb.k1
  exact hI.load (show aXm < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [KpP.D])) (by rw [ho.2.2.2.1]; exact hs.get (i := sK) (by simp))
    hy (by rw [ho.2.2.2.1]; simp at this; omega_arith) (by rw [ho.2.2.2.1]; simp)

theorem _root_.VG.Proof.Ffdh.AArch64.In.lpreY {p : KpP} {xb : List Byte} {mi : BitVec 64} {t : State} (hI : In (p.D xb) mi t) (ho : Ok p xb) :
    LPre aXm sY sK ((p.D xb).ld p.yp p.yb.length) t := by
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hy : Src t p.B p.Z p.yp p.yb := hb.srcs (p.yp, p.yb) (by simp [KpP.D])
  have := hb.k1
  exact hI.lpre (show aXm < 8 by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [KpP.D])) (by rw [ho.2.2.2.1]; exact hs.get (i := sK) (by simp))
    hy (by rw [ho.2.2.2.1]; simp at this; omega_arith) (by rw [ho.2.2.2.1]; simp)

/-- With y in `aXm`. -/
def K8 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aXm) (p.D xb).w = p.Y) ∧ Ok p xb ∧ p.pv = true

theorem k7_k8 (p : KpP) (xb : List Byte) (t : State) (h : K7 p xb t)
    (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs (Crt.loadArr aXm sY sK)) t fun u => K8 p xb u ∧ KX t u := by
  have hpv : p.pv = true := by
    rw [k7_eval h] at he
    by_contra hc
    simp [bit, hc] at he
  obtain ⟨⟨mi, hI, -⟩, ho⟩ := h
  exact WP.mono (hI.loadY ho) fun u ⟨⟨hu, hv, _⟩, k⟩ => ⟨⟨⟨mi, hu, hv⟩, ho, hpv⟩, k⟩

/-- y's range, as the code compares. -/
abbrev KpP.rg (p : KpP) (xb : List Byte) : Prop := 1 < p.Y ∧ 2 * (p.Y / 2) + 1 < (p.D xb).P

/-- After y's range. -/
def K9 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ t.gpr .x9 = bit (p.rg xb)) ∧ Ok p xb ∧ p.pv = true

theorem k8_k9 (p : KpP) (xb : List Byte) (t : State) (h : K8 p xb t) :
    WP isa (seqs (range aXm)) t fun u => K9 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hy⟩, ho, hpv⟩ := h
  exact WP.mono (hI.range (show aXm < 8 by decide) (by decide)) fun u ⟨⟨hu, h9, _⟩, k⟩ =>
    ⟨⟨⟨mi, hu, by rw [h9, hy]⟩, ho, hpv⟩, k⟩

theorem k9_eval {p : KpP} {xb : List Byte} {t : State} (h : K9 p xb t) :
    isa.eval (.zero .x .x9) t = some (bit (p.rg xb) == 0) := by
  obtain ⟨⟨_, _, h9⟩, _⟩ := h
  rw [eval_zero, h9]

/-- After `R² mod p`. -/
def K10 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb

theorem k9_k10 (M : Mont) (p : KpP) (xb : List Byte) (t : State) (h : K9 p xb t)
    (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs (r2Steps M.mm)) t fun u => K10 p xb u ∧ KX t u := by
  have hr : p.rg xb := by
    rw [k9_eval h] at he
    by_contra hc
    simp [bit, hc] at he
  obtain ⟨⟨mi, hI, -⟩, ho, hpv⟩ := h
  exact WP.mono (hI.r2 M) fun u ⟨⟨hu, _⟩, k⟩ => ⟨⟨⟨mi, hu⟩, ho, hpv, hr⟩, k⟩

/-- `g^x mod p` in `aY`. -/
def K14 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aY) (p.D xb).w = (p.D xb).G ^ X xb % (p.D xb).P) ∧
    Ok p xb ∧ p.pv = true ∧ p.rg xb

theorem k10_k14 (W : Window) (M : Mont) (S : Selector) (p : KpP) (xb : List Byte) (t : State) (h : K10 p xb t) :
    WP isa (seqs (pow W.code S.code M.mm sG sK sX sXl)) t fun u => K14 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM⟩, ho, hpv, hr⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [KpP.D])
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D xb).dp + BitVec.ofNat 64 (p.D xb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega_arith)
    (by rw [hb.glen]) (hs.get (i := sX) (v := p.xp) (by simp [KpP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [KpP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; have := ho.2.2.1; omega_arith)) fun u ⟨hu, hY, _, k⟩ => ⟨⟨⟨mi, hu, hY⟩, ho, hpv, hr⟩, k⟩

/-- With y in `aXm`. -/
def K15 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aY) (p.D xb).w = (p.D xb).G ^ X xb % (p.D xb).P ∧
    wv t.mem (p.G xb) (slot (p.D xb).w aXm) (p.D xb).w = p.Y) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb

theorem k14_k15 (p : KpP) (xb : List Byte) (t : State) (h : K14 p xb t) :
    WP isa (seqs (Crt.loadArr aXm sY sK)) t fun u => K15 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hY⟩, ho, hpv, hr⟩ := h
  have hI := hM.inn
  have hG := hI.2.1.good.scr.nowrap
  have sY := slot_le (w := (p.D xb).w) (show aY < 8 by decide)
  have sYX := slot_sep (w := (p.D xb).w) (show aY ≠ aXm by decide)
  exact WP.mono (hI.loadY ho) fun u ⟨⟨hu, hv, o⟩, k⟩ => ⟨⟨⟨mi, hu, by rw [o.wv (by omega_arith) (by omega_arith)]; exact hY, hv⟩,
    ho, hpv, hr⟩, k⟩

/-- After the comparison of `g^x mod p` with y. -/
def K16 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  t.gpr .x9 = bit ((p.D xb).G ^ X xb % (p.D xb).P = p.Y) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb

theorem k15_k16 (p : KpP) (xb : List Byte) (t : State) (h : K15 p xb t) :
    WP isa (seqs (eqArr aY aXm)) t fun u => K16 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hY, hy⟩, ho, hpv, hr⟩ := h
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact WP.mono (eqArr_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D xb).w by omega_arith)
    (show (p.D xb).w < 2 ^ 31 by omega_arith) (show aY < 8 by decide) (show aXm < 8 by decide))
    fun u ⟨h9, _, k⟩ => ⟨⟨by rw [h9, hY, hy], ho, hpv, hr⟩, k.mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.CheckPrivate

end

end


/-!
# `vg_ffdh_check_private` on AArch64: correctness

From `kpContract`'s precondition, `CheckPrivate.code` returns the status
(`kp_correct`), by its stages.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

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

/-- The final part. -/
abbrev fin (W : Window) (M : Mont) (S : Selector) : List (Prog isa) :=
  pow W.code S.code M.mm sG sK sX sXl ++ Crt.loadArr aXm sY sK ++ eqArr aY aXm ++ [.block [mov .x0 .x9]]

theorem tail_eq (W : Window) (M : Mont) (S : Selector) :
    CheckPrivate.tail W.code S.code M.mm = r2Steps M.mm ++ fin W M S := rfl

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    CheckPrivate.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (Crt.loadArr aXm sX sXl ++
      (CheckPrivate.scalarRange ++ ([.ite (.zero .x .x9) (ret 2) (seqs (Crt.loadArr aXm sY sK ++ (range aXm ++
        ([.ite (.zero .x .x9) (ret 0) (seqs (CheckPrivate.tail W.code S.code M.mm))] : List (Prog isa)))))] : List (Prog isa))))) := by
  simp only [CheckPrivate.main, List.append_assoc]

/-- The public data of a state. -/
def kpOf (s : State) : KpP :=
  ⟨s.gpr .x7, (stackArg s 0).toNat * 8, (s.gpr .x2).toNat, (s.gpr .x1).toNat, s.gpr .x0, kpDom s, s.gpr .x3,
    kpY s, s.gpr .x5, (s.gpr .x6).toNat,
    privateValid (domainOf (s.gpr .x2).toNat (kpDom s)) (Spec.Rsa.os2ip (kpX s)), s.sp⟩

theorem cr_of (s : State) (h : kpPre s) : CR (kpOf s) (kpX s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A return of `r`, after which `post` holds. -/
theorem ret_post {s₀ t : State} {r : Nat} (hr : r < 65536) (hk : KX s₀ t)
    (hv : domainValid (s₀.gpr .x2).toNat (kpDom s₀) → r = privateStatus (domainOf (s₀.gpr .x2).toNat (kpDom s₀))
      (Spec.Rsa.os2ip (kpY s₀)) (Spec.Rsa.os2ip (kpX s₀))) :
    WP isa (ret r) t fun u => abiPreserved s₀ u ∧ kpContract.post s₀ u :=
  WP.mono (ret_ok t hr) fun u ⟨⟨h0, _⟩, k⟩ => ⟨abiPreserved_of_keep (keep_trans hk (k.mono (by decide))), fun hd => by
    show ((u.gpr .x0).setWidth 32).toNat = _
    rw [h0, setWidth32_ofNat (by omega_using [hr]), hv hd]⟩

theorem bit_false' {t : State} {P : Prop} [Decidable P] (h : isa.eval (.zero .x .x9) t = some (bit P == 0))
    (he : isa.eval (.zero .x .x9) t = some true) : ¬ P := by
  rw [h] at he
  intro hp
  simp [bit, hp] at he

/-- `vg_ffdh_check_private`. -/
theorem kp_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : kpContract.pre s) :
    ∃ t s', Exec isa (CheckPrivate.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      kpContract.post s s' := by
  suffices hwp : WP isa (CheckPrivate.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ kpContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  have hok := cr_ok hCR
  have hst : ∀ r, (domainValid (s.gpr .x2).toNat (kpDom s) → r = privateStatus (domainOf (s.gpr .x2).toNat (kpDom s))
      (Spec.Rsa.os2ip (kpY s)) (Spec.Rsa.os2ip (kpX s))) ↔ (domainValid (kpOf s).k (kpOf s).dom →
      r = privateStatus (kpOf s).a (kpOf s).Y (X (kpX s))) := fun r => Iff.rfl
  have hpv : (kpOf s).pv = privateValid (kpOf s).a (X (kpX s)) := rfl
  generalize kpOf s = p at hCR hok hst hpv
  generalize hxb : kpX s = xb at hCR hok hpv
  have hb₀ := cr_base p xb s hCR
  unfold CheckPrivate.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p xb s hCR) fun t₁ ⟨e1, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D xb).mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · refine ret_post (by decide) k₂ ((hst 0).mpr fun hd => ?_)
    rw [hxb] at *
    have := domainValid_mod hd
    have hm : (p.D xb).mv = false := by cases hm' : (p.D xb).mv <;> simp_all
    exact absurd this (by show ¬ (p.D xb).mv = true; rw [hm]; decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  have hm := ce_valid ce he
  have hodd := (valid_facts hm hb₀.k1).1
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (kstep k₃ (k1_k2 p xb t₃
    ⟨h₃, hok⟩) fun t₄ h₄ k₄ => ?_)
  refine wp_seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (kstep k₄ (k2_k7 p xb t₄ h₄)
    fun t₉ h₉ k₉ => ?_)
  rw [seqs_one]
  refine WP.ite (bit (p.pv = true) == 0) (k7_eval h₉) (fun hb => ?_) (fun hb => ?_)
  · -- x out of range.
    refine ret_post (by decide) k₉ ((hst 2).mpr fun hd => ?_)
    have hn := bit_false' (k7_eval h₉) (by rw [k7_eval h₉, hb])
    rw [privateStatus_eq (by unfold domainValid at hd; simp only [Bool.and_eq_true] at hd; exact hd.1),
      ite_eq_left (by rw [hxb, ← hpv]; simpa using hn)]
  have he₉ : isa.eval (.zero .x .x9) t₉ = some false := by rw [k7_eval h₉, hb]
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [range]) (kstep k₉ (k7_k8 p xb t₉ h₉ he₉)
    fun t₁₀ h₁₀ k₁₀ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (kstep k₁₀ (k8_k9 p xb t₁₀ h₁₀) fun t₁₁ h₁₁ k₁₁ => ?_)
  rw [seqs_one]
  have hpvT : p.pv = true := h₁₀.2.2
  have hpvX : privateValid p.a (X xb) = true := by rw [← hpv]; exact hpvT
  have hpf : ∀ hd : domainValid p.k p.dom = true, privateStatus p.a p.Y (X xb) =
      if publicValid ⟨p.a, p.Y⟩ = true ∧ p.a.g ^ X xb % p.a.p = p.Y then 1 else 0 := fun hd => by
    rw [privateStatus_eq (by unfold domainValid at hd; simp only [Bool.and_eq_true] at hd; exact hd.1),
      ite_eq_right (by simp [hpvX])]
  refine WP.ite (bit (p.rg xb) == 0) (k9_eval h₁₁) (fun hb => ?_) (fun hb => ?_)
  · -- y out of range.
    refine ret_post (by decide) k₁₁ ((hst 0).mpr fun hd => ?_)
    have hn := bit_false' (k9_eval h₁₁) (by rw [k9_eval h₁₁, hb])
    rw [hxb, hpf hd, ite_eq_right fun ⟨hv, _⟩ => hn ⟨((publicValid_eq _ _).mp hv).1.1,
      (lt_pm1 hodd _).mpr ((publicValid_eq _ _).mp hv).1.2⟩]
  have he₁₁ : isa.eval (.zero .x .x9) t₁₁ = some false := by rw [k9_eval h₁₁, hb]
  rw [tail_eq]
  refine wp_seqs_append (by simp [r2Steps]) (by simp [fin, pow]) (kstep k₁₁ (k9_k10 M p xb t₁₁ h₁₁ he₁₁)
    fun t₁₅ h₁₅ k₁₅ => ?_)
  simp only [fin, List.append_assoc]
  refine wp_seqs_append (by simp [pow]) (by simp [Crt.loadArr]) (kstep k₁₅ (k10_k14 W M S p xb t₁₅ h₁₅)
    fun t₁₆ h₁₆ k₁₆ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [eqArr]) (kstep k₁₆ (k14_k15 p xb t₁₆ h₁₆)
    fun t₁₇ h₁₇ k₁₇ => ?_)
  refine wp_seqs_append (by simp [eqArr]) (by simp) (kstep k₁₇ (k15_k16 p xb t₁₇ h₁₇) fun t₁₈ h₁₈ k₁₈ => ?_)
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (c := .block [mov .x0 .x9]) (Q := fun t => t.gpr .x0 = t₁₈.gpr .x9) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h0, k⟩ =>
      ⟨abiPreserved_of_keep (keep_trans k₁₈ (k.mono (by decide))), fun hd => ?_⟩
  show ((t.gpr .x0).setWidth 32).toNat = _
  obtain ⟨h9, -, -, hr⟩ := h₁₈
  refine (hst _).mpr (fun hd' => ?_) hd
  have hpa : parametersValid p.a = true := by
    unfold domainValid at hd'; simp only [Bool.and_eq_true] at hd'; exact hd'.1
  rw [h0, h9, setWidth32_bit, hxb, hpf hd']
  by_cases hc : (p.D xb).G ^ X xb % (p.D xb).P = p.Y
  · -- A power of the checked generator is in its subgroup.
    have hG : p.a.g ^ X xb % p.a.p = p.Y := hc
    have hpub : publicValid ⟨p.a, p.Y⟩ = true := by
      rw [← hG]
      exact (publicValid_power hpa (X xb)).mpr ⟨by rw [hG]; exact hr.1, by rw [hG]; exact (lt_pm1 hodd _).mp hr.2⟩
    rw [ite_eq_left hc, ite_eq_left ⟨hpub, hc⟩]
  · rw [ite_eq_right hc, ite_eq_right fun ⟨_, h'⟩ => hc h']

end VG.Proof.Ffdh.AArch64.CheckPrivate

end

end

/-!
# `vg_ffdh_check_private` on AArch64: constant time

Runs with the same public data (`KpP`: all but x's octets, and whether x is
in range) leak the same (`kp_constantTime`): the exponentiation is RSA's,
constant time in the exponent, and the only branch on x is on its range,
which the status gives.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)
open VG.Spec.Ffdh

/-- A stage of some scalar. -/
def Ex (Φ : KpP → List Byte → State → Prop) (p : KpP) (t : State) : Prop := ∃ xb, Φ p xb t

theorem ex_post {Φ Ψ : KpP → List Byte → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (Ex Φ)) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → WP isa c s fun u => Ψ p xb u ∧ KX s u) : RelCT isa (Two (Ex Φ)) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨xb, h⟩ => WP.mono (hw p xb s h) fun _ h => ⟨xb, h.1⟩

theorem ex_post' {Φ Ψ : KpP → List Byte → State → Prop} {c : Prog isa} {P : KpP → State → Prop}
    (hct : RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c fun _ _ => True)
    (hw : ∀ p xb s, Φ p xb s → P p s → WP isa c s fun u => Ψ p xb u ∧ KX s u) :
    RelCT isa (Two fun p s => Ex Φ p s ∧ P p s) c (Two (Ex Ψ)) :=
  two_post hct fun p s ⟨⟨xb, h⟩, hp⟩ => WP.mono (hw p xb s h hp) fun _ h => ⟨xb, h.1⟩

/-- The working space, as the arithmetic sees it. -/
abbrev KpP.ws (p : KpP) : Ws := ⟨off p.B (inner ((p.k + 7) / 8)), slot ((p.k + 7) / 8) 8, (p.k + 7) / 8⟩

/-- The inner workspace's base. -/
abbrev KpP.g (p : KpP) : Addr := off p.B (inner ((p.k + 7) / 8))

/-- After the entry. -/
def E1' (p : KpP) (xb : List Byte) (t : State) : Prop := E1 (p.D xb) t ∧ Ok p xb

/-- After `domHead`. -/
def CE' (p : KpP) (xb : List Byte) (t : State) : Prop := CE (p.D xb) t ∧ Ok p xb

theorem k1_lpre' (p : KpP) (xb : List Byte) (t : State) (h : K1 p xb t) :
    LPre aXm sX sXl ((p.D xb).ld p.xp p.xl) t := by
  have := k1_lpre p xb t h
  rw [h.2.1] at this
  exact this

/-- `g^x`'s public data. -/
abbrev KpP.pwG (p : KpP) : PowPub :=
  ⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.dp + BitVec.ofNat 64 p.k, p.k, p.xp, p.xl⟩

theorem k10_pre (p : KpP) (xb : List Byte) (t : State) (h : K10 p xb t) : PS0 sG sK sX sXl p.pwG t := by
  obtain ⟨⟨mi, hM⟩, ho, -⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hx : Src t p.B p.Z p.xp xb := hb.srcs (p.xp, xb) (by simp [KpP.D])
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have := hM.ps0 (bp := sG) (bl := sK) (ep := sX) (el := sXl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sG) (v := (p.D xb).dp + BitVec.ofNat 64 (p.D xb).k) (by simp))
    (by rw [hb.glen]; exact hs.get (i := sK) (by simp)) hb.gsrc (by rw [hb.glen]; simp; omega_using [hk1])
    (by rw [hb.glen]) (hs.get (i := sX) (v := p.xp) (by simp [KpP.D]))
    (by rw [ho.1]; exact hs.get (i := sXl) (by simp [KpP.D])) hx (by rw [ho.1]; exact ho.2.1)
    (by rw [ho.1]; have := ho.2.2.1; omega_using [hk2, this])
  rw [hb.glen, ho.1] at this
  exact this

/-- The tail. -/
theorem tail_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex K9 p s ∧ isa.eval (.zero .x .x9) s = some false)
      (seqs (CheckPrivate.tail W.code S.code M.mm)) fun _ _ => True := by
  rw [tail_eq]
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp [fin, pow]) (RelCT.seq (R := Two (Ex K10))
    (ex_post' ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨⟨xb₁, ⟨mi₁, hI₁, _⟩, _⟩, _⟩
        ⟨⟨xb₂, ⟨mi₂, hI₂, _⟩, _⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D xb₁).w by omega_using [ew, this]) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h) fun p xb s h he => k9_k10 M p xb s h he) ?_)
  simp only [fin, List.append_assoc]
  refine RelCT.seqs_append (by simp [pow]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex K14))
    (ex_post (two_map KpP.pwG (fun p s ⟨xb, h⟩ => k10_pre p xb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (k10_k14 W M S)) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [eqArr]) (RelCT.seq (R := Two (Ex K15))
    (ex_post (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.yp,
        p.yb.length⟩ : BPub)) (fun p s ⟨xb, ⟨mi, hM, _⟩, ho, _⟩ => hM.inn.lpreY ho)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) k14_k15) ?_)
  refine RelCT.seqs_append (by simp [eqArr]) (by simp) (RelCT.seq (R := Two (Ex K16))
    (ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hI, _⟩, _⟩ => hI.goodW1.1)
      (eqArr_ct (by decide) (by decide) (by taint_decide))) k15_k16) ?_)
  rw [seqs_one]
  exact two_taint [] (pins_nil _) (by taint_decide)

/-- The public part of the run's data. -/
abbrev KpP.pub (p : KpP) : FD := (p.D []).pub

/-- x's range checks (`ScalarRange.scalarRange_ct`). -/
theorem scalar_ct :
    RelCT isa (Two (Ex K2)) (seqs (CheckPrivate.scalarRange)) (Two (Ex K7)) :=
  ex_post (two_map KpP.pub (fun p _ ⟨xb, ⟨mi, hI, hx⟩, _⟩ => ⟨p.D xb, X xb, rfl, mi, hI, hx⟩)
    (ScalarRange.scalarRange_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) k2_k7

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex CE' p s ∧ isa.eval (.zero .x .x9) s = some false)
      (CheckPrivate.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex K1))
    (two_post (two_map (fun p : KpP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨xb, h⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨xb, h⟩, he⟩ => WP.mono (ce_in _ s h.1 he) fun u ⟨hu, _⟩ =>
        ⟨xb, hu, h.2⟩) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (RelCT.seq
    (R := Two (Ex K2)) (ex_post (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8,
      (p.k + 7) / 8⟩, p.xp, p.xl⟩ : BPub)) (fun p s ⟨xb, h⟩ => k1_lpre' p xb s h)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) k1_k2) ?_)
  refine RelCT.seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (RelCT.seq (R := Two (Ex K7))
    scalar_ct ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k7_eval h₁, k7_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) ?_
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [range]) (RelCT.seq (R := Two (Ex K8))
    (ex_post' (two_map (fun p : KpP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.yp,
        p.yb.length⟩ : BPub)) (fun p s ⟨⟨xb, ⟨mi, hI, _⟩, ho⟩, _⟩ => hI.lpreY ho)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) fun p xb s h he => k7_k8 p xb s h he) ?_)
  refine RelCT.seqs_append (by simp [range]) (by simp) (RelCT.seq (R := Two (Ex K9))
    (ex_post (two_map KpP.ws (fun p s ⟨xb, ⟨mi, hI, _⟩, _⟩ => hI.goodW1) (range_ct (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))) k8_k9) ?_)
  rw [seqs_one]
  exact two_ite (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ => by rw [k9_eval h₁, k9_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (tail_ct W M S)

/-- `CheckPrivate.code` leaks the same in runs with the same public data. -/
theorem kp_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex CR)) (CheckPrivate.code W.code S.code M.mm) fun _ _ => True := by
  unfold CheckPrivate.code
  refine RelCT.seq (R := Two (Ex CE')) (RelCT.block_append (RelCT.seq (two_piece (Ψ := Ex E1')
      [.x0, .x1, .x2, .x3, .x5, .x6, .x7] (pins_of entryRegs fun p s ⟨xb, h⟩ => cr_regs p xb s h) (by taint_decide)
      fun p s ⟨xb, h⟩ => WP.mono (cr_e1 p xb s h) fun _ h' => ⟨xb, h'.1, cr_ok h⟩)
    (ex_post (two_map (fun p : KpP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨_, h, _⟩ => h.dhp) domHead_ct)
      fun p xb s h => WP.mono (e1_ce _ s h.1) fun u ⟨hu, k⟩ => ⟨⟨hu, h.2⟩, k⟩))) ?_
  exact two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁, ce_eval h₂]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S)

/-- The public data of the second run. -/
theorem cr_pub {s₁ s₂ : State} (h₂ : kpPre s₂) (hp : kpPub s₁ s₂) : CR (kpOf s₁) (kpX s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_one, stackArgs_one] at ha
  simp only [List.cons.injEq, and_true] at ha
  unfold kpLeak at hl
  simp only [List.append_assoc] at hl
  obtain ⟨hd, hl'⟩ := List.append_inj hl (by simp [kpDom, Spec.Rsa.bytesAt, r1])
  obtain ⟨hy, hs⟩ := List.append_inj hl' (by simp [kpY, Spec.Rsa.bytesAt, r4])
  have hd' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd
  have hy' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, hsp.symm, r7.symm, by rw [← ha]; rfl, by rw [← r2]; rfl, by rw [← r1]; rfl, r0.symm, hd'.symm,
    r3.symm, hy'.symm, r5.symm, by rw [← r6]; rfl, rfl, ?_⟩
  -- Whether x is in range, from the statuses.
  show privateValid (domainOf (s₁.gpr .x2).toNat (kpDom s₁)) (Spec.Rsa.os2ip (kpX s₁)) =
    privateValid (domainOf (s₁.gpr .x2).toNat (kpDom s₁)) (Spec.Rsa.os2ip (kpX s₂))
  rw [r2, hd'] at hs ⊢
  rw [hy'] at hs
  unfold privateStatus at hs
  generalize privateValid _ (Spec.Rsa.os2ip (kpX s₁)) = b₁ at hs ⊢
  generalize privateValid _ (Spec.Rsa.os2ip (kpX s₂)) = b₂ at hs ⊢
  cases b₁ <;> cases b₂ <;> simp at hs ⊢ <;> split at hs <;> simp at hs

/-- `vg_ffdh_check_private` is constant time. -/
theorem kp_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa kpContract.pre kpContract.pub (CheckPrivate.code W.code S.code M.mm) :=
  RelCT.constantTime ((kp_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨kpOf s₁, ⟨kpX s₁, cr_of s₁ h₁⟩, ⟨kpX s₂, cr_pub h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.CheckPrivate

end

end

/-!
# `vg_ffdh_check_private` on AArch64: verified

Correct (`kp_correct`) and constant time (`kp_constantTime`) against
`kpContract`, which the shared contract implies (`kp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem kp_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.CheckPrivate.code W.code S.code M.mm)
      (Spec.Ffdh.checkPrivateContract abi) :=
  Verified.of_correct (kp_correct W M S) (kp_constantTime W M S) kp_implies

end VG.Proof.Ffdh.AArch64.CheckPrivate
