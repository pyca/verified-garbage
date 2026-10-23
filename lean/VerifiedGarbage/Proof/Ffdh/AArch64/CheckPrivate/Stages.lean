module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Pieces
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call

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

/-- Back in the outer workspace, with `R² mod p`. -/
def K11 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D xb) mi t ∧ R2f (p.D xb) t) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb

theorem k10_k11 (p : KpP) (xb : List Byte) (t : State) (h : K10 p xb t) :
    WP isa (.block [leave]) t fun u => K11 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM⟩, ho, hpv, hr⟩ := h
  exact WP.mono (leave_ok hM.2.1.sub) fun u ⟨⟨h0, hm⟩, k⟩ =>
    ⟨⟨⟨mi, hM.inn.pa hm k h0, hM.r2f.mem hm⟩, ho, hpv, hr⟩, k.mono (by decide)⟩

/-- After the test of the domain's length. -/
def K12 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D xb) mi t ∧ R2f (p.D xb) t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.dl - 2 * p.k)) ∧ Ok p xb ∧
    p.pv = true ∧ p.rg xb

theorem k11_k12 (p : KpP) (xb : List Byte) (t : State) (h : K11 p xb t) :
    WP isa (.block qTest) t fun u => K12 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR⟩, ho, hpv, hr⟩ := h
  exact WP.mono hP.qtest fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨⟨mi, hP.outside (o := 256) (n := 0) (by decide)
    (by simp only [inner, slot, hdrBytes]; omega_arith) (fun x _ => by rw [hm]) k.rd k.wr ((k.gpr .x0 (by decide)).trans
      hP.2.2.2.2.2.2), hR.mem hm, h3⟩, ho, hpv, hr⟩, k.mono (by decide)⟩

theorem k12_eval {p : KpP} {xb : List Byte} {t : State} (h : K12 p xb t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) := by
  obtain ⟨⟨_, _, _, h3⟩, _⟩ := h
  rw [eval_zero, h3]

/-- y's subgroup check, as the code computes it. -/
abbrev KpP.qc (p : KpP) (xb : List Byte) : Prop :=
  p.dl = 3 * p.k → p.Y ^ Spec.Rsa.os2ip (p.D xb).qb % (p.D xb).P = 1

/-- After y's subgroup check. -/
def K13 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ t.gpr .x9 = bit (p.qc xb)) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb

theorem enterOne_eq : [enter, movi .x9 1] = [enter] ++ [movi .x9 1] := rfl

theorem k12_k13n (p : KpP) (xb : List Byte) (t : State) (h : K12 p xb t)
    (he : isa.eval (.zero .x .x3) t = some true) :
    WP isa (.block [enter, movi .x9 1]) t fun u => K13 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, h3⟩, ho, hpv, hr⟩ := h
  have h2 := hP.1.noq (by rw [eval_zero, h3] at he; simpa using he)
  have hk1 := hP.1.k1
  rw [enterOne_eq, WP.block_append_iff]
  refine WP.mono hP.enterM fun u ⟨⟨hI, hm⟩, k⟩ => WP.mono (WP.keep [.x9] (Q := fun v => v.gpr .x9 = 1 ∧
    v.mem = u.mem) (by brun) (by decide) (by decide) (by decide +kernel)) fun v ⟨⟨h9, hmv⟩, k'⟩ =>
      ⟨⟨⟨mi, (hI.md (hR.mem hm)).keep hmv k' (by decide), ?_⟩, ho, hpv, hr⟩, keep_trans k (k'.mono (by decide))⟩
  rw [h9]
  unfold bit
  rw [ite_eq_left (fun e => absurd (e.symm.trans h2) (by simp at hk1 ⊢; omega_arith))]

/-- q's octets from its first nonzero one. -/
abbrev KpP.qe (p : KpP) (xb : List Byte) : List Byte := (p.D xb).qb.drop (lead (p.D xb).qb)

theorem qe_facts {p : KpP} {xb : List Byte} {t : State} (hb : Base (p.D xb) t) (hq : p.dl = 3 * p.k) :
    (p.qe xb).length = p.k - lead (p.D xb).qb ∧ 1 ≤ (p.qe xb).length ∧ (p.qe xb).length ≤ p.k ∧
      Spec.Rsa.os2ip (p.qe xb) = Spec.Rsa.os2ip (p.D xb).qb ∧
      Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D xb).qb)) (p.qe xb) := by
  have hl := hb.qlen hq
  have := hb.k1
  simp only [KpP.D_k] at hl this
  have hne : (p.D xb).qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have hlead := lead_lt hne
  refine ⟨by rw [List.length_drop, hl], by rw [List.length_drop]; omega_arith, by rw [List.length_drop]; omega_arith,
    os2ip_drop_lead _, hb.qsrc.drop _⟩

/-- The exponent slots: q from its first nonzero octet. -/
def EpS (p : KpP) (xb : List Byte) (m : Mem) : Prop :=
  word m p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D xb).qb) ∧
    word m p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead (p.D xb).qb)

/-- After q's scan. -/
def K12s (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D xb) mi t ∧ R2f (p.D xb) t ∧ EpS p xb t.mem) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb ∧ p.dl = 3 * p.k

theorem k12_s (p : KpP) (xb : List Byte) (t : State) (h : K12 p xb t) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (scan sQ)) t fun u => K12s p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, -⟩, ho, hpv, hr⟩ := h
  have hb := hP.1
  refine WP.mono (hP.scan hq) fun u ⟨⟨⟨hP', hEp, hEl⟩, f⟩, k₁⟩ => ⟨⟨⟨mi, hP', hR.hdr hb f (fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl <;> simp only [sEp, sEl, sFn] <;> omega_arith), hEp, hEl⟩, ho, hpv, hr, hq⟩, k₁⟩

/-- In the inner workspace again, with `R² mod p`. -/
def K12e (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ EpS p xb t.mem) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb ∧ p.dl = 3 * p.k

theorem s_e (p : KpP) (xb : List Byte) (t : State) (h : K12s p xb t) :
    WP isa (.block [enter]) t fun u => K12e p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, hE⟩, rest⟩ := h
  exact WP.mono hP.enterM fun v ⟨⟨hI, hm⟩, k₂⟩ => ⟨⟨⟨mi, hI.md (hR.mem hm), by unfold EpS; rw [hm]; exact hE⟩, rest⟩, k₂⟩

/-- `y^q mod p` in `aY`. -/
def K12p (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aY) (p.D xb).w =
    p.Y ^ Spec.Rsa.os2ip (p.D xb).qb % (p.D xb).P) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb ∧ p.dl = 3 * p.k

theorem e_pre (p : KpP) (xb : List Byte) (t : State) (h : K12e p xb t) :
    PS0 sY sK sEp sEl ((p.D xb).pw p.yp p.k (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D xb).qb))
      (p.k - lead (p.D xb).qb)) t := by
  obtain ⟨⟨mi, hM, hEp, hEl⟩, ho, -, -, hq⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hy : Src t p.B p.Z p.yp p.yb := hb.srcs (p.yp, p.yb) (by simp [KpP.D])
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts hb hq
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have := hM.ps0 (bp := sY) (bl := sK) (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [KpP.D])) (by rw [ho.2.2.2.1]; exact hs.get (i := sK) (by simp)) hy
    (by rw [ho.2.2.2.1]; omega_arith) (by rw [ho.2.2.2.1]; simp) hEp (by rw [hl]; exact hEl) hsrc h1 (by omega_arith)
  rw [ho.2.2.2.1, hl] at this
  exact this

theorem e_p (W : Window) (M : Mont) (S : Selector) (p : KpP) (xb : List Byte) (t : State) (h : K12e p xb t) :
    WP isa (seqs (pow W.code S.code M.mm sY sK sEp sEl)) t fun u => K12p p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hEp, hEl⟩, ho, hpv, hr, hq⟩ := h
  have hb := hM.1
  have hs := hM.2.2.2.1
  have hy : Src t p.B p.Z p.yp p.yb := hb.srcs (p.yp, p.yb) (by simp [KpP.D])
  obtain ⟨hl, h1, hk, hQ, hsrc⟩ := qe_facts hb hq
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  exact WP.mono (hM.pow W M S (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sY) (v := p.yp) (by simp [KpP.D])) (by rw [ho.2.2.2.1]; exact hs.get (i := sK) (by simp)) hy
    (by rw [ho.2.2.2.1]; omega_arith) (by rw [ho.2.2.2.1]; simp) hEp (by rw [hl]; exact hEl) hsrc h1 (by omega_arith))
    fun w' ⟨hM', hY, _, k₃⟩ => ⟨⟨⟨mi, hM', by rw [hY, hQ]⟩, ho, hpv, hr, hq⟩, k₃⟩

theorem p_k13 (p : KpP) (xb : List Byte) (t : State) (h : K12p p xb t) :
    WP isa (seqs (isOne aY)) t fun u => K13 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM', hY⟩, ho, hpv, hr, hq⟩ := h
  have hI' := hM'.inn
  have ew := hI'.1.ew
  have hk1 : 64 ≤ p.k := hI'.1.k1
  have hk2 : p.k ≤ 1024 := hI'.1.k2
  have ek : (p.D xb).k = p.k := rfl
  refine WP.mono (eqArr_ok hI'.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D xb).w by omega_arith)
    (show (p.D xb).w < 2 ^ 31 by omega_arith) (show aY < 8 by decide) (show aOne < 8 by decide))
    fun x ⟨h9, hmx, k₄⟩ => ⟨⟨⟨mi, hM'.keep hmx k₄ (by decide), ?_⟩, ho, hpv, hr⟩, k₄.mono (by decide)⟩
  rw [h9, hY, hI'.2.2.1.one]
  exact bit_iff ⟨fun e _ => e, fun e => e hq⟩

theorem k12_k13q (W : Window) (M : Mont) (S : Selector) (p : KpP) (xb : List Byte) (t : State) (h : K12 p xb t)
    (he : isa.eval (.zero .x .x3) t = some false) :
    WP isa (seqs (scan sQ ++ ([.block [enter]] : List (Prog isa)) ++ pow W.code S.code M.mm sY sK sEp sEl ++ isOne aY)) t
      fun u => K13 p xb u ∧ KX t u := by
  have hq := h.1.choose_spec.1.1.q (by rw [k12_eval h] at he; simpa using he)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_seqs_append (by simp [scan]) (by simp) (WP.mono (k12_s p xb t h hq) fun u ⟨hu, k₁⟩ =>
    wp_seqs_cons (by simp [pow]) (WP.mono (s_e p xb u hu) fun v ⟨hv, k₂⟩ =>
      wp_seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (WP.mono (e_p W M S p xb v hv) fun w' ⟨hw, k₃⟩ =>
        WP.mono (p_k13 p xb w' hw) fun x ⟨hx, k₄⟩ => ⟨hx, keep_trans (keep_trans k₁ k₂) (keep_trans k₃ k₄)⟩)))

theorem k13_eval {p : KpP} {xb : List Byte} {t : State} (h : K13 p xb t) :
    isa.eval (.zero .x .x9) t = some (bit (p.qc xb) == 0) := by
  obtain ⟨⟨_, _, h9⟩, _⟩ := h
  rw [eval_zero, h9]

/-- `g^x mod p` in `aY`. -/
def K14 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, Md (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aY) (p.D xb).w = (p.D xb).G ^ X xb % (p.D xb).P) ∧
    Ok p xb ∧ p.pv = true ∧ p.rg xb ∧ p.qc xb

theorem k13_k14 (W : Window) (M : Mont) (S : Selector) (p : KpP) (xb : List Byte) (t : State) (h : K13 p xb t)
    (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs (pow W.code S.code M.mm sG sK sX sXl)) t fun u => K14 p xb u ∧ KX t u := by
  have hqc : p.qc xb := by
    rw [k13_eval h] at he
    by_contra hc
    simp [bit, hc] at he
  obtain ⟨⟨mi, hM, -⟩, ho, hpv, hr⟩ := h
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
    (by rw [ho.1]; have := ho.2.2.1; omega_arith)) fun u ⟨hu, hY, _, k⟩ => ⟨⟨⟨mi, hu, hY⟩, ho, hpv, hr, hqc⟩, k⟩

/-- With y in `aXm`. -/
def K15 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D xb) mi t ∧ wv t.mem (p.G xb) (slot (p.D xb).w aY) (p.D xb).w = (p.D xb).G ^ X xb % (p.D xb).P ∧
    wv t.mem (p.G xb) (slot (p.D xb).w aXm) (p.D xb).w = p.Y) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb ∧ p.qc xb

theorem k14_k15 (p : KpP) (xb : List Byte) (t : State) (h : K14 p xb t) :
    WP isa (seqs (Crt.loadArr aXm sY sK)) t fun u => K15 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hM, hY⟩, ho, hpv, hr, hqc⟩ := h
  have hI := hM.inn
  have hG := hI.2.1.good.scr.nowrap
  have sY := slot_le (w := (p.D xb).w) (show aY < 8 by decide)
  have sYX := slot_sep (w := (p.D xb).w) (show aY ≠ aXm by decide)
  exact WP.mono (hI.loadY ho) fun u ⟨⟨hu, hv, o⟩, k⟩ => ⟨⟨⟨mi, hu, by rw [o.wv (by omega_arith) (by omega_arith)]; exact hY, hv⟩,
    ho, hpv, hr, hqc⟩, k⟩

/-- After the comparison of `g^x mod p` with y. -/
def K16 (p : KpP) (xb : List Byte) (t : State) : Prop :=
  t.gpr .x9 = bit ((p.D xb).G ^ X xb % (p.D xb).P = p.Y) ∧ Ok p xb ∧ p.pv = true ∧ p.rg xb ∧ p.qc xb

theorem k15_k16 (p : KpP) (xb : List Byte) (t : State) (h : K15 p xb t) :
    WP isa (seqs (eqArr aY aXm)) t fun u => K16 p xb u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hY, hy⟩, ho, hpv, hr, hqc⟩ := h
  have hb := hI.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  exact WP.mono (eqArr_ok hI.2.1.good (Nat.le_refl _) (show 1 ≤ (p.D xb).w by omega_arith)
    (show (p.D xb).w < 2 ^ 31 by omega_arith) (show aY < 8 by decide) (show aXm < 8 by decide))
    fun u ⟨h9, _, k⟩ => ⟨⟨by rw [h9, hY, hy], ho, hpv, hr, hqc⟩, k.mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.CheckPrivate
