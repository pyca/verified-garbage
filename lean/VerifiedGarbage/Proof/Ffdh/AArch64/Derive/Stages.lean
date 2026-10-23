module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
public import VerifiedGarbage.Impl.Ffdh.AArch64.Derive
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

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
  refine WP.mono (VG.Proof.Rsa.AArch64.zeroOut_ok hs h0 (by omega) (by decide) (by decide) hO hK (by omega)
    (by omega) ⟨fun i hi => (hd i hi).1, fun i hi => (hd i hi).2⟩) fun u ⟨hb, hfr, k⟩ => ?_
  have hout := outside_of_frame (fun j hj => (hd j hj).2) hfr
  have e : ∀ i < 32, word u.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hout.word (Or.inl (by omega)) (by omega)
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
