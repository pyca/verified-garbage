module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
public import VerifiedGarbage.Proof.Ffdh.AArch64.OutMask
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

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
