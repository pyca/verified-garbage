module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
public import VerifiedGarbage.Proof.Ffdh.AArch64.Out
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ffdh_generate_key` on AArch64: the stages of a run up to the scalar

The public data (`GkP`) are the working space, the lengths, the pointers,
the domain, and whether the scalar is in range; the random octets are
secret. A run from a state with the public data `p` and the octets `rb`
(`CR p rb`) goes through the shared stages of the data `p.D₀ rb` (the
random octets an input) up to the scalar's octets in `x`, and of the data
`p.D₁ rb` (the scalar's octets an input) after them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data. -/
structure GkP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  dom : List Byte
  xp : Addr
  yp : Addr
  rp : Addr
  /-- Whether the scalar is in range. -/
  pv : Bool
  sp : Addr

/-- The run's data, with the random octets an input. -/
def GkP.D₀ (p : GkP) (rb : List Byte) : FD :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, [(sX, p.xp), (sY, p.yp), (sRand, p.rp)], [(p.rp, rb)]⟩

@[simp] theorem GkP.D₀_B (p : GkP) (rb : List Byte) : (p.D₀ rb).B = p.B := rfl
@[simp] theorem GkP.D₀_Z (p : GkP) (rb : List Byte) : (p.D₀ rb).Z = p.Z := rfl
@[simp] theorem GkP.D₀_k (p : GkP) (rb : List Byte) : (p.D₀ rb).k = p.k := rfl
@[simp] theorem GkP.D₀_dl (p : GkP) (rb : List Byte) : (p.D₀ rb).dl = p.dl := rfl
@[simp] theorem GkP.D₀_dp (p : GkP) (rb : List Byte) : (p.D₀ rb).dp = p.dp := rfl
@[simp] theorem GkP.D₀_dom (p : GkP) (rb : List Byte) : (p.D₀ rb).dom = p.dom := rfl

/-- The parameters. -/
abbrev GkP.a (p : GkP) : Spec.Ffdh.Parameters := Spec.Ffdh.domainOf p.k p.dom

/-- The mask of the bound's first nonzero octet. -/
abbrev GkP.msk (p : GkP) (rb : List Byte) : BitVec 64 :=
  BitVec.ofNat 64 (KeyScalar.smearN (p.D₀ rb).bc.toNat)

/-- The scalar's octets. -/
def GkP.xo (p : GkP) (rb : List Byte) : List Byte := KeyScalar.cut rb (p.D₀ rb).bl ((p.msk rb).setWidth 8)

/-- The run's data, with the scalar's octets an input. -/
abbrev GkP.D₁ (p : GkP) (rb : List Byte) : FD := (p.D₀ rb).withSrcs [(p.xp, p.xo rb)]

/-- The scalar. -/
abbrev GkP.s (p : GkP) (rb : List Byte) : Nat := Spec.Ffdh.scalarOfOctets p.a rb

/-- A state the contract allows, with the public data `p` and the random octets `rb`. -/
def CR (p : GkP) (rb : List Byte) (s : State) : Prop :=
  gkPre s ∧ s.sp = p.sp ∧ stackArg s 1 = p.B ∧ (stackArg s 2).toNat * 8 = p.Z ∧ (s.gpr .x6).toNat = p.k ∧
    (s.gpr .x5).toNat = p.dl ∧ s.gpr .x4 = p.dp ∧ gkDom s = p.dom ∧ s.gpr .x0 = p.xp ∧ s.gpr .x2 = p.yp ∧
    s.gpr .x7 = p.rp ∧ gkRand s = rb ∧ p.pv = Spec.Ffdh.privateValid p.a (p.s rb)

/-- The outputs' and the inputs' regions apart. -/
def Geo (p : GkP) : Prop :=
  (⟨p.xp, p.k⟩ : Region).Disjoint ⟨p.yp, p.k⟩ ∧ (⟨p.xp, p.k⟩ : Region).Disjoint ⟨p.dp, p.dl⟩ ∧
    (⟨p.xp, p.k⟩ : Region).Disjoint ⟨p.rp, p.k⟩ ∧ (⟨p.yp, p.k⟩ : Region).Disjoint ⟨p.dp, p.dl⟩ ∧
    p.xp.toNat + p.k ≤ 2 ^ 64 ∧ p.yp.toNat + p.k ≤ 2 ^ 64 ∧ p.dp.toNat + p.dl ≤ 2 ^ 64 ∧
    p.rp.toNat + p.k ≤ 2 ^ 64

/-- The lengths and the regions. -/
def Ok (p : GkP) (rb : List Byte) : Prop :=
  rb.length = p.k ∧ Geo p ∧ p.pv = Spec.Ffdh.privateValid p.a (p.s rb)

/-- `x` and `y`, writable and outside the working space. -/
def Dst (p : GkP) (t : State) : Prop :=
  ∀ j < p.k, (InRegions t.wr (p.xp + BitVec.ofNat 64 j) 1 ∧ p.Z ≤ ofs p.B (p.xp + BitVec.ofNat 64 j)) ∧
    (InRegions t.wr (p.yp + BitVec.ofNat 64 j) 1 ∧ p.Z ≤ ofs p.B (p.yp + BitVec.ofNat 64 j))

theorem Dst.keep {p : GkP} {t u : State} (h : Dst p t) {rs : List Reg} (k : Keep rs t u) : Dst p u :=
  fun j hj => ⟨⟨by rw [k.wr]; exact (h j hj).1.1, (h j hj).1.2⟩, ⟨by rw [k.wr]; exact (h j hj).2.1, (h j hj).2.2⟩⟩

theorem Dst.wr {p : GkP} {t u : State} (h : Dst p t) (hw : u.wr = t.wr) : Dst p u :=
  fun j hj => ⟨⟨by rw [hw]; exact (h j hj).1.1, (h j hj).1.2⟩, ⟨by rw [hw]; exact (h j hj).2.1, (h j hj).2.2⟩⟩

/-- Bytes of regions apart are apart. -/
theorem ne_of_disj {a b : Addr} {n m i j : Nat} (hd : (⟨a, n⟩ : Region).Disjoint ⟨b, m⟩) (ha : a.toNat + n ≤ 2 ^ 64)
    (hb : b.toNat + m ≤ 2 ^ 64) (hi : i < n) (hj : j < m) : a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j :=
  fun he => hd _ (contains_byte a hi (by omega)) (he ▸ contains_byte b hj (by omega))

/-- What the code uses of the precondition. -/
structure GkCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .x6).toNat
  k2 : (s.gpr .x6).toNat ≤ 1024
  dl : (s.gpr .x5).toNat = 2 * (s.gpr .x6).toNat ∨ (s.gpr .x5).toNat = 3 * (s.gpr .x6).toNat
  xl : (s.gpr .x1).toNat = (s.gpr .x6).toNat
  yl : (s.gpr .x3).toNat = (s.gpr .x6).toNat
  rl : (stackArg s 0).toNat = (s.gpr .x6).toNat
  hZ : 128 * (s.gpr .x6).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  ha1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x4) (gkDom s)
  rnd : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x7) (gkRand s)
  xw : ∀ j < (s.gpr .x6).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  xs : ∀ j < (s.gpr .x6).toNat, (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) (s.gpr .x0 + BitVec.ofNat 64 j)
  yw : ∀ j < (s.gpr .x6).toNat, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 j) 1
  ys : ∀ j < (s.gpr .x6).toNat, (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) (s.gpr .x2 + BitVec.ofNat 64 j)
  geo : (⟨s.gpr .x0, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x6).toNat⟩ ∧
    (⟨s.gpr .x0, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩ ∧
    (⟨s.gpr .x0, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (s.gpr .x6).toNat⟩ ∧
    (⟨s.gpr .x2, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩ ∧
    (s.gpr .x0).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64

theorem gkCtx_of {s : State} (h : gkPre s) : GkCtx s := by
  obtain ⟨hsp, hrd, hwr, dXY, dXD, dXR, dXS, dXA, dYD, dYR, dYS, dYA, dDS, dRS, dSA, wX, wY, wD, wR, wS, ⟨hk1, hk2⟩,
    hdl, hxl, hyl, hrl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  refine ⟨hk1, hk2, hdl, hxl, hyl, hrl, by omega, hs,
    ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 by
        simp only [stackArgAddr, Nat.mul_zero, Nat.mul_one, BitVec.add_zero]]
      exact Offset.contains_base _ (by omega) (by omega)⟩,
    src_of_region (by rw [hrd]; simp) (by omega) dDS,
    src_of_region (by rw [hrd]; simp) (by omega) dRS,
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dXS (contains_byte _ (by omega) (by omega)),
    fun j hj => ⟨⟨s.gpr .x2, (s.gpr .x3).toNat⟩, by rw [hwr]; simp, contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dYS (contains_byte _ (by omega) (by omega)), ?_⟩
  rw [hxl, hyl] at dXY
  rw [hxl] at dXD wX
  rw [hxl, hrl] at dXR
  rw [hyl] at dYD wY
  rw [hrl] at wR
  exact ⟨dXY, dXD, dXR, dYD, wX, wY, wD, wR⟩

theorem cr_base (p : GkP) (rb : List Byte) (s : State) (h : CR p rb s) : Base (p.D₀ rb) s := by
  have c := gkCtx_of h.1
  obtain ⟨B, Z, k, dl, dp, dom, xp, yp, rp, pv, sp⟩ := p
  obtain ⟨-, -, hB, hZ, hk, hdl, hdp, hdom, -, -, hrp, hrb, -⟩ := h
  unfold GkP.D₀
  subst hB hZ hk hdl hdp hdom hrp hrb
  have hr := c.rnd
  refine ⟨c.hs, c.k1, c.k2, c.dl, c.hZ, c.dom, bytesAt_length _ _ _, fun e he => ?_, fun q hq => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rw [he]; exact hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [argSlots]

theorem cr_dst (p : GkP) (rb : List Byte) (s : State) (h : CR p rb s) : Dst p s := by
  have c := gkCtx_of h.1
  obtain ⟨-, -, hB, hZ, hk, -, -, -, hxp, hyp, -⟩ := h
  intro j hj
  rw [← hk] at hj
  rw [← hB, ← hZ, ← hxp, ← hyp]
  exact ⟨⟨c.xw j hj, c.xs j hj⟩, ⟨c.yw j hj, c.ys j hj⟩⟩

theorem cr_ok {p : GkP} {rb : List Byte} {s : State} (h : CR p rb s) : Ok p rb := by
  have c := gkCtx_of h.1
  obtain ⟨-, -, -, -, hk, hdl, hdp, -, hxp, hyp, hrp, hrb, hpv⟩ := h
  refine ⟨by rw [← hrb, bytesAt_length, c.rl, hk], ?_, hpv⟩
  have g := c.geo
  rw [hk, hdl, hdp, hxp, hyp, hrp] at g
  exact g

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
theorem gkEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    WP isa (.block GenerateKey.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sX) = s.gpr .x0 ∧ word t.mem B (8 * sY) = s.gpr .x2 ∧ word t.mem B (8 * sDom) = s.gpr .x4 ∧
      word t.mem B (8 * sDomLen) = s.gpr .x5 ∧ word t.mem B (8 * sK) = s.gpr .x6 ∧
      word t.mem B (8 * sRand) = s.gpr .x7 ∧ Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x8] s t := by
  have ha1' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := ha1
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = B := hB
  refine WP.mono (WP.keep [.x0, .x8] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((((s.mem.writeW (off B (8 * sX)) (s.gpr .x0)).writeW (off B (8 * sY)) (s.gpr .x2)).writeW
        (off B (8 * sDom)) (s.gpr .x4)).writeW (off B (8 * sDomLen)) (s.gpr .x5)).writeW (off B (8 * sK))
          (s.gpr .x6)).writeW (off B (8 * sRand)) (s.gpr .x7)) (by
    unfold GenerateKey.entry
    brun [Crt.stw, exec_ldrSp_x' _ (show 8 % 8 = 0 ∧ 8 < 32768 by decide) ha1', hB',
      hdr_enc (show sX < 32 by decide), hdr_enc (show sY < 32 by decide), hdr_enc (show sDom < 32 by decide),
      hdr_enc (show sDomLen < 32 by decide), hdr_enc (show sK < 32 by decide), hdr_enc (show sRand < 32 by decide),
      hw sX (by decide), hw sY (by decide), hw sDom (by decide), hw sDomLen (by decide), hw sK (by decide),
      hw sRand (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k⟩
  all_goals try (rw [hm]; simp (disch := decide) only [hdrStore_hdr, word_writeW_self]; done)
  rw [hm]
  intro x hx
  have e : ∀ i, i < 32 → ∀ (m : Mem) (v : BitVec 64), (m.writeW (off B (8 * i)) v) x = m x := fun i hi m v =>
    writeW_outside m B v (d := 8 * i) (by omega) x (by omega)
  rw [e sRand (by decide), e sK (by decide), e sDomLen (by decide), e sDom (by decide), e sY (by decide),
    e sX (by decide)]

/-- After the entry. -/
def G1 (p : GkP) (rb : List Byte) (t : State) : Prop := E1 (p.D₀ rb) t ∧ Dst p t ∧ Ok p rb

theorem cr_g1 (p : GkP) (rb : List Byte) (s : State) (h : CR p rb s) :
    WP isa (.block GenerateKey.entry) s fun t => G1 p rb t ∧ KX s t := by
  have hb := cr_base p rb s h
  have hd := cr_dst p rb s h
  have ho := cr_ok h
  have c := gkCtx_of h.1
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hs : Scr s p.B p.Z := hb.scr
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, -, hxp, hyp, hrp, -⟩ := h
  have hw : ∀ i < 32, InRegions s.wr (off p.B (8 * i)) 8 := fun i hi => hs.st (by omega)
  refine WP.mono (gkEntry_ok hB hw c.ha1) fun t ⟨h0, hX, hY, hD, hL, hK, hR, ho', k⟩ => ?_
  refine ⟨⟨⟨hb.keep (InScr.of_outside ho' (show 0 + 8 * 32 ≤ p.Z by omega)) k, h0, ?_⟩, hd.keep k, ho⟩,
    k.mono (by decide)⟩
  intro q hq
  simp only [FD.hdr, GkP.D₀, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · show word t.mem p.B (8 * sDomLen) = BitVec.ofNat 64 p.dl; rw [hL, ← hdl, ofNat_toNat64]
  · show word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k; rw [hK, ← hk, ofNat_toNat64]
  · exact hX.trans hxp
  · exact hY.trans hyp
  · exact hR.trans hrp

/-! ## The scalar's octets -/

/-- After `domHead`. -/
def GC (p : GkP) (rb : List Byte) (t : State) : Prop := CE (p.D₀ rb) t ∧ Dst p t ∧ Ok p rb

theorem g1_gc (p : GkP) (rb : List Byte) (t : State) (h : G1 p rb t) :
    WP isa (.block domHead) t fun u => GC p rb u ∧ KX t u :=
  WP.mono (e1_ce _ t h.1) fun _ ⟨hu, k⟩ => ⟨⟨hu, h.2.1.keep k, h.2.2⟩, k⟩

/-- In the inner workspace, with the random octets an input. -/
def GI (p : GkP) (rb : List Byte) (t : State) : Prop := (∃ mi, In (p.D₀ rb) mi t) ∧ Dst p t ∧ Ok p rb

theorem gc_gi (p : GkP) (rb : List Byte) (t : State) (h : GC p rb t) (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) t fun u => GI p rb u ∧ KX t u :=
  WP.mono (ce_in _ t h.1 he) fun _ ⟨hu, k⟩ => ⟨⟨hu, h.2.1.keep k, h.2.2⟩, k⟩

/-- In the outer workspace. -/
def GP (p : GkP) (rb : List Byte) (t : State) : Prop := (∃ mi, Pa (p.D₀ rb) mi t) ∧ Dst p t ∧ Ok p rb

theorem gi_gp (p : GkP) (rb : List Byte) (t : State) (h : GI p rb t) :
    WP isa (.block [leave]) t fun u => GP p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, hd, ho⟩ := h
  exact WP.mono hI.leave fun u ⟨hu, k⟩ => ⟨⟨⟨mi, hu⟩, hd.keep k, ho⟩, k⟩

/-- After the bound's scan. -/
def GS (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₀ rb) mi t ∧ word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - (p.D₀ rb).bl) ∧
    t.gpr .x3 = BitVec.ofNat 64 (p.D₀ rb).bc.toNat) ∧ Dst p t ∧ Ok p rb

theorem gp_gs (p : GkP) (rb : List Byte) (t : State) (h : GP p rb t) :
    WP isa (seqs GenerateKey.bound) t fun u => GS p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP⟩, hd, ho⟩ := h
  exact WP.mono hP.bound fun u ⟨⟨hu, _, hEl, h3, _⟩, k⟩ => ⟨⟨⟨mi, hu, hEl, h3⟩, hd.keep k, ho⟩, k⟩

/-- The smear of an octet. -/
theorem smear_ok {t : State} {c : Byte} (h3 : t.gpr .x3 = BitVec.ofNat 64 c.toNat) :
    WP isa (.block GenerateKey.smear) t fun u =>
      (u.gpr .x3 = BitVec.ofNat 64 (KeyScalar.smearN c.toNat) ∧ u.mem = t.mem) ∧ Keep [.x3, .x5] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  unfold GenerateKey.smear
  brun [h3]
  have hc := c.isLt
  have hs : KeyScalar.smearN c.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (KeyScalar.smearN_lt _ hc) (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, KeyScalar.smearN] at hs ⊢
  rw [Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt hs]

/-- The loop's registers. -/
def GB (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₀ rb) mi t ∧ t.gpr .x1 = p.rp ∧ t.gpr .x2 = p.xp ∧ t.gpr .x10 = 0 ∧
    t.gpr .x11 = BitVec.ofNat 64 (p.D₀ rb).bl ∧ t.gpr .x12 = p.msk rb ∧ t.gpr .x13 = BitVec.ofNat 64 255 ∧
    t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 p.k) ∧ Dst p t ∧ Ok p rb

/-- The block's loads. -/
theorem setBlk_ok {t : State} {B xp rp : Addr} {k bl : Nat} {msk : BitVec 64} (h0 : t.gpr .x0 = B)
    (h3 : t.gpr .x3 = msk) (hK : word t.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hL : word t.mem B (8 * sEl) = BitVec.ofNat 64 (k - bl)) (hX : word t.mem B (8 * sX) = xp)
    (hR : word t.mem B (8 * sRand) = rp) (hbl : bl ≤ k) (hk : k < 2 ^ 32)
    (hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8) :
    WP isa (.block [mov .x12 .x3, ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, ldh .x1 sRand,
        movi .x13 255, movi .x7 0, movi .x10 0, ldh .x14 sK]) t fun u =>
      (u.gpr .x1 = rp ∧ u.gpr .x2 = xp ∧ u.gpr .x10 = 0 ∧ u.gpr .x11 = BitVec.ofNat 64 bl ∧ u.gpr .x12 = msk ∧
        u.gpr .x13 = BitVec.ofNat 64 255 ∧ u.gpr .x7 = 0 ∧ u.gpr .x14 = BitVec.ofNat 64 k ∧ u.mem = t.mem) ∧
      Keep [.x1, .x2, .x7, .x10, .x11, .x12, .x13, .x14] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, h3, hdr_enc (show sK < 32 by decide), hdr_enc (show sEl < 32 by decide), hdr_enc (show sX < 32 by decide),
    hdr_enc (show sRand < 32 by decide), hl sK (by decide), hl sEl (by decide), hl sX (by decide),
    hl sRand (by decide), hK, hL, hX, hR]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem gs_gb (p : GkP) (rb : List Byte) (t : State) (h : GS p rb t) :
    WP isa (.block (GenerateKey.smear ++ [mov .x12 .x3, ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11,
      ldh .x2 sX, ldh .x1 sRand, movi .x13 255, movi .x7 0, movi .x10 0, ldh .x14 sK])) t fun u =>
      GB p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hL, h3⟩, hd, ho⟩ := h
  have hb := hP.1
  have hk2 := hb.k2
  have hbl := hb.bl_lt
  refine WP.block_append_iff.mpr (WP.mono (smear_ok h3) fun t₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_)
  have hP₁ := hP.keep hm₁ k₁ (by decide)
  have hO := hP₁.outer
  have hs := hP₁.2.2.2.2.1
  refine WP.mono (setBlk_ok (bl := (p.D₀ rb).bl) hO.x0 h3₁ (hs.get (i := sK) (v := BitVec.ofNat 64 (p.D₀ rb).k)
    (by simp)) (by rw [hm₁]; exact hL) (hs.get (i := sX) (v := p.xp) (by simp [GkP.D₀]))
    (hs.get (i := sRand) (v := p.rp) (by simp [GkP.D₀])) (by omega) (by omega) fun i hi => hO.ld hi)
    fun u ⟨⟨h1, h2, h10, h11, h12, h13, h7, h14, hm⟩, k⟩ =>
      ⟨⟨⟨mi, hP₁.keep hm k (by decide), h1, h2, h10, h11, h12, h13, h7, h14⟩, hd.keep (k₁.trans k), ho⟩,
        keep_trans (k₁.mono (by decide)) (k.mono (by decide))⟩

/-- The scalar's octets in `x`: the run's data with them an input. -/
def GX (p : GkP) (rb : List Byte) (t : State) : Prop := (∃ mi, Pa (p.D₁ rb) mi t) ∧ Dst p t ∧ Ok p rb

theorem cb_eq {rb : List Byte} {ld i : Nat} (t : Byte) (hld : ld < rb.length) (hi : i < rb.length) :
    cb rb ld t i = (KeyScalar.cut rb ld t)[i]'(by rw [KeyScalar.cut_length t hld]; exact hi) := by
  rw [KeyScalar.cut_get t hld hi, cb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem xo_length (p : GkP) (rb : List Byte) (hbl : (p.D₀ rb).bl < p.k) (ho : Ok p rb) :
    (p.xo rb).length = p.k := by
  rw [GkP.xo, KeyScalar.cut_length _ (by rw [ho.1]; exact hbl), ho.1]

theorem gb_gx (p : GkP) (rb : List Byte) (t : State) (h : GB p rb t) :
    WP isa (countLoop .x14 VG.Impl.Ffdh.AArch64.Domain.GenerateKey.cutBody) t fun u => GX p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, h1, h2, h10, h11, h12, h13, h7, h14⟩, hd, ho⟩ := h
  obtain ⟨hrl, ⟨gXY, gXD, gXR, gYD, nX, nY, nD, nR⟩, -⟩ := id ho
  have hb := hP.1
  have hk1 : 64 ≤ p.k := hb.k1
  have hk2 : p.k ≤ 1024 := hb.k2
  have hbl := hb.bl_lt
  simp only [GkP.D₀_k] at hbl
  have hr : Src t p.B p.Z p.rp rb := hb.srcs (p.rp, rb) (by simp [GkP.D₀])
  refine WP.mono (cut_ok (k := p.k) (rb := rb) (by omega) (by omega) hbl h1 h2 h10 h11 h12 h13 h7 h14
    (fun i hi => hr.rd i (by omega))
    (fun i hi => by
      rw [hr.val i (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some])
    (fun i hi => (hd i hi).1.1)
    (fun i hi i' hi' => (ne_of_disj gXR nX nR hi' hi).symm)) fun u hI => ?_
  have k := hI.keep
  have hout : Outside p.B p.Z (2 ^ 64) t.mem u.mem := outside_of_frame (fun j hj => (hd j hj).1.2) hI.frame
  have hxl := xo_length p rb hb.bl_lt ho
  refine ⟨⟨⟨mi, hP.out (D := p.D₀ rb) hout k.rd k.wr ((k.gpr .x0 (by decide)).trans hP.2.2.2.2.2.2)
    (fun i hi => hI.frame _ fun j hj => (ne_of_disj gXD nX nD hj (by have := hb.doml; simp only [GkP.D₀_dl, GkP.D₀_dom] at this hi; omega)).symm) ?_⟩,
    hd.keep k, ho⟩, k.mono (by decide)⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hxl] at hi
    have := (hd i hi).1.1
    rw [← k.wr] at this
    obtain ⟨r, hr', hc⟩ := this
    exact ⟨r, List.mem_append_right _ hr', hc⟩
  · rw [hxl] at hi
    rw [hI.bytes i hi, cb_eq _ (by omega) (by omega)]
    rfl
  · rw [hxl] at hi
    exact (hd i hi).1.2

@[simp] theorem GkP.D₁_B (p : GkP) (rb : List Byte) : (p.D₁ rb).B = p.B := rfl
@[simp] theorem GkP.D₁_Z (p : GkP) (rb : List Byte) : (p.D₁ rb).Z = p.Z := rfl
@[simp] theorem GkP.D₁_k (p : GkP) (rb : List Byte) : (p.D₁ rb).k = p.k := rfl
@[simp] theorem GkP.D₁_dl (p : GkP) (rb : List Byte) : (p.D₁ rb).dl = p.dl := rfl
@[simp] theorem GkP.D₁_dp (p : GkP) (rb : List Byte) : (p.D₁ rb).dp = p.dp := rfl
@[simp] theorem GkP.D₁_dom (p : GkP) (rb : List Byte) : (p.D₁ rb).dom = p.dom := rfl

/-- In the inner workspace, with the scalar's octets an input. -/
def G2 (p : GkP) (rb : List Byte) (t : State) : Prop := (∃ mi, In (p.D₁ rb) mi t) ∧ Dst p t ∧ Ok p rb

theorem gx_g2 (p : GkP) (rb : List Byte) (t : State) (h : GX p rb t) :
    WP isa (.block [enter]) t fun u => G2 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP⟩, hd, ho⟩ := h
  exact WP.mono hP.enter fun u ⟨hu, k⟩ => ⟨⟨⟨mi, hu⟩, hd.keep k, ho⟩, k⟩

/-- The scalar, as the code computes it. -/
abbrev GkP.X (p : GkP) (rb : List Byte) : Nat := Spec.Rsa.os2ip (p.xo rb)

/-- The inner workspace's base. -/
abbrev GkP.G (p : GkP) (rb : List Byte) : Addr := off (p.D₁ rb).B (inner (p.D₁ rb).w)

/-- With the scalar in `aXm`. -/
def G3 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, In (p.D₁ rb) mi t ∧ wv t.mem (p.G rb) (slot (p.D₁ rb).w aXm) (p.D₁ rb).w = p.X rb) ∧ Ok p rb

theorem g2_lpre (p : GkP) (rb : List Byte) (t : State) (h : G2 p rb t) :
    LPre aXm sX sK ((p.D₁ rb).ld p.xp p.k) t := by
  obtain ⟨⟨mi, hI⟩, hd, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hx : Src t p.B p.Z p.xp (p.xo rb) := hb.srcs (p.xp, p.xo rb) (by simp)
  have hxl := xo_length p rb hb.bl_lt ho
  have := hb.k1
  have := hI.lpre (sp := sX) (sl := sK) (show aXm < 8 by decide) (by decide) (by decide) (hs.get (i := sX) (v := p.xp) (by simp [GkP.D₀]))
    (by rw [hxl]; exact hs.get (i := sK) (by simp)) hx (by rw [hxl]; simp at this ⊢; omega) (by rw [hxl]; simp)
  rw [hxl] at this
  exact this

theorem g2_g3 (p : GkP) (rb : List Byte) (t : State) (h : G2 p rb t) :
    WP isa (seqs (Crt.loadArr aXm sX sK)) t fun u => G3 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hI⟩, hd, ho⟩ := h
  have hb := hI.1
  have hs := hI.2.2.2.2.1
  have hx : Src t p.B p.Z p.xp (p.xo rb) := hb.srcs (p.xp, p.xo rb) (by simp)
  have hxl := xo_length p rb hb.bl_lt ho
  have := hb.k1
  exact WP.mono (hI.load (show aXm < 8 by decide) (by decide) (by decide) (by decide) (by decide)
    (hs.get (i := sX) (v := p.xp) (by simp [GkP.D₀])) (by rw [hxl]; exact hs.get (i := sK) (by simp)) hx
    (by rw [hxl]; simp at this ⊢; omega) (by rw [hxl]; simp)) fun u ⟨⟨hu, hv, _⟩, k⟩ =>
      ⟨⟨⟨mi, hu, hv⟩, ho⟩, k⟩

end VG.Proof.Ffdh.AArch64.GenerateKey
