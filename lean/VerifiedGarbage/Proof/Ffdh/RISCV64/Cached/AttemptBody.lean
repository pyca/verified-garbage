module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Scalar
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Out
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the cached attempt's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: the body

`goodC_ok`: x in range, `g^x mod p` by the context's comb, then as
`vg_ffdh_derive_public` (`exOut_split`, the status). `bodyC_ok`: x cut from
`rand` at the context's width, its range, out of range zeros and the status
2, in range `goodC_ok`, then x's octets masked by the status 1.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.GenerateKey (XR maskPre_ok masked_ok outX_scr)
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.Bignum.RISCV64.Win (WinO A)
open VG.Proof.Bignum (slot)

/-- What the comb reads besides the exchange's state: the context at `C`
(its address and its three public words in the header's words 4–7), its
entries and `R² mod p`, for the width `bits` and g `G`. -/
structure CX (x : XD) (C : Addr) (bits G : Nat) (s : State) : Prop where
  hC : word s.mem x.S 32 = C
  hbw : word s.mem x.S 40 = BitVec.ofNat 64 bits
  hyw : word s.mem x.S 48 = BitVec.ofNat 64 ((bits + 7) / 8)
  hRw : word s.mem x.S 56 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  ctx : CtxRd s x.S x.Z C x.w
  sepX : ∀ y, ofs C y < 8 * ctxWords x.w → x.k ≤ ofs x.X y
  sepO : ∀ y, ofs C y < 8 * ctxWords x.w → x.k ≤ ofs x.O y
  ents : ∀ a < 32, ent s.mem C x.w a = combM G x.p x.w (Spec.Rsa.FixedBaseComb.exponent bits a)
  r2 : wordsVal s.mem C (rowOff x.w 1) x.w = 2 ^ (64 * x.w) * 2 ^ (64 * x.w) % x.p
  hG : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) = G
  b1 : 1 ≤ bits
  bk : bits ≤ 8 * x.k

/-- `CX` after a change of the arrays. -/
theorem CX.keep {x : XD} {C : Addr} {bits G : Nat} {s t : State} (h : CX x C bits G s) (hc : Ctx x s)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : Arr x s.mem t.mem) : CX x C bits G t := by
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d := fun d hd =>
    Outside.word hm (Or.inl hd) (by have := hc.scr.nowrap; omega_arith)
  have hctx : Outside C (8 * ctxWords x.w) (2 ^ 64) s.mem t.mem := ctx_of_scr hm (by omega_arith) h.ctx.sep
  have hr1 := row_fits (w := x.w) (j := 1) (by decide)
  exact ⟨by rw [hw 32 (by decide)]; exact h.hC, by rw [hw 40 (by decide)]; exact h.hbw,
    by rw [hw 48 (by decide)]; exact h.hyw, by rw [hw 56 (by decide)]; exact h.hRw, h.ctx.congr hrd hwr, h.sepX,
    h.sepO, fun a ha => by rw [ent_keep hctx h.ctx.hn ha]; exact h.ents a ha,
    by rw [Outside.wordsVal hctx (Or.inl hr1) (by have := h.ctx.hn; omega_arith)]; exact h.r2,
    by rw [Pub.bytes_apart hm (by omega_arith) hc.sepY]; exact h.hG, h.b1, h.bk⟩

/-- `CX` after a change of x's octets. -/
theorem CX.ofX {x : XD} {R C : Addr} {bits G : Nat} {s t : State} (h : CX x C bits G s) (hc : Ctx x s)
    (hx : XR x R s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (ho : Outside x.X 0 x.k s.mem t.mem)
    (hYD : x.Y = off x.D x.k) : CX x C bits G t := by
  have hn := hc.scr.nowrap
  have hL := hc.hL
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d := fun d hd =>
    Pub.Outside.word_apart ho hx.sepSX (by omega_arith) (by have := hc.hZ; unfold slot hdrBytes at this; omega_arith) hn
  have hctx : Outside C (8 * ctxWords x.w) (2 ^ 64) s.mem t.mem := fun y hy => ho y (Or.inr (by
    rcases hy with hy | hy
    · have := h.sepX y hy; omega_arith
    · have := (y - C).isLt; simp only [ofs] at hy; omega_arith))
  have hr1 := row_fits (w := x.w) (j := 1) (by decide)
  exact ⟨by rw [hw 32 (by decide)]; exact h.hC, by rw [hw 40 (by decide)]; exact h.hbw,
    by rw [hw 48 (by decide)]; exact h.hyw, by rw [hw 56 (by decide)]; exact h.hRw, h.ctx.congr hrd hwr, h.sepX,
    h.sepO, fun a ha => by rw [ent_keep hctx h.ctx.hn ha]; exact h.ents a ha,
    by rw [Outside.wordsVal hctx (Or.inl hr1) (by have := h.ctx.hn; omega_arith)]; exact h.r2,
    by
      rw [Pub.bytes_apart (Z := x.k) ho (by omega_arith) fun i hi y hy => by
        have h' := hx.sepDX (x.k + i) (by omega_arith) y hy
        rw [← Derive.off_off, ← hYD] at h'; exact h']
      exact h.hG, h.b1, h.bk⟩

theorem status_bv (c : Prop) [Decidable c] :
    BitVec.ofNat 64 3 - (BitVec.ofNat 64 (if c then 1 else 0) <<< 1) = BitVec.ofNat 64 (if c then 1 else 3) := by
  split <;> decide

/-- x in range: `g^x mod p` by the comb to `y` or zeros, the status 1 or 3. -/
theorem goodC_ok {x : XD} {C : Addr} {bits G : Nat} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0)
    (hcx : CX x C bits G s) (hxl : x.xl = x.k) :
    let z := Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.k)) 0) x.p
    WP isa good s fun t =>
      (Spec.Rsa.bytesAt t.mem x.O x.k = (if 1 < z ∧ z < x.p - 1 then Spec.Rsa.i2osp z x.k else List.replicate x.k 0) ∧
        t.gpr .a0 = BitVec.ofNat 64 (if 1 < z ∧ z < x.p - 1 then 1 else 3)) ∧
      t.gpr .s6 = x.S ∧ ∃ m, Arr x s.mem m ∧ Outside x.O 0 x.k m t.mem := by
  intro z
  obtain ⟨hb, hp, h0⟩ := h
  have hc := hb.ctx
  have hv := h0.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv hc.k64
  have hk := hc.k64; have hk' := hc.k1024
  have hZ := hc.hZ
  have hn := hc.scr.nowrap
  have hpk : x.p < 256 ^ x.k := by
    have := VG.Proof.Bignum.os2ip_lt (x.db.take x.k)
    rwa [take_len hc.hL.1 hc] at this
  have hP : 0 < x.p := by omega_arith
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hlen : (Spec.Rsa.bytesAt s.mem x.X x.k).length = x.k := VG.Proof.Bignum.bytesAt_length _ _ _
  have ci : CombIn s x.S C x.X x.Z x.w (Spec.Rsa.bytesAt s.mem x.X x.k) x.p G bits := by
    refine ⟨hc.scr, by omega_arith, by omega_arith, hZ, hb.a7, hb.s5, hb.t0, hb.s6, hc.hX.trans (BitVec.add_zero _),
      by rw [hlen]; exact hb.s11,
      hcx.hC, hcx.hRw, hcx.ctx, hcx.ents, hcx.r2, hp, fun n hn => hc.rdX n (by rw [hlen] at hn; omega_arith),
      fun n hn => hc.sepX n (by rw [hlen] at hn; omega_arith), fun n hn => by simp [Spec.Rsa.bytesAt, off],
      by rw [hlen]; omega_arith,
      ⟨hf.1, hf.2.1, (Rsa.FixedBaseComb.rows_small (show bits ≤ 8192 by have := hcx.bk; omega_arith)).1⟩,
      by have := hcx.b1; omega_arith⟩
  unfold good exOut
  refine WP.seq (WP.mono (comb_ok ci) fun s₁ ⟨⟨z1, p1, o1⟩, k1⟩ => ?_)
  replace z1 : wordsVal s₁.mem x.S (slot x.w 4) x.w = z := z1
  have ar1 : Arr x s.mem s₁.mem := arr_of o1 (by unfold slot hdrBytes; omega_arith) (by
    have := Win.slot24 x.w; unfold slot hdrBytes at hZ this ⊢; omega_arith)
  have hc1 := hc.keep k1.2.1 k1.2.2 ar1
  have rw1 : RW x s₁ := ⟨(k1.gpr (by decide)).trans hb.s6, (k1.gpr (by decide)).trans hb.a7,
    (k1.gpr (by decide)).trans hb.s5, (k1.gpr (by decide)).trans hb.t0, (k1.gpr (by decide)).trans hb.s11⟩
  have hzP : z < x.p := by
    show Spec.Rsa.powMod G _ x.p < x.p
    rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP
  refine WP.seq (WP.seq (WP.mono (exOut_split hc1 rw1 p1 hf.1 (by rw [z1]; exact hzP) hpk) fun s₇ ⟨_, h7⟩ =>
      WP.seq (WP.mono h7 fun s₈ ⟨_, h8⟩ => WP.mono h8 fun t op => ?_)))
  obtain ⟨m, am, om⟩ := op.mem
  refine WP.mono (WP.keep [.a0, .t2] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 3 - (t.gpr .a0 <<< 1) ∧
    u.mem = t.mem) (by unfold Derive.status; brun [fin64_exec_li_lit (show 3 < 2048 by decide)]) (by rfl) (by rfl))
    fun u ⟨⟨ua, um⟩, ku⟩ => ⟨?_, (ku.gpr (by decide)).trans op.s6, m, ar1.trans am, by rw [um]; exact om⟩
  rw [um, ua, op.out, op.a0, z1, status_bv]
  exact ⟨rfl, rfl⟩

/-! ## The body -/

/-- The status of x, from its value. -/
def stat (x : XD) (m : Mem) (G sv : Nat) : Nat :=
  if ¬ (0 < sv ∧ sv < bnd m x.D x.k x.L x.p) then 2 else
    if 1 < G ^ sv % x.p ∧ G ^ sv % x.p < x.p - 1 then 1 else 3

theorem stat_lt (x : XD) (m : Mem) (G sv : Nat) : stat x m G sv < 4 := by
  unfold stat; split <;> [decide; split <;> decide]

/-- x: `rand` cut at the width `bits`. -/
abbrev xoOf (m : Mem) (R : Addr) (k bits : Nat) : List Byte := cut (Spec.Rsa.bytesAt m R k) (k - (bits + 7) / 8) (tbOf bits)

/-- What the body leaves, from `s` after p's check. -/
def GPost (x : XD) (R : Addr) (bits G : Nat) (s t : State) : Prop :=
  (Spec.Rsa.modulusValid x.p x.k = true →
    let sv := Spec.Rsa.os2ip (xoOf s.mem R x.k bits)
    t.gpr .a0 = BitVec.ofNat 64 (stat x s.mem G sv) ∧
      Spec.Rsa.bytesAt t.mem x.O x.k =
        (if stat x s.mem G sv = 1 then Spec.Rsa.i2osp (G ^ sv % x.p) x.k else List.replicate x.k 0) ∧
      Spec.Rsa.bytesAt t.mem x.X x.k = (if stat x s.mem G sv = 1 then xoOf s.mem R x.k bits
        else List.replicate x.k 0)) ∧
  t.gpr .s6 = x.S ∧ ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d

/-- For a valid p: the scalar, its range, the comb or zeros, and the mask of
x. -/
theorem bodyC_ok {x : XD} {R C : Addr} {bits G : Nat} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0)
    (ha : AR x s) (hx : XR x R s) (h1 : s.gpr .t1 = R) (hYD : x.Y = off x.D x.k) (hcx : CX x C bits G s) :
    WP isa body s (GPost x R bits G s) := by
  have hv := h.2.2.mp hz
  have hb := h.1
  have hc := hb.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  unfold slot hdrBytes at hZ
  have hxk : x.xl = x.k := hx.xl
  unfold body
  -- x.
  refine WP.seq (WP.mono (WP.rdwr (scalarC_ok h hz ha hx h1 hcx.b1 hcx.bk hcx.hbw hcx.hyw))
    fun s₁ ⟨⟨h41, z1, ha1, hx1, xb, xo⟩, r1, w1, _⟩ => ?_)
  have hcx1 := hcx.ofX hc hx r1 w1 xo hYD
  have hc1 := h41.1.ctx
  have hw1 : ∀ d, d + 8 ≤ 256 → word s₁.mem x.S d = word s.mem x.S d := fun d hd =>
    Pub.Outside.word_apart xo hx.sepSX (by omega_arith) (by omega_arith) hn
  have hB1 : bnd s₁.mem x.D x.k x.L x.p = bnd s.mem x.D x.k x.L x.p := by
    unfold bnd
    by_cases hq : x.L = 3 * x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart (Z := x.k) xo (by omega_arith) fun i hi y hy => by
        have h' := hx.sepDX (2 * x.k + i) (by omega_arith) y hy
        rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  change Spec.Rsa.bytesAt s₁.mem x.X x.k = xoOf s.mem R x.k bits at xb
  generalize hxo : xoOf s.mem R x.k bits = xo' at xb ⊢
  have hsv : Spec.Rsa.os2ip xo' < 2 ^ bits := by
    rw [← hxo, scalarC_value (by simp [Spec.Rsa.bytesAt]) hcx.b1 hcx.bk]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  -- x's range.
  refine WP.seq (WP.seq (WP.mono (WP.rdwr (Derive.xRange_ok h41 hv ha1)) fun s₂ ⟨⟨h42, z2, m2, a2⟩, r2, w2', _⟩ => ?_))
  rw [hxk, xb, hB1] at m2
  have hcx2 := hcx1.keep hc1 r2 w2' a2
  have hc2 := h42.1.ctx
  have hZ1 := hc1.hZ
  unfold slot hdrBytes at hZ1
  have hw2 : ∀ d, d + 8 ≤ 256 → word s₂.mem x.S d = word s₁.mem x.S d := fun d hd =>
    Outside.word a2 (Or.inl hd) (by omega_arith)
  have hX2 : Spec.Rsa.bytesAt s₂.mem x.X x.k = xo' := by
    rw [Pub.bytes_apart (Z := x.Z) a2 (by omega_arith) (by rw [← hxk]; exact hc1.sepX), xb]
  generalize hsvd : Spec.Rsa.os2ip xo' = sv at hsv m2 ⊢
  -- The branches.
  have hite : WP isa (.ite (.zero .s9) Derive.dpBad good) s₂ fun t =>
      (Spec.Rsa.bytesAt t.mem x.O x.k =
          (if stat x s.mem G sv = 1 then Spec.Rsa.i2osp (G ^ sv % x.p) x.k else List.replicate x.k 0) ∧
        t.gpr .a0 = BitVec.ofNat 64 (stat x s.mem G sv)) ∧
      t.gpr .s6 = x.S ∧ ∃ m, Arr x s₂.mem m ∧ Outside x.O 0 x.k m t.mem := by
    refine WP.ite (s₂.gpr .s9 == 0) (Steps.eval_zero _ _) (fun h9 => ?_) (fun h9 => ?_)
    · have h9' : s₂.gpr .s9 = 0 := by simpa using h9
      rw [m2] at h9'
      have hr : ¬ (0 < sv ∧ sv < bnd s.mem x.D x.k x.L x.p) := fun hr => by
        rw [decide_eq_true hr] at h9'; exact absurd h9' (by decide)
      have hst : stat x s.mem G sv = 2 := by unfold stat; rw [ite_eq_left hr]
      refine WP.mono (Derive.bad_ok h42.1 (by rw [m2, decide_eq_false hr]; rfl)) fun t ⟨⟨tb, ta⟩, t6, ot⟩ =>
        ⟨⟨by rw [hst, ite_eq_right (by decide)]; exact tb, by rw [hst]; exact ta⟩, t6, s₂.mem, Outside.refl _ _ _ _, ot⟩
    · have h9' : s₂.gpr .s9 ≠ 0 := by simpa using h9
      rw [m2] at h9'
      have hr : 0 < sv ∧ sv < bnd s.mem x.D x.k x.L x.p := by
        by_contra hr; rw [decide_eq_false hr] at h9'; exact h9' rfl
      refine WP.mono (goodC_ok h42 z2 hcx2 hxk) fun t ⟨⟨tb, ta⟩, t6, m, am, om⟩ => ⟨?_, t6, m, am, om⟩
      rw [hX2, hsvd, Rsa.FixedBaseComb.high_zero bits sv hsv, VG.Proof.Bignum.powMod_eq] at tb ta
      have hst : stat x s.mem G sv = if 1 < G ^ sv % x.p ∧ G ^ sv % x.p < x.p - 1 then 1 else 3 := by
        unfold stat; rw [ite_eq_right (fun h' => h' hr)]
      refine ⟨?_, by rw [ta, hst]⟩
      rw [tb, hst]
      by_cases hc' : 1 < G ^ sv % x.p ∧ G ^ sv % x.p < x.p - 1
      · rw [ite_eq_left hc', ite_eq_left hc', ite_eq_left rfl]
      · rw [ite_eq_right hc', ite_eq_right hc', ite_eq_right (by decide)]
  refine WP.mono (WP.rdwr hite) fun s₃ ⟨⟨⟨tO, ta⟩, t6, m, am, om⟩, r3, w3, _⟩ => ?_
  have hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem x.S d = word s.mem x.S d := fun d hd => by
    refine (Pub.Outside.word_apart om hx.sepSO (by omega_arith) (by omega_arith) hn).trans ?_
    show Mont.word m _ _ = _
    rw [Outside.word am (Or.inl hd) (by omega_arith), hw2 d hd, hw1 d hd]
  have hX3 : Spec.Rsa.bytesAt s₃.mem x.X x.k = xo' := by
    rw [Pub.bytes_apart (Z := x.k) om (by omega_arith) hx.sepXO,
      Pub.bytes_apart (Z := x.Z) am (by omega_arith) (by rw [← hxk]; exact hc2.sepX), hX2]
  -- The mask of x.
  unfold GenerateKey.maskX
  have hs3 := hc2.scr.congr (by rw [w3])
  refine WP.seq (WP.mono (maskPre_ok (X := x.X) (k := x.k) hs3 (by omega_arith) t6 ta (stat_lt _ _ _ _)
    (by rw [hw3 8 (by decide)]; exact hc.hX)
    (by rw [hw3 16 (by decide), hc.hXL, hxk])) fun s₄ ⟨⟨m4, ma1, mt5, mm⟩, k4⟩ => ?_)
  refine WP.mono (masked_ok (c := decide (stat x s.mem G sv = 1)) (by omega_arith) (by omega_arith) hx.nwX
    (by rw [k4.2.2, w3, w2', w1]; exact hx.wX) ma1 (by rw [m4]; simp) mt5) fun t ⟨⟨tb, to⟩, kt⟩ =>
      ⟨fun _ => ?_, ?_, ?_⟩
  · dsimp only
    rw [hxo, hsvd]
    refine ⟨by rw [kt.gpr (by decide), k4.gpr (by decide), ta], ?_, ?_⟩
    · rw [Pub.bytes_apart (Z := x.k) to (by omega_arith) hx.sepOX, mm, tO]
    · rw [tb, mm, hX3]
      by_cases h1 : stat x s.mem G sv = 1 <;> simp [h1]
  · exact (kt.gpr (by decide)).trans ((k4.gpr (by decide)).trans t6)
  · intro d hd
    refine (Pub.Outside.word_apart to hx.sepSX (by omega_arith) (by omega_arith) hn).trans ?_
    show Mont.word s₄.mem _ _ = _
    rw [mm, hw3 d hd]

end VG.Proof.Ffdh.RISCV64.Cached
