module

import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeCheck
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Proof.Ed448.RISCV64.VSel
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.RISCV64.VChecks
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
import VerifiedGarbage.Proof.X448.RISCV64.Setup
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeY

/-! ### `Ed448.RISCV64.VDecodeNeg`, which only this module used -/

section

/-!
# Ed448's verification on RISCV64: the negated point

`decodeNeg xo yo` writes `-x'` to `xo` and `y` to `yo`, for `x'` the decoded
x-coordinate: `(x - x) - x` if the low bit of `x` (fully reduced at `OUT`) is
the sign, else `x` (`decodeNeg_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

theorem xor_le_one' {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The slots of `-x'` and `y`, above the field area and below `PK`, at multiples of 4. -/
def NegOut (xo yo : Nat) : Prop :=
  1064 ≤ xo ∧ xo + 56 ≤ PK ∧ 1064 ≤ yo ∧ yo + 56 ≤ PK ∧ (xo + 56 ≤ yo ∨ yo + 56 ≤ xo) ∧
    xo % 4 = 0 ∧ yo % 4 = 0

theorem decodeNeg_ok {s : State} (hc : VCtx b s) {xo yo : Nat} (ho : NegOut xo yo) {x y : Fe}
    (hx : FS s.mem b DXX = x) (hy : FS s.mem b DY = y)
    (hout : VG.Spec.X448.bytesAt s.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val)
    {sg : Nat} (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa (.block (decodeNeg xo yo)) s fun t => VCtx b t ∧ Rest R64.clob64 s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩] s.mem t.mem ∧
      FS t.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x ∧ FS t.mem b yo = y ∧
      FS t.mem b DK = FS s.mem b DK := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain ⟨hx1, hx2, hy1, hy2, hxy, hx4, hy4⟩ := ho
  have hPK : PK = 1456 := rfl
  have hDY : DY = 168 := rfl
  have hA := ACC_eq
  unfold decodeNeg
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS0 : SlotsOk s.mem b [DXX, DY, DK] (FS s.mem b) := fun _ _ => rfl
  refine WP.append (R64.subS (o := DTMP) (x := DXX) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc.ctx hS0) fun s1 ⟨hr1, hf1, hS1⟩ => ?_
  have hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (R64.subS (o := DNEG) (x := DTMP) (y := DXX) (by decide) (by decide) (by decide) (by decide)
    hc1.ctx hS1) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  have hf12 : Frame [FA b] s.mem s2.mem := hf1.trans hf2
  -- The mask: the low bit of `x` against the sign.
  have hb2 : s2.mem (b + BitVec.ofNat 64 OUT) = BitVec.ofNat 8 x.val := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := OUT) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact byte0 hout
  have hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact hs
  refine wp_lbz (a := b + BitVec.ofNat 64 OUT) (by decide) (by rw [hc2.a0, BitVec.add_zero])
    (by rw [← BitVec.add_zero (b + BitVec.ofNat 64 OUT)]; exact (by rw [Offset.add_add]; exact hc2.inR (by omega_arith)))
    fun s3 u3 => wp_li (by decide) fun s4 u4 => wp_and fun s5 u5 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by omega_arith)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), hc2.ctx.a3])
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr]; exact hc2.inR (by omega_arith)) fun s6 u6 => wp_xor fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_sub fun s9 u9 => ?_
  have hm9 : s9.mem = s2.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  have hr9 : Rest [.a4, .a5, .a6, .t0] s2 s9 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest (by decide)).trans (u9.rest (by decide)))))))
  have hc9 : VCtx b s9 := hc2.of_rest hr9 (by decide) (by decide)
  have hsg' : sg < 2 ^ 64 := by omega_arith
  have hm : x.val % 2 ^^^ sg ≤ 1 := xor_le_one' (by omega_arith) hsg
  have e5 : (s5.gpr .a5).toNat = x.val % 2 := by
    rw [u5.gpr, BitVec.toNat_and, u4.other _ (by decide), u4.gpr, u3.gpr, hb2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega_arith
  have e6 : (s6.gpr .a4).toNat = sg := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, hs2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega_arith
  have e7 : s7.gpr .a5 = BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    apply BitVec.eq_of_toNat_eq
    rw [u7.gpr, BitVec.toNat_xor, u6.other _ (by decide), e5, e6, toNat_imm (by omega_arith)]
  have e11 : s9.gpr .t0 = 0 - BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), e7]; rfl
  -- The selections.
  refine WP.append (sel_ok (b := b) (o := xo) (q := DNEG) (r := DXX) (by omega_arith) (by decide) (by decide)
    (by unfold DNEG; omega_arith) (by unfold DXX; omega_arith) hx4 (by decide) (by decide) hc9.ctx hm e11) fun s10 h10 => ?_
  have hc10 : VCtx b s10 := hc9.of_rest h10.rest (by decide) (by decide)
  refine WP.mono (sel_ok (b := b) (o := yo) (q := DY) (r := DY) (by omega_arith) (by decide) (by decide)
    (by unfold DY; omega_arith) (by unfold DY; omega_arith) hy4 (by decide) (by decide) hc10.ctx hm (by rw [h10.rest.gpr _ (by decide), e11]))
    fun t ht => ?_
  have hrt : Rest R64.clob64 s t :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr9.mono (by decide)).trans
      ((h10.rest.mono (by decide)).trans (ht.rest.mono (by decide)))))
  -- The values.
  have v2 : ∀ q ∈ [DNEG, DXX, DY, DK], FS s2.mem b q = upd (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX))
      DNEG (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DTMP -
        upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DXX) q := fun q hq => hS2 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> decide)
  have hx' : FS s.mem b 672 = x := hx
  have hy' : FS s.mem b 168 = y := hy
  have eN : FS s2.mem b DNEG = (x - x) - x := by
    rw [v2 DNEG (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  have eX : FS s2.mem b DXX = x := by
    rw [v2 DXX (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  have eY : FS s2.mem b DY = y := by
    rw [v2 DY (by simp)]; simp only [upd, DNEG, DTMP, DY, Nat.reduceEqDiff, ↓reduceIte, hy']
  have hxo : FS s10.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x := by
    rw [fs_pick hm h10.lo, hm9, eN, eX]
  have eK : FS s2.mem b DK = FS s.mem b DK := by
    rw [v2 DK (by simp)]; simp only [upd, DNEG, DTMP, DK, Nat.reduceEqDiff, ↓reduceIte]
  refine ⟨hc.of_rest hrt (by decide) (by decide), hrt, ?_, ?_, ?_, ?_⟩
  · refine (hf12.mono (by simp)).trans ?_
    rw [← hm9]
    exact (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  · -- `xo` is kept by the write of `yo`.
    rw [← hxo]
    have e := limb_frame (o := xo) ht.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := xo + 4 * k) (n := 4) (e := yo) (k := 4 * 14) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- `y`, kept by the write of `xo`.
    rw [fs_pick hm ht.lo]
    have e := limb_frame (o := DY) h10.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by unfold DY; omega_arith) (by omega_arith) (by omega_arith)
    rw [show FS s10.mem b DY = FS s9.mem b DY by rw [FS, V, val32_congr e]; rfl, hm9, eY]
    unfold pick VG.Proof.X25519.sel; split <;> rfl

  · -- `d`, kept by both writes.
    rw [← eK, ← hm9]
    have f : Frame [⟨b + BitVec.ofNat 64 xo, 4 * 14⟩, ⟨b + BitVec.ofNat 64 yo, 4 * 14⟩] s9.mem t.mem :=
      (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
    have e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl

end

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.VDecodeX`, which only this module used -/

section

/-! ### `Ed448.RISCV64.VRoot`, which only this module used -/

section

/-!
# Ed448 on RISCV64: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2`
(`rootQ_ok`) by X448's addition chain for the inversion as far as
`z^(2²²³ - 1)` (`R64.chain223Call_ok`), then 223 squarings and the product with
`z^(2²²² - 1)`, since `(p-3)/4 = (2²²³ - 1) 2²²³ + (2²²² - 1)` (`root_exp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Impl.X448.RISCV64.R64 (T6)
open VG.Spec.X448 (P Fe)

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

/-- `(p - 3) / 4 = (2²²³ - 1) 2²²³ + (2²²² - 1)`. -/
theorem root_exp : (2 ^ 223 - 1) * 2 ^ 223 + (2 ^ 222 - 1) = RE := by decide +kernel

section
variable {b : Addr}

theorem rootQ_ok {qs : List Nat} (hq : R64.Sep8 R qs = true) (hZ : Z2 ∈ qs)
    (hT : R64.TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .t2 = a) :
    WP isa root s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) RE)) := by
  have hZR : Z2 ≠ R := by decide
  obtain ⟨hfR, hfT, hC⟩ := R64.drop_R hq hT hc hS h0
  have hZf : Z2 ∈ qs.filter (· ≠ R) := by simp [hZ, hZR]
  unfold root
  refine WP.seq (WP.mono (R64.chain223Call_ok hfR hZf hfT hC) fun s1 h1 => ?_)
  obtain ⟨f6, _⟩ := R64.temps_get hfT (t := T6) (by decide)
  refine WP.seq (WP.mono (R64.sqnP (z := v Z2) (ea := 2 ^ 223 - 1) (by decide) (by decide) (by sep8)
    (by decide) (by simp) (by look) h1) fun s2 h2 => ?_)
  refine WP.mono (R64.opMulP (z := v Z2) (ea := (2 ^ 223 - 1) * 2 ^ 223) (eb := 2 ^ 222 - 1) (ee := RE)
    (by sep8) (by decide) (by simp) (by simp) (by look) (by look) root_exp h2) fun s3 ⟨c3, h3⟩ =>
    ⟨h3.stp, h3.ctx, fun q hq' => ?_⟩
  by_cases eR : q = R
  · subst eR
    rw [h3.slots _ List.mem_cons_self, upd_self, upd_self]
  · have hq'' : q ∈ qs.filter (· ≠ R) := by simp [hq', eR]
    have e6 : q ≠ T6 := fun e => (R64.temps_get hT (t := T6) (by decide)).2 (e ▸ hq')
    rw [h3.slots q (by repeat (first | exact hq'' | apply List.mem_cons_of_mem)), upd_of_ne _ _ eR]
    simp only [R64.chainV, upd_of_ne _ _ e6, upd_of_ne _ _ eR]

end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification on RISCV64: the candidate x-coordinate

`decodeX` computes, from `y` at `DY`, `1` at `DON` and `d` at `DK`,
`u = y² - 1` (at `DU`), `v = d y² - 1` (at `DV`), `t = u³v` (at `DT`) and
`x = t (t (uv)²)^((p-3)/4)` (at `DXX`) (`decodeX_ok`), as `recoverRef` has
them.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Spec.X448 (P Fe)

/-- The field operations of `decodeX` before the power. -/
def xOps : List FOp :=
  [.mul DYY DY DY, .sub DU DYY DON, .mul DV DK DYY, .sub DV DV DON, .mul DT DU DU, .mul DT DT DU,
    .mul DT DT DV, .mul DW DU DV, .mul DW DW DW, .mul Z2 DT DW]

theorem decodeX_eq : decodeX = R64.opsCode xOps (.seq root (Impl.X448.RISCV64.R64.mul DXX DT R)) := rfl

/-- The slots `decodeX` reads, and `R` and `Z2`. -/
def XQ : List Nat := [DY, DON, DK, R, Z2]

theorem xOps_ok : R64.opsOk xOps XQ = true := by decide

/-- The slots kept across `root`: not `DYY` and `DW`, which its chain uses. -/
def RootQ : List Nat := [R, Z2, DT, DV, DU, DY, DK]

theorem RootQ_sub : ∀ q ∈ RootQ, q ∈ outsQ xOps XQ := by decide

/-- `u`, `v`, `t` and the candidate `x` for `y`. -/
def uOf (y : Fe) : Fe := y * y - 1
def vOf (y : Fe) : Fe := Spec.Ed448.d * (y * y) - 1
def tOf (y : Fe) : Fe := uOf y * uOf y * uOf y * vOf y
def xOf (y : Fe) : Fe :=
  tOf y * VG.Proof.X448.pw (tOf y * ((uOf y * vOf y) * (uOf y * vOf y))) RE

section
variable {b : Addr}

theorem decodeX_ok {s : State} (hc : Ctx b s) {y : Fe} (hy : FS s.mem b DY = y) (hon : FS s.mem b DON = 1)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa decodeX s fun t => R64.Stp b s t ∧ Ctx b t ∧ FS t.mem b DXX = xOf y ∧ FS t.mem b DV = vOf y ∧
      FS t.mem b DU = uOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d := by
  have hy' : FS s.mem b 168 = y := hy
  have hon' : FS s.mem b 224 = 1 := hon
  have hd' : FS s.mem b 336 = Spec.Ed448.d := hd
  have h0 : R64.Cur b s (s.gpr .t2) (s.gpr .t1) XQ (FS s.mem b) s := ⟨hc, R64.Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeX_eq]
  refine R64.ops_ok xOps XQ _ s xOps_ok h0 fun s1 h1 => ?_
  refine WP.seq (WP.mono (rootQ_ok (qs := RootQ) (by decide) (by decide) (by decide) h1.ctx
    (fun q hq _ => h1.slots q (RootQ_sub q hq)) h1.t2) fun s2 ⟨hst2, hc2, hS2⟩ => ?_)
  refine WP.mono (R64.mulS (o := DXX) (x := DT) (y := R) (by decide) (by decide) (by decide) (by decide) hc2 hS2)
    fun t ⟨hrt, hft, hSt⟩ => ?_
  refine ⟨h1.stp.trans (hst2.trans ⟨hrt.mono (by decide), hft⟩), hc2.of_rest hrt (by decide), ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | rw [hSt DXX (by decide)] | rw [hSt DV (by decide)] | rw [hSt DU (by decide)]
    | rw [hSt DY (by decide)] | rw [hSt DK (by decide)]
  all_goals
    simp only [upd, runOps, xOps, FOp.out, FOp.val, DXX, DT, DV, DU, DY, DK, DW, DYY, DON, R, Z2,
      Nat.reduceEqDiff, ↓reduceIte, hy', hon', hd', xOf, tOf, uOf, vOf]
end

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's verification on RISCV64: decoding a point

`decode p xo yo` decodes the 57 bytes at `p` (RFC 8032 §5.2.3): `BAD` stays 0
exactly when they encode a point, and then `xo` and `yo` hold the
coordinates of its negation (`decode_ok`), by `decodePoint_impl`.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

theorem fin_neg_neg {n : Nat} [NeZero n] (x : Fin n) : 0 - (0 - x) = x := by grind

theorem fin_neg_sub {n : Nat} [NeZero n] (x : Fin n) : (x - x) - x = 0 - x := by rw [Fin.sub_self]

/-- The negation of the decoded x-coordinate, as `decodeNeg` selects it. -/
theorem neg_pick (x : Fe) {sg : Nat} (hsg : sg ≤ 1) :
    pick (x.val % 2 ^^^ sg) ((x - x) - x) x =
      0 - (if (x.val % 2 == 1) == (sg == 1) then x else (x - x) - x) := by
  rw [fin_neg_sub]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl <;>
    simp only [h, pick, VG.Proof.X25519.sel, Nat.reduceXor, ↓reduceIte, beq_self_eq_true,
      Nat.zero_ne_one, beq_iff_eq] <;> first | rfl | exact (fin_neg_neg x).symm

/-- The regions `decode` writes. -/
abbrev decW (b : Addr) (xo yo : Nat) : List Region :=
  yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩]

section
variable {b : Addr}

theorem decode_eq (p xo yo : Nat) : decode p xo yo =
    .seq (.block (decodeY p)) (.seq decodeCoreCall (.block (decodeNeg xo yo))) := rfl

/-- The 57 bytes at `p` in terms of the words and the last byte. -/
theorem bytes57 (m : Mem) (p : Nat) :
    Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).take 56) = yw m b p ∧
      ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).getD 56 0).toNat =
        (m (b + BitVec.ofNat 64 (p + 56))).toNat := by
  constructor
  · rw [show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
      List.take_left' (by simp [Spec.X25519.bytesAt]), Proof.Ed448.decodeLE_eq, show (56 : Nat) = 4 * 14 from rfl]
    rw [show Spec.X25519.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) =
      VG.Spec.X448.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) from rfl, leNum_bytesAt4]
    exact val32_congr fun k _ => wd_shift _ _ _ _
  · rw [getD_bytesAt _ _ (by decide), Offset.add_add]

/-- The writes of the shared core and its return-address slot. -/
abbrev coreW (b : Addr) : List Region := yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩]

/-- The decoded candidate, sign, canonical bytes and accumulated checks. -/
def CoreFacts (b : Addr) (y : Fe) (sg : Nat) (m : Mem) (t : State) : Prop :=
  FS t.mem b DXX = xOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d ∧
  t.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg ∧
  VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 (xOf y).val ∧
  (bad t.mem b = 0 ↔ bad m b = 0 ∧ vOf y * (xOf y * xOf y) = uOf y ∧ ¬ (xOf y = 0 ∧ sg = 1))

theorem decodeCore_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCore s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (yW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCore
  refine WP.seq (WP.mono (decodeX_ok hc.ctx hy hon hd)
    fun s2 ⟨hst2, hc2', hx2, hv2, hu2, hy2, hd2⟩ => ?_)
  have hc2 : VCtx b s2 := hc.of_rest hst2.rest (by decide) (by decide)
  have hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [← hs]
    exact hst2.frame _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by decide) (by decide) _
        (Region.contains_self _ _) h
  refine WP.mono (decodeCheck_ok hc2 hx2 hv2 hu2 hsg hs2)
    fun s3 ⟨hc3, hr3, hf3, hk3, hs3, hout3, hb3⟩ => ?_
  have hb2 : bad s2.mem b = bad s.mem b := by
    unfold bad
    rw [hst2.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  exact ⟨hc3, hst2.rest.trans hr3, (hst2.frame.mono (by simp [yW])).trans hf3,
    by rw [hk3 DXX (by simp), hx2], by rw [hk3 DY (by simp), hy2],
    by rw [hk3 DK (by simp), hd2], hs3.trans hs2, hout3, by rwa [hb2] at hb3⟩

/-- The shared decode call preserves its caller's return address, including
across its nested exponentiation call. -/
theorem decodeCoreCall_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCoreCall s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (coreW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCoreCall
  refine WP.seq (R64.sd_ok hc.ctx (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc1 := hc.of_rest (u1.rest []) (by decide) (by decide)
  have fs : Frame [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩] s.mem s1.mem := by
    rw [u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have keepFS {q : Nat} (hq : q + 56 ≤ DECODE_RA) : FS s1.mem b q = FS s.mem b q := by
    have e := limb_frame fs (o := q) fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      have hRA : DECODE_RA = 1712 := rfl
      exact Offset.disjoint b (.inl (by omega_using [hq, hk])) (by omega_using [hq, hk, hRA]) (by decide)
    rw [FS, V, val32_congr e]; rfl
  have hsign : s1.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) :=
    fs _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact Offset.disjoint b (d := SIGN) (n := 1) (e := DECODE_RA) (k := 8)
        (by decide) (by decide) (by decide) _ (Region.contains_self _ _) hcon
  have hbad : bad s1.mem b = bad s.mem b := by
    unfold bad
    rw [fs.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)) (by decide)]
  have hcE : VCtx b s1.callEntry := ⟨⟨hc1.ctx.a3, hc1.ctx.al, hc1.ctx.wr⟩, hc1.ws, hc1.a0⟩
  obtain ⟨tr, s2, he, hc2, hr2, hf2, facts⟩ := decodeCore_ok hcE
    ((keepFS (q := DY) (by decide)).trans hy) ((keepFS (q := DON) (by decide)).trans hon)
    ((keepFS (q := DK) (by decide)).trans hd) hsg (hsign.trans hs)
  have hra := hr2.gpr .ra (by decide)
  have hret : isa.ret s1.callEntry s2 = some s2 := by simp only [isa, ret, hra, ↓reduceIte]
  refine WP.seq ⟨_, s2, Exec.call (call_callEntry s1) he hret, ?_⟩
  have saved : s2.mem.readW (b + BitVec.ofNat 64 DECODE_RA) 64 = s.gpr .ra := by
    rw [hf2.readW (Region.contains_self _ (64 / 8)) ?_ (by decide), State.callEntry_mem,
      u1.mem, Mem.readW_writeW_self64]
    intro r hr
    simp only [yW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base b (by decide) (by decide)
    all_goals exact Offset.disjoint b (by decide) (by decide) (by decide)
  refine R64.ld_ok hc2.ctx (by decide) (by decide) fun s3 u3 => WP.block_nil ?_
  have rest : Rest R64.work s s3 := by
    refine ⟨?_, u3.rd.trans (hr2.rd.trans u1.rd), u3.wr.trans (hr2.wr.trans u1.wr),
      u3.sp.trans (hr2.sp.trans u1.sp)⟩
    intro r hr
    by_cases er : r = .ra
    · subst r; exact u3.gpr.trans saved
    · rw [u3.other r er, hr2.gpr r hr,
        State.callEntry_gpr s1 (by
          have hn : ∀ (r : Reg), r ∉ R64.work → r ≠ Reg.ra → r ∉ linkRegs := by
            intro r; cases r <;> simp [R64.work, linkRegs]
          exact hn r hr er), u1.gpr]
  refine ⟨hc2.of_rest (u3.rest (ws := [.ra]) (by decide)) (by decide) (by decide), rest, ?_, ?_⟩
  · rw [u3.mem]
    exact (fs.mono (by simp [coreW])).trans (hf2.mono (by simp [coreW]))
  · unfold CoreFacts at facts ⊢
    rw [u3.mem]
    simpa only [State.callEntry_mem, hbad] using facts

theorem decode_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p)
    (hp' : p + 57 ≤ 1696) (hp4 : p % 4 = 0) {xo yo : Nat} (ho : NegOut xo yo) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa (decode p xo yo) s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (decW b xo yo) s.mem t.mem ∧
      FS t.mem b DK = Spec.Ed448.d ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)).isSome) ∧
      ∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57) = some pt →
        FS t.mem b xo = 0 - pt.X ∧ FS t.mem b yo = pt.Y ∧ pt.Z = 1 := by
  rw [decode_eq]
  refine WP.seq (WP.mono (decodeY_ok hc hp hp' hp4) fun s1 ⟨hc1, hr1, hf1, hy1, hon1, hk1, hs1, hb1⟩ => ?_)
  generalize hB : (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat = B at hs1 hb1
  have hBl : B < 256 := by rw [← hB]; exact BitVec.isLt _
  have hsg : B / 128 ≤ 1 := by omega_using [hB]
  generalize hY : VG.Proof.X448.toFe (yw s.mem b p) = y
  have hy : FS s1.mem b DY = y := by rw [FS, hy1, hY]
  have hon : FS s1.mem b DON = 1 := by rw [FS, hon1]; rfl
  refine WP.seq (WP.mono (decodeCoreCall_ok hc1 hy hon (hk1.trans hd) hsg hs1)
    fun s3 ⟨hc3, hr3, hf3, hx3, hy3, hd3, hs3, hout3, hb3⟩ => ?_)
  refine WP.mono (decodeNeg_ok hc3 ho hx3 hy3 hout3 hsg hs3)
    fun t ⟨hct, hrt, hft, hxt, hyt, hkt⟩ => ?_
  obtain ⟨ho1, ho2, ho3, ho4, ho5, -, -⟩ := ho
  have hPK : PK = 1456 := rfl
  obtain ⟨o1, o2, o3, o4⟩ := offs
  -- The code's view of `decodePoint`.
  obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem p
  rw [hB] at eB
  have hdp := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)
    (by simp [Spec.Ed448.bytesAt]) _ B e56 eB y (uOf y) (vOf y) (tOf y) (xOf y) hY rfl rfl rfl (by
      rw [xOf, Proof.Ed448.rootPow_eq, VG.Proof.X448.pow_pw]; rfl)
  have hbt : bad t.mem b = bad s3.mem b := by
    unfold bad
    rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      all_goals exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)) (by decide)]
  refine ⟨hct, hr1.mono (by decide) |>.trans (hr3.trans (hrt.mono (by decide))), ?_,
    by rw [hkt, hd3], ?_, ?_⟩
  · -- The frame.
    refine (hf1.mono (by simp [decW])).trans ((hf3.mono (by simp [coreW, decW])).trans (hft.mono ?_))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [decW]
  · -- The checks.
    rw [hbt, hb3, hb1, hdp]
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC, Option.isSome_some]
      exact ⟨fun h => ⟨h.1.1, rfl⟩, fun h => ⟨⟨h.1, hC.1.2, hC.1.1⟩, hC.2⟩⟩
    · rw [ite_eq_right hC, Option.isSome_none]
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => absurd ⟨⟨h3, h2⟩, h4⟩ hC, fun h => absurd h.2 (by decide)⟩
  · intro pt hpt
    rw [hdp] at hpt
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC] at hpt
      cases Option.some.inj hpt
      exact ⟨by rw [hxt, neg_pick _ hsg], hyt, rfl⟩
    · rw [ite_eq_right hC] at hpt
      exact absurd hpt (by simp)

end

end VG.Proof.Ed448.RISCV64
