module

import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Half
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The inversion's rows

A row of a batch (`Divstep.row`) leaves five words `W` at `t` with
`W + 2²⁵⁶ (ka + kb) ≡ c + X' a + Y' b` (mod `2³²⁰`) (`row_ok`): `a`, `b` the
magnitudes in `ma`, `mb`, `X'`, `Y'` the four words at `xo`, `yo`
complemented by the masks `sa`, `sb`, `c` the carry in `car`, and `ka`, `kb`
the corrections of the tops (`corrV`). Exactly, given magnitudes of at most
`2⁶²`: the words below the top carry nothing out. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Proof.X25519.AArch64 (exec_eor_x exec_and_x exec_sub_x exec_add_x exec_lsr)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (ldx corr digit top row half)

variable {large : Bool}

/-- The correction of a row's top for a word `x` (complemented) and magnitude
`m`: `m` if `x`'s sign is set (`signed`), or if the mask `r` is (else). -/
def corrV (signed : Bool) (x m r : Word) : Word := if signed then ((0 : Word) - (x >>> 63)) &&& m else r &&& m

theorem ldx_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : o % 8 = 0)
    (ho' : o + 8 ≤ workSize large) {r : Reg} (hr : r ≠ .x8) :
    WP isa (.block (ldx o r)) s fun t =>
      t.gpr .x8 = word s.mem base o ^^^ s.gpr r ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [ldx, runBlock_cons, runStep_some, runBlock_nil, load_sc hs ho ho', exec_eor_x,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, hr, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr'
    simp only [RegUpd.gpr_write, hr', ite_false]

theorem corr_ok (s : State) (signed : Bool) {d m r : Reg} (hz : s.gpr .x12 = 0)
    (hd12 : d ≠ .x12) (hmd : m ≠ d) :
    WP isa (.block (corr signed d m r)) s fun t =>
      t.gpr d = 0 - corrV signed (s.gpr .x8) (s.gpr m) (s.gpr r) ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  cases signed
  · simp only [corr, Bool.false_eq_true, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
      exec_and_x, exec_sub_x, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [RegUpd.gpr_write, Ne.symm hd12, hz, corrV, ite_true,
        ite_false, Bool.false_eq_true, BitVec.setWidth_eq]
    · simp only [List.mem_singleton] at hr'
      simp only [RegUpd.gpr_write, hr', ite_false]
  · simp only [corr, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
      exec_and_x, exec_sub_x, exec_lsr (by decide : 63 < 64), Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [RegUpd.gpr_write, Ne.symm hd12, hmd, hz, corrV, ite_true,
        ite_false, BitVec.setWidth_eq]
    · simp only [List.mem_singleton] at hr'
      simp only [RegUpd.gpr_write, hr', ite_false]

theorem st_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat} (ha : d % 8 = 0)
    (hd : d + 8 ≤ workSize large) (r : Reg) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ KeepRegs [] s t :=
  WP.block_cons_iff.mpr ⟨_, store_sc hs ha hd r, WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-- The registers of a row: none is a temporary, `x0` or `x12`. -/
def RowRegs (ma sa mb sb : Reg) : Prop :=
  ∀ r ∈ [ma, sa, mb, sb], r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧
    r ≠ .x10 ∧ r ≠ .x12

instance (ma sa mb sb : Reg) : Decidable (RowRegs ma sa mb sb) := by
  unfold RowRegs; exact inferInstance

theorem digit_arith {W PX PY w1 c1 e1 w c e : Nat} (hW : W < 2 ^ 64)
    (hPX : PX ≤ (2 ^ 64 - 1) * 2 ^ 62) (hPY : PY ≤ (2 ^ 64 - 1) * 2 ^ 62)
    (h1 : w1 + 2 ^ 64 * c1 + 2 ^ 128 * e1 = W + 2 ^ 64 * 0 + PX)
    (h2 : w + 2 ^ 64 * c + 2 ^ 128 * e = w1 + 2 ^ 64 * c1 + PY) :
    w + 2 ^ 64 * c = W + PX + PY := by
  omega

theorem prod_le {x : Word} {a : Nat} (h : a ≤ 2 ^ 62) : x.toNat * a ≤ (2 ^ 64 - 1) * 2 ^ 62 :=
  Nat.mul_le_mul (by have := x.isLt; omega) h

/-- A word below a row's top. -/
theorem digit_ok {s : State} {base : Addr} (hs : Scr s base large) {t xo yo : Nat}
    {ma sa mb sb wi : Reg} (hr : RowRegs ma sa mb sb)
    (hwi : wi ≠ .x1 ∧ wi ≠ .x8 ∧ wi ≠ .x9 ∧ wi ≠ .x10 ∧ wi ≠ .x12)
    (hz : s.gpr .x12 = 0) (hA : (s.gpr ma).toNat ≤ 2 ^ 62) (hB : (s.gpr mb).toNat ≤ 2 ^ 62)
    (ht : t % 8 = 0 ∧ t + 8 ≤ workSize large) (hx : xo % 8 = 0 ∧ xo + 8 ≤ workSize large)
    (hy : yo % 8 = 0 ∧ yo + 8 ≤ workSize large) :
    WP isa (.block (digit t xo yo ma sa mb sb wi)) s fun u =>
      (u.gpr .x1).toNat + 2 ^ 64 * (u.gpr .x2).toNat =
        (s.gpr wi).toNat + (word s.mem base xo ^^^ s.gpr sa).toNat * (s.gpr ma).toNat +
          (word s.mem base yo ^^^ s.gpr sb).toNat * (s.gpr mb).toNat ∧
      u.mem = s.mem.writeW (off base t) (u.gpr .x1) ∧
      KeepRegs [.x1, .x2, .x8, .x9, .x10] s u := by
  obtain ⟨⟨ma0, ma1, ma2, -, ma8, ma9, ma10, ma12⟩, ⟨sa0, sa1, sa2, -, sa8, sa9, sa10, sa12⟩,
    ⟨mb0, mb1, mb2, -, mb8, mb9, mb10, mb12⟩, ⟨sb0, sb1, sb2, -, sb8, sb9, sb10, sb12⟩⟩ :=
    (by simpa only [RowRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hr :
      (ma ≠ .x0 ∧ ma ≠ .x1 ∧ ma ≠ .x2 ∧ ma ≠ .x3 ∧ ma ≠ .x8 ∧ ma ≠ .x9 ∧ ma ≠ .x10 ∧ ma ≠ .x12) ∧
      (sa ≠ .x0 ∧ sa ≠ .x1 ∧ sa ≠ .x2 ∧ sa ≠ .x3 ∧ sa ≠ .x8 ∧ sa ≠ .x9 ∧ sa ≠ .x10 ∧ sa ≠ .x12) ∧
      (mb ≠ .x0 ∧ mb ≠ .x1 ∧ mb ≠ .x2 ∧ mb ≠ .x3 ∧ mb ≠ .x8 ∧ mb ≠ .x9 ∧ mb ≠ .x10 ∧ mb ≠ .x12) ∧
      (sb ≠ .x0 ∧ sb ≠ .x1 ∧ sb ≠ .x2 ∧ sb ≠ .x3 ∧ sb ≠ .x8 ∧ sb ≠ .x9 ∧ sb ≠ .x10 ∧ sb ≠ .x12))
  obtain ⟨w1, w8, w9, w10, w12⟩ := hwi
  simp only [digit, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hs hx.1 hx.2 sa8) fun a ⟨a8, ka⟩ => ?_
  have hsa : Scr a base large := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok a (by decide) ma9 w9 w10 (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun b ⟨⟨e1, _, h1⟩, kb⟩ => ?_
  have hsb : Scr b base large := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hsb hy.1 hy.2 sb8) fun c ⟨c8, kc⟩ => ?_
  have hsc : Scr c base large := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok c (by decide) mb9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun d ⟨⟨e2, _, h2⟩, kd⟩ => ?_
  have hsd : Scr d base large := hsc.of_keeps kd (by decide)
  refine WP.mono (st_ok hsd ht.1 ht.2 .x1) fun u ⟨mu, ku⟩ => ?_
  -- the registers each step read
  have ga : ∀ r, r ≠ .x8 → a.gpr r = s.gpr r := fun r h => ka.gpr r (by simpa using h)
  have gb : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x2 → b.gpr r = a.gpr r := fun r h9 h10 h1 h2 =>
    kb.gpr r (by simp [h9, h10, h1, h2])
  have gc : ∀ r, r ≠ .x8 → c.gpr r = b.gpr r := fun r h => kc.gpr r (by simpa using h)
  have gd : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x2 → d.gpr r = c.gpr r := fun r h9 h10 h1 h2 =>
    kd.gpr r (by simp [h9, h10, h1, h2])
  have gu : ∀ r, u.gpr r = d.gpr r := fun r => ku.gpr r (by simp)
  have amem : a.mem = s.mem := ka.mem
  have bmem : b.mem = a.mem := kb.mem
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kd.rd, kc.rd, kb.rd, ka.rd],
    by rw [ku.wr, kd.wr, kc.wr, kb.wr, ka.wr], by rw [ku.sp, kd.sp, kc.sp, kb.sp, ka.sp]⟩⟩
  · rw [gu, gu]
    rw [a8, ga ma ma8, ga wi w8, ga .x12 (by decide), hz] at h1
    rw [c8, gc mb mb8, gc .x1 (by decide), gc .x2 (by decide),
      gb mb mb9 mb10 mb1 mb2, gb sb sb9 sb10 sb1 sb2, ga mb mb8, ga sb sb8, bmem, amem] at h2
    rw [show (0 : Word).toNat = 0 from rfl] at h1
    exact digit_arith (s.gpr wi).isLt (prod_le hA) (prod_le hB) h1 h2
  · rw [mu, kd.mem, kc.mem, bmem, amem, gu]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gu, gd r hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1, gc r hr.2.2.1, gb r hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1,
      ga r hr.2.2.1]

theorem add_ok (s : State) (d n m : Reg) :
    WP isa (.block [.add .x d n m]) s fun t => t.gpr d = s.gpr n + s.gpr m ∧ Keeps [d] s t := by
  refine WP.block_cons_iff.mpr ⟨_, exec_add_x, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _
    (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩

theorem neg_toNat (v : Word) : ((0 : Word) - v).toNat = (2 ^ 64 - v.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub, show (0 : Word).toNat = 0 from rfl, Nat.add_zero]

theorem top_arith {W PX PY KA KB w1 h e w w4 e' : Nat} (hKA : KA < 2 ^ 64) (hKB : KB < 2 ^ 64)
    (h1 : w1 + 2 ^ 64 * h + 2 ^ 128 * e = W + 2 ^ 64 * ((2 ^ 64 - KA) % 2 ^ 64) + PX)
    (h2 : w + 2 ^ 64 * w4 + 2 ^ 128 * e' =
      w1 + 2 ^ 64 * ((h + (2 ^ 64 - KB) % 2 ^ 64) % 2 ^ 64) + PY) :
    (w + 2 ^ 64 * w4 + 2 ^ 64 * (KA + KB)) % 2 ^ 128 = (W + PX + PY) % 2 ^ 128 := by
  omega

/-- The top two words of a row: `w + 2⁶⁴ w' + 2⁶⁴ (ka + kb) ≡ x2 + X' a + Y' b` (mod `2¹²⁸`). -/
theorem top_ok {s : State} {base : Addr} (hs : Scr s base large) (signed : Bool) {t xo yo : Nat}
    {ma sa mb sb : Reg} (hr : RowRegs ma sa mb sb) (hz : s.gpr .x12 = 0)
    (ht : t % 8 = 0 ∧ t + 16 ≤ workSize large) (hx : xo % 8 = 0 ∧ xo + 8 ≤ workSize large)
    (hy : yo % 8 = 0 ∧ yo + 8 ≤ workSize large) :
    WP isa (.block (top signed t xo yo ma sa mb sb)) s fun u =>
      ((u.gpr .x1).toNat + 2 ^ 64 * (u.gpr .x3).toNat +
          2 ^ 64 * ((corrV signed (word s.mem base xo ^^^ s.gpr sa) (s.gpr ma) (s.gpr sa)).toNat +
            (corrV signed (word s.mem base yo ^^^ s.gpr sb) (s.gpr mb) (s.gpr sb)).toNat)) % 2 ^ 128 =
        ((s.gpr .x2).toNat + (word s.mem base xo ^^^ s.gpr sa).toNat * (s.gpr ma).toNat +
          (word s.mem base yo ^^^ s.gpr sb).toNat * (s.gpr mb).toNat) % 2 ^ 128 ∧
      u.mem = (s.mem.writeW (off base t) (u.gpr .x1)).writeW (off base (t + 8)) (u.gpr .x3) ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] s u := by
  obtain ⟨⟨_, ma1, ma2, ma3, ma8, ma9, ma10, ma12⟩, ⟨_, sa1, sa2, sa3, sa8, sa9, sa10, sa12⟩,
    ⟨_, mb1, mb2, mb3, mb8, mb9, mb10, mb12⟩, ⟨_, sb1, sb2, sb3, sb8, sb9, sb10, sb12⟩⟩ :=
    (by simpa only [RowRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hr :
      (ma ≠ .x0 ∧ ma ≠ .x1 ∧ ma ≠ .x2 ∧ ma ≠ .x3 ∧ ma ≠ .x8 ∧ ma ≠ .x9 ∧ ma ≠ .x10 ∧ ma ≠ .x12) ∧
      (sa ≠ .x0 ∧ sa ≠ .x1 ∧ sa ≠ .x2 ∧ sa ≠ .x3 ∧ sa ≠ .x8 ∧ sa ≠ .x9 ∧ sa ≠ .x10 ∧ sa ≠ .x12) ∧
      (mb ≠ .x0 ∧ mb ≠ .x1 ∧ mb ≠ .x2 ∧ mb ≠ .x3 ∧ mb ≠ .x8 ∧ mb ≠ .x9 ∧ mb ≠ .x10 ∧ mb ≠ .x12) ∧
      (sb ≠ .x0 ∧ sb ≠ .x1 ∧ sb ≠ .x2 ∧ sb ≠ .x3 ∧ sb ≠ .x8 ∧ sb ≠ .x9 ∧ sb ≠ .x10 ∧ sb ≠ .x12))
  simp only [top, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hs hx.1 hx.2 sa8) fun a ⟨a8, ka⟩ => ?_
  have ga : ∀ r, r ≠ .x8 → a.gpr r = s.gpr r := fun r h => ka.gpr r (by simpa using h)
  have hsa : Scr a base large := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (corr_ok a signed ((ga _ (by decide)).trans hz) (by decide) ma3)
    fun b ⟨b3, kb⟩ => ?_
  have gb : ∀ r, r ≠ .x3 → b.gpr r = a.gpr r := fun r h => kb.gpr r (by simpa using h)
  have hsb : Scr b base large := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok b (by decide) ma9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun c ⟨⟨e1, _, h1⟩, kc⟩ => ?_
  have gc : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x3 → c.gpr r = b.gpr r := fun r h9 h10 h1 h3 =>
    kc.gpr r (by simp [h9, h10, h1, h3])
  have hsc : Scr c base large := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldx_ok hsc hy.1 hy.2 sb8) fun d ⟨d8, kd⟩ => ?_
  have gd : ∀ r, r ≠ .x8 → d.gpr r = c.gpr r := fun r h => kd.gpr r (by simpa using h)
  have hsd : Scr d base large := hsc.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  have dz : d.gpr .x12 = 0 := by
    rw [gd _ (by decide), gc _ (by decide) (by decide) (by decide) (by decide), gb _ (by decide),
      ga _ (by decide), hz]
  refine WP.mono (corr_ok d signed dz (by decide) mb2) fun e ⟨e2, ke⟩ => ?_
  have ge : ∀ r, r ≠ .x2 → e.gpr r = d.gpr r := fun r h => ke.gpr r (by simpa using h)
  have hse : Scr e base large := hsd.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_ok e .x3 .x3 .x2) fun f ⟨f3, kf⟩ => ?_
  have gf : ∀ r, r ≠ .x3 → f.gpr r = e.gpr r := fun r h => kf.gpr r (by simpa using h)
  have hsf : Scr f base large := hse.of_keeps kf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (half_ok f (by decide) mb9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun g ⟨⟨e2', _, h2⟩, kg⟩ => ?_
  have gg : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x1 → r ≠ .x3 → g.gpr r = f.gpr r := fun r h9 h10 h1 h3 =>
    kg.gpr r (by simp [h9, h10, h1, h3])
  have hsg : Scr g base large := hsf.of_keeps kg (by decide)
  rw [WP.block_cons_iff]
  refine ⟨_, store_sc hsg ht.1 (by omega) .x1, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, store_sc (hsg.setMem _) (by omega) (by omega) .x3, WP.block_nil ?_⟩
  -- memory: the loads read `s.mem`
  have mc : c.mem = s.mem := by rw [kc.mem, kb.mem, ka.mem]
  have mf : f.mem = s.mem := by rw [kf.mem, ke.mem, kd.mem, mc]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by simp only [kg.rd, kf.rd, ke.rd, kd.rd, kc.rd, kb.rd, ka.rd],
    by simp only [kg.wr, kf.wr, ke.wr, kd.wr, kc.wr, kb.wr, ka.wr],
    by simp only [kg.sp, kf.sp, ke.sp, kd.sp, kc.sp, kb.sp, ka.sp]⟩⟩
  · simp only
    rw [b3, gb .x2 (by decide), gb .x8 (by decide), gb ma ma3] at h1
    rw [a8, ga .x2 (by decide), ga ma ma8, ga sa sa8, neg_toNat] at h1
    have hx3 : f.gpr .x3 = c.gpr .x3 +
        (0 - corrV signed (word s.mem base yo ^^^ s.gpr sb) (s.gpr mb) (s.gpr sb)) := by
      rw [f3, ge .x3 (by decide), gd .x3 (by decide), e2, d8, gd mb mb8, gd sb sb8,
        gc mb mb9 mb10 mb1 mb3, gc sb sb9 sb10 sb1 sb3, gb mb mb3, gb sb sb3, ga mb mb8,
        ga sb sb8, mc]
    have hx1 : f.gpr .x1 = c.gpr .x1 := by
      rw [gf .x1 (by decide), ge .x1 (by decide), gd .x1 (by decide)]
    have hx8 : f.gpr .x8 = word s.mem base yo ^^^ s.gpr sb := by
      rw [gf .x8 (by decide), ge .x8 (by decide), d8, gc sb sb9 sb10 sb1 sb3, gb sb sb3,
        ga sb sb8, mc]
    have hmb : f.gpr mb = s.gpr mb := by
      rw [gf mb mb3, ge mb mb2, gd mb mb8, gc mb mb9 mb10 mb1 mb3, gb mb mb3, ga mb mb8]
    rw [hx3, hx1, hx8, hmb, BitVec.toNat_add, neg_toNat] at h2
    exact top_arith (corrV signed _ _ _).isLt (corrV signed _ _ _).isLt h1 h2
  · simp only [mf, kg.mem]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only
    rw [gg r hr.2.2.2.2.1 hr.2.2.2.2.2 hr.1 hr.2.2.1, gf r hr.2.2.1, ge r hr.2.1, gd r hr.2.2.2.1,
      gc r hr.2.2.2.2.1 hr.2.2.2.2.2 hr.1 hr.2.2.1, gb r hr.2.2.1, ga r hr.2.2.2.1]

/-- Five words at `t`. -/
abbrev val5 (m : Mem) (base : Addr) (t : Nat) : Nat :=
  fe m base t + 2 ^ 256 * (word m base (t + 32)).toNat

/-- The four words at `o`, complemented by the mask `s`. -/
abbrev flip4 (m : Mem) (base : Addr) (o : Nat) (s : Word) : Nat :=
  val4 (word m base o ^^^ s) (word m base (o + 8) ^^^ s) (word m base (o + 16) ^^^ s)
    (word m base (o + 24) ^^^ s)

theorem row_arith {C P0 P1 P2 P3 Q0 Q1 Q2 Q3 w0 w1 w2 w3 w4 c1 c2 c3 K : Nat}
    (d0 : w0 + 2 ^ 64 * c1 = C + P0 + Q0) (d1 : w1 + 2 ^ 64 * c2 = c1 + P1 + Q1)
    (d2 : w2 + 2 ^ 64 * c3 = c2 + P2 + Q2)
    (d3 : (w3 + 2 ^ 64 * w4 + 2 ^ 64 * K) % 2 ^ 128 = (c3 + P3 + Q3) % 2 ^ 128) :
    (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4 + 2 ^ 256 * K) % (2 ^ 256 * 2 ^ 64) =
      (C + (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) +
        (Q0 + 2 ^ 64 * Q1 + 2 ^ 128 * Q2 + 2 ^ 192 * Q3)) % (2 ^ 256 * 2 ^ 64) := by
  omega

theorem val4_mul (x0 x1 x2 x3 : Word) (a : Nat) :
    val4 x0 x1 x2 x3 * a = x0.toNat * a + 2 ^ 64 * (x1.toNat * a) + 2 ^ 128 * (x2.toNat * a) +
      2 ^ 192 * (x3.toNat * a) := by
  simp only [val4, Nat.add_mul, Nat.mul_assoc]

/-- A row: `W + 2²⁵⁶ (ka + kb) ≡ c + X' a + Y' b` (mod `2³²⁰`). -/
theorem row_ok {s : State} {base : Addr} (hs : Scr s base large) (signed : Bool) {t xo yo : Nat}
    {ma sa mb sb car : Reg} (hr : RowRegs ma sa mb sb)
    (hcar : car ≠ .x1 ∧ car ≠ .x8 ∧ car ≠ .x9 ∧ car ≠ .x10 ∧ car ≠ .x12)
    (hz : s.gpr .x12 = 0) (hA : (s.gpr ma).toNat ≤ 2 ^ 62) (hB : (s.gpr mb).toNat ≤ 2 ^ 62)
    (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) (hx : xo % 8 = 0 ∧ xo + 32 ≤ workSize large)
    (hy : yo % 8 = 0 ∧ yo + 32 ≤ workSize large) (hsx : t + 40 ≤ xo ∨ xo + 32 ≤ t)
    (hsy : t + 40 ≤ yo ∨ yo + 32 ≤ t) :
    WP isa (.block (row signed t xo yo ma sa mb sb car)) s fun u =>
      (val5 u.mem base t + 2 ^ 256 *
          ((corrV signed (word s.mem base (xo + 24) ^^^ s.gpr sa) (s.gpr ma) (s.gpr sa)).toNat +
            (corrV signed (word s.mem base (yo + 24) ^^^ s.gpr sb) (s.gpr mb) (s.gpr sb)).toNat)) %
          (2 ^ 256 * 2 ^ 64) =
        ((s.gpr car).toNat + flip4 s.mem base xo (s.gpr sa) * (s.gpr ma).toNat +
          flip4 s.mem base yo (s.gpr sb) * (s.gpr mb).toNat) % (2 ^ 256 * 2 ^ 64) ∧
      Outside base t 40 s.mem u.mem ∧ KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] s u := by
  have _hcap := workSize_le large
  have hrr := hr
  obtain ⟨⟨_, ma1, ma2, ma3, ma8, ma9, ma10, ma12⟩, ⟨_, sa1, sa2, sa3, sa8, sa9, sa10, sa12⟩,
    ⟨_, mb1, mb2, mb3, mb8, mb9, mb10, mb12⟩, ⟨_, sb1, sb2, sb3, sb8, sb9, sb10, sb12⟩⟩ :=
    (by simpa only [RowRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hr :
      (ma ≠ .x0 ∧ ma ≠ .x1 ∧ ma ≠ .x2 ∧ ma ≠ .x3 ∧ ma ≠ .x8 ∧ ma ≠ .x9 ∧ ma ≠ .x10 ∧ ma ≠ .x12) ∧
      (sa ≠ .x0 ∧ sa ≠ .x1 ∧ sa ≠ .x2 ∧ sa ≠ .x3 ∧ sa ≠ .x8 ∧ sa ≠ .x9 ∧ sa ≠ .x10 ∧ sa ≠ .x12) ∧
      (mb ≠ .x0 ∧ mb ≠ .x1 ∧ mb ≠ .x2 ∧ mb ≠ .x3 ∧ mb ≠ .x8 ∧ mb ≠ .x9 ∧ mb ≠ .x10 ∧ mb ≠ .x12) ∧
      (sb ≠ .x0 ∧ sb ≠ .x1 ∧ sb ≠ .x2 ∧ sb ≠ .x3 ∧ sb ≠ .x8 ∧ sb ≠ .x9 ∧ sb ≠ .x10 ∧ sb ≠ .x12))
  have k5 : ∀ r ∈ ([.x1, .x2, .x8, .x9, .x10] : List Reg), r ∈ ([.x1, .x2, .x3, .x8, .x9, .x10] : List Reg) := by
    decide
  -- a register the row keeps
  have keep : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → r ∉ ([.x1, .x2, .x3, .x8, .x9, .x10] : List Reg) := by
    intro r h
    have := hrr r h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1⟩
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ workSize large → e + 8 ≤ workSize large →
      ∀ (m : Mem) (v : Word), word (m.writeW (off base d) v) base e = word m base e :=
    fun h hd he m v => word_writeW_sep m base v h.symm (by omega_arith) (by omega_arith)
  simp only [row, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok hs hr hcar hz hA hB ⟨ht.1, by omega_arith⟩ ⟨hx.1, by omega_arith⟩ ⟨hy.1, by omega_arith⟩)
    fun u0 ⟨e0, m0, k0⟩ => ?_
  have hs0 : Scr u0 base large := ⟨(k0.gpr _ (by decide)).trans hs.x0, k0.wr ▸ hs.wr, hs.nowrap⟩
  have g0 : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → u0.gpr r = s.gpr r := fun h =>
    k0.gpr _ fun hm => keep h (k5 _ hm)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok hs0 hr (by decide) ((k0.gpr _ (by decide)).trans hz)
    (by rw [g0 (r := ma) (by simp)]; exact hA) (by rw [g0 (r := mb) (by simp)]; exact hB)
    ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩)
    fun u1 ⟨e1, m1, k1⟩ => ?_
  have hs1 : Scr u1 base large := ⟨(k1.gpr _ (by decide)).trans hs0.x0, k1.wr ▸ hs0.wr, hs.nowrap⟩
  have g1 : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → u1.gpr r = s.gpr r := fun h =>
    (k1.gpr _ fun hm => keep h (k5 _ hm)).trans (g0 h)
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok hs1 hr (by decide) ((k1.gpr _ (by decide)).trans ((k0.gpr _ (by decide)).trans hz))
    (by rw [g1 (r := ma) (by simp)]; exact hA) (by rw [g1 (r := mb) (by simp)]; exact hB)
    ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩)
    fun u2 ⟨e2, m2, k2⟩ => ?_
  have hs2 : Scr u2 base large := ⟨(k2.gpr _ (by decide)).trans hs1.x0, k2.wr ▸ hs1.wr, hs.nowrap⟩
  have g2 : ∀ {r : Reg}, r ∈ [ma, sa, mb, sb] → u2.gpr r = s.gpr r := fun h =>
    (k2.gpr _ fun hm => keep h (k5 _ hm)).trans (g1 h)
  refine WP.mono (top_ok hs2 signed hr ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans
      ((k0.gpr _ (by decide)).trans hz))) ⟨by omega_arith, by omega_arith⟩ ⟨by omega_arith, by omega_arith⟩
      ⟨by omega_arith, by omega_arith⟩)
    fun u ⟨e3, m3, k3⟩ => ?_
  -- the words the later steps read are the first's
  have r1 : ∀ e, (t + 8 ≤ e ∨ e + 8 ≤ t) → e + 8 ≤ workSize large → word u0.mem base e = word s.mem base e :=
    fun e h he => by rw [m0]; exact sep h (by omega_arith) he _ _
  have r2 : ∀ e, (t + 16 ≤ e ∨ e + 8 ≤ t) → e + 8 ≤ workSize large → word u1.mem base e = word s.mem base e :=
    fun e h he => by rw [m1, sep (by omega_arith) (by omega_arith) he, r1 e (by omega_arith) he]
  have r3 : ∀ e, (t + 24 ≤ e ∨ e + 8 ≤ t) → e + 8 ≤ workSize large → word u2.mem base e = word s.mem base e :=
    fun e h he => by rw [m2, sep (by omega_arith) (by omega_arith) he, r2 e (by omega_arith) he]
  rw [g0 (r := sa) (by simp), g0 (r := ma) (by simp), g0 (r := sb) (by simp), g0 (r := mb) (by simp), r1 _ (by omega_arith) (by omega_arith),
    r1 _ (by omega_arith) (by omega_arith)] at e1
  rw [g1 (r := sa) (by simp), g1 (r := ma) (by simp), g1 (r := sb) (by simp), g1 (r := mb) (by simp), r2 _ (by omega_arith) (by omega_arith),
    r2 _ (by omega_arith) (by omega_arith)] at e2
  rw [g2 (r := sa) (by simp), g2 (r := ma) (by simp), g2 (r := sb) (by simp), g2 (r := mb) (by simp), r3 _ (by omega_arith) (by omega_arith),
    r3 _ (by omega_arith) (by omega_arith)] at e3
  -- the words of the result
  have w0 : word u.mem base t = u0.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), sep (by omega_arith) (by omega_arith) (by omega_arith), m2,
      sep (by omega_arith) (by omega_arith) (by omega_arith), m1, sep (by omega_arith) (by omega_arith) (by omega_arith), m0,
      word_writeW_self]
  have w1 : word u.mem base (t + 8) = u1.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), sep (by omega_arith) (by omega_arith) (by omega_arith), m2,
      sep (by omega_arith) (by omega_arith) (by omega_arith), m1, word_writeW_self]
  have w2 : word u.mem base (t + 16) = u2.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), sep (by omega_arith) (by omega_arith) (by omega_arith), m2,
      word_writeW_self]
  have w3 : word u.mem base (t + 24) = u.gpr .x1 := by
    rw [m3, sep (by omega_arith) (by omega_arith) (by omega_arith), word_writeW_self]
  have w4 : word u.mem base (t + 32) = u.gpr .x3 := by
    rw [m3, show t + 32 = t + 24 + 8 by omega_arith, word_writeW_self]
  refine ⟨?_, ?_, ((k0.mono k5).trans (k1.mono k5)).trans ((k2.mono k5).trans k3)⟩
  · simp only [val5, fe, w0, w1, w2, w3, w4, flip4, val4_mul]
    exact row_arith e0 e1 e2 e3
  · have o0 : Outside base t 40 s.mem u0.mem := by
      rw [m0]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
    have o1 : Outside base t 40 u0.mem u1.mem := by
      rw [m1]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
    have o2 : Outside base t 40 u1.mem u2.mem := by
      rw [m2]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)
    have o3 : Outside base t 40 u2.mem u.mem := by
      rw [m3]
      exact ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    exact o0.trans (o1.trans (o2.trans o3))

end VG.Proof.Ed25519.AArch64.Inv
