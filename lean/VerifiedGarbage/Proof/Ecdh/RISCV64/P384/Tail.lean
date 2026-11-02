module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Check
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ECDH and public keys over P-384 on RISC-V: the multiplication and after

What follows the point's setup in both functions (`tail`): the masks of `d`
in `[1, n-1]` into the flag (`range_ok`), `R = [d]P` by a call of
`vg_p384_mul` (`mul_rv`), `Z^(p-2)` by its chain (`chainPow_ok`), and `x = X Z^(p-2)`
out of Montgomery's form (`affine_ok`). The callees' `Keeps` are frames
(`unch_of_mulKeeps`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

/-!
## ECDH and public keys over P-384 on RISC-V: the setup

The constants (`consts_ok`: `setConst` for each, apart), and what both
functions' setups share.
-/

namespace VG.Proof.Ecdh.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P384
open VG.Proof.X25519.RISCV64 (Rest)

/-- Constants to slots below 41, each its own. -/
theorem consts_ok : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ L, e.1 < 41) →
    (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst 6 (p384.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (p384.sl e.1, 48)) s.mem s'.mem ∧
      ∀ e ∈ L, sv base s' e.1 = e.2 % 2 ^ 384
  | [], s, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Unch.refl _ _ _, by simp⟩
  | (i, x) :: L, s, base, hw, hlt, hnd => by
    simp only [List.mem_cons, forall_eq_or_imp] at hlt
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (setConst_ok 6 hw (o := p384.sl i) (x := x) (by rw [sl_eq]; omega)
      (by rw [sl_eq]; omega)) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_)
    refine WP.mono (consts_ok L (hw.of_rest r₁) hlt.2 hnd.2) fun s₂ ⟨r₂, U₂, e₂⟩ => ⟨r₁.trans r₂, ?_, ?_⟩
    · exact O₁.unch.trans U₂
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · show wordsVal _ _ _ _ = _
        rw [U₂.wordsVal (fun w hw => by
          simp only [List.mem_map] at hw
          obtain ⟨e', he', rfl⟩ := hw
          have hne : e'.1 ≠ i := fun h => hnd.1 ⟨e', he', h⟩
          have := hlt.2 e' he'
          simp only [sl_eq]; omega) (by rw [sl_eq]; omega)]
        exact e₁
      · exact e₂ e he

/-- The constants, as `consts_ok` takes them. -/
theorem constCode_eq : constCode p384 = (consts p384).flatMap fun e => setConst 6 (p384.sl e.1) e.2 := rfl

/-- The constants' slots. -/
theorem consts_slots : ∀ e ∈ consts p384, e.1 < 41 := by decide

theorem consts_nodup : ((consts p384).map Prod.fst).Nodup := by decide

/-- The constants are below `2²⁵⁶`. -/
theorem consts_lt : ∀ e ∈ consts p384, e.2 < 2 ^ 384 := by decide

/-- `sd t, d(r)` at the working space's base, in `r`. -/
theorem sd_reg {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} {r : Reg} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0)
    {t : Reg} {d : Nat} (hd : d + 8 ≤ 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t r d :: is)) s Q :=
  wp_sd (by omega) (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    ⟨_, hwr, Offset.contains_base base (by omega) (by omega)⟩ k

/-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3 := by
  rw [saveCode]
  refine sd_reg h0 hwr hal (d := 0) (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_reg (by rw [u₁.gpr]; exact h0) (by rw [u₁.wr]; exact hwr) hal (d := 8) (by decide) (by decide)
    fun s₂ u₂ => ?_
  refine sd_reg (by rw [u₂.gpr, u₁.gpr]; exact h0) (by rw [u₂.wr, u₁.wr]; exact hwr) hal (d := 16) (by decide)
    (by decide) fun s₃ u₃ => ?_
  refine sd_reg (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr) hal (d := 24)
    (by decide) (by decide) fun s₄ u₄ => ?_
  refine sd_reg (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr)
    hal (d := 32) (by decide) (by decide) fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  have g₅ : ∀ x, s₅.gpr x = s.gpr x := fun x => by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have m₅ : s₅.mem = ((((s.mem.writeW (off base 0) (s.gpr .s0)).writeW (off base 8) (s.gpr .s1)).writeW
      (off base 16) (s.gpr .s2)).writeW (off base 24) (s.gpr .ra)).writeW (off base 32) (s.gpr .s3) := by
    simp only [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  have O : ∀ {d} {m : Mem} {v : BitVec 64}, d ≤ 32 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun h => writeW_outside _ _ _ (by omega)
  have hw₈ : WsReg s₈ base := by
    refine ⟨by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, h0], ?_, hn, hal⟩
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr
  have w0 : ∀ {d e} {m : Mem} {v : BitVec 64}, d ≤ 32 → e ≤ 32 → d + 8 ≤ e ∨ e + 8 ≤ d →
      word (m.writeW (off base e) v) base d = word m base d :=
    fun hd he h => (O he).word h (by omega)
  have e₆ : s₆.gpr r = s₅.gpr r := by
    by_cases h : r = .s0
    · subst h; exact u₆.gpr
    · exact u₆.other _ h
  refine ⟨hw₈, by rw [u₈.other _ (by decide), u₇.gpr, e₆, g₅, h0],
    by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅], fun x h1 h2 h3 => by
      rw [u₈.other _ h2, u₇.other _ h3, u₆.other _ h1, g₅],
    by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₈, m₅]
    exact (((((O (by decide)).unch.trans (O (by decide)).unch).trans (O (by decide)).unch).trans
      (O (by decide)).unch).trans (O (by decide)).unch).cover (by decide)
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, word_writeW_self]


end VG.Proof.Ecdh.RISCV64.P384

namespace VG.Proof.Ecdh.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P384
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What `vg_p384_mul` may write, as ranges of offsets. -/
abbrev mulKW : List (Nat × Nat) := [(736, 144), (880, 672), (160, 48), (1984, 48), (2224, 2 ^ 64)]

theorem unch_of_mulKeeps {base : Addr} {m m' : Mem} (h : MC.Keeps base m m') : Unch base mulKW m m' := by
  intro x hx
  have e := fun w hw => hx w hw
  simp only [mulKW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  have hb : ofs base x < 2 ^ 64 := (x - base).isLt
  have hlt : ofs base x < 2224 := by omega
  have ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ (by show _ < 8192; omega) ?_ ?_
  · simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
      Impl.Weierstrass.Mul.Curve.bitsAt, MC, Impl.Weierstrass.Mul.p384, true_and]
    omega
  · simp only [Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes, Impl.Weierstrass.Mul.Curve.slot,
      MC, Impl.Weierstrass.Mul.p384]
    omega

/-- What `vg_p384_check_point` may write, as ranges of offsets. -/
abbrev checkKW : List (Nat × Nat) :=
  [(160, 48), (1840, 48), (2032, 48), (2080, 48), (3712, 384), (1696, 48), (1744, 48), (1888, 48), (2128, 48),
    (FL, 8), (8192, 2 ^ 64)]

theorem unch_of_checkKeeps {base : Addr} {m m' : Mem} (h : CC.Keeps base m m') : Unch base checkKW m m' := by
  intro x hx
  have e := fun w hw => hx w hw
  simp only [checkKW, FL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  have hb : ofs base x < 2 ^ 64 := (x - base).isLt
  have hlt : ofs base x < 8192 := by omega
  have ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ hlt ?_ ?_
  · simp only [Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.slot, CC,
      Impl.Weierstrass.CheckPoint.p384, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega
  · simp only [Impl.Weierstrass.CheckPoint.Curve.Out, Impl.Weierstrass.CheckPoint.Curve.slot,
      Impl.Weierstrass.CheckPoint.Curve.flagAt, CC, Impl.Weierstrass.CheckPoint.p384,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

/-- A call on the working space, then `s0` from `s3`. -/
theorem wsCallR_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {K : Contract isa}
    (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hpre : ∀ t : State, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .a0 = base → t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s' s'' : State, Kp s s'' → s''.mem = s'.mem → ∀ t : State, t.gpr .a0 = base → t.mem = s.mem →
      K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s'') :
    WP isa (Cfg.wsCall f body) s Q := by
  rw [Cfg.wsCall]
  refine WP.seq (wsCall_ok hn hK hw hpre fun s' K' t a m hp => wp_mv fun s'' u => WP.block_nil ?_)
  refine hQ s' s'' ⟨fun r hr => ?_, by rw [u.rd, K'.rd], by rw [u.wr, K'.wr], by rw [u.sp, K'.sp]⟩ u.mem t a m hp
  by_cases h : r = .s0
  · subst h; rw [u.gpr, K'.gpr _ (by decide), h3, hw.s0]
  · rw [u.other _ h, K'.gpr _ hr]

/-- A slot below the flag's. -/
theorem sl_lt {i : Nat} (hi : i < 44) : p384.sl i % 8 = 0 ∧ p384.sl i + 8 * 6 ≤ 4096 ∧ p384.sl i + 8 * 6 ≤ FL := by
  simp only [Cfg.sl, slot, show p384.n = 6 from rfl, FL]; omega

/-- The masks of `x < n` and `x ≠ 0` into the flag, for `x` at slot `i`. -/
theorem rangeOf_ok {i : Nat} (hi : i < 41) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeOf p384 i)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s i < sv base s MN)) &&&
        maskOf (!decide (sv base s i = 0)) := by
  obtain ⟨a8, -, aF⟩ := sl_lt (by omega : i < 44)
  have a2 : p384.sl i + 8 * 6 ≤ 2048 := by rw [sl_eq]; omega
  rw [rangeOf, show p384.n = 6 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := 6) (a := p384.sl i) (m := p384.sl MN) a8
    (by decide) a2 (by decide)) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (zeroMask_ok hw₂ (n := 6) (a := p384.sl i) a8 (by omega))
    fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  refine WP.cons (exec_logicImm (by decide)) ?_
  have hw₃' := (hw₂.of_rest r₃).of_kp (Kp.of_upd (Upd.write s₃ .a7 (s₃.gpr .a7 ^^^ BitVec.ofInt 64 (-1))))
  refine WP.mono (andFlag_ok hw₃') fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans
      ((Kp.of_upd (Upd.write s₃ .a7 _)).trans (Kp.of_rest r₄))))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have k₂ : sv base s₂ i = sv base s i := by
      show wordsVal _ _ _ _ = _
      rw [O₂.wordsVal (.inl aF) (by omega), m₁]
    rw [f₄]
    simp only [State.write, ↓reduceIte]
    rw [m₃, f₂, m₁, g₁, g₃, not_mask]
    simp only [sv] at k₂
    rw [k₂]

/-- The masks of `d < n` and `d ≠ 0` into the flag. -/
theorem range_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeCode p384)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < sv base s MN)) &&&
        maskOf (!decide (sv base s K = 0)) :=
  rangeOf_ok (by decide) hw

/-- The constants `tail` reads. -/
structure TailConsts (base : Addr) (s : State) : Prop where
  mp : sv base s MP = W.p
  mn : sv base s MN = W.n
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  onep : sv base s ONEP = 1 * 2 ^ 384 % W.p
  ap : sv base s AP = W.a * 2 ^ 384 % W.p
  b3p : sv base s B3P = 3 * W.b * 2 ^ 384 % W.p
  expp : sv base s EXPP = W.p - 2

theorem mn_eq {base : Addr} {s : State} (h : TailConsts base s) : sv base s MN = W.n := h.mn

theorem TailConsts.of_unch {base : Addr} {s s' : State} {W' : List (Nat × Nat)} (h : TailConsts base s)
    (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', p384.sl i + 48 ≤ w.1 ∨ w.1 + w.2 ≤ p384.sl i) :
    TailConsts base s' := by
  have e : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], sv base s' i = sv base s i := fun i hi =>
    sv_unch U i (hW i hi) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨(e MP (by simp)).trans h.mp, (e MN (by simp)).trans h.mn, (e ZERO (by simp)).trans h.zero,
    (e ONE (by simp)).trans h.one, (e ONEP (by simp)).trans h.onep, (e AP (by simp)).trans h.ap,
    (e B3P (by simp)).trans h.b3p, (e EXPP (by simp)).trans h.expp⟩

theorem chainLay : ChainLayR (chainP p384) 6 where
  n := rfl
  k1 := by decide
  acc := by decide
  base := by decide
  tbl := by decide
  short := by decide
  acc8 := by decide
  base8 := by decide
  tbl8 := by decide
  acc_base := by decide
  acc_tbl := by decide
  base_tbl := by decide

/-- The chain is `p - 2`'s. -/
theorem chainP_ok : ChainOkR (chainP p384) (W.p - 2) := ChainOkR.of_check (by lit_decide)

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv base s ACC < W.p) (hone : sv base s ONE = 1) :
    WP isa (affineCoord p384 t o a) s fun s' =>
      Kp s s' ∧ Unch base [(p384.sl t, 48), (own 6, 384), (p384.sl o, 48), (own 6, 384)] s.mem s'.mem ∧
      sv base s' o < W.p ∧
      Fin.ofNat W.p (sv base s' o) = toM W.p (2 ^ 384) (sv base s a) * toM W.p (2 ^ 384) (sv base s ACC) := by
  have hl : ∀ i, i < 44 → p384.sl i + 8 * p384Field.S.k ≤ own p384Field.S.k := fun i hi => by
    show 64 + 48 * i + 48 ≤ 3712 + 0 - 0 + 0; omega
  have hs : ∀ i, i < 44 → p384.sl i < 4095 := fun i hi => by rw [sl_eq]; omega
  have hk4 : p384Field.S.k = 6 := rfl
  rw [affineCoord]
  refine WP.seq (WP.mono (mulCall_ok field_ok hw (o := p384.sl t) (a := p384.sl a) (b := p384.sl ACC) (hl t ht)
    (hl a ha) (hl ACC (by decide)) (hs t ht) (hs a ha) (hs ACC (by decide)) hacc) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  have one₁ : sv base s₁ ONE = 1 := by
    rw [← hone]
    exact sv_unch (C₁.mem : Unch _ _ _ _) ONE (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [sl_eq, ONE]; simp only [ONE, ACC] at htm; omega
      · decide)
  refine WP.mono (mulCall_ok field_ok (hw.of_kp C₁.kp) (o := p384.sl o) (a := p384.sl t) (b := p384.sl ONE)
    (hl o ho) (hl t ht) (hl ONE (by decide)) (hs o ho) (hs t ht) (hs ONE (by decide))
    (by show sv base s₁ ONE < W.p; rw [one₁]; decide)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ⟨C₁.kp.trans C₂.kp,
      Unch.trans (C₁.mem : Unch _ _ _ _) (C₂.mem : Unch _ _ _ _), lt₂, ?_⟩
  have e₂' : sv base s₂ o * 2 ^ 384 % W.p = sv base s₁ t * 1 % W.p := by
    rw [← one₁]; exact e₂
  rw [toM_one_mul unit e₂']
  exact toM_mul unit e₁

/-- The coordinates the multiplication's contract decodes. -/
theorem dq (hL : VG.Proof.Weierstrass.Law W) (x : Nat) : MC.toPoint.dec x = toM W.p (2 ^ 384) x :=
  VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit x

theorem coord_sv (m : Mem) (base : Addr) (i : Nat) (hi : i < 100 := by decide) :
    MC.toPoint.coordAt m base (p384.sl i) = wordsVal m base (p384.sl i) 6 :=
  coordAt_eq m base (by rw [sl_eq]; omega)

/-- The point the multiplication's contract reads. -/
theorem point_eq (hL : VG.Proof.Weierstrass.Law W) (m : Mem) (base : Addr) :
    MC.point base m = .affine (toM W.p (2 ^ 384) (wordsVal m base (p384.sl RX) 6))
      (toM W.p (2 ^ 384) (wordsVal m base (p384.sl RY) 6)) := by
  unfold Impl.Weierstrass.Mul.Curve.point
  rw [dq hL, dq hL]
  show Point.affine (toM W.p (2 ^ 384) (MC.toPoint.coordAt m base (p384.sl RX)))
    (toM W.p (2 ^ 384) (MC.toPoint.coordAt m base (p384.sl RY))) = _
  rw [coord_sv _ _ RX, coord_sv _ _ RY]
  rfl

theorem rep_of_represents {X Y Z : Fe W} {P : Point W} (h : Impl.Weierstrass.MulBase.Represents X Y Z P) :
    Rep W X Y Z P := by
  cases P <;> exact h

/-- What `tail` writes. -/
abbrev tailW : List (Nat × Nat) :=
  [(FL, 8)] ++ mulKW ++ chainWx (chainP p384) 6 ++
    [(p384.sl XM, 48), (own 6, 384), (p384.sl XO, 48), (own 6, 384)]

/-- `tail` with a call of `mulName`, whose code is `mulCode`, that computes
`R = [d]P` as `vg_p384_mul`'s contract says (`hcall`, from the state after
the range's masks, which changes only the flag): the range of `d` into the
flag, `R = [d]P`, `Z^(p-2)`, and `x`. -/
theorem tailWith_ok (hL : VG.Proof.Weierstrass.Law W) {mulName : String} {mulCode : Prog isa} {s : State}
    {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s)
    (hcall : ∀ s₁ : State, WsReg s₁ base → s₁.gpr .s3 = base → Kp s s₁ → Unch base [(FL, 8)] s.mem s₁.mem →
      s₁.syms = s.syms →
      WP isa (Cfg.wsCall mulName mulCode) s₁ fun s₂ => Kp s₁ s₂ ∧
        MC.ResultInRange (MC.scalar base s₁.mem) (MC.point base s₁.mem) base s₁.mem s₂.mem) :
    WP isa (tail p384 mulName mulCode) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 384) (sv base s' RX)) (toM W.p (2 ^ 384) (sv base s' RY))
          (toM W.p (2 ^ 384) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 384) (sv base s RX))
            (toM W.p (2 ^ 384) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 384) (sv base s' RX) * toM W.p (2 ^ 384) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 384) (sv base s' ACC) = toM W.p (2 ^ 384) (sv base s' RZ) ^ (W.p - 2) := by
  have hp0 : 0 < W.p := by decide
  rw [tail]
  -- The range.
  refine WP.seq (WP.mono (show WP isa _ s fun s' => _ ∧ s'.syms = s.syms from
    let ⟨t, s', he, hq⟩ := range_ok hw; ⟨t, s', he, hq, Exec.syms he⟩) fun s₁ ⟨⟨K₁, O₁, f₁⟩, sy₁⟩ => ?_)
  have hw₁ := hw.of_kp K₁
  have U₁ := O₁.unch
  have e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega)
      (by omega)
  have hc₁ := hc.of_unch U₁ (by decide)
  rw [mn_eq hc] at f₁
  -- The multiplication.
  refine WP.seq (WP.mono (hcall s₁ hw₁ (by rw [K₁.gpr _ (by decide)]; exact h3) K₁ U₁ sy₁) fun s₂ ⟨K₂, hp₂'⟩ => ?_)
  obtain ⟨hR, hK⟩ := hp₂'
  have U₂ : Unch base mulKW s₁.mem s₂.mem := unch_of_mulKeeps hK
  have hw₂ := hw₁.of_kp K₂
  have hc₂ := hc₁.of_unch U₂ (by decide)
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (chainPow_ok (P := chainP p384) (F := p384Field) field_ok chainLay unit hw₂
    (one := p384.sl ONEP) (by decide) (by decide)
    (by show sv base s₂ ONEP = _; rw [hc₂.onep]; rfl) chainP_ok) fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  have hw₃ := hw₂.of_kc K₃
  have hc₃ := hc₂.of_unch U₃ (by decide)
  -- `x`.
  refine WP.mono (affine_ok hw₃ (t := XM) (o := XO) (a := RX) (by decide) (by decide) (by decide) (by decide)
    lt₃ hc₃.one) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  have e₄ : ∀ i ∈ [RX, RY, RZ], sv base s₄ i = sv base s₂ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    have h3 : sv base s₃ i = sv base s₂ i := sv_unch U₃ i (by rcases hi with rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl <;> decide)
    rw [← h3]
    exact sv_unch U₄ i (by rcases hi with rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl <;> decide)
  have fl₄ : word s₄.mem base FL = word s₁.mem base FL :=
    fl_unch ((U₂.trans U₃).trans U₄) (by decide)
  have k₁ : MC.scalar base s₁.mem = sv base s K := by
    rw [← e₁ K (by decide)]; exact coord_sv _ _ K
  have acc₄ : sv base s₄ ACC = sv base s₃ ACC := sv_unch U₄ ACC (by decide)
  have v₃' : toM W.p (2 ^ 384) (sv base s₃ ACC) = toM W.p (2 ^ 384) (sv base s₂ RZ) ^ (W.p - 2) := v₃
  refine ⟨K₁.kc.trans (K₂.kc.trans (K₃.trans K₄.kc)), ((U₁.trans U₂).trans U₃).trans U₄, by rw [fl₄, f₁], ?_, lt₄,
    ?_, by rw [acc₄]; exact lt₃, by rw [acc₄, v₃', e₄ RZ (by simp)]⟩
  · intro h1 hn
    rw [k₁, point_eq hL] at hR
    obtain ⟨⟨bx, by', bz⟩, hrep⟩ := hR h1 hn
    simp only [Impl.Weierstrass.Point.Curve.pointAt] at bx by' bz hrep
    have c0 : MC.toPoint.coordAt s₂.mem base MC.pAt = sv base s₂ RX := coord_sv _ _ RX
    have c1 : MC.toPoint.coordAt s₂.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
      sv base s₂ RY := coord_sv _ _ RY
    have c2 : MC.toPoint.coordAt s₂.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
      sv base s₂ RZ := coord_sv _ _ RZ
    rw [c0, c1, c2] at hrep
    rw [c0] at bx; rw [c1] at by'; rw [c2] at bz
    rw [dq hL, dq hL, dq hL] at hrep
    rw [e₄ RX (by simp), e₄ RY (by simp), e₄ RZ (by simp), ← e₁ RX (by decide), ← e₁ RY (by decide)]
    exact ⟨rep_of_represents hrep, bx, by', bz⟩
  · rw [v₄, v₃', e₄ RX (by simp), e₄ RZ (by simp),
      show sv base s₃ RX = sv base s₂ RX from sv_unch U₃ RX (by decide)]


/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  hd _ (Offset.contains_base p (by omega) (by omega))

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  ⟨_, hr, Offset.contains_base p ho (by omega)⟩

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := hsep i hi
  simp only [Region.Contains] at this
  exact U _ fun w hw => .inr (by have := hW w hw; simp only [ofs]; omega)

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts p384, sv base s e.1 = e.2) (k : Nat)
    (hk : k < (consts p384).length := by decide) : sv base s (consts p384)[k].1 = (consts p384)[k].2 :=
  hc _ (List.getElem_mem hk)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at' {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega)


/-- `tail` with `vg_p384_mul`. -/
theorem tail_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX < W.p) (hy : sv base s RY < W.p)
    (hon : Spec.Weierstrass.onCurve W (.affine (toM W.p (2 ^ 384) (sv base s RX))
      (toM W.p (2 ^ 384) (sv base s RY))) = true) :
    WP isa (tail p384 "vg_p384_mul" mulP384) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 384) (sv base s' RX)) (toM W.p (2 ^ 384) (sv base s' RY))
          (toM W.p (2 ^ 384) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 384) (sv base s RX))
            (toM W.p (2 ^ 384) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 384) (sv base s' RX) * toM W.p (2 ^ 384) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 384) (sv base s' ACC) = toM W.p (2 ^ 384) (sv base s' RZ) ^ (W.p - 2) := by
  refine tailWith_ok hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ _ => ?_
  have hc₁ := hc.of_unch U₁ (by decide)
  have e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega)
      (by omega)
  refine wsCallR_ok Impl.Ecdsa.RISCV64.mulP384_noFrames (mul_rv hL) hw₁ h3₁ (fun t r w a m => ?_)
    fun s₂' s₂ K₂ mm₂ t a₂ m₂ hp₂ => ⟨K₂, ?_⟩
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw₁.nowrap, by rw [a]; exact hw₁.al, ?_, ?_⟩
    · rw [a, m]
      refine ⟨(coord_sv _ _ MP).trans hc₁.mp, (coord_sv _ _ ZERO).trans hc₁.zero,
        (coord_sv _ _ ONEP).trans hc₁.onep, (coord_sv _ _ AP).trans hc₁.ap, (coord_sv _ _ B3P).trans hc₁.b3p⟩
    · rw [a, m]
      refine ⟨?_, ?_, ?_⟩
      · show MC.toPoint.coordAt s₁.mem base (p384.sl RX) < W.p
        rw [coord_sv _ _ RX]; exact Nat.lt_of_le_of_lt (Nat.le_of_eq (e₁ RX (by decide))) hx
      · show MC.toPoint.coordAt s₁.mem base (p384.sl RY) < W.p
        rw [coord_sv _ _ RY]; exact Nat.lt_of_le_of_lt (Nat.le_of_eq (e₁ RY (by decide))) hy
      rw [point_eq hL]
      show Spec.Weierstrass.onCurve W (.affine (toM _ _ (sv base s₁ RX)) (toM _ _ (sv base s₁ RY))) = true
      rw [e₁ RX (by decide), e₁ RY (by decide)]; exact hon
  · have := hp₂
    simp only [mulRVc, State.withRegions_mem] at this
    rw [a₂, m₂, ← mm₂] at this
    exact this

end VG.Proof.Ecdh.RISCV64.P384
