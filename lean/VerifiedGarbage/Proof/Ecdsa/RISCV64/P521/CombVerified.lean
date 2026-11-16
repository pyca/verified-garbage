module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Comb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulVerified
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Comb
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulVerified
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU

/-!
# `vg_p521_mul_g` on RISC-V: the contract, and ECDH's `tail` with it

`vg_p521_mul_g(ws = a0)`, an internal function: `vg_p521_mul`'s contract
(`mulRVc`) for `Q = G`, with the table of the comb (`VG_P521_COMB`, its only
readable region): `mulGRVc`, which `mulG_rv` proves from `body_ok` around the
table's address (`lla`), the saves past the numbered slots (at `3304`, by
`sdAt`), the result's conversion from limbs (`convOut_ok`) and the loads.
`tailG_ok` is ECDH's `tail` with `R = [k]G` by a call of it, for P-521's
signatures and public keys, as `Proof/Ecdsa/RISCV64/P384/CombVerified.lean`
gives P-384's.
-/

@[expose] public section

-- `p`, below `2^576`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.P521.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (WP.mono_syms WP.of_syms wp_syms_frame)

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The table's region, at the address `lla` gives its symbol. -/
abbrev tabRegion (s : State) : Region := ⟨s.syms p521Sym, 764928⟩

/-- `vg_p521_mul_g(ws = a0)`: the table its only readable region, its words
there, at a multiple of 64, apart from the working space. -/
def mulGRVc : Contract isa where
  pre s := s.rd = [tabRegion s] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧
    (∀ i < 95616, s.mem.readW (s.syms p521Sym + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0) ∧
    (s.syms p521Sym).toNat % 64 = 0 ∧ (s.syms p521Sym).toNat + 764928 ≤ 2 ^ 64 ∧
    Region.Disjoint (tabRegion s) ⟨s.gpr .a0, 8192⟩
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (Spec.Weierstrass.G W) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.syms p521Sym = s₂.syms p521Sym

theorem combWords_eq : p521CombWords = tabWords := by unfold p521CombWords; rfl

/-- The table, apart from the working space. -/
theorem tabOk_of_pre {s : State} {base : Addr} (hrd : (tabRegion s) ∈ s.rd)
    (hheld : ∀ i < 95616, s.mem.readW (s.syms p521Sym + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0)
    (hal : (s.syms p521Sym).toNat % 64 = 0) (hfit : (s.syms p521Sym).toNat + 764928 ≤ 2 ^ 64)
    (hd : Region.Disjoint (tabRegion s) ⟨base, 8192⟩) : TabOk s base (s.syms p521Sym) where
  held i hi := by rw [hheld i hi, combWords_eq]
  al := hal
  rd := hrd
  fit := hfit
  far d hd' := by
    obtain hc : (tabRegion s).Contains (s.syms p521Sym + BitVec.ofNat 64 d) 1 :=
      Offset.contains_base _ (by omega_using [hd']) (by omega_using [hd'])
    have := hd _ hc
    simp only [Region.Contains, Nat.not_le] at this
    simp only [ofs]; omega_using [this]

/-- The saves, at `mulSave = 3304`. -/
abbrev savesG : List (Nat × Nat) := [(3304, 8), (3312, 8), (3320, 8), (3328, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keepsG_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (savesG ++ (bodyW ++ coutW)) m m') :
    MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ savesG ++ (bodyW ++ coutW), (1072 ≤ w.1 ∧ w.1 + w.2 ≤ 2296) ∨ 3304 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p521, true_and] at hown hp
  omega_using [hp, hw', hown]



/-- `vg_p521_mul_g` meets `mulGRVc`, given the group law. -/
theorem mulG_rv (hL : Law W) (s : State) (hs : mulGRVc.pre s) :
    ∃ t s', Exec isa mulGP521 s t s' ∧ abiPreserved s s' ∧ mulGRVc.post s s' := by
  obtain ⟨hrd, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, hheld, htal, htfit, hdisj⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hdisj
  obtain hT₀ : TabOk s base (s.syms p521Sym) :=
    tabOk_of_pre (by rw [hrd]; exact List.mem_singleton_self _) hheld htal htfit hdisj
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  obtain hp0 : 0 < W.p := by decide
  obtain ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 9 :=
    fun m _ ho => coordAt_eq m base (by omega_using [ho])
  obtain dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 576) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  suffices h : WP isa mulGP521 s fun s' => abiPreserved s s' ∧ mulGRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulGP521, show WindowU.c.mulSave = 3304 from rfl]
  simp only [List.singleton_append, List.append_assoc]
  rw [← List.append_nil (ldAt .s0 .s0 3304)]
  refine WP.seq (WP.cons exec_lla ?_)
  generalize hs₀ : s.write .t0 (s.syms p521Sym) = s₀
  obtain u₀ : Upd s s₀ .t0 (s.syms p521Sym) := hs₀ ▸ Upd.write _ _ _
  obtain b₀ : s₀.gpr .a0 = base := by rw [u₀.other _ (by decide), hb]
  refine sdAt_a0 b₀ (by rw [u₀.wr]; exact hwr') hal (by decide) (d := 3304) (by decide)
    (by decide) fun s₁ u₁ => ?_
  refine sdAt_a0 (by rw [u₁.gpr]; exact b₀) (by rw [u₁.wr, u₀.wr]; exact hwr') hal
    (by decide) (d := 3312) (by decide) (by decide) fun s₂ u₂ => ?_
  refine sdAt_a0 (by rw [u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₂.wr, u₁.wr, u₀.wr]; exact hwr')
    hal (by decide) (d := 3320) (by decide) (by decide) fun s₃ u₃ => ?_
  refine sdAt_a0 (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact b₀)
    (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal (by decide) (d := 3328) (by decide) (by decide)
    fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  obtain g₄ : ∀ r, s₄.gpr r = s₀.gpr r := fun r => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain g₆ : ∀ r, r ≠ .s0 → r ≠ .s4 → s₆.gpr r = s₀.gpr r := fun r h0 h2 => by
    rw [u₆.other r h2, u₅.other r h0, g₄]
  obtain hw₆ : WsReg s₆ base := ⟨by rw [u₆.other _ (by decide), u₅.gpr, g₄, b₀],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr', hfit, hal⟩
  obtain m₄ : s₄.mem = (((s.mem.writeW (off base 3304) (s.gpr .s0)).writeW (off base 3312) (s.gpr .s1)).writeW
      (off base 3320) (s.gpr .ra)).writeW (off base 3328) (s.gpr .s4) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.mem]
    rw [u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide)]
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  obtain O₄ : Unch base savesG s.mem s₆.mem := by
    rw [m₆, m₄]
    exact ((((writeW_outside _ _ _ (by omega_using [])).unch.trans (writeW_outside _ _ _ (by omega_using [])).unch).trans
      (writeW_outside _ _ _ (by omega_using [])).unch).trans (writeW_outside _ _ _ (by omega_using [])).unch)
  obtain sv₆ : ∀ i, i < 45 → sv base s₆ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [savesG, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p521.sl i + 72 ≤ 3304 := by simp only [Cfg.sl, slot, p521]; omega_using [hi]
      rcases hw with rfl | rfl | rfl | rfl <;> (simp only; omega_using [this]))
      (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
  obtain cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p521.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
  obtain hT₆ : TabOk s₆ base (s.syms p521Sym) :=
    hT₀.of_unch (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]) (by decide) O₄
  -- The slots' values, from the contract's.
  obtain hz' : sv base s₆ ZERO = 0 := by rw [sv₆ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  obtain hone' : sv base s₆ ONEP = 2 ^ 576 % W.p := by
    rw [sv₆ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  obtain ha' : sv base s₆ AP = 2 ^ 576 * W.a % W.p := by
    rw [sv₆ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  obtain hb3' : sv base s₆ B3P = 2 ^ 576 * (3 * W.b) % W.p := by
    rw [sv₆ _ (by decide)]; refine (cs B3P (by decide)).symm.trans (hb3.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  -- The body.
  refine WP.seq (WP.mono (body_ok hL hw₆ (by rw [u₆.gpr, u₅.other _ (by decide), g₄, u₀.gpr]) hT₆ hz' hone' ha' hb3')
    fun q₇ ⟨K₇, U₇, pR₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kc K₇
  obtain z₇ : wordsVal q₇.mem base (WindowU.c.sl ZERO) 9 = 0 := by
    rw [U₇.wordsVal (by decide) (by decide)]; exact hz'
  -- Back to Montgomery's form.
  refine WP.seq (WP.mono (convOut_ok hw₇ z₇ pR₇.x pR₇.y pR₇.z) fun q₈ ⟨K₈, U₈, cv₈⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₈
  obtain ⟨ox₈, oy₈, oz₈⟩ := cv₈
  have R₇ := pR₇.rep
  obtain KK : Kc s₆ q₈ := K₇.trans K₈.kc
  obtain UU : Unch base (bodyW ++ coutW) s₆.mem q₈.mem := U₇.trans U₈
  -- The loads.
  obtain hw₈ := hw₆.of_kc KK
  obtain far : ∀ d ∈ [3304, 3312, 3320, 3328], word q₈.mem base d = word s₄.mem base d := fun d hd => by
    rw [UU.word (fun w hw => by
      have := (by decide : ∀ w ∈ bodyW ++ coutW, w.1 + w.2 ≤ 3304 ∨ 3376 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega_using [this, hd]) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd]), m₆]
  obtain w28 : word q₈.mem base 3328 = s.gpr .s4 := by rw [far 3328 (by simp), m₄, word_writeW_self]
  obtain w20 : word q₈.mem base 3320 = s.gpr .ra := by
    rw [far 3320 (by simp), m₄, (writeW_outside (d := 3328) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      word_writeW_self]
  obtain w12 : word q₈.mem base 3312 = s.gpr .s1 := by
    rw [far 3312 (by simp), m₄, (writeW_outside (d := 3328) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3320) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  obtain w04 : word q₈.mem base 3304 = s.gpr .s0 := by
    rw [far 3304 (by simp), m₄, (writeW_outside (d := 3328) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3320) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 3312) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  refine ldAt_ws hw₈ (d := 3320) (by decide) (by decide) fun s₉ u₉ => ?_
  refine ldAt_ws (hw₈.of_kp (Kp.of_upd u₉)) (d := 3328) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  obtain hw₁₀ : WsReg s₁₀ base := ⟨by rw [u₁₀.other .s0 (by decide), u₉.other .s0 (by decide)]; exact hw₈.s0,
    by rw [u₁₀.wr, u₉.wr]; exact hw₈.wr, hfit, hal⟩
  refine ldAt_ws hw₁₀ (d := 3312) (by decide) (by decide) fun s₁₁ u₁₁ => ?_
  obtain hw₁₁ : WsReg s₁₁ base := ⟨by rw [u₁₁.other .s0 (by decide)]; exact hw₁₀.s0,
    by rw [u₁₁.wr]; exact hw₁₀.wr, hfit, hal⟩
  refine ldAt_ws hw₁₁ (d := 3304) (by decide) (by decide) fun s₁₂ u₁₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₁₁ : s₁₁.mem = q₈.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₁₂.gpr, m₁₁, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.mem, u₉.mem, w12]
    by_cases h2 : r = .s4
    · subst h2; rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.mem, w28]
    rw [u₁₂.other _ h0, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ (fun e => by subst e; revert hr; decide),
      KK.gpr r hr h1, g₆ r h0 h2, u₀.other _ (fun e => by subst e; revert hr; decide)]
  · rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, KK.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, w20]
  · have m₁₂ : s₁₂.mem = q₈.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₁₂.mem
    rw [hb, m₁₂]
    refine ⟨fun _ _ => ?_, keepsG_of_unch (O₄.trans UU)⟩
    obtain e : MC.scalar base s.mem = sv base s₆ K := by rw [sv₆ _ (by decide)]; exact cs K (by decide)
    obtain c8 : ∀ i, i < 45 → MC.toPoint.coordAt q₈.mem base (p521.sl i) = sv base q₈ i := fun i hi =>
      ca q₈.mem (by simp only [Cfg.sl, slot, p521]; omega_using [hi])
    obtain x0 : MC.toPoint.coordAt q₈.mem base MC.pAt = sv base q₈ RX := c8 RX (by decide)
    obtain x1 : MC.toPoint.coordAt q₈.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₈ RY := c8 RY (by decide)
    obtain x2 : MC.toPoint.coordAt q₈.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₈ RZ := c8 RZ (by decide)
    have ex : sv base q₈ RX = P521Unsat.uv (P521Unsat.wv base q₇ (WindowU.c.sl RX)) * 2 ^ 55 % W.p := ox₈
    have ey : sv base q₈ RY = P521Unsat.uv (P521Unsat.wv base q₇ (WindowU.c.sl RY)) * 2 ^ 55 % W.p := oy₈
    have ez : sv base q₈ RZ = P521Unsat.uv (P521Unsat.wv base q₇ (WindowU.c.sl RZ)) * 2 ^ 55 % W.p := oz₈
    rw [e]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0, ex]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1, ey]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2, ez]; exact Nat.mod_lt _ hp0
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq, ex, ey, ez, toM_out, toM_out, toM_out]
      exact represents_of_rep R₇

/-! ## The table, for the callers -/

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.CombU VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Point)
open VG.Proof.Ecdh.RISCV64.P521 (TailConsts tailW tailWith_ok coord_sv point_eq sv_unch sl_eq FL)

/-- The table, as the callers of `vg_p521_mul_g` hold it, for the working
space at `base`. -/
structure TabAt (base : Addr) (s : State) : Prop where
  rd : tabRegion s ∈ s.rd
  held : ∀ i < 95616, s.mem.readW (s.syms p521Sym + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0
  al : (s.syms p521Sym).toNat % 64 = 0
  fit : (s.syms p521Sym).toNat + 764928 ≤ 2 ^ 64
  disj : Region.Disjoint (tabRegion s) ⟨base, 8192⟩

/-- The table survives what changes memory only in the working space. -/
theorem TabAt.of_mem {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabAt base s' := by
  obtain hT := tabOk_of_pre h.rd h.held h.al h.fit h.disj
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hm _ ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact hT.far _ (by omega_using [hi, hb])

theorem TabAt.of_unch {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    {W' : List (Nat × Nat)} (hW : ∀ w ∈ W', w.1 + w.2 ≤ 8192) (hu : Unch base W' s.mem s'.mem) : TabAt base s' :=
  h.of_mem hsy hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega_using [hx, this]

/-- The table survives what keeps the symbols and changes memory only in
writable regions apart from it. -/
theorem TabAt.of_frame {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hF : Frame s.wr s.mem s'.mem) (hd : ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r) : TabAt base s' := by
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hF _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by omega_using [hi, hb])]
  omega_using [hi, hb]

theorem combWords_length : p521CombWords.length = 95616 := by
  rw [combWords_eq]
  exact tcombWords_length comb7_len comb7_lenH

/-- A memory holding the table at `0x100000`, for the witnesses of the
contracts with it (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p521CombWords

theorem combSatMem_held : ∀ i < p521CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p521CombWords.getD i 0 := by
  obtain h := constMem_held 0x100000 p521CombWords (by rw [combWords_length]; decide)
  unfold combSatMem
  exact h

/-- The table, as `abi.withConsts p521CombConsts` gives it, for a working space
among the writable regions. -/
theorem tabAt_of_consts {st : Nat} {s : State} {base : Addr} (h : ConstsOk p521CombConsts st s)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) : TabAt base s := by
  have h' : ConstsOk [(p521Sym, p521CombWords)] st s := h
  obtain hr := ConstsOk.rd1 h'
  obtain hw' := ConstsOk.wr1 h' _ hw
  obtain hf := ConstsOk.fit h' List.mem_cons_self
  rw [combWords_length] at hr hw' hf
  exact ⟨hr, fun i hi => ConstsOk.held1 h' i (by rw [combWords_length]; exact hi),
    ConstsOk.aligned h' List.mem_cons_self, hf, hw'⟩

theorem tab_wr_of_consts {st : Nat} {s : State} (h : ConstsOk p521CombConsts st s) :
    ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r := by
  have h' : ConstsOk [(p521Sym, p521CombWords)] st s := h
  obtain hw' := ConstsOk.wr1 h'
  rw [combWords_length] at hw'
  exact hw'

/-- `tail` with `vg_p521_mul_g`, from `G` in `R`'s first two slots. -/
theorem tailG_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX = W.gx * 2 ^ 576 % W.p)
    (hy : sv base s RY = W.gy * 2 ^ 576 % W.p) (hT : TabAt base s) :
    WP isa (Impl.Ecdh.RISCV64.Cfg.tail p521 mulGP521Name mulGP521) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 576) (sv base s' RX)) (toM W.p (2 ^ 576) (sv base s' RY))
          (toM W.p (2 ^ 576) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 576) (sv base s RX))
            (toM W.p (2 ^ 576) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 576) (sv base s' RX) * toM W.p (2 ^ 576) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 576) (sv base s' ACC) = toM W.p (2 ^ 576) (sv base s' RZ) ^ (W.p - 2) := by
  refine tailWith_ok hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ sy₁ => ?_
  obtain hc₁ := hc.of_unch U₁ (by decide)
  obtain e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega_using [hi])
      (by omega_using [hi])
  obtain hT₁ : TabAt base s₁ := hT.of_unch sy₁ K₁.rd (by decide) U₁
  obtain eG : MC.point base s₁.mem = Spec.Weierstrass.G W := by
    rw [point_eq hL]
    show Point.affine (toM _ _ (sv base s₁ RX)) (toM _ _ (sv base s₁ RY)) = _
    rw [e₁ RX (by decide), e₁ RY (by decide), hx, hy]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  -- The call, with the table its readable region.
  rw [Cfg.wsCall, eG]
  refine WP.seq (WP.seq (WP.cons (exec_addi (by decide)) (WP.block_nil ?_)))
  generalize hs₂ : s₁.write .a0 (s₁.gpr wb + BitVec.ofInt 64 0) = s₂
  obtain u₂ : Upd s₁ s₂ .a0 (s₁.gpr wb + BitVec.ofInt 64 0) := hs₂ ▸ Upd.write _ _ _
  obtain sy₂ : s₂.syms = s₁.syms := by rw [← hs₂]; rfl
  obtain K₂ : Kp s₁ s₂ := Kp.of_upd u₂
  obtain a0₂ : s₂.gpr .a0 = base := by rw [u₂.gpr, hw₁.s0]; simp
  obtain hcov : Covers [⟨base, 8192⟩] s₂.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.wr]; exact hw₁.wr
  obtain htab : Covers [tabRegion s₂] s₂.rd := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.rd, tabRegion, sy₂]; exact hT₁.rd
  obtain e0 : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).gpr .a0 = base := by
    simp only [State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), a0₂]
  obtain em : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).mem = s₁.mem := by
    simp only [State.withRegions_mem, State.callEntry_mem, u₂.mem]
  refine WP.call (mulG_rv hL) (rd := [tabRegion s₂]) (wr := [⟨base, 8192⟩]) ?_ (Covers.append htab hcov) hcov
    (fun s₃ r₃ w₃ p₃ _ G₃ _ hp => ?_) Impl.Ecdsa.RISCV64.CombU.mulGP521_noFrames
  · refine ⟨rfl, by rw [e0]; rfl, by rw [e0]; exact hw₁.nowrap, by rw [e0]; exact hw₁.al, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, em]
      exact ⟨(coord_sv _ _ MP).trans hc₁.mp, (coord_sv _ _ ZERO).trans hc₁.zero,
        (coord_sv _ _ ONEP).trans hc₁.onep, (coord_sv _ _ AP).trans hc₁.ap, (coord_sv _ _ B3P).trans hc₁.b3p⟩
    · rw [em]; exact fun i hi => by rw [show (s₂.callEntry.withRegions _ _).syms = s₁.syms from sy₂]; exact hT₁.held i hi
    · exact (show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂) ▸ hT₁.al
    · exact (show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂) ▸ hT₁.fit
    · rw [e0]
      simp only [tabRegion]
      rw [show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂]
      exact hT₁.disj
  -- `s0` from `s3`.
  refine wp_mv fun s₄ u₄ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₄.rd, r₃, K₂.rd], by rw [u₄.wr, w₃, K₂.wr],
    by rw [u₄.sp, p₃, K₂.sp]⟩, ?_⟩
  · by_cases h : r = .s0
    · subst h; rw [u₄.gpr, G₃ _ (by decide), K₂.gpr _ (by decide), h3₁, hw₁.s0]
    · rw [u₄.other _ h, G₃ _ hr, K₂.gpr _ hr]
  · have := hp
    simp only [mulGRVc, State.withRegions_mem] at this
    rw [e0] at this
    rw [show s₂.callEntry.mem = s₁.mem by rw [State.callEntry_mem, u₂.mem]] at this
    rw [u₄.mem]
    exact this

/-! The constant-time analyses of the calls of the functions on limbs from their arguments, with
the comb's table public, each done once for every check of code that calls it, which keep what is
public of `s0`–`s11`: the functions write none of them. -/
taint_summary uMulSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "mul") Impl.Weierstrass.RISCV64.P521Unsat.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uAddSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "add") Impl.Weierstrass.RISCV64.P521Unsat.addFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uSubSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "sub") Impl.Weierstrass.RISCV64.P521Unsat.subFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uPackSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "pack") Impl.Weierstrass.RISCV64.P521Unsat.packFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
taint_summary uUnpackSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.RISCV64.P521Unsat.S.fn "unpack") Impl.Weierstrass.RISCV64.P521Unsat.unpackFn)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

/-! The same for the multiplication modulo `p` in Montgomery's form, which the comb's callers
call (the inversion and the affine coordinates). -/
taint_summary pMulSymSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p521p.fn "mul") Impl.Weierstrass.RISCV64.P521Field.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

/-! The constant-time analysis of the call of `vg_p521_mul_g` from its argument, with the comb's
table public, done once for every check of code that calls it, which keeps what is public of `s2`,
`s3` and `s5`–`s11`: the function writes none of them (`s0`, `s1` and `s4` it restores from
memory). -/
taint_summary mulGSum : (taintSym [p521Sym]) (Taint.ofRegs [.a0])
  (.call mulGP521Name mulGP521)
  keeping (Taint.ofRegs [.s2, .s3, .s5, .s6, .s7, .s8, .s9, .s10, .s11])
  using uMulSymSum uAddSymSum uSubSymSum uPackSymSum uUnpackSymSum

end VG.Proof.Ecdsa.RISCV64.P521.Comb
