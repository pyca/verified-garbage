module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Comb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulVerified
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Comb
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulVerified
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Tail
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail

/-!
# `vg_p384_mul_g` on RISC-V: the contract, and ECDH's `tail` with it

`vg_p384_mul_g(ws = a0)`, an internal function: `vg_p384_mul`'s contract
(`mulRVc`) for `Q = G`, with the table of the comb (`VG_P384_COMB`, its only
readable region): `mulGRVc`, which `mulG_rv` proves from `body_ok` around the
table's address (`lla`), the saves past the numbered slots (at `2224`, by
`sdAt`) and their loads; `mulG_ct` is its constant time, by taint tracking.
`tailG_ok` is ECDH's `tail` with `R = [k]G` by a call of it, for P-384's
signatures and public keys, as `Proof/Ecdsa/RISCV64/Comb/Tail.lean` gives
P-256's.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.P384.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (WP.mono_syms WP.of_syms wp_syms_frame)

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W MC coordAt_eq represents_of_rep unit)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The table's region, at the address `lla` gives its symbol. -/
abbrev tabRegion (s : State) : Region := ⟨s.syms p384Sym, 337920⟩

/-- `vg_p384_mul_g(ws = a0)`: the table its only readable region, its words
there, at a multiple of 64, apart from the working space; `b` in Montgomery's
form at slot 40 (byte 1984), for the complete addition for `a = -3`. -/
def mulGRVc : Contract isa where
  pre s := s.rd = [tabRegion s] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧
    wordsVal s.mem (s.gpr .a0) 1984 6 = W.b * 2 ^ 384 % W.p ∧
    (∀ i < 42240, s.mem.readW (s.syms p384Sym + BitVec.ofNat 64 (8 * i)) 64 = p384CombWords.getD i 0) ∧
    (s.syms p384Sym).toNat % 64 = 0 ∧ (s.syms p384Sym).toNat + 337920 ≤ 2 ^ 64 ∧
    Region.Disjoint (tabRegion s) ⟨s.gpr .a0, 8192⟩
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (Spec.Weierstrass.G W) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.syms p384Sym = s₂.syms p384Sym

theorem combWords_eq : p384CombWords = tabWords := by unfold p384CombWords; rfl

/-- The table, apart from the working space. -/
theorem tabOk_of_pre {s : State} {base : Addr} (hrd : (tabRegion s) ∈ s.rd)
    (hheld : ∀ i < 42240, s.mem.readW (s.syms p384Sym + BitVec.ofNat 64 (8 * i)) 64 = p384CombWords.getD i 0)
    (hal : (s.syms p384Sym).toNat % 64 = 0) (hfit : (s.syms p384Sym).toNat + 337920 ≤ 2 ^ 64)
    (hd : Region.Disjoint (tabRegion s) ⟨base, 8192⟩) : TabOk s base (s.syms p384Sym) where
  held i hi := by rw [hheld i hi, combWords_eq]
  al := hal
  rd := hrd
  fit := hfit
  far d hd' := by
    have hc : (tabRegion s).Contains (s.syms p384Sym + BitVec.ofNat 64 d) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have := hd _ hc
    simp only [Region.Contains, Nat.not_le] at this
    simp only [ofs]; omega

/-- The saves, at `mulSave = 2224`. -/
abbrev savesG : List (Nat × Nat) := [(2224, 8), (2232, 8), (2240, 8), (2248, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keepsG_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (savesG ++ bodyW) m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hw' := (by decide : ∀ w ∈ savesG ++ bodyW, (w.1 = 736 ∧ w.2 = 816) ∨ 2224 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p384, true_and] at hown hp
  omega


/-- `vg_p384_mul_g` meets `mulGRVc`, given the group law. -/
theorem mulG_rv (hL : Law W) (s : State) (hs : mulGRVc.pre s) :
    ∃ t s', Exec isa mulGP384 s t s' ∧ abiPreserved s s' ∧ mulGRVc.post s s' := by
  obtain ⟨hrd, hwr, hfit, hal, ⟨-, hz, hone, ha, -⟩, hbp, hheld, htal, htfit, hdisj⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hbp hdisj
  have hT₀ : TabOk s base (s.syms p384Sym) :=
    tabOk_of_pre (by rw [hrd]; exact List.mem_singleton_self _) hheld htal htfit hdisj
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 384) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  suffices h : WP isa mulGP384 s fun s' => abiPreserved s s' ∧ mulGRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulGP384, Cfg.combFn, show p384.mulSave = 2224 from rfl]
  simp only [List.singleton_append, List.append_assoc]
  rw [← List.append_nil (ldAt .s0 .s0 2224)]
  refine WP.seq (WP.cons exec_lla ?_)
  generalize hs₀ : s.write .t0 (s.syms p384Sym) = s₀
  have u₀ : Upd s s₀ .t0 (s.syms p384Sym) := hs₀ ▸ Upd.write _ _ _
  have b₀ : s₀.gpr .a0 = base := by rw [u₀.other _ (by decide), hb]
  refine VG.Proof.Ecdsa.RISCV64.P384.sdAt_a0 b₀ (by rw [u₀.wr]; exact hwr') hal (by decide) (d := 2224) (by decide)
    (by decide) fun s₁ u₁ => ?_
  refine VG.Proof.Ecdsa.RISCV64.P384.sdAt_a0 (by rw [u₁.gpr]; exact b₀) (by rw [u₁.wr, u₀.wr]; exact hwr') hal
    (by decide) (d := 2232) (by decide) (by decide) fun s₂ u₂ => ?_
  refine VG.Proof.Ecdsa.RISCV64.P384.sdAt_a0 (by rw [u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₂.wr, u₁.wr, u₀.wr]; exact hwr')
    hal (by decide) (d := 2240) (by decide) (by decide) fun s₃ u₃ => ?_
  refine VG.Proof.Ecdsa.RISCV64.P384.sdAt_a0 (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact b₀)
    (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal (by decide) (d := 2248) (by decide) (by decide)
    fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have g₄ : ∀ r, s₄.gpr r = s₀.gpr r := fun r => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have g₆ : ∀ r, r ≠ .s0 → r ≠ .s4 → s₆.gpr r = s₀.gpr r := fun r h0 h2 => by
    rw [u₆.other r h2, u₅.other r h0, g₄]
  have hw₆ : WsReg s₆ base := ⟨by rw [u₆.other _ (by decide), u₅.gpr, g₄, b₀],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr', hfit, hal⟩
  have m₄ : s₄.mem = (((s.mem.writeW (off base 2224) (s.gpr .s0)).writeW (off base 2232) (s.gpr .s1)).writeW
      (off base 2240) (s.gpr .ra)).writeW (off base 2248) (s.gpr .s4) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.mem]
    rw [u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide)]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have O₄ : Unch base savesG s.mem s₆.mem := by
    rw [m₆, m₄]
    exact ((((writeW_outside _ _ _ (by omega)).unch.trans (writeW_outside _ _ _ (by omega)).unch).trans
      (writeW_outside _ _ _ (by omega)).unch).trans (writeW_outside _ _ _ (by omega)).unch)
  have e₆ : ∀ d, d + 48 ≤ 2224 → wordsVal s₆.mem base d 6 = wordsVal s.mem base d 6 := fun d hd =>
    O₄.wordsVal (by simp; omega) (by omega)
  have cs : ∀ d, d < 4096 → MC.toPoint.coordAt s.mem base d = wordsVal s.mem base d 6 := fun d hd =>
    coordAt_eq s.mem base (by omega)
  have tm : ∀ x, toM W.p (2 ^ 384) (x * 2 ^ (64 * 6) % W.p) = Fin.ofNat W.p x := fun x => toM_mont unit
  have hT₆ : TabOk s₆ base (s.syms p384Sym) :=
    hT₀.of_unch (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]) (by decide) O₄
  have hz₆ : wordsVal s₆.mem base 208 6 = 0 := by rw [e₆ 208 (by omega), ← cs 208 (by omega)]; exact hz
  have h1₆ : wordsVal s₆.mem base 304 6 = oneM := by
    rw [e₆ 304 (by omega), ← cs 304 (by omega)]
    refine hone.trans ?_
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  have ha₆ : wordsVal s₆.mem base 352 6 = W.a * 2 ^ (64 * 6) % W.p := by
    rw [e₆ 352 (by omega), ← cs 352 (by omega)]; exact ha
  have hb₆ : wordsVal s₆.mem base 1984 6 = W.b * 2 ^ (64 * 6) % W.p := by
    rw [e₆ 1984 (by omega)]; exact hbp
  -- The body.
  refine WP.seq (WP.mono (body_ok hL hw₆ (by rw [u₆.gpr, u₅.other _ (by decide), g₄, u₀.gpr]) hT₆ hz₆ h1₆
    (by simp only [tmv]; rw [ha₆]; exact tm _) (by simp only [tmv]; rw [hb₆]; exact tm _)
    (by rw [ha₆]; exact Nat.mod_lt _ (by decide)) (by rw [hb₆]; exact Nat.mod_lt _ (by decide)))
    fun s₇ ⟨K₇, U₇, _, lt₇, R₇⟩ => ?_)
  have hw₇ := hw₆.of_kc K₇
  -- The loads.
  have far : ∀ d ∈ [2224, 2232, 2240, 2248], word s₇.mem base d = word s₄.mem base d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rw [U₇.word (fun w hw => by
      simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega) (by omega), m₆]
  have w28 : word s₇.mem base 2248 = s.gpr .s4 := by rw [far 2248 (by simp), m₄, word_writeW_self]
  have w20 : word s₇.mem base 2240 = s.gpr .ra := by
    rw [far 2240 (by simp), m₄, (writeW_outside (d := 2248) _ base _ (by omega)).word (by omega) (by omega),
      word_writeW_self]
  have w12 : word s₇.mem base 2232 = s.gpr .s1 := by
    rw [far 2232 (by simp), m₄, (writeW_outside (d := 2248) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 2240) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  have w04 : word s₇.mem base 2224 = s.gpr .s0 := by
    rw [far 2224 (by simp), m₄, (writeW_outside (d := 2248) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 2240) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 2232) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  refine ldAt_ws hw₇ (d := 2240) (by decide) (by decide) fun s₈ u₈ => ?_
  refine ldAt_ws (hw₇.of_kp (Kp.of_upd u₈)) (d := 2248) (by decide) (by decide) fun s₉ u₉ => ?_
  have hw₉ : WsReg s₉ base := ⟨by rw [u₉.other .s0 (by decide), u₈.other .s0 (by decide)]; exact hw₇.s0,
    by rw [u₉.wr, u₈.wr]; exact hw₇.wr, hfit, hal⟩
  refine ldAt_ws hw₉ (d := 2232) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  have hw₁₀ : WsReg s₁₀ base := ⟨by rw [u₁₀.other .s0 (by decide)]; exact hw₉.s0,
    by rw [u₁₀.wr]; exact hw₉.wr, hfit, hal⟩
  refine ldAt_ws hw₁₀ (d := 2224) (by decide) (by decide) fun s₁₁ u₁₁ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₁₀ : s₁₀.mem = s₇.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₁₁.gpr, m₁₀, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.mem, u₈.mem, w12]
    by_cases h2 : r = .s4
    · subst h2; rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, w28]
    rw [u₁₁.other _ h0, u₁₀.other _ h1, u₉.other _ h2, u₈.other _ (fun e => by subst e; revert hr; decide),
      K₇.gpr r hr h1, g₆ r h0 h2, u₀.other _ (fun e => by subst e; revert hr; decide)]
  · rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, K₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, w20]
  · have m₁₁ : s₁₁.mem = s₇.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₁₁.mem
    rw [hb, m₁₁]
    refine ⟨fun _ _ => ?_, keepsG_of_unch (O₄.trans U₇)⟩
    have e : MC.scalar base s.mem = wordsVal s₆.mem base 1552 6 := by
      rw [e₆ 1552 (by omega)]; exact cs 1552 (by omega)
    have c7 : ∀ d, d < 4096 → MC.toPoint.coordAt s₇.mem base d = wordsVal s₇.mem base d 6 := fun d hd =>
      coordAt_eq s₇.mem base (by omega)
    have x0 : MC.toPoint.coordAt s₇.mem base MC.pAt = wordsVal s₇.mem base 736 6 := c7 736 (by omega)
    have x1 : MC.toPoint.coordAt s₇.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        wordsVal s₇.mem base 784 6 := c7 784 (by omega)
    have x2 : MC.toPoint.coordAt s₇.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        wordsVal s₇.mem base 832 6 := c7 832 (by omega)
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lt₇
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact lt₇.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact lt₇.2.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact lt₇.2.2
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₇

/-! ## Constant time -/

theorem mulG_ct : ConstantTime isa mulGRVc.pre mulGRVc.pub mulGP384 :=
  VG.Taint.constantTime (A := taintSym [p384Sym]) (Taint.ofRegs [.a0])
    (fun _ _ _ _ ⟨hsp, h0, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact h0⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)


open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W MC unit sv)
open VG.Spec.Weierstrass (Point)
open VG.Proof.Ecdh.RISCV64.P384 (TailConsts tailW tailWith_ok coord_sv point_eq sv_unch sl_eq FL)

/-- The table, as the callers of `vg_p384_mul_g` hold it, for the working
space at `base`. -/
structure TabAt (base : Addr) (s : State) : Prop where
  rd : tabRegion s ∈ s.rd
  held : ∀ i < 42240, s.mem.readW (s.syms p384Sym + BitVec.ofNat 64 (8 * i)) 64 = p384CombWords.getD i 0
  al : (s.syms p384Sym).toNat % 64 = 0
  fit : (s.syms p384Sym).toNat + 337920 ≤ 2 ^ 64
  disj : Region.Disjoint (tabRegion s) ⟨base, 8192⟩

/-- The table survives what changes memory only in the working space. -/
theorem TabAt.of_mem {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabAt base s' := by
  have hT := tabOk_of_pre h.rd h.held h.al h.fit h.disj
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hm _ ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact hT.far _ (by omega)

theorem TabAt.of_unch {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    {W' : List (Nat × Nat)} (hW : ∀ w ∈ W', w.1 + w.2 ≤ 8192) (hu : Unch base W' s.mem s'.mem) : TabAt base s' :=
  h.of_mem hsy hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega

/-- The table survives what keeps the symbols and changes memory only in
writable regions apart from it. -/
theorem TabAt.of_frame {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hF : Frame s.wr s.mem s'.mem) (hd : ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r) : TabAt base s' := by
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hF _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by omega)]
  omega

theorem combWords_length : p384CombWords.length = 42240 := by
  rw [combWords_eq]
  exact tcombWords_length comb7_len comb7_lenH

/-- A memory holding the table at `0x100000`, for the witnesses of the
contracts with it (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p384CombWords

theorem combSatMem_held : ∀ i < p384CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384CombWords.getD i 0 := by
  have h := constMem_held 0x100000 p384CombWords (by rw [combWords_length]; decide)
  unfold combSatMem
  exact h

/-- The table, as `abi.withConsts p384CombConsts` gives it, for a working space
among the writable regions. -/
theorem tabAt_of_consts {st : Nat} {s : State} {base : Addr} (h : ConstsOk p384CombConsts st s)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) : TabAt base s := by
  have h' : ConstsOk [(p384Sym, p384CombWords)] st s := h
  have hr := ConstsOk.rd1 h'
  have hw' := ConstsOk.wr1 h' _ hw
  have hf := ConstsOk.fit h' List.mem_cons_self
  rw [combWords_length] at hr hw' hf
  exact ⟨hr, fun i hi => ConstsOk.held1 h' i (by rw [combWords_length]; exact hi),
    ConstsOk.aligned h' List.mem_cons_self, hf, hw'⟩

theorem tab_wr_of_consts {st : Nat} {s : State} (h : ConstsOk p384CombConsts st s) :
    ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r := by
  have h' : ConstsOk [(p384Sym, p384CombWords)] st s := h
  have hw' := ConstsOk.wr1 h'
  rw [combWords_length] at hw'
  exact hw'

/-- `tail` with `vg_p384_mul_g`, from `G` in `R`'s first two slots. -/
theorem tailG_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX = W.gx * 2 ^ 384 % W.p)
    (hy : sv base s RY = W.gy * 2 ^ 384 % W.p) (hbp : sv base s BP = W.b * 2 ^ 384 % W.p) (hT : TabAt base s) :
    WP isa (Impl.Ecdh.RISCV64.Cfg.tail p384 mulGP384Name mulGP384) s fun s' =>
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
  refine tailWith_ok hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ sy₁ => ?_
  have hc₁ := hc.of_unch U₁ (by decide)
  have e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega)
      (by omega)
  have hT₁ : TabAt base s₁ := hT.of_unch sy₁ K₁.rd (by decide) U₁
  have eG : MC.point base s₁.mem = Spec.Weierstrass.G W := by
    rw [point_eq hL]
    show Point.affine (toM _ _ (sv base s₁ RX)) (toM _ _ (sv base s₁ RY)) = _
    rw [e₁ RX (by decide), e₁ RY (by decide), hx, hy]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  -- The call, with the table its readable region.
  rw [Cfg.wsCall, eG]
  refine WP.seq (WP.seq (WP.cons (exec_addi (by decide)) (WP.block_nil ?_)))
  generalize hs₂ : s₁.write .a0 (s₁.gpr wb + BitVec.ofInt 64 0) = s₂
  have u₂ : Upd s₁ s₂ .a0 (s₁.gpr wb + BitVec.ofInt 64 0) := hs₂ ▸ Upd.write _ _ _
  have sy₂ : s₂.syms = s₁.syms := by rw [← hs₂]; rfl
  have K₂ : Kp s₁ s₂ := Kp.of_upd u₂
  have a0₂ : s₂.gpr .a0 = base := by rw [u₂.gpr, hw₁.s0]; simp
  have hcov : Covers [⟨base, 8192⟩] s₂.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.wr]; exact hw₁.wr
  have htab : Covers [tabRegion s₂] s₂.rd := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.rd, tabRegion, sy₂]; exact hT₁.rd
  have e0 : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).gpr .a0 = base := by
    simp only [State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), a0₂]
  have em : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).mem = s₁.mem := by
    simp only [State.withRegions_mem, State.callEntry_mem, u₂.mem]
  refine WP.call (mulG_rv hL) (rd := [tabRegion s₂]) (wr := [⟨base, 8192⟩]) ?_ (Covers.append htab hcov) hcov
    (fun s₃ r₃ w₃ p₃ _ G₃ _ hp => ?_) Impl.Ecdsa.RISCV64.Comb.mulGP384_noFrames
  · refine ⟨rfl, by rw [e0]; rfl, by rw [e0]; exact hw₁.nowrap, by rw [e0]; exact hw₁.al, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, em]
      exact ⟨(coord_sv _ _ MP).trans hc₁.mp, (coord_sv _ _ ZERO).trans hc₁.zero,
        (coord_sv _ _ ONEP).trans hc₁.onep, (coord_sv _ _ AP).trans hc₁.ap, (coord_sv _ _ B3P).trans hc₁.b3p⟩
    · rw [e0, em]; exact (e₁ BP (by decide)).trans hbp
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

end VG.Proof.Ecdsa.RISCV64.P384.Comb
