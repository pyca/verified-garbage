module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Lit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Lit
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_p256_mul_g` on RISC-V: the contract

`vg_p256_mul_g(ws = a0)`, an internal function: `vg_p256_mul`'s contract
(`mulRVc`) for `Q = G`, which it does not read, with the table of the comb
(`VG_P256_COMB`, its only readable region): `mulGRVc`. `mulG_rv` proves it
from `body_ok`, around the table's address (`lla`, first), the saves of
`s0`, `s1`, `ra` and `s4` (past the numbered slots) and their loads.
`mulG_ct` is its constant time, by taint tracking: only the pointer, in
`a0`, and the table's address are public.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Comb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (W MC coordAt_eq represents_of_rep unit)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The table's region, at the address `lla` gives its symbol. -/
abbrev tabRegion (s : State) : Region := ⟨s.syms p256Sym, 151552⟩

/-- `vg_p256_mul_g(ws = a0)`: the table its only readable region, its words
there, at a multiple of 64, apart from the working space. -/
def mulGRVc : Contract isa where
  pre s := s.rd = [tabRegion s] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧
    (∀ i < 18944, s.mem.readW (s.syms p256Sym + BitVec.ofNat 64 (8 * i)) 64 = p256CombWords.getD i 0) ∧
    (s.syms p256Sym).toNat % 64 = 0 ∧ (s.syms p256Sym).toNat + 151552 ≤ 2 ^ 64 ∧
    Region.Disjoint (tabRegion s) ⟨s.gpr .a0, 8192⟩
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (Spec.Weierstrass.G W) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.syms p256Sym = s₂.syms p256Sym

theorem combWords_eq : p256CombWords = tabWords := by unfold p256CombWords; rfl

/-- The table, apart from the working space. -/
theorem tabOk_of_pre {s : State} {base : Addr} (hrd : (tabRegion s) ∈ s.rd)
    (hheld : ∀ i < 18944, s.mem.readW (s.syms p256Sym + BitVec.ofNat 64 (8 * i)) 64 = p256CombWords.getD i 0)
    (hal : (s.syms p256Sym).toNat % 64 = 0) (hfit : (s.syms p256Sym).toNat + 151552 ≤ 2 ^ 64)
    (hd : Region.Disjoint (tabRegion s) ⟨base, 8192⟩) : TabOk s base (s.syms p256Sym) where
  held i hi := by rw [hheld i hi, combWords_eq]
  al := hal
  rd := hrd
  fit := hfit
  far d hd' := by
    have hc : (tabRegion s).Contains (s.syms p256Sym + BitVec.ofNat 64 d) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have := hd _ hc
    simp only [Region.Contains, Nat.not_le] at this
    simp only [ofs]; omega

/-- The saves, at `mulSave = 1504`. -/
abbrev savesG : List (Nat × Nat) := [(1504, 8), (1512, 8), (1520, 8), (1528, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keepsG_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (savesG ++ bodyW) m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Spec.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hw' := (by decide : ∀ w ∈ savesG ++ bodyW, (w.1 = 512 ∧ w.2 = 544) ∨ 1504 ≤ w.1) w hw
  simp only [Spec.Weierstrass.Mul.Curve.Own, Spec.Weierstrass.Mul.Curve.slot, Spec.Weierstrass.Mul.Curve.tmpAt,
    Spec.Weierstrass.Mul.Curve.bitsAt, Spec.Weierstrass.Mul.Curve.pAt, Spec.Weierstrass.Mul.Curve.ptBytes,
    MC, Spec.Weierstrass.Mul.p256, true_and] at hown hp
  omega


/-- `vg_p256_mul_g` meets `mulGRVc`, given the group law. -/
theorem mulG_rv (hL : Law W) (s : State) (hs : mulGRVc.pre s) :
    ∃ t s', Exec isa mulGP256 s t s' ∧ abiPreserved s s' ∧ mulGRVc.post s s' := by
  obtain ⟨hrd, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, hheld, htal, htfit, hdisj⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hdisj
  have hT₀ : TabOk s base (s.syms p256Sym) :=
    tabOk_of_pre (by rw [hrd]; exact List.mem_singleton_self _) hheld htal htfit hdisj
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  suffices h : WP isa mulGP256 s fun s' => abiPreserved s s' ∧ mulGRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulGP256, Cfg.combFn, show p256.mulSave = 1504 from rfl]
  refine WP.seq (WP.cons exec_lla ?_)
  generalize hs₀ : s.write .t0 (s.syms p256Sym) = s₀
  have u₀ : Upd s s₀ .t0 (s.syms p256Sym) := hs₀ ▸ Upd.write _ _ _
  have b₀ : s₀.gpr .a0 = base := by rw [u₀.other _ (by decide), hb]
  refine sd_a0 b₀ (by rw [u₀.wr]; exact hwr') hal (d := 1504) (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_a0 (by rw [u₁.gpr]; exact b₀) (by rw [u₁.wr, u₀.wr]; exact hwr') hal (d := 1512) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sd_a0 (by rw [u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal (d := 1520)
    (by decide) (by decide) fun s₃ u₃ => ?_
  refine sd_a0 (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal
    (d := 1528) (by decide) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have g₄ : ∀ r, s₄.gpr r = s₀.gpr r := fun r => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have g₆ : ∀ r, r ≠ .s0 → r ≠ .s4 → s₆.gpr r = s₀.gpr r := fun r h0 h2 => by
    rw [u₆.other r h2, u₅.other r h0, g₄]
  have hw₆ : WsReg s₆ base := ⟨by rw [u₆.other _ (by decide), u₅.gpr, g₄, b₀],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr', hfit, hal⟩
  have m₄ : s₄.mem = (((s.mem.writeW (off base 1504) (s.gpr .s0)).writeW (off base 1512) (s.gpr .s1)).writeW
      (off base 1520) (s.gpr .ra)).writeW (off base 1528) (s.gpr .s4) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.mem]
    rw [u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide)]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have O₄ : Unch base savesG s.mem s₆.mem := by
    rw [m₆, m₄]
    exact ((((writeW_outside _ _ _ (by omega)).unch.trans (writeW_outside _ _ _ (by omega)).unch).trans
      (writeW_outside _ _ _ (by omega)).unch).trans (writeW_outside _ _ _ (by omega)).unch)
  have e₆ : ∀ d, d + 32 ≤ 1504 → wordsVal s₆.mem base d 4 = wordsVal s.mem base d 4 := fun d hd =>
    O₄.wordsVal (by simp; omega) (by omega)
  have cs : ∀ d, d < 4096 → MC.toPoint.coordAt s.mem base d = wordsVal s.mem base d 4 := fun d hd =>
    coordAt_eq s.mem base (by omega)
  have tm : ∀ x, toM W.p (2 ^ 256) (x * 2 ^ (64 * 4) % W.p) = Fin.ofNat W.p x := fun x => toM_mont unit
  have hT₆ : TabOk s₆ base (s.syms p256Sym) :=
    hT₀.of_unch (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]) (by decide) O₄
  have hz₆ : wordsVal s₆.mem base 160 4 = 0 := by rw [e₆ 160 (by omega), ← cs 160 (by omega)]; exact hz
  have h1₆ : wordsVal s₆.mem base 224 4 = oneM := by
    rw [e₆ 224 (by omega), ← cs 224 (by omega)]
    refine hone.trans ?_
    simp only [Spec.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  have ha₆ : wordsVal s₆.mem base 256 4 = W.a * 2 ^ (64 * 4) % W.p := by
    rw [e₆ 256 (by omega), ← cs 256 (by omega)]; exact ha
  have hb₆ : wordsVal s₆.mem base 288 4 = (3 * W.b) * 2 ^ (64 * 4) % W.p := by
    rw [e₆ 288 (by omega), ← cs 288 (by omega)]; exact hb3
  -- The body.
  refine WP.seq (WP.mono (body_ok hL hw₆ (by rw [u₆.gpr, u₅.other _ (by decide), g₄, u₀.gpr]) hT₆ hz₆ h1₆
    (by simp only [tmv]; rw [ha₆]; exact tm _) (by simp only [tmv]; rw [hb₆]; exact tm _)
    (by rw [ha₆]; exact Nat.mod_lt _ (by decide)) (by rw [hb₆]; exact Nat.mod_lt _ (by decide)))
    fun s₇ ⟨K₇, U₇, _, lt₇, R₇⟩ => ?_)
  have hw₇ := hw₆.of_kc K₇
  -- The loads.
  have far : ∀ d ∈ [1504, 1512, 1520, 1528], word s₇.mem base d = word s₄.mem base d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rw [U₇.word (fun w hw => by
      simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega) (by omega), m₆]
  have w28 : word s₇.mem base 1528 = s.gpr .s4 := by rw [far 1528 (by simp), m₄, word_writeW_self]
  have w20 : word s₇.mem base 1520 = s.gpr .ra := by
    rw [far 1520 (by simp), m₄, (writeW_outside (d := 1528) _ base _ (by omega)).word (by omega) (by omega),
      word_writeW_self]
  have w12 : word s₇.mem base 1512 = s.gpr .s1 := by
    rw [far 1512 (by simp), m₄, (writeW_outside (d := 1528) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 1520) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  have w04 : word s₇.mem base 1504 = s.gpr .s0 := by
    rw [far 1504 (by simp), m₄, (writeW_outside (d := 1528) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 1520) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 1512) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  refine ld_ws hw₇ (d := 1520) (by decide) (by decide) fun s₈ u₈ => ?_
  refine ld_ws (hw₇.of_kp (Kp.of_upd u₈)) (d := 1528) (by decide) (by decide) fun s₉ u₉ => ?_
  have hw₉ : WsReg s₉ base := ⟨by rw [u₉.other .s0 (by decide), u₈.other .s0 (by decide)]; exact hw₇.s0,
    by rw [u₉.wr, u₈.wr]; exact hw₇.wr, hfit, hal⟩
  refine ld_ws hw₉ (d := 1512) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  have hw₁₀ : WsReg s₁₀ base := ⟨by rw [u₁₀.other .s0 (by decide)]; exact hw₉.s0,
    by rw [u₁₀.wr]; exact hw₉.wr, hfit, hal⟩
  refine ld_ws hw₁₀ (d := 1504) (by decide) (by decide) fun s₁₁ u₁₁ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
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
    have e : MC.scalar base s.mem = wordsVal s₆.mem base 1056 4 := by
      rw [e₆ 1056 (by omega)]; exact cs 1056 (by omega)
    have c7 : ∀ d, d < 4096 → MC.toPoint.coordAt s₇.mem base d = wordsVal s₇.mem base d 4 := fun d hd =>
      coordAt_eq s₇.mem base (by omega)
    have x0 : MC.toPoint.coordAt s₇.mem base MC.pAt = wordsVal s₇.mem base 512 4 := c7 512 (by omega)
    have x1 : MC.toPoint.coordAt s₇.mem base (MC.pAt + Spec.Weierstrass.Point.elemBytes MC.toPoint.k) =
        wordsVal s₇.mem base 544 4 := c7 544 (by omega)
    have x2 : MC.toPoint.coordAt s₇.mem base (MC.pAt + 2 * Spec.Weierstrass.Point.elemBytes MC.toPoint.k) =
        wordsVal s₇.mem base 576 4 := c7 576 (by omega)
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lt₇
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Spec.Weierstrass.Point.Curve.pointAt, x0]; exact lt₇.1
    · show _ < W.p; rw [Spec.Weierstrass.Point.Curve.pointAt, x1]; exact lt₇.2.1
    · show _ < W.p; rw [Spec.Weierstrass.Point.Curve.pointAt, x2]; exact lt₇.2.2
    · rw [Spec.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₇

/-! ## Constant time -/

theorem mulG_ct : ConstantTime isa mulGRVc.pre mulGRVc.pub mulGP256 :=
  VG.Taint.constantTime (A := taintSym [p256Sym]) (Taint.ofRegs [.a0])
    (fun _ _ _ _ ⟨hsp, h0, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact h0⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ecdsa.RISCV64.Comb
