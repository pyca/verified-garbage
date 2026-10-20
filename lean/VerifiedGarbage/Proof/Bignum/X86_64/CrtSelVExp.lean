module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSelV
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.CrtMath

/-!
# RSA with the CRT on x86-64: the table's selection with AVX2

`Crt.tabSelectV` reads entry `v` of the window's table into `[aT]` as
`Crt.tabSelect` does (`tabSelV_ok`), its passes four words at a time
(`CrtSelV.lean`), so it is a `CrtSel` (`CrtSel.avx`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## A pass's head -/

theorem r12V_eq (M : Nat) (hM : 2 * M < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * M) >>> 2) + (BitVec.ofNat 64 (2 * M) >>> 2) +
      ((BitVec.ofNat 64 (2 * M) >>> 2) + (BitVec.ofNat 64 (2 * M) >>> 2)) = BitVec.ofNat 64 (4 * (M / 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- A pass's registers, as `gRegs_ok`, and `r12 = 4 ⌊M / 2⌋` for `M = ⌈w / 2⌉`. -/
theorem gRegsV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc p n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hw' : wx < 2 ^ 30)
    (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p))
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))) :
    WP isa (.block Crt.gatherRegsV) t fun t' =>
      t'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ t'.gpr .rcx = off P (slot wx (8 + 8 * p)) ∧
      t'.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ t'.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) ∧
      t'.gpr .r12 = BitVec.ofNat 64 (4 * ((wx + 1) / 2 / 2)) ∧
      t'.gpr .rbx = off P (slot wx Crt.aT) ∧ t'.mem = t.mem ∧ (∀ y l, t'.lane y l = t.lane y l) ∧
      Keep [.r15, .rcx, .r12, .r11, .r13, .rbx] t t' := by
  refine WP.block_append_iff.mpr (WP.mono (WP.vecKeep (by decide) (gRegs_ok hc hw' hJ hE))
    fun t₁ ⟨⟨h15, hcx, h11, h13, hbx, hm, _, k₁⟩, hx₁, hy₁⟩ => ?_)
  refine WP.mono (WP.vecKeep (by decide) (WP.keep [.r12] (Q := fun t' => t'.gpr .r12 =
      BitVec.ofNat 64 (4 * ((wx + 1) / 2 / 2)) ∧ t'.mem = t₁.mem) (by
    xrun [h13, r12V_eq ((wx + 1) / 2) (by omega)]) rfl)) fun t' ⟨⟨⟨h12, hm'⟩, k'⟩, hx', hy'⟩ =>
      ⟨by rw [k'.gpr (by decide)]; exact h15, by rw [k'.gpr (by decide)]; exact hcx,
        by rw [k'.gpr (by decide)]; exact h11, by rw [k'.gpr (by decide)]; exact h13, h12,
        by rw [k'.gpr (by decide)]; exact hbx, hm'.trans hm,
        fun y l => by simp only [State.lane, hx', hy', hx₁, hy₁], (k₁.trans k').mono (by decide)⟩

/-- `x := r14` in every quadword: `vmovq`, `vpbroadcastq`. -/
theorem dupV_ok {s : State} (x : XReg) :
    WP isa (.block [.vop (.vmovq x .r14), .vop (.vpbroadcastq .l256 x x)]) s fun t =>
      (∀ l < 2, ∀ q < 2, q128 (t.lane x l) q = s.gpr .r14) ∧ (∀ y, y ≠ x → ∀ l, t.lane y l = s.lane y l) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl q hq => ?_, fun y hy l => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [VOp.exec, State.lane_setV256, ↓reduceIte, VG.X86_64.RegUpd.xmm_setV]
    rw [show qword ((0 : BitVec 64) ++ s.gpr .r14) 0 = s.gpr .r14 from q128_low _]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp only [↓reduceIte, Nat.one_ne_zero] <;>
      exact q128_pair _ hq
  · simp only [VOp.exec, State.lane_setV256, State.lane_setV128, hy, ↓reduceIte]

/-- The mask of `k + j = v` in every quadword of `x`, `v` in `sNib` and `k` in `r15`. -/
theorem gMaskV_ok {t : State} {P : Addr} {k j v : Nat} (hdi : t.gpr .rdi = P)
    (hld : InRegions (t.rd ++ t.wr) (off P (8 * Crt.sNib)) 8) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 k) (hk : k < 32) (hj : j < 8) (hv : v < 32) (x : XReg) :
    WP isa (.block (Crt.selMaskV (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x)) t fun t' =>
      (∀ l < 2, ∀ q < 2, q128 (t'.lane x l) q = mask (decide (k + j = v))) ∧
      (∀ y, y ≠ x → ∀ l, t'.lane y l = t.lane y l) ∧ t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.selMaskV (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x =
    ([.mov .r14 (.reg .r15), .alu .add .r14 (.imm (BitVec.ofNat 32 j)), .alu .xor .r14 (.mem (hdr Crt.sNib)),
      .alu .cmp .r14 (.imm 1), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.vop (.vmovq x .r14), .vop (.vpbroadcastq .l256 x x)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.vecKeep rfl (WP.keep [.r14] (Q := fun t' =>
      (∃ b : Bool, b = decide (BitVec.ofNat 64 k + BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 v = 0) ∧
        t'.gpr .r14 = mask b) ∧ t'.mem = t.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hld, hN, h15, sx_ofNat (show j < 2 ^ 31 by omega)]
    exact ⟨_, decide_lt_one _, rfl⟩) rfl)) fun t₁ ⟨⟨⟨⟨b, hb, h14⟩, hm⟩, k₁⟩, hx₁, hy₁⟩ => ?_)
  refine WP.mono (dupV_ok x) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun l hl q hq => ?_,
    fun y hy' l => by rw [hy y hy' l]; simp only [State.lane, hx₁, hy₁], by rw [hm', hm], ?_⟩
  · rw [hd l hl q hq, h14, hb, BitVec.ofNat_add_ofNat]
    congr 1
    exact decide_eq_decide.mpr (xor_eq_zero_iff.trans (ofNat64_inj (by omega) (by omega)))
  · exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- The mask of `p ≠ 0` in every quadword of `ymm7`, `8 p` in `r15`. -/
theorem gKeepV_ok {t : State} {p : Nat} (h15 : t.gpr .r15 = BitVec.ofNat 64 (8 * p)) (hp : p < 4) :
    WP isa (.block Crt.keepMaskV) t fun t' =>
      (∀ l < 2, ∀ q < 2, q128 (t'.lane .xmm7 l) q = mask (decide (p ≠ 0))) ∧
      (∀ y, y ≠ .xmm7 → ∀ l, t'.lane y l = t.lane y l) ∧ t'.mem = t.mem ∧ Keep [.r14] t t' := by
  rw [show Crt.keepMaskV =
    ([.mov32 .r14 (.imm 0), .alu .cmp .r14 (.reg .r15), .alu .sbb .r14 (.reg .r14)] : List Instr) ++
    ([.vop (.vmovq .xmm7 .r14), .vop (.vpbroadcastq .l256 .xmm7 .xmm7)] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.vecKeep (by decide) (WP.keep [.r14] (Q := fun t' =>
      t'.gpr .r14 = mask (decide (p ≠ 0)) ∧ t'.mem = t.mem) (by
    xrun [h15]
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;> decide) rfl))
      fun t₁ ⟨⟨⟨h14, hm⟩, k₁⟩, hx₁, hy₁⟩ => ?_)
  refine WP.mono (dupV_ok .xmm7) fun t' ⟨hd, hy, hg, hm', hrd, hwr⟩ => ⟨fun l hl q hq => by rw [hd l hl q hq, h14],
    fun y hy' l => by rw [hy y hy' l]; simp only [State.lane, hx₁, hy₁], by rw [hm', hm], ?_⟩
  exact ⟨fun r hr => by rw [hg]; exact k₁.1 r hr, hrd.trans k₁.2.1, hwr.trans k₁.2.2⟩

/-- A pass's head with AVX2: its registers, masks and bases. -/
theorem gathHeadV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v p : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) (hw' : wx < 2 ^ 30) (hv : v < 32) (hp : p < 4)
    (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) (hJ : word t.mem P (8 * Crt.sJ) = BitVec.ofNat 64 (8 * p))
    (hE : word t.mem P (8 * Crt.sEnt) = off P (slot wx (8 + 8 * p))) :
    WP isa (seqs Crt.gatherHeadV) t fun s => GRegsV P wx p v s ∧ s.gpr .r14 = BitVec.ofNat 64 0 ∧
      s.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) ∧ s.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧ s.mem = t.mem ∧
      Keep mmRegs t s := by
  simp only [Crt.gatherHeadV, seqs]
  refine WP.seq (WP.mono (gRegsV_ok hc hw' hJ hE) fun t₁ ⟨h15, hcx, h11, h13, h12, hbx, hm₁, _, k₁⟩ => ?_)
  have hdi₁ : t₁.gpr .rdi = P := (k₁.gpr (by decide)).trans hc.good.rdi
  have hld : ∀ s : State, s.mem = t.mem → s.rd = t.rd → s.wr = t.wr →
      InRegions (s.rd ++ s.wr) (off P (8 * Crt.sNib)) 8 := fun s _ hrd hwr => by
    rw [hrd, hwr]; exact hc.ld (by decide)
  have mstep : ∀ (s : State) (j : Nat) (x : XReg), j < 8 → s.gpr .rdi = P → s.mem = t.mem → s.rd = t.rd →
      s.wr = t.wr → s.gpr .r15 = BitVec.ofNat 64 (8 * p) →
      WP isa (.block (Crt.selMaskV (BitVec.ofNat 32 j) (.mem (hdr Crt.sNib)) x)) s fun s' =>
        (∀ l < 2, ∀ q < 2, q128 (s'.lane x l) q = mask (decide (8 * p + j = v))) ∧
        (∀ y, y ≠ x → ∀ l, s'.lane y l = s.lane y l) ∧
        s'.mem = t.mem ∧ s'.gpr .rdi = P ∧ s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .r15 = BitVec.ofNat 64 (8 * p) ∧
        Keep [.r14] s s' :=
    fun s j x hj hdi hm hrd hwr h15 => WP.mono (gMaskV_ok hdi (hld s hm hrd hwr) (by rw [hm]; exact hN) h15
      (by omega) hj hv x) fun s' ⟨hq, hy, hm', k⟩ =>
        ⟨hq, hy, hm'.trans hm, (k.gpr (by decide)).trans hdi, k.2.1.trans hrd, k.2.2.trans hwr,
          (k.gpr (by decide)).trans h15, k⟩
  refine WP.seq (WP.mono (mstep t₁ 0 .xmm8 (by decide) hdi₁ hm₁ k₁.2.1 k₁.2.2 h15)
    fun s₀ ⟨q₀, y₀, m₀, d₀, r₀, w₀, f₀, k₀⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₀ 1 .xmm9 (by decide) d₀ m₀ r₀ w₀ f₀)
    fun s₁ ⟨q₁, y₁, m₁, d₁, r₁, w₁, f₁, k₁'⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₁ 2 .xmm10 (by decide) d₁ m₁ r₁ w₁ f₁)
    fun s₂ ⟨q₂, y₂, m₂, d₂, r₂, w₂, f₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₂ 3 .xmm11 (by decide) d₂ m₂ r₂ w₂ f₂)
    fun s₃ ⟨q₃, y₃, m₃, d₃, r₃, w₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₃ 4 .xmm12 (by decide) d₃ m₃ r₃ w₃ f₃)
    fun s₄ ⟨q₄, y₄, m₄, d₄, r₄, w₄, f₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₄ 5 .xmm13 (by decide) d₄ m₄ r₄ w₄ f₄)
    fun s₅ ⟨q₅, y₅, m₅, d₅, r₅, w₅, f₅, k₅⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₅ 6 .xmm14 (by decide) d₅ m₅ r₅ w₅ f₅)
    fun s₆ ⟨q₆, y₆, m₆, d₆, r₆, w₆, f₆, k₆⟩ => ?_)
  refine WP.seq (WP.mono (mstep s₆ 7 .xmm15 (by decide) d₆ m₆ r₆ w₆ f₆)
    fun s₇ ⟨q₇, y₇, m₇, d₇, r₇, w₇, f₇, k₇⟩ => ?_)
  refine WP.seq (WP.mono (gKeepV_ok f₇ hp) fun s₈ ⟨q₈, y₈, m₈, k₈⟩ => ?_)
  have kM := ((((((((k₀.trans k₁').trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈)
  have hcx₈ : s₈.gpr .rcx = off P (slot wx (8 + 8 * p)) := (kM.gpr (by decide)).trans hcx
  have h11₈ : s₈.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2)) := (kM.gpr (by decide)).trans h11
  refine WP.mono (WP.vecKeep (by decide) (gBases_ok hcx₈ h11₈)) fun s₉ ⟨⟨hb, h14, m₉, _, k₉⟩, hx₉, hy₉⟩ => ?_
  have kA := kM.trans k₉
  have l₉ : ∀ y l, s₉.lane y l = s₈.lane y l := fun y l => by simp only [State.lane, hx₉, hy₉]
  have hG : GRegsV P wx p v s₉ := by
    refine ⟨hb, by rw [kA.gpr (by decide)]; exact hbx, by rw [kA.gpr (by decide)]; exact h13,
      by rw [kA.gpr (by decide)]; exact h12, fun k hk l hl q hq => ?_, fun l hl q hq => by rw [l₉]; exact q₈ l hl q hq⟩
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show gX 0 = .xmm8 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide), y₂ _ (by decide), y₁ _ (by decide)]; exact q₀ l hl q hq
    · rw [show gX 1 = .xmm9 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide), y₂ _ (by decide)]; exact q₁ l hl q hq
    · rw [show gX 2 = .xmm10 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide), y₃ _ (by decide)]; exact q₂ l hl q hq
    · rw [show gX 3 = .xmm11 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide),
        y₄ _ (by decide)]; exact q₃ l hl q hq
    · rw [show gX 4 = .xmm12 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide), y₅ _ (by decide)]
      exact q₄ l hl q hq
    · rw [show gX 5 = .xmm13 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide), y₆ _ (by decide)]; exact q₅ l hl q hq
    · rw [show gX 6 = .xmm14 from rfl, l₉, y₈ _ (by decide), y₇ _ (by decide)]; exact q₆ l hl q hq
    · rw [show gX 7 = .xmm15 from rfl, l₉, y₈ _ (by decide)]; exact q₇ l hl q hq
  exact ⟨hG, h14, by rw [kA.gpr (by decide)]; exact h11, by rw [kA.gpr (by decide)]; exact h15,
    by rw [m₉, m₈, m₇], (k₁.trans kA).mono (by decide)⟩

/-- The words of `[aT]` below `2 ⌈w / 2⌉` after a pass's chunks: the four-word
loop if any, then the last two words if left. -/
theorem gChunksV_ok {s : State} {B : Addr} {wx p v : Nat} (hs : Scr s B (slot wx 8 + tabBytes wx 32))
    (hG : GRegsV B wx p v s) (hp : p < 4) (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    {c : Prog isa} {Q : State → Prop}
    (hk : ∀ t, (∃ s₀ : State, s₀.mem = s.mem ∧ GathInvV s₀ B wx p v (2 * ((wx + 1) / 2)) t ∧
        (∀ r, r ≠ .r14 → s₀.gpr r = s.gpr r) ∧ (∀ y l, s₀.lane y l = s.lane y l) ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr) →
      WP isa c t Q) :
    WP isa (.seq (.block [.alu .test .r12 (.reg .r12)])
      (.seq (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne)
          (.block []))
        (.seq (.block [.alu .cmp .r14 (.reg .r13)]) (.seq (.ite .ne (.block (Crt.gatherBodyV .l128 2)) (.block [])) c)))) s
      Q := by
  have hM := (wx + 1) / 2
  -- `ZF` of `r12 = 4 ⌊M / 2⌋`.
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t => t.zf = some (decide ((wx + 1) / 2 / 2 = 0)) ∧ t.mem = s.mem ∧
      (∀ y l, t.lane y l = s.lane y l) ∧ t.gpr .r12 = s.gpr .r12) (by
    xrun [hG.r12, BitVec.and_self, ofNat_beq_zero (show 4 * ((wx + 1) / 2 / 2) < 2 ^ 64 by omega)]
    exact ⟨decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩, fun _ _ => rfl⟩) rfl)
    fun s₁ ⟨⟨hz₁, hm₁, hl₁, h12₁⟩, k₁⟩ => ?_)
  have hg₁ : s₁.gpr = s.gpr := funext fun r => by
    by_cases hr : r = .r12
    · rw [hr, h12₁]
    · exact k₁.1 r (by simpa using hr)
  have hs₁ : Scr s₁ B (slot wx 8 + tabBytes wx 32) := hs.congr k₁.2.2
  have hG₁ : GRegsV B wx p v s₁ := hG.congr (fun r _ => by rw [hg₁]) (fun y _ _ l => hl₁ y l)
  have h14₁ : s₁.gpr .r14 = BitVec.ofNat 64 0 := by rw [hg₁]; exact h14
  -- The four-word chunks.
  have hloop : WP isa (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] :
      List Instr))) .ne) (.block [])) s₁ (GathInvV s₁ B wx p v (4 * ((wx + 1) / 2 / 2))) := by
    by_cases hN : (wx + 1) / 2 / 2 = 0
    · refine WP.ite false (by simp [eval, hz₁, hN]) (by simp) (fun _ => WP.block_nil ?_)
      rw [hN]; exact GathInvV.init h14₁
    · refine WP.ite true (by simp [eval, hz₁, hN]) (fun _ => ?_) (by simp)
      exact gLoopV_ok hs₁ hG₁ hp h14₁ (by omega) (by omega) hw' hG₁.r12
  refine WP.seq (WP.mono hloop fun s₂ hI₂ => ?_)
  -- The last two words, if left.
  have hr13 : s₂.gpr .r13 = BitVec.ofNat 64 (2 * ((wx + 1) / 2)) := by rw [hI₂.gpr _ (by decide)]; exact hG₁.r13
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.zf = some (decide (4 * ((wx + 1) / 2 / 2) = 2 * ((wx + 1) / 2))) ∧
      t.mem = s₂.mem ∧ (∀ y l, t.lane y l = s₂.lane y l) ∧ t.gpr .r14 = s₂.gpr .r14) (by
    xrun [hI₂.r14, hr13, ofNat_sub_beq (show 4 * ((wx + 1) / 2 / 2) < 2 ^ 64 by omega)
      (show 2 * ((wx + 1) / 2) < 2 ^ 64 by omega)]
    exact fun _ _ => rfl) rfl) fun s₃ ⟨⟨hz₃, hm₃, hl₃, h14₃⟩, k₃⟩ => ?_)
  have hg₃ : s₃.gpr = s₂.gpr := funext fun r => by
    by_cases hr : r = .r14
    · rw [hr, h14₃]
    · exact k₃.1 r (by simpa using hr)
  have hI₃ : GathInvV s₁ B wx p v (4 * ((wx + 1) / 2 / 2)) s₃ :=
    ⟨by rw [hg₃]; exact hI₂.r14, fun r hr => by rw [hg₃]; exact hI₂.gpr r hr,
      fun y h0 h1 l => (hl₃ y l).trans (hI₂.xmm y h0 h1 l), k₃.2.1.trans hI₂.rd, k₃.2.2.trans hI₂.wr,
      by rw [hm₃]; exact hI₂.out, fun k hk => by rw [hm₃]; exact hI₂.val k hk⟩
  have hfin : ∀ t, GathInvV s₁ B wx p v (2 * ((wx + 1) / 2)) t →
      ∃ s₀ : State, s₀.mem = s.mem ∧ GathInvV s₀ B wx p v (2 * ((wx + 1) / 2)) t ∧
        (∀ r, r ≠ .r14 → s₀.gpr r = s.gpr r) ∧ (∀ y l, s₀.lane y l = s.lane y l) ∧ s₀.rd = s.rd ∧ s₀.wr = s.wr :=
    fun t h => ⟨s₁, hm₁, h, fun r _ => by rw [hg₁], hl₁, k₁.2.1, k₁.2.2⟩
  refine WP.seq (WP.mono ?_ hk)
  by_cases hodd : 4 * ((wx + 1) / 2 / 2) = 2 * ((wx + 1) / 2)
  · refine WP.ite false (by simp [eval, hz₃, hodd]) (by simp) (fun _ => WP.block_nil (hfin _ ?_))
    rw [← hodd]; exact hI₃
  · refine WP.ite true (by simp [eval, hz₃, hodd]) (fun _ => ?_) (by simp)
    refine WP.mono (gStepV_ok .l128 hs₁ hG₁ hp (c := 4 * ((wx + 1) / 2 / 2)) (by simp only [nl]; omega) rfl hI₃)
      fun t ⟨hI, _⟩ => hfin t ?_
    rw [show 2 * ((wx + 1) / 2) = 4 * ((wx + 1) / 2 / 2) + 2 * nl .l128 by simp only [nl]; omega]
    exact hI

/-- The pass's end with AVX2: as `gEnd_ok`, `ZF` after the fourth. -/
theorem gEndV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc p n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) (hp : p < 4) (h7 : t.gpr .rax = off P (slot wx (8 + 8 * p + 7)))
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (8 * (wx + 2))) (h15 : t.gpr .r15 = BitVec.ofNat 64 (8 * p)) :
    WP isa (.block Crt.gatherEndV) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx (8 + 8 * (p + 1))))).writeW (off P (8 * Crt.sJ))
        (BitVec.ofNat 64 (8 * (p + 1))) ∧ t'.zf = some (decide (p + 1 = 4)) ∧ Keep [.rax] t t' := by
  have hs : slot wx (8 + 8 * p + 7) + 8 * (wx + 2) = slot wx (8 + 8 * (p + 1)) := by
    rw [← slot_succ, show 8 + 8 * p + 7 + 1 = 8 + 8 * (p + 1) by omega]
  have h8 : BitVec.ofNat 64 (8 * p) + 8 = BitVec.ofNat 64 (8 * (p + 1)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t.mem.writeW (off P (8 * Crt.sEnt))
      (off P (slot wx (8 + 8 * (p + 1))))).writeW (off P (8 * Crt.sJ)) (BitVec.ofNat 64 (8 * (p + 1))) ∧
      t'.zf = some (decide (p + 1 = 4))) (by
    unfold Crt.gatherEndV
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sEnt) (by decide), hc.st (i := Crt.sJ) (by decide),
      h7, h11, h15, off_add_eq, hs, sx_ofNat (show 8 < 2 ^ 31 by omega), h8]
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
      ofNat_sub_beq (show 8 * (p + 1) < 2 ^ 64 by omega) (show 32 < 2 ^ 64 by decide)]
    exact decide_eq_decide.mpr (by omega)) rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- Pass `p` of the selection with AVX2. -/
theorem gPassV_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v p : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 32) (hp : p < 4) (hI : GathPassInv t₀ P wx minv X Xc v 32 p t) :
    WP isa (seqs Crt.gatherPassV) t fun t' => t'.zf = some (decide (p + 1 = 4)) ∧
      GathPassInv t₀ P wx minv X Xc v 32 (p + 1) t' := by
  have hc := hI.ctx
  have hn := hc.scrT.nowrap
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hTa := slot_succ wx Crt.aT
  have hT8 := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  rw [show seqs Crt.gatherPassV = .seq (seqs Crt.gatherHeadV) (.seq (.block [.alu .test .r12 (.reg .r12)])
      (.seq (.ite .ne (.loop (.block (Crt.gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne)
          (.block []))
        (.seq (.block [.alu .cmp .r14 (.reg .r13)]) (.seq (.ite .ne (.block (Crt.gatherBodyV .l128 2)) (.block []))
          (.block Crt.gatherEndV))))) from rfl]
  refine WP.seq (WP.mono (gathHeadV_ok hc hw' hv hp hI.nib hI.idx hI.ent) fun s₉ ⟨hG, h14, h11, h15, hm₉, kA⟩ => ?_)
  have hs₉ : Scr s₉ P (slot wx 8 + tabBytes wx 32) := hc.scrT.congr kA.2.2
  -- The chunks.
  refine gChunksV_ok hs₉ hG hp h14 hw hw' fun s₁₀ ⟨s₀, hm₀, hL, hg₀, _, hrd₀, hwr₀⟩ => ?_
  have hgL : ∀ r, r ≠ .r14 → s₁₀.gpr r = s₉.gpr r := fun r hr => (hL.gpr r hr).trans (hg₀ r hr)
  have kL : Keep [.r14] s₉ s₁₀ := ⟨fun r hr => hgL r (by simpa using hr), hL.rd.trans hrd₀, hL.wr.trans hwr₀⟩
  have oL : Outside P (slot wx Crt.aT) (8 * (wx + 2)) t.mem s₁₀.mem := by
    rw [← hm₉, ← hm₀]; exact hL.out.mono (Nat.le_refl _) (by omega)
  have hc₁₀ : CExpCtx s₁₀ P wx minv X Xc 32 :=
    hc.of_win (Frm.of_outside oL (by simp [crtWinRanges])) (by rw [kL.2.2, kA.2.2]) ((kA.trans kL).gpr (by decide))
  refine WP.mono (gEndV_ok hc₁₀ hp (by rw [hgL _ (by decide)]; exact hG.base 7 (by decide))
    (by rw [hgL _ (by decide)]; exact h11) (by rw [hgL _ (by decide)]; exact h15)) fun t' ⟨hm', hz, k'⟩ => ⟨hz, ?_⟩
  -- What changed.
  have o₁ := writeW_outside s₁₀.mem P (d := 8 * Crt.sEnt) (off P (slot wx (8 + 8 * (p + 1)))) (by decide)
  have o₂ := writeW_outside (s₁₀.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx (8 + 8 * (p + 1))))) P
    (d := 8 * Crt.sJ) (BitVec.ofNat 64 (8 * (p + 1))) (by decide)
  rw [← hm'] at o₂
  have fL : Frm P (selRanges wx) t.mem s₁₀.mem := Frm.of_outside oL (by simp [selRanges])
  have fE : Frm P (selRanges wx) s₁₀.mem t'.mem :=
    (Frm.of_outside o₁ (by simp [selRanges])).trans (Frm.of_outside o₂ (by simp [selRanges]))
  have hT : ∀ k < 2 * ((wx + 1) / 2), word t'.mem P (slot wx Crt.aT + 8 * k) = word s₁₀.mem P (slot wx Crt.aT + 8 * k) :=
    fun k hk => by
      have := hdr_lt_slot wx Crt.aT (show Crt.sJ < 32 by decide)
      have := hdr_lt_slot wx Crt.aT (show Crt.sEnt < 32 by decide)
      rw [o₂.word (by omega) (by omega), o₁.word (by omega) (by omega)]
  have hE : ∀ j < 32, ∀ k < 2 * ((wx + 1) / 2), word t.mem P (slot wx (8 + j) + 8 * k) =
      word t₀.mem P (slot wx (8 + j) + 8 * k) := fun j hj k hk =>
    hI.frm.word_eq (fun r hr => by
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      have := slot_mono wx (show 8 ≤ 8 + j by omega)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega
      · simp only [Crt.sEnt, sFn]; omega
      · simp only [Crt.sJ, sFn]; omega) (by have := ent_le wx hj; omega)
  refine ⟨hc₁₀.of_win (fE.mono (selRanges_sub wx)) k'.2.2 (k'.gpr (by decide)), ?_, ?_, ?_, Or.inr fun k hk => ?_,
    hI.frm.trans (fL.trans fE), ((hI.keep.trans ((kA.trans kL).trans k')).mono (by decide))⟩
  · have := hdr_lt_slot wx Crt.aT (show Crt.sNib < 32 by decide)
    rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), oL.word (by omega) (by omega)]
    exact hI.nib
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm', word_writeW_self]
  · rw [hT k hk, hL.val k hk, hm₀, hm₉]
    simp only [gvalV, gacc_eq, gath_and_mask]
    have hold := hI.val
    have hv' : v < 32 := hv
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · by_cases h8 : v < 8
      · simp [h8, show v ≤ 8 * 0 + 7 by omega, hE v (by omega) k hk]
      · simp [h8, show ¬ v ≤ 8 * 0 + 7 by omega]
    · rcases hold with h | hold
      · omega
      rw [hold k hk]
      have hp0' : p ≠ 0 := by omega
      by_cases h8 : v < 8 * p
      · simp [h8, hp0', show ¬ 8 * p ≤ v by omega, show v < 8 * (p + 1) by omega]
      · by_cases h8' : v < 8 * (p + 1)
        · simp [h8, h8', hp0', show 8 * p ≤ v by omega, show v ≤ 8 * p + 7 by omega,
            show 8 + 8 * p + (v - 8 * p) = 8 + v by omega, hE v (by omega) k hk]
        · simp [h8, h8', hp0', show ¬ v ≤ 8 * p + 7 by omega]

theorem tabSelectV_eq : Crt.tabSelectV = [.block [.mov .rax (.mem (hdr Crt.sTab)), .store (hdr Crt.sEnt) .rax,
    .mov32 .rax (.imm 0), .store (hdr Crt.sJ) .rax], .loop (seqs Crt.gatherPassV) .ne,
    .block [.vop .vzeroupper]] := rfl

/-- `vzeroupper` keeps all but the vector registers' upper bits. -/
theorem vzu_ok (s : State) : WP isa (.block [.vop .vzeroupper]) s fun t =>
    t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The selection with AVX2: `[aT] := T_v`. -/
theorem tabSelV_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx t P wx minv X Xc 32) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 32)
    (ht : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)) (hN : word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (seqs Crt.tabSelectV) t fun t' => CExpCtx t' P wx minv X Xc 32 ∧
      wv t'.mem P (slot wx Crt.aT) wx = wv t.mem P (slot wx (8 + v)) wx ∧
      Frm P (selRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  rw [tabSelectV_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sEnt) (off P (slot wx 8)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sEnt)) (off P (slot wx 8))) P (d := 8 * Crt.sJ)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (selRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
  have h₁ : GathPassInv t₁ P wx minv X Xc v 32 0 t₁ := by
    refine ⟨hc.of_win (f₁.mono (selRanges_sub wx)) k₁.2.2 (k₁.gpr (by decide)), ?_, ?_, ?_, .inl rfl,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, word_writeW_self]; rfl
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 4) (by decide) (GathPassInv t₁ P wx minv X Xc v 32)
    (fun p _ hp s hI => gPassV_ok hw hw' hv hp hI) (fun s h => h) h₁) fun t₂ hI => ?_)
  -- `vzeroupper`.
  refine WP.mono (vzu_ok t₂) fun t₃ ⟨hg₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have hEv : ∀ i < wx, word t₁.mem P (slot wx (8 + v) + 8 * i) = word t.mem P (slot wx (8 + v) + 8 * i) :=
    fun i hi => f₁.word_eq (fun r hr => by
      have := slot_mono wx (show 8 ≤ 8 + v by omega)
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := slot_le (w := wx) (show Crt.aT < 8 by decide); simp only; omega
      · simp only [Crt.sEnt, sFn]; omega
      · simp only [Crt.sJ, sFn]; omega) (by have := ent_le wx hv; omega)
  have k₂ : Keep mmRegs t t₂ := (k₁.trans hI.keep).mono (by decide)
  refine ⟨hI.ctx.of_frm (by rw [hm₃]; exact Frm.refl _ _ _) (by rw [hwr₃]) (by rw [hg₃]), wv_congr2 fun i hi => ?_,
    by rw [hm₃]; exact f₁.trans hI.frm, ⟨fun r hr => by rw [hg₃]; exact k₂.1 r hr, hrd₃.trans k₂.2.1, hwr₃.trans k₂.2.2⟩⟩
  rw [hm₃]
  rcases hI.val with h | h
  · omega
  rw [h i (by omega), ite_eq_left (by omega), hEv i hi]

/-- The selection with AVX2, from a table of 32 entries. -/
def CrtSel.avx : CrtSel 32 := ⟨Crt.tabSelectV, by simp [tabSelectV_eq], tabSelV_ok⟩

end VG.Proof.Bignum.X86_64
