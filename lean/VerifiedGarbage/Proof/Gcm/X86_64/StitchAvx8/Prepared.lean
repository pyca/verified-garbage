import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.Gcm.Powers

/-!
# The eight-state loop with a prepared key context

Untrusted: everything here is checked by Lean. `encR` is `enc` with
`setupR`, which loads `H'` … `H'⁸` from the prepared key context
(`Spec.Gcm.PreparedPowersRepr`) rather than computing them: what it loads
is `hInvF (Hⁿ)` (`pair_values`), and `x · φ (hInvF (Hⁿ)) = φ (H)ⁿ`, so it
leaves what `setupG` does (`setupGR_ok`), and the rest is `enc`'s
(`setupWith_ok`, `encForWith_ok`): `stitchR_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch
open VG.Proof.Gcm.X86_64.Pclmul (const_ok Only rev_eq)
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupGR setupR prepOff preg lows setupC initCounter encForWith encR dec)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Spec.Gcm (Block blockAt hpow)

/-- The SSE code of `setupGR`. -/
def setupGRS : List Instr :=
  Impl.Gcm.X86_64.Pclmul.const .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++
  Impl.Gcm.X86_64.Pclmul.const .xmm1 poly ++
  (List.range 8).map fun i => .movdquLoad (preg i) (at_ .rdi (prepOff (i + 1)))

theorem lane0_setupGR : lane0Block setupGR = some setupGRS := by decide +kernel

/-- The first `n` loads of `setupGRS`. -/
theorem loadsS_ok (s : State) (n : Nat) (hn : n ≤ 8)
    (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 16) :
    WP isa (.block ((List.range n).map fun i => .movdquLoad (preg i) (at_ .rdi (prepOff (i + 1))))) s fun t =>
      (∀ i < n, t.xmm (preg i) = s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 128) ∧
      Only ((List.range n).map preg) s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hv, ho⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    apply WP.of_runBlock
    have hi : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((prepOff (n + 1) : Nat) : Int)) 16 := by
      rw [ho.rd, ho.wr, ho.gpr .rdi (by decide)]; exact hin n (by omega)
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128,
      VG.Proof.Gcm.X86_64.Pclmul.ea_at, hi, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun i hi' => ?_, ?_⟩
    · by_cases he : i = n
      · subst he
        simp only [State.setXmm, ite_true, ho.mem, ho.gpr .rdi (by decide)]
      · have hne : preg i ≠ preg n := fun h => he (StitchAvx.preg_inj i (by omega) n (by omega) h)
        simp only [State.setXmm, hne, ite_false]
        exact hv i (by omega)
    · rw [List.map_append, List.map_cons, List.map_nil]
      refine ho.trans (rs' := [preg n]) ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
      have : r ≠ preg n := fun h => hr (h ▸ List.mem_singleton_self _)
      simp only [State.setXmm, this, ite_false]

/-- `setupGRS`: the constants, and the eight powers loaded. -/
theorem setupGRS_ok (t : State)
    (hin : ∀ i < 8, InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 16) :
    WP isa (.block setupGRS) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ i < 8, t'.xmm (preg i) = t.mem.readW (t.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 128) ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [setupGRS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  refine WP.mono (loadsS_ok t₂ 8 (by decide) (fun i hi => by
    rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr .rdi (by decide)]; exact hin i hi)) fun t₃ ⟨l₃, o₃⟩ => ?_
  have hp : ∀ r ∈ List.map preg (List.range 8), r ≠ .xmm0 ∧ r ≠ .xmm1 := by decide
  refine ⟨?_, ?_, fun i hi => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [o₃.xmm _ (fun h => (hp _ h).1 rfl), o₂.xmm _ (by decide), c₁, rev_eq]
  · rw [o₃.xmm _ (fun h => (hp _ h).2 rfl), c₂]
  · rw [l₃ i hi, o₁₂.mem, o₁₂.gpr .rdi (by decide)]
  · rw [o₃.gpr r hr, o₁₂.gpr r hr]
  · rw [o₃.mem, o₁₂.mem]
  · rw [o₃.rd, o₁₂.rd]
  · rw [o₃.wr, o₁₂.wr]

/-- What a prepared key context holds at `prepOff n`. -/
theorem prep_val {m : Mem} {p : Addr} (hp : Spec.Gcm.PreparedPowersRepr m p) {n : Nat} (h1 : 1 ≤ n)
    (h8 : n ≤ 8) : m.readW (p + BitVec.ofNat 64 (prepOff n)) 128 = hInvF (hpow (Spec.Gcm.ctxH m p) n) := by
  by_cases he : n % 2 = 0
  · have h := StitchZR.pair_values hp (j := n - 1) (l := 0) (by omega) (by omega) (by decide)
    rw [show prepOff n = 240 + 16 * (n - 1) + 16 * 0 by simp only [prepOff, he, ite_true]; omega, h]
    congr 2; omega
  · have h := StitchZR.pair_values hp (j := n) (l := 1) (by omega) (by omega) (by decide)
    rw [show prepOff n = 240 + 16 * n + 16 * 1 by simp only [prepOff, he, ite_false]; omega, h]
    congr 2

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

/-- `setupGR` leaves what `setupG` does, from a prepared key context. -/
theorem setupGR_ok {s₀ : State} (hp : SPrePrepared s₀) : WP isa (.block setupGR) s₀ (GPost s₀) := by
  have hin : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((prepOff (i + 1) : Nat) : Int)) 16 :=
    fun i hi => by
      rw [BitVec.ofInt_natCast]
      exact in_sub hp.k_in (by simp only [prepOff]; split <;> omega)
  refine WP.mono (WP.lane0 lane0_setupGR (setupGRS_ok (s₀.proj 0) hin))
    fun t ⟨⟨h0, h1, hl, hg, hm, hrd, hwr⟩, _, _⟩ => ⟨h0, h1, fun i hi => ?_, hg, hm, hrd, hwr⟩
  change x * φ ((t.proj 0).xmm (preg i)) = _
  rw [hl i hi, BitVec.ofInt_natCast]
  change x * φ (s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (prepOff (i + 1))) 128) = _
  rw [prep_val hp.pow (by omega) (by omega), x_φ_hInvF]
  rfl

theorem setupR_split : setupR = setupGR ++ lows 8 ++ (setupC ++ metaCode ++ counterHead) ++ counterTail := by
  simp only [setupR, initCounter, metaCode, counterHead, counterTail, List.append_assoc,
    List.cons_append, List.nil_append]

theorem setupR_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa (.block setupR) s₀ fun s => ∃ P : Nat → Block,
      Ready s₀ P s ∧ ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
  rw [setupR_split]
  exact setupWith_ok hp.base (setupGR_ok hp)

theorem preR_same {s t : State} (h : SPrePrepared s) (hf : YFrame [] s t) : SPrePrepared t := by
  have hb := pre_same h.base hf
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor
  · exact hb
  all_goals with_reducible assumption

/-- Encryption with a prepared key context, of any number of blocks from 16 on. -/
theorem encR_ok {s₀ : State} (hp : SPrePrepared s₀) : WP isa encR s₀ (EPost s₀) := by
  apply dispatch_ok hp.base <;> intro t hf hn
  all_goals
    have ht : nr t = nr s₀ := by simp only [nr, hf.gpr]
    have hw := encForWith_ok (preR_same hp hf).base (setupR_ok (preR_same hp hf))
    rw [ht, hn] at hw
    exact WP.mono hw fun u hu => epost_same hf hu

theorem stitchR_ok : StitchOkM CtxMode.prepared encR dec 1 :=
  ⟨fun _ hp _ => encR_ok hp.toPrepared, fun s₀ hp hm => stitch_ok.2 s₀ hp.base hm⟩

end VG.Proof.Gcm.X86_64.StitchAvx8
