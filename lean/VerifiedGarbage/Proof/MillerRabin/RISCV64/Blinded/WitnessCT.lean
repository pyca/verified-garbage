module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.LoadCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.LoadCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time of a draw's witness

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/WitnessCT.lean`):
`witness_ct`, two runs of `witness` from the same draw `X` (public, as the
tape is) leak the same trace: `atLeast2` and `ltN` branch on nothing, and
their flags, which the branches test, are functions of `X` and `c`
(`atLeast2_ok`, `ltN_ok`); in `force`, the top word's offset, loaded from the
header, fixes the address of the second load and store (`forceA_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A witness's start: the context and the draw `X` cut to the bits of `c − 1`. -/
def WS (a : BD × Nat) (s : State) : Prop :=
  BCtx s a.1.B a.1.L a.1.w a.1.c a.1.R a.1.rl a.1.t a.1.b a.1.ch ∧ s.sp = a.1.sp ∧
    A s.mem a.1.B a.1.w 4 = a.2 % 2 ^ (64 * a.1.t + a.1.b)

/-- After `atLeast2`. -/
def W1 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, WS a s₀ ∧ ((s.gpr .a3 = 0#64 ↔ A s₀.mem a.1.B a.1.w 4 < 2) ∧ s.mem = s₀.mem) ∧
    Keep a2Regs s₀ s ∧ s.sp = s₀.sp

/-- After `ltN`. -/
def W2 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₁, W1 a s₁ ∧ (s.gpr .s4 = (if (A s₁.mem a.1.B a.1.w 4 ||| 1) < a.1.c then BitVec.allOnes 64 else 0) ∧
    Frm a.1.B [(slot a.1.w 3, 8 * (a.1.w + 2)), (slot a.1.w 6, 8 * (a.1.w + 2))] s₁.mem s.mem) ∧
    Keep ltNRegs s₁ s ∧ s.sp = s₁.sp

theorem W1.env {a : BD × Nat} {s : State} (h : W1 a s) : Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp := by
  obtain ⟨s₀, ⟨c, sp, -⟩, -, k, hsp⟩ := h
  exact ⟨c.prep.env.keep k (by decide), hsp.trans sp⟩

/-- What `W2` gives: the working space's registers, the flags, and the
header words. -/
theorem W2.facts {a : BD × Nat} {s : State} (h : W2 a s) :
    Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp ∧
      (s.gpr .a3 = 0#64 ↔ a.2 % 2 ^ (64 * a.1.t + a.1.b) < 2) ∧
      s.gpr .s4 = (if (a.2 % 2 ^ (64 * a.1.t + a.1.b) ||| 1) < a.1.c then BitVec.allOnes 64 else 0) ∧
      word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) ∧
      word s.mem a.1.B (8 * hTop) = BitVec.ofNat 64 (2 ^ a.1.b - 1) := by
  obtain ⟨s₁, h₁, ⟨h4, f2⟩, k2, sp2⟩ := h
  obtain ⟨s₀, ⟨c, sp, hx⟩, ⟨h3, m1⟩, k1, sp1⟩ := h₁
  have e := c.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have es : ∀ j, slot a.1.w j = 256 + j * (8 * (a.1.w + 2)) := fun _ => rfl
  have kw : ∀ d, d + 8 ≤ slot a.1.w 3 → word s.mem a.1.B d = word s₀.mem a.1.B d := fun d hd => by
    rw [← m1]; exact f2.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] at hd ⊢ <;> omega) (by rw [es] at hd; omega)
  refine ⟨(e.keep k1 (by decide)).keep k2 (by decide), sp2.trans (sp1.trans sp), ?_, ?_,
    (kw _ (by simp only [hTopOff, es]; omega)).trans c.topOff, (kw _ (by simp only [hTop, es]; omega)).trans c.top⟩
  · rw [k2.gpr (by decide), h3, hx]
  · rw [h4, m1, hx]

/-- The first part of `force`: `x | 2` stored, and the top word's address in `t3`. -/
abbrev forceA : List Instr :=
  base .t3 4 ++ [.load .d .t2 .t3 0, .logicImm .or .t2 .t2 2, .store .d .t2 .t3 0] ++ topAddr

/-- The rest: the top bit cleared. -/
abbrev forceB : List Instr :=
  [ldh .t4 hTop, .shift .srl .d .t4 .t4 1, .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0]

theorem force_eq : force = forceA ++ forceB := by
  simp only [force, forceA, forceB, List.append_assoc]

theorem forceA_ok {s : State} {B : Addr} {L w t : Nat} (e : Env s B (8 * L) w)
    (hoff : word s.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) :
    WP isa (.block forceA) s fun x => x.gpr .t3 = off B (slot w 4 + 8 * t) ∧ x.gpr .s6 = B ∧ x.sp = s.sp := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := e.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.rdwr (e.base (rd := .t3) (by decide) 4)) fun y ⟨⟨⟨y3, ym⟩, ky⟩, _, _, ysp⟩ => ?_
  have ey : Env y B (8 * L) w := e.keep ky (by decide)
  have h4 : slot w 4 + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have o1 := writeW_outside s.mem B (word s.mem B (slot w 4) ||| 2#64) h4
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun (z : State) =>
      z.mem = s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64))
    (by brun [y3, ym, ey.hs.ld (d := slot w 4) (n := 8) (by rw [es]; omega),
          ey.hs.al8 (d := slot w 4) (by rw [es]; omega) (by rw [es]; omega),
          ey.hs.st (d := slot w 4) (n := 8) (by rw [es]; omega), BitVec.add_zero]) (by rfl) (by rfl)))
    fun z ⟨⟨zm, kz⟩, _, _, zsp⟩ => ?_
  have ez : Env z B (8 * L) w := ey.keep kz (by decide)
  have hoff' : word z.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t) := by
    rw [zm, o1.word (by simp only [hTopOff]; rw [es]; omega) (by simp only [hTopOff]; omega)]; exact hoff
  exact WP.mono (topAddr_ok ez hoff') fun x ⟨x3, x6, xsp⟩ => ⟨x3, x6, xsp.trans (zsp.trans ysp)⟩

theorem beq_zero_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0#64 ↔ P) : (x == 0) = decide P := by
  by_cases hp : P
  · rw [decide_eq_true hp]; exact beq_iff_eq.mpr (h.mpr hp)
  · rw [decide_eq_false hp]; exact beq_false_of_ne fun e => hp (h.mp e)

theorem witness_ct : RelCT isa (Two WS) witness fun _ _ => True := by
  have pS : Pins WS [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.1.prep.env, h.2.1⟩
  have p1 : Pins W1 [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => h.env
  have p2 : Pins W2 [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s h => ⟨h.facts.1, h.facts.2.1⟩
  -- `force`, from `W2`.
  have hforce : ∀ (Φ : BD × Nat → State → Prop), (∀ a s, Φ a s → W2 a s) →
      RelCT isa (Two Φ) (.block force) fun _ _ => True := fun Φ hΦ => by
    have pF : Pins Φ [.a7, .s5, .t0, .s6] := Pins.of_imp p2 hΦ
    let FA : BD × Nat → State → Prop := fun a s =>
      s.gpr .t3 = off a.1.B (slot a.1.w 4 + 8 * a.1.t) ∧ s.gpr .s6 = a.1.B ∧ s.sp = a.1.sp
    have pA : Pins FA [.t3, .s6] := by
      intro a s₁ s₂ ⟨a3, a6, asp⟩ ⟨b3, b6, bsp⟩
      refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a3, b3]
      · rw [a6, b6]
    rw [force_eq]
    refine RelCT.block_append (RelCT.seq (two_post (Ψ := FA) (two_taint _ pF (by taint_decide)) fun a s h => ?_)
      (two_taint (c := .block forceB) _ pA (by taint_decide)))
    obtain ⟨e, sp, -, -, hoff, -⟩ := (hΦ a s h).facts
    exact WP.mono (forceA_ok e hoff) fun x ⟨x3, x6, xsp⟩ => ⟨x3, x6, xsp.trans sp⟩
  unfold witness
  refine RelCT.seq (two_post (Ψ := W1) (two_taint _ pS (by taint_decide)) fun a s h =>
    WP.mono (WP.rdwr (atLeast2_ok h.1.prep.env)) fun t ⟨ht, _, _, tsp⟩ => ⟨s, h, ht.1, ht.2, tsp⟩) ?_
  refine RelCT.seq (two_post (Ψ := W2) (two_taint _ p1 (by taint_decide)) fun a s h => ?_) ?_
  · obtain ⟨s₀, ⟨c, -, -⟩, ⟨-, m1⟩, k1, _⟩ := id h
    exact WP.mono (WP.rdwr (ltN_ok (c := a.1.c) h.env.1 (by rw [m1]; exact c.prep.n)))
      fun t ⟨ht, _, _, tsp⟩ => ⟨s, h, ht.1, ht.2, tsp⟩
  refine two_ite (fun a s₁ s₂ h₁ h₂ => ?_) (hforce _ fun _ _ h => h.1) ?_
  · rw [Steps.eval_zero, Steps.eval_zero, beq_zero_of_iff h₁.facts.2.2.1, beq_zero_of_iff h₂.facts.2.2.1]
  refine two_ite (fun a s₁ s₂ h₁ h₂ => ?_) (hforce _ fun _ _ h => h.1.1) ?_
  · rw [Steps.eval_zero, Steps.eval_zero, h₁.1.facts.2.2.2.1, h₂.1.facts.2.2.2.1]
  exact two_taint _ (Pins.of_imp p2 fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.MillerRabin.RISCV64.Blinded
