module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Witness
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Witness
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on PPC64LE: constant time of a witness

`witness_ct`: two runs of `witness` from the same draw `X` (public, as the
tape is) leak the same trace. `atLeast2` and `ltC` pass the taint analysis;
their flags, which the branches test, are functions of `X` and `c`
(`atLeast2_ok`, `ltC_ok`); in `force`, the top word's offset, loaded from the
header, fixes the address of the second load and store (`forceA_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)

/-- A witness's start: the context and the draw `X` cut to the bits of `c − 1`. -/
def WS (a : BD × Nat) (s : State) : Prop :=
  BCtx s a.1.B a.1.L a.1.w a.1.c a.1.R a.1.rl a.1.t a.1.b a.1.ch ∧ s.sp = a.1.sp ∧
    wv s.mem a.1.B (slot a.1.w 4) a.1.w = a.2 % 2 ^ (64 * a.1.t + a.1.b)

/-- After `atLeast2`. -/
def W1 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₀, WS a s₀ ∧ ((s.gpr .r24 = 0#64 ↔ wv s₀.mem a.1.B (slot a.1.w 4) a.1.w < 2) ∧ s.mem = s₀.mem) ∧
    Keep a2Regs s₀ s

/-- After `ltC`. -/
def W2 (a : BD × Nat) (s : State) : Prop :=
  ∃ s₁, W1 a s₁ ∧ (s.gpr .r20 = 0#64 - BitVec.ofNat 64
      (if (wv s₁.mem a.1.B (slot a.1.w 4) a.1.w ||| 1) < a.1.c then 1 else 0) ∧
    Frm a.1.B [(slot a.1.w 3, 8 * (a.1.w + 2)), (slot a.1.w 6, 8 * (a.1.w + 2))] s₁.mem s.mem) ∧
    Keep ltCRegs s₁ s

theorem W1.env {a : BD × Nat} {s : State} (h : W1 a s) : Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp := by
  obtain ⟨s₀, ⟨c, sp, -⟩, -, k⟩ := h
  exact ⟨c.prep.env.keep k (by decide), k.sp.trans sp⟩

/-- What `W2` gives: the working space's registers, the flags, and the
header words. -/
theorem W2.facts {a : BD × Nat} {s : State} (h : W2 a s) :
    Env s a.1.B (8 * a.1.L) a.1.w ∧ s.sp = a.1.sp ∧
      (s.gpr .r24 = 0#64 ↔ a.2 % 2 ^ (64 * a.1.t + a.1.b) < 2) ∧
      s.gpr .r20 = 0#64 - BitVec.ofNat 64 (if (a.2 % 2 ^ (64 * a.1.t + a.1.b) ||| 1) < a.1.c then 1 else 0) ∧
      word s.mem a.1.B (8 * hTopOff) = BitVec.ofNat 64 (8 * a.1.t) ∧
      word s.mem a.1.B (8 * hTop) = BitVec.ofNat 64 (2 ^ a.1.b - 1) := by
  obtain ⟨s₁, h₁, ⟨h20, f2⟩, k2⟩ := h
  obtain ⟨s₀, ⟨c, sp, hx⟩, ⟨h24, m1⟩, k1⟩ := h₁
  have e := c.prep.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (a.1.w + 2)) ≤ 8 * a.1.L := e.hZ
  have es : ∀ j, slot a.1.w j = 256 + j * (8 * (a.1.w + 2)) := fun _ => rfl
  have kw : ∀ d, d + 8 ≤ slot a.1.w 3 → word s.mem a.1.B d = word s₀.mem a.1.B d := fun d hd => by
    rw [← m1]; exact f2.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] at hd ⊢ <;> omega) (by rw [es] at hd; omega)
  refine ⟨(e.keep k1 (by decide)).keep k2 (by decide), k2.sp.trans (k1.sp.trans sp), ?_, ?_,
    (kw _ (by simp only [hTopOff, es]; omega)).trans c.topOff, (kw _ (by simp only [hTop, es]; omega)).trans c.top⟩
  · rw [k2.gpr .r24 (by decide), h24, hx]
  · rw [h20, m1, hx]

/-- The first part of `force`: `x | 2` stored, and the top word's address in `r5`. -/
abbrev forceA : List Instr :=
  PublicChecked.base .r5 4 ++ [.load .d .r3 .r5 0, .li .r4 2, .logic .or .r3 .r3 .r4, .store .d .r3 .r5 0,
    ldh .r6 hTopOff, .add .r5 .r5 .r6]

/-- The rest: the top bit cleared. -/
abbrev forceB : List Instr :=
  [ldh .r4 hTop, .lsr .d .r4 .r4 1, .load .d .r3 .r5 0, .logic .and .r3 .r3 .r4, .store .d .r3 .r5 0]

theorem force_eq : force = forceA ++ forceB := by
  simp only [force, forceA, forceB, List.append_assoc, List.cons_append, List.nil_append]

theorem forceA_ok {s : State} {B : Addr} {Z w t : Nat} (e : Env s B Z w)
    (hoff : word s.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)) :
    WP isa (.block forceA) s fun x => x.gpr .r5 = off B (slot w 4 + 8 * t) ∧ x.gpr .r31 = B ∧ x.sp = s.sp := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  rw [WP.block_append_iff]
  refine WP.mono (e.base (rd := .r5) (by decide) (by decide) 4) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  have hy : Scr y B Z := hs.congr ky.wr
  have y31 : y.gpr .r31 = B := (ky.gpr .r31 (by decide)).trans e.h31
  have h4 : slot w 4 + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have o1 := writeW_outside s.mem B (word s.mem B (slot w 4) ||| 2#64) h4
  have r128 : (s.mem.writeW (off B (slot w 4)) (word s.mem B (slot w 4) ||| 2#64)).readW (B + 128#64) 64 =
      BitVec.ofNat 64 (8 * t) := (o1.word (by rw [es]; omega) (by omega)).trans hoff
  simp only [ldh, hTopOff]
  prun [y5, ym, y31, hy.ld (d := slot w 4) (n := 8) (by rw [es]; omega),
    hy.st (d := slot w 4) (n := 8) (by rw [es]; omega), hy.ld (d := 128) (n := 8) (by omega), r128, BitVec.add_zero]
  exact ky.sp

theorem beq_zero_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0#64 ↔ P) : (x == 0) = decide P := by
  by_cases hp : P
  · rw [decide_eq_true hp]; exact beq_iff_eq.mpr (h.mpr hp)
  · rw [decide_eq_false hp]; exact beq_false_of_ne fun e => hp (h.mp e)

theorem witness_ct : RelCT isa (Two WS) witness fun _ _ => True := by
  have pS : Pins WS [.r10, .r11, .r29, .r31] := pins_env (fun a => a.1) fun a s h => ⟨h.1.prep.env, h.2.1⟩
  have p1 : Pins W1 [.r10, .r11, .r29, .r31] := pins_env (fun a => a.1) fun a s h => h.env
  have p2 : Pins W2 [.r10, .r11, .r29, .r31] := pins_env (fun a => a.1) fun a s h => ⟨h.facts.1, h.facts.2.1⟩
  -- `force`, from `W2`.
  have hforce : ∀ (Φ : BD × Nat → State → Prop), (∀ a s, Φ a s → W2 a s) →
      RelCT isa (Two Φ) (.block force) fun _ _ => True := fun Φ hΦ => by
    have pF : Pins Φ [.r10, .r11, .r29, .r31] := Pins.of_imp p2 hΦ
    let FA : BD × Nat → State → Prop := fun a s =>
      s.gpr .r5 = off a.1.B (slot a.1.w 4 + 8 * a.1.t) ∧ s.gpr .r31 = a.1.B ∧ s.sp = a.1.sp
    have pA : Pins FA [.r5, .r31] := by
      intro a s₁ s₂ ⟨a5, a31, asp⟩ ⟨b5, b31, bsp⟩
      refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a5, b5]
      · rw [a31, b31]
    rw [force_eq]
    refine RelCT.block_append (RelCT.seq (two_post (two_taint _ pF (by taint_decide)) fun a s h => ?_)
      (two_taint _ pA (by taint_decide)))
    obtain ⟨e, sp, -, -, hoff, -⟩ := (hΦ a s h).facts
    exact WP.mono (forceA_ok e hoff) fun x ⟨x5, x31, xsp⟩ => ⟨x5, x31, xsp.trans sp⟩
  unfold witness
  refine RelCT.seq (two_post (Ψ := W1) (two_taint _ pS (by taint_decide)) fun a s h =>
    WP.mono (atLeast2_ok h.1.prep.env) fun t ht => ⟨s, h, ht⟩) ?_
  refine RelCT.seq (two_post (Ψ := W2) (two_taint _ p1 (by taint_decide)) fun a s h => ?_) ?_
  · obtain ⟨s₀, ⟨c, -, -⟩, ⟨-, m1⟩, k1⟩ := id h
    exact WP.mono (ltC_ok (c := a.1.c) h.env.1 (by rw [m1]; exact c.prep.n)) fun t ht => ⟨s, h, ht⟩
  refine two_ite (fun a s₁ s₂ h₁ h₂ => ?_) (hforce _ fun _ _ h => h.1) ?_
  · rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, beq_zero_of_iff h₁.facts.2.2.1,
      beq_zero_of_iff h₂.facts.2.2.1]
  refine two_ite (fun a s₁ s₂ h₁ h₂ => ?_) (hforce _ fun _ _ h => h.1.1) ?_
  · rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, h₁.1.facts.2.2.2.1, h₂.1.facts.2.2.2.1]
  exact two_taint _ (Pins.of_imp p2 fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.MillerRabin.PPC64LE.Blinded
