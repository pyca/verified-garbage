module

public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Impl.Mont.X86.ContextSquares
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Montgomery setup with a short loop of squares -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- Squaring in Montgomery form doubles the exponent above the radix. -/
theorem setup_square_power {v n k m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m)
    (hv : v < m)
    (h : v * 2 ^ (64 * n) % m =
      (2 ^ (64 * n + k) % m) * (2 ^ (64 * n + k) % m) % m) :
    v = 2 ^ (64 * n + 2 * k) % m := by
  have eqpow : 2 ^ (64 * n + k) * 2 ^ (64 * n + k) =
      2 ^ (64 * n + 2 * k) * 2 ^ (64 * n) := by
    simp only [← Nat.pow_add]
    congr 1
    omega
  have he : v % m = 2 ^ (64 * n + 2 * k) % m :=
    VG.Proof.Bignum.mont_cancel hc (by rw [h, ← Nat.mul_mod, eqpow])
  rwa [Nat.mod_eq_of_lt hv] at he

/-- The setup loop preserves the context and one, and doubles the exponent
above R at each iteration. Its writes are the original setup's ranges. -/
structure SetupInv (n m size a i : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .esi = BitVec.ofNat 32 (6 - i)
  one : wordsVal t.mem base (slot n 3) n = wordsVal s.mem base (slot n 3) n
  value : wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n + 2 ^ i * a) % m
  mem : Outs base (setupRanges n) s.mem t.mem
  keeps : Keeps powerClob s t

theorem setupSquareStep_ok {n size m a i : Nat} {base : Addr} {s t : State}
    (I : SetupInv n m size a i base s t) (hi : i < 6) :
    WP isa (setupSquareStep n) t fun u =>
      SetupInv n m size a (i + 1) base s u ∧ u.zf = some (decide (i + 1 = 6)) := by
  unfold setupSquareStep squareStep
  refine WP.seq (WP.mono (context_mul_ok I.context (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_) fun u ⟨Cu, K, lt, Mu⟩ => ?_)
  · rw [I.value]
    exact Nat.mod_lt _ (by have := I.context.gt_one; omega)
  · have Vu : wordsVal u.mem base (slot n 4) n = 2 ^ (64 * n + 2 ^ (i + 1) * a) % m := by
      have V := setup_square_power I.context.coprime lt (by simpa only [I.value] using Mu)
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using V
    have one := context_slot_val I.context (i := 3) (by decide) (by decide) (by decide) (by decide) K
    have out : Outs base (setupRanges n) t.mem u.mem := K.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [setupRanges, contextMod, accLen, words] <;> omega)
    have count : u.gpr .esi = BitVec.ofNat 32 (6 - i) := (K.gpr .esi (by decide)).trans I.counter
    refine wp_subS rfl fun v uv _ => ?_
    refine wp_cmpS rfl fun w fw zw => WP.block_nil ?_
    have mem : w.mem = u.mem := fw.mem.trans uv.mem
    have keep : Keeps powerClob u w := uv.keeps.mono (by decide) |>.trans (fw.keeps powerClob)
    have Cw : Context n m base size w :=
      ⟨Cu.scr.of_keeps keep (by decide), Cu.size_le, mem ▸ Cu.modulus, Cu.gt_one, mem ▸ Cu.inverse⟩
    refine ⟨⟨Cw, ?_, mem ▸ one.trans I.one, mem ▸ Vu, mem ▸ I.mem.trans out,
      I.keeps.trans (((VG.Proof.Mont.X86.Dynamic.OpKeep.keeps K).mono (by decide)).trans keep)⟩, ?_⟩
    · rw [fw.gpr, uv.gpr, count, counter_sub (by omega) (by omega)]
      congr 1
    · rw [zw, uv.gpr, count, counter_sub (by omega) (by omega), counter_zero (by omega) (by omega)]
      simp only [show (6 - i = 1) ↔ i + 1 = 6 by omega]

theorem setupSquares_ok {n size m a : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (V : wordsVal s.mem base (slot n 4) n = 2 ^ (64 * n + a) % m) :
    WP isa (setupSquares n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 3) n = wordsVal s.mem base (slot n 3) n ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n + 64 * a) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold setupSquares
  refine WP.seq (wp_movS rfl fun u su _ => WP.block_nil ?_)
  have ku : Keeps powerClob s u := su.keeps.mono (by decide)
  have Cu : Context n m base size u :=
    ⟨C.scr.of_keeps ku (by decide), C.size_le, su.mem ▸ C.modulus, C.gt_one, su.mem ▸ C.inverse⟩
  have init : SetupInv n m size a 0 base s u := by
    refine ⟨Cu, su.gpr, su.mem ▸ rfl, ?_, su.mem ▸ Outs.refl _ _ _, ku⟩
    simpa only [su.mem, Nat.pow_zero, Nat.one_mul] using V
  have loop : WP isa (.loop (setupSquareStep n) .ne) u (SetupInv n m size a 6 base s) := by
    refine WP.loop (M := isa)
      (fun k t => ∃ i, k = 6 - i ∧ i < 6 ∧ SetupInv n m size a i base s t)
      ?_ 6 u ⟨0, rfl, by decide, init⟩
    rintro k t ⟨i, rfl, hi, I⟩
    refine WP.mono (setupSquareStep_ok I hi) fun v ⟨next, zf⟩ => ?_
    by_cases done : i + 1 = 6
    · refine .inl ⟨?_, done ▸ next⟩
      simp only [eval, zf, done, decide_true, Option.map_some, Bool.not_true]
    · refine .inr ⟨?_, 6 - (i + 1), by omega, i + 1, rfl, by omega, next⟩
      simp only [eval, zf, decide_eq_false done, Option.map_some, Bool.not_false]
  exact WP.mono loop fun t I => ⟨I.context, I.one, I.value, I.mem, I.keeps⟩


end VG.Proof.Mont.X86.Dynamic
