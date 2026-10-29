module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext

import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Each array iteration extends the modular prefix and updates public control -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayLoad.lean`, which only this module imported.
section

/-! # Load the next high-to-low candidate word through its public frame pointer -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayState.loadWord {g : ArrayGeometry} (v : g.Valid) {candidate exponent i : Nat} {s : State}
    (S : ArrayState g candidate exponent i s) (index : i < g.n) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.Mod64.loadWord) s fun t =>
      ArrayState g candidate exponent i t ∧
      t.gpr .esi = VG.Proof.MillerRabin.exponentWord candidate (g.n - 1 - i) ∧
      t.mem = s.mem ∧ Keeps [.eax, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Mod64.loadWord
  refine wp_movS (S.context.stack.read 0 (by decide)) fun a A _ => ?_
  have address : a.ea ⟨.eax, 0⟩ = off g.base (g.src + 4 * (g.n - 1 - i)) := by
    change addr (a.gpr .eax) 0 = _
    rw [A.gpr, S.pointer, ArrayGeometry.pointer_eq index]
    have H := S.context.scratch.ea (d := g.src + 4 * (g.n - 1 - i)) (by have := v.sourceFit; omega)
    change addr (s.gpr .edi) (g.src + 4 * (g.n - 1 - i)) = _ at H
    rw [S.context.workspace] at H
    simpa only [addr, BitVec.add_zero] using H
  have access := (S.context.scratch.of_keeps A.keeps (by decide)).read
    (d := g.src + 4 * (g.n - 1 - i)) (n := 4) (by have := v.sourceFit; omega)
  have read : readSrc a (.mem ⟨.eax, 0⟩) =
      some (s.mem.readW (off g.base (g.src + 4 * (g.n - 1 - i))) 32) := by
    change a.load32 (a.ea ⟨.eax, 0⟩) = _
    rw [address, State.load32, ite_eq_left_iff.mpr (fun bad => absurd access bad), A.mem]
  refine wp_movS read fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .esi] s t := (A.keeps.mono (by decide)).widen T.keeps
  have M : t.mem = s.mem := T.mem.trans A.mem
  refine ⟨⟨S.context.keepReadonly K (by decide) (by decide) M, ?_, ?_, ?_, ?_⟩, ?_, M, K⟩
  · rw [M]
    exact S.pointer
  · rw [M]
    exact S.count
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact S.value
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact S.bound
  · rw [T.gpr]
    exact VG.Proof.MillerRabin.read_exponentWord S.context.candidateValue (by omega)

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayCount.lean`, which only this module imported.
section

/-! # Decrement the public native-word count in the caller's frame -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem countDown_ok {p : BitVec 32} {s : State} (C : Sieve.StackContext p s) {q : Nat}
    (positive : 0 < q) (bound : q < 2 ^ 32)
    (value : s.mem.readW (off (p.setWidth 64) 4) 32 = BitVec.ofNat 32 q) :
    WP isa (.block countDown) s fun t =>
      t.mem.readW (off (p.setWidth 64) 4) 32 = BitVec.ofNat 32 (q - 1) ∧
      t.zf = some (decide (q - 1 = 0)) ∧ Outside (p.setWidth 64) 4 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold countDown
  refine wp_movS (C.read 4 (by decide)) fun a A _ => wp_subS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have next : b.gpr .eax = BitVec.ofNat 32 (q - 1) := by
    rw [B.gpr, A.gpr, value]
    change BitVec.ofNat 32 q - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  have stack := C.keep K (by decide)
  refine wp_storeS (stack.address 4 (by decide))
    (VG.Proof.Mont.X86.Rt.ws_write stack.ws (y := 4) (n := 4) (by decide)) fun c S => ?_
  have Kc := S.keeps []
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, K.widen (Kc.trans (T.keeps []))⟩
  · rw [T.mem, S.mem, Mem.readW_writeW_self32, next]
  · rw [Z, Kc.1 .eax (by decide), next]
    change some (BitVec.ofNat 32 (q - 1) - 0#32 == 0) = _
    rw [BitVec.sub_zero, ofNat_beq_zero (by omega)]
  · rw [T.mem, S.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayPrevious.lean`, which only this module imported.
section

/-! # Move the public source pointer to the preceding native word -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem previousWord_ok {g : ArrayGeometry} {s : State} {i : Nat}
    (C : Sieve.StackContext g.sp s)
    (pointer : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i) :
    WP isa (.block previousWord) s fun t =>
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer (i + 1) ∧
      Outside (g.sp.setWidth 64) 0 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold previousWord
  refine wp_movS (C.read 0 (by decide)) fun a A _ => wp_subS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have next : b.gpr .eax = g.pointer (i + 1) := by
    rw [B.gpr, A.gpr, pointer]
    unfold ArrayGeometry.pointer
    rw [BitVec.sub_sub]
    change _ - (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  have stack := C.keep K (by decide)
  refine wp_storeS (stack.address 0 (by decide))
    (VG.Proof.Mont.X86.Rt.ws_write stack.ws (y := 0) (n := 4) (by decide)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, Mem.readW_writeW_self32, next]
  · rw [T.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayAdvance.lean`, which only this module imported.
section

/-! # The complete public control update preserves the candidate and exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem advance_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent i q : Nat} {s : State}
    (C : ArrayContext g candidate exponent s) (positive : 0 < q) (bound : q < 2 ^ 32)
    (pointer : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i)
    (count : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 q) :
    WP isa (.block advance) s fun t =>
      ArrayContext g candidate exponent t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer (i + 1) ∧
      t.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (q - 1) ∧
      t.zf = some (decide (q - 1 = 0)) ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold advance
  refine WP.block_append (WP.mono (previousWord_ok C.stack pointer) fun a ⟨P, Oa, Ka⟩ => ?_)
  have Ca := C.keepFrame v Ka (by decide) (by decide)
    (arrayStackFrame (Oa.mono (by decide) (by decide)))
  have countA : a.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 q :=
    (BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (by decide) (by decide))).trans count
  refine WP.mono (countDown_ok Ca.stack positive bound countA) fun t ⟨N, Z, Ot, Kt⟩ => ?_
  refine ⟨Ca.keepFrame v Kt (by decide) (by decide) (arrayStackFrame (Ot.mono (by decide) (by decide))),
    ?_, N, Z, (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), Ka.trans Kt⟩
  exact (BitVec.eq_of_toNat_eq (Ot.w32 (d := 0) (by decide) (by decide))).trans P

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayMath.lean`, which only this module imported.
section

/-! # Extend a high-to-low modular prefix by one complete native word -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64

theorem high_prefix_step (candidate k : Nat) :
    candidate / 2 ^ (32 * (k + 1)) * 2 ^ 32 + (VG.Proof.MillerRabin.exponentWord candidate k).toNat =
      candidate / 2 ^ (32 * k) := by
  rw [VG.Proof.MillerRabin.exponentWord, BitVec.toNat_ofNat,
    show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  have H := Nat.div_add_mod (candidate / 2 ^ (32 * k)) (2 ^ 32)
  omega

theorem high_mod_step (candidate exponent k : Nat) :
    ((candidate / 2 ^ (32 * (k + 1)) % exponent) * 2 ^ 32 +
      (VG.Proof.MillerRabin.exponentWord candidate k).toNat) % exponent =
      candidate / 2 ^ (32 * k) % exponent := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod, high_prefix_step]

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/Shift32.lean`, which only this module imported.
section

/-! # One native word supplies its bits from most to least significant -/

section
namespace VG.Proof.RsaKeyGen

theorem shift_step32 (x k i : Nat) (hki : k + i = 31) :
    (x % 2 ^ (k + 1)) * 2 ^ i < 2 ^ 32 ∧
    (decide (2 ^ 32 ≤ (x % 2 ^ (k + 1)) * 2 ^ i + (x % 2 ^ (k + 1)) * 2 ^ i)).toNat = x / 2 ^ k % 2 ∧
    ((x % 2 ^ (k + 1)) * 2 ^ i + (x % 2 ^ (k + 1)) * 2 ^ i) % 2 ^ 32 = (x % 2 ^ k) * 2 ^ (i + 1) ∧
    x / 2 ^ (k + 1) * 2 + x / 2 ^ k % 2 = x / 2 ^ k := by
  rw [Nat.mod_pow_succ]
  have hPQ : 2 ^ k * 2 ^ i = 2 ^ 31 := by rw [← Nat.pow_add, hki]
  have hb : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlow : x % 2 ^ k * 2 ^ i < 2 ^ 31 := by
    rw [← hPQ]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  have hexp : (x % 2 ^ k + 2 ^ k * (x / 2 ^ k % 2)) * 2 ^ i = x % 2 ^ k * 2 ^ i + 2 ^ 31 * (x / 2 ^ k % 2) := by
    rw [Nat.add_mul, ← hPQ, Nat.mul_right_comm (2 ^ k) _ (2 ^ i)]
  have h2i : x % 2 ^ k * 2 ^ (i + 1) = 2 * (x % 2 ^ k * 2 ^ i) := by
    rw [Nat.pow_succ]; rw [Nat.mul_comm 2, Nat.mul_assoc]
  have hdiv : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hexp, h2i, hdiv]
  have hd := Nat.div_add_mod (x / 2 ^ k) 2
  generalize x % 2 ^ k * 2 ^ i = M at hlow ⊢
  generalize x / 2 ^ k % 2 = b at hb hd ⊢
  refine ⟨by omega, ?_, by omega, by omega⟩
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

end VG.Proof.RsaKeyGen
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64WordMath.lean`, which only this module imported.
section

/-! # The fixed native-word reduction consumes the input's high-to-low bits -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64

def shifted (x i : Nat) : Nat := (x % 2 ^ (32 - i)) * 2 ^ i
def consumed (x i : Nat) : Nat := x / 2 ^ (32 - i)

theorem word_step (x i : Nat) (index : i < 32) (word : BitVec 32) (value : word.toNat = shifted x i) :
    (word + word).toNat = shifted x (i + 1) ∧
      consumed x i * 2 + (incoming word).toNat = consumed x (i + 1) := by
  have H := VG.Proof.RsaKeyGen.shift_step32 x (31 - i) i (by omega)
  rw [show 31 - i + 1 = 32 - i by omega, show 31 - i = 32 - (i + 1) by omega] at H
  have bitValue : (incoming word).toNat = x / 2 ^ (32 - (i + 1)) % 2 := by
    unfold incoming
    rw [value]
    exact H.2.1
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add, value]
    exact H.2.2.1
  · rw [bitValue]
    exact H.2.2.2

theorem consumed_mod_step (r x i exponent bit : Nat) (advance : consumed x i * 2 + bit = consumed x (i + 1)) :
    (2 * ((r * 2 ^ i + consumed x i) % exponent) + bit) % exponent =
      (r * 2 ^ (i + 1) + consumed x (i + 1)) % exponent := by
  rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
  congr 1
  rw [Nat.pow_succ]
  grind

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64Word.lean`, which only this module imported.
section

/-! # A fixed native word reduces as one radix-2³² digit -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

structure WordState (s₀ : State) (base : Addr) (exponent i : Nat) (s : State) : Prop where
  value : pair (s.gpr .ecx) (s.gpr .ebx) =
    (pair (s₀.gpr .ecx) (s₀.gpr .ebx) * 2 ^ i + consumed (s₀.gpr .esi).toNat i) % exponentValue s₀.mem base exponent
  bound : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s₀.mem base exponent
  wordValue : (s.gpr .esi).toNat = shifted (s₀.gpr .esi).toNat i
  memory : s.mem = s₀.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ s

theorem steps_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size)
    (remainder : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s.mem base exponent)
    (count : Nat) (limit : count ≤ 32) :
    WP isa (.block (steps exponent count)) s (WordState s base exponent count) := by
  induction count with
  | zero =>
    refine WP.block_nil ⟨?_, remainder, ?_, rfl, Keeps.refl _ _⟩
    · simp only [Nat.pow_zero, Nat.mul_one, consumed, Nat.sub_zero,
        Nat.div_eq_of_lt (s.gpr .esi).isLt, Nat.add_zero, Nat.mod_eq_of_lt remainder]
    · simp only [shifted, Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (s.gpr .esi).isLt]
  | succ i ih =>
    unfold steps
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.block_append (WP.mono (ih (by omega)) fun t T => ?_)
    have math := word_step (s.gpr .esi).toNat i (by omega) (t.gpr .esi) T.wordValue
    refine WP.mono (bit_ok (scratch.of_keeps T.keeps (by decide)) fit
      (by rw [T.memory]; exact T.bound)) fun u ⟨value, bound, shiftedWord, mem, keep⟩ => ?_
    rw [T.memory, T.value] at value
    refine ⟨value.trans (consumed_mod_step _ _ _ _ _ math.2), ?_, ?_, mem.trans T.memory, T.keeps.trans keep⟩
    · rw [T.memory] at bound
      exact bound
    · rw [shiftedWord]
      exact math.1

theorem word_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size)
    (remainder : pair (s.gpr .ecx) (s.gpr .ebx) < exponentValue s.mem base exponent) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Mod64.word exponent)) s fun t =>
      pair (t.gpr .ecx) (t.gpr .ebx) =
        (pair (s.gpr .ecx) (s.gpr .ebx) * 2 ^ 32 + (s.gpr .esi).toNat) % exponentValue s.mem base exponent ∧
      pair (t.gpr .ecx) (t.gpr .ebx) < exponentValue s.mem base exponent ∧
      t.gpr .esi = 0#32 ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (steps_ok scratch fit remainder 32 (by decide)) fun t T => ?_
  refine ⟨?_, T.bound, ?_, T.memory, T.keeps⟩
  · simpa only [consumed, Nat.sub_self, Nat.pow_zero, Nat.div_one] using T.value
  · apply BitVec.eq_of_toNat_eq
    change (t.gpr .esi).toNat = 0
    simpa only [shifted, Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.zero_mul] using T.wordValue

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayState.step {g : ArrayGeometry} (v : g.Valid) {candidate exponent i : Nat} {s : State}
    (S : ArrayState g candidate exponent i s) (index : i < g.n) :
    WP isa (arrayStep g.exponent) s fun t =>
      ArrayState g candidate exponent (i + 1) t ∧ t.zf = some (decide (i + 1 = g.n)) ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold arrayStep
  refine WP.seq (WP.mono (S.loadWord v index) fun a ⟨A, inputWord, Ma, Ka⟩ => ?_)
  refine WP.seq (WP.mono (word_ok A.context.scratch v.exponentFit
    (by rw [A.context.exponentEq]; exact A.bound)) fun b ⟨value, bound, _, Mb, Kb⟩ => ?_)
  have Cb := A.context.keepReadonly Kb (by decide) (by decide) Mb
  rw [A.context.exponentEq, A.value, inputWord,
    show g.n - i = (g.n - 1 - i) + 1 by omega, high_mod_step] at value
  rw [A.context.exponentEq] at bound
  have Pb : b.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i := by rw [Mb]; exact A.pointer
  have Nb : b.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (g.n - i) := by rw [Mb]; exact A.count
  have countBound : g.n - i < 2 ^ 32 := by have := v.sourceFit; have := Cb.scratch.nowrap; omega
  refine WP.mono (advance_ok v Cb (by omega) countBound Pb Nb) fun t ⟨Ct, P, N, Z, O, K⟩ => ?_
  refine ⟨⟨Ct, P, ?_, ?_, ?_⟩, ?_, ?_, ((Ka.mono (by decide)).trans Kb).widen K⟩
  · rw [show g.n - i - 1 = g.n - (i + 1) by omega] at N
    exact N
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide), value,
      show g.n - 1 - i = g.n - (i + 1) by omega]
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact bound
  · simpa only [show g.n - i - 1 = 0 ↔ i + 1 = g.n by omega] using Z
  · rw [Mb, Ma] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Mod64
