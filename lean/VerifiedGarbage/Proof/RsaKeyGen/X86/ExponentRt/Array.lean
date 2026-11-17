module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `RsaKeyGen.X86.Mod64ArrayStep`, which this module and modules that import it used -/

section

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
    show g.n - i = (g.n - 1 - i) + 1 by omega_using [index], high_mod_step] at value
  rw [A.context.exponentEq] at bound
  have Pb : b.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i := by rw [Mb]; exact A.pointer
  have Nb : b.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (g.n - i) := by rw [Mb]; exact A.count
  have countBound : g.n - i < 2 ^ 32 := by have := v.sourceFit; have := Cb.scratch.nowrap; omega_arith
  refine WP.mono (advance_ok v Cb (by omega_using [index]) countBound Pb Nb) fun t ⟨Ct, P, N, Z, O, K⟩ => ?_
  refine ⟨⟨Ct, P, ?_, ?_, ?_⟩, ?_, ?_, ((Ka.mono (by decide)).trans Kb).widen K⟩
  · rw [show g.n - i - 1 = g.n - (i + 1) by omega_using []] at N
    exact N
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide), value,
      show g.n - 1 - i = g.n - (i + 1) by omega_using []]
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact bound
  · simpa only [show g.n - i - 1 = 0 ↔ i + 1 = g.n by omega_using [index]] using Z
  · rw [Mb, Ma] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Mod64

end

end

/-! # The remainder of the saved candidate minus one by `e`, at a run-time width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayInit.lean`, which only this module imported.
section

/-! # The array reduction starts with remainder zero -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem zeroRemainder_ok (s : State) :
    WP isa (.block zeroRemainder) s fun t =>
      t.gpr .ecx = 0#32 ∧ t.gpr .ebx = 0#32 ∧ t.mem = s.mem ∧ Keeps [.ecx, .ebx] s t := by
  unfold zeroRemainder
  refine wp_movS rfl fun a A _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .ecx (by decide), A.gpr]; rfl, by rw [T.gpr]; rfl,
    T.mem.trans A.mem, (A.keeps.mono (by decide)).widen T.keeps⟩

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayLoop.lean`, which only this module imported.
section

/-! # Reduce every native word while preserving the full modular prefix invariant -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem loop_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (S : ArrayState g candidate exponent 0 s) :
    WP isa (.loop (arrayStep g.exponent) .ne) s fun t =>
      ArrayState g candidate exponent g.n t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let Inv := fun q t => ∃ i, i + q = g.n ∧ 0 < q ∧ ArrayState g candidate exponent i t ∧
    Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  refine WP.loop (M := isa) Inv ?_ g.n s ⟨0, by omega, v.positive, S, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  rintro q t ⟨i, count, positive, T, O, K⟩
  refine WP.mono (T.step v (by omega)) fun u ⟨U, Z, Ou, Ku⟩ => ?_
  by_cases done : i + 1 = g.n
  · left
    refine ⟨?_, done ▸ U, O.trans Ou, K.trans Ku⟩
    change u.zf.map Bool.not = some false
    rw [Z, decide_eq_true done]
    rfl
  · right
    refine ⟨?_, q - 1, by omega, i + 1, by omega, by omega, U, O.trans Ou, K.trans Ku⟩
    change u.zf.map Bool.not = some true
    rw [Z, decide_eq_false done]
    rfl

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt
open VG.Proof.RsaKeyGen.X86.Mod64

/-- The geometry of the reduction of array 5 by `e` (at byte 128). -/
def geometry (sp workspace : BitVec 32) (size w : Nat) : ArrayGeometry := ⟨sp, workspace, size, 2 * w, slot w 5, 128⟩

theorem init_ok {sp workspace : BitVec 32} {size w : Nat} (v : (geometry sp workspace size w).Valid)
    {candidate exponent : Nat} {s : State} (C : ArrayContext (geometry sp workspace size w) candidate exponent s)
    (positive : 0 < exponent) (hw : w ≤ 64)
    (len : s.mem.readW (off (geometry sp workspace size w).base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block arrayInit) s fun t =>
      ArrayState (geometry sp workspace size w) candidate exponent 0 t ∧
      Outside (sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have hn := v.sourceFit
  change slot w 5 + 4 * (2 * w) ≤ size at hn
  have wpos := v.positive
  change 0 < 2 * w at wpos
  have nowrap := C.scratch.nowrap
  change (workspace.setWidth 64).toNat + size ≤ 2 ^ 32 at nowrap
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := workspace.isLt; omega_using [])] at nowrap
  have header : 8 ≤ size := by have := slot5_lo w; omega_using [hn, wpos]
  unfold arrayInit
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine savedPtr_ok C.scratch header len (by decide) (by decide) (by decide) fun a Ka Ma eaxA => ?_
  have Sa := C.scratch.of_keeps Ka (by decide)
  refine wp_movS (readSrc_sc Sa (by change 4 + 4 ≤ size; omega_using [header])) fun b B _ => wp_addS rfl fun c D _ => wp_subS rfl fun d E _ => ?_
  have Kd : Keeps [.eax, .edx] s d :=
    (((Ka.mono (by decide)).trans (B.keeps.mono (by decide))).trans (D.keeps.mono (by decide))).trans
      (E.keeps.mono (by decide))
  have Cd := C.stack.keep Kd (by decide)
  refine wp_storeS (Cd.address 0 (by decide)) (ws_write Cd.ws (by decide)) fun e F => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun f G => ?_
  have Kf : Keeps [.eax, .edx] s f := (Kd.trans ((F.keeps []).mono (by decide))).trans (G.keeps.mono (by decide))
  have Cf := C.stack.keep Kf (by decide)
  refine wp_storeS (Cf.address 4 (by decide)) (ws_write Cf.ws (by decide)) fun g H => ?_
  have Kg : Keeps [.eax, .edx] s g := Kf.trans ((H.keeps []).mono (by decide))
  have lenB : b.gpr .edx = BitVec.ofNat 32 (8 * w) := by rw [B.gpr, Ma, len]
  have edi : s.gpr .edi = workspace := C.workspace
  have ptr : d.gpr .eax = (geometry sp workspace size w).pointer 0 := by
    rw [E.gpr, D.gpr, B.other .eax (by decide), eaxA, lenB, edi]
    apply BitVec.eq_of_toNat_eq
    have h4 : (4 : BitVec 32).toNat = 4 := rfl
    simp only [geometry, ArrayGeometry.pointer, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h4]
    have := workspace.isLt
    have := slot5_lo w
    omega_using [wpos]
  have count : f.gpr .edx = BitVec.ofNat 32 (2 * w) := by
    rw [G.gpr, F.gpr, E.other .edx (by decide), D.other .edx (by decide), lenB]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw]),
      Nat.mod_eq_of_lt (by omega_using [hw]), Nat.shiftRight_eq_div_pow]
    omega_using []
  have Oe : Outside (sp.setWidth 64) 0 4 s.mem e.mem := by
    rw [F.mem, E.mem, D.mem, B.mem, Ma]
    exact writeW32_outside _ _ _ (by decide)
  have Og : Outside (sp.setWidth 64) 4 4 e.mem g.mem := by
    rw [H.mem, G.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Cg := C.keepFrame v Kg (by decide) (by decide)
    (arrayStackFrame ((Oe.mono (by decide) (by decide)).trans (Og.mono (by decide) (by decide))))
  have Pg : g.mem.readW (off (sp.setWidth 64) 0) 32 = (geometry sp workspace size w).pointer 0 := by
    rw [BitVec.eq_of_toNat_eq (Og.w32 (d := 0) (by decide) (by decide)), F.mem]
    exact (Mem.readW_writeW_self32 ..).trans ptr
  have Ng : g.mem.readW (off (sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (2 * w) := by
    rw [H.mem]
    exact (Mem.readW_writeW_self32 ..).trans count
  refine WP.mono (zeroRemainder_ok g) fun t ⟨Zc, Zb, M, K⟩ => ?_
  have Ct := Cg.keepReadonly K (by decide) (by decide) M
  have zero : pair (t.gpr .ecx) (t.gpr .ebx) = 0 := by rw [Zc, Zb]; rfl
  have bound : candidate < 2 ^ (32 * (2 * w)) := by rw [← C.candidateValue]; exact val32_lt ..
  refine ⟨⟨Ct, by rw [M]; exact Pg, by rw [M]; exact Ng, ?_, ?_⟩, ?_, (Kg.mono (by decide)).trans (K.mono (by decide))⟩
  · change pair (t.gpr .ecx) (t.gpr .ebx) = (candidate / 2 ^ (32 * (2 * w - 0))) % exponent
    rw [zero, Nat.sub_zero, Nat.div_eq_of_lt bound, Nat.zero_mod]
  · rw [zero]; exact positive
  · rw [M]
    exact (Oe.mono (by decide) (by decide)).trans (Og.mono (by decide) (by decide))

theorem array_ok {sp workspace : BitVec 32} {size w : Nat} (v : (geometry sp workspace size w).Valid)
    {candidate exponent : Nat} {s : State} (C : ArrayContext (geometry sp workspace size w) candidate exponent s)
    (positive : 0 < exponent) (hw : w ≤ 64)
    (len : s.mem.readW (off (geometry sp workspace size w).base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa array s fun t =>
      ArrayContext (geometry sp workspace size w) candidate exponent t ∧
      pair (t.gpr .ecx) (t.gpr .ebx) = candidate % exponent ∧
      Outside (sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (init_ok v C positive hw len) fun u ⟨U, O, K⟩ => ?_)
  refine WP.mono (loop_ok v U) fun t ⟨T, Ot, Kt⟩ => ?_
  refine ⟨T.context, ?_, O.trans Ot, (K.mono (by decide)).trans Kt⟩
  simpa only [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using T.value

theorem array_noSp : NoSp array := by
  apply NoSp.of_all
  have bitSafe (e : Nat) : (VG.Impl.RsaKeyGen.X86.Mod64.bit e).all (fun i => !Taint.clobbers i .esp) = true := by rfl
  simp only [Code.allInstrs_eq, array, VG.Impl.RsaKeyGen.X86.Mod64.arrayStep, instrs,
    List.all_append, VG.Impl.RsaKeyGen.X86.Mod64.word, VG.Impl.RsaKeyGen.X86.Mod64.steps, List.all_flatMap, bitSafe]
  rfl

theorem framed_context {base : Addr} {size w candidate exponent : Nat} {s : State}
    (S : Scr s base size) (width : 4 ≤ w) (space : slot w 5 + 8 * w ≤ size)
    (value : val32 s.mem base (slot w 5) (2 * w) = candidate)
    (eValue : exponentValue s.mem base 128 = exponent)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    (geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w).Valid ∧
      ArrayContext (geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w) candidate exponent (allocFrame 20 s) := by
  let g : ArrayGeometry := geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w
  have baseEq : g.base = base := S.edi
  have lo := slot5_lo w
  refine ⟨⟨by change 0 < 2 * w; omega_using [width], by change slot w 5 + 4 * (2 * w) ≤ size; omega_using [space],
    by change 128 + 8 ≤ size; omega_using [space, lo], by
    change (⟨g.base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩
    rw [baseEq]
    exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega_using [fit]) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))⟩, ?_⟩
  refine ⟨?_, VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (s := s) (by omega_using [fit]), ?_, ?_⟩
  · change Scr (allocFrame 20 s) g.base size
    rw [baseEq]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S fit separate
  · change val32 s.mem g.base (slot w 5) (2 * w) = candidate
    rw [baseEq]; exact value
  · change exponentValue s.mem g.base 128 = exponent
    rw [baseEq]; exact eValue

theorem framed_ok {base : Addr} {size w candidate exponent : Nat} {s : State}
    (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64) (space : slot w 5 + 8 * w ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (value : val32 s.mem base (slot w 5) (2 * w) = candidate)
    (eValue : exponentValue s.mem base 128 = exponent) (ePositive : 0 < exponent)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa (.frame (.alloc 20) array (.free 20)) s fun t =>
      Scr t base size ∧ pair (t.gpr .ecx) (t.gpr .ebx) = candidate % exponent ∧
      val32 t.mem base (slot w 5) (2 * w) = candidate ∧ exponentValue t.mem base 128 = exponent ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let g : ArrayGeometry := geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w
  have baseEq : g.base = base := S.edi
  have lo := slot5_lo w
  have valid : g.Valid := ⟨by change 0 < 2 * w; omega_using [width], by change slot w 5 + 4 * (2 * w) ≤ size; omega_using [space],
    by change 128 + 8 ≤ size; omega_using [space, lo], by
    change (⟨g.base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩
    rw [baseEq]
    exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega_using [fit]) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h]))⟩
  have C : ArrayContext g candidate exponent (allocFrame 20 s) := by
    refine ⟨?_, VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (s := s) (by omega_using [fit]), ?_, ?_⟩
    · rw [baseEq]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S fit separate
    · change val32 s.mem g.base (slot w 5) (2 * w) = candidate
      rw [baseEq]; exact value
    · change exponentValue s.mem g.base 128 = exponent
      rw [baseEq]; exact eValue
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega_using [fit]) array_noSp ?_
  · refine WP.mono (array_ok valid C ePositive hw (by rw [allocFrame_mem, baseEq]; exact len))
      fun t ⟨T, result, O, K⟩ => ?_
    have Kout := VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps K (by decide)
    refine ⟨S.of_keeps Kout (by decide), ?_, ?_, ?_, ?_, Kout⟩
    · rw [freed_gpr _ _ (by decide), freed_gpr _ _ (by decide)]
      exact result
    · rw [← baseEq]; exact T.candidateValue
    · rw [← baseEq]; exact T.exponentEq
    · have F : Frame [g.stackRegion] (allocFrame 20 s).mem t.mem := arrayStackFrame O
      rw [allocFrame_mem] at F
      exact F

end VG.Proof.RsaKeyGen.X86.ExponentRt
