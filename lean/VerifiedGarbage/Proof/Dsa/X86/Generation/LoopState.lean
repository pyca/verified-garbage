module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessTape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestedDraw
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopEnd
public import VerifiedGarbage.Proof.Dsa.Generation.MrPolicy

/-! The witness loop tracks the exact tape suffix and shared mathematical loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

def loopRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .ebp]

structure LoopReady (s₀ : State) (base : Addr) (bytes n len candidate checks startLen : Nat)
    (result : Option (Bool × List Byte)) (measure : Nat) (r : List Byte) (ptr : BitVec 32)
    (i uniform : Nat) (s : State) : Prop where
  prime : PrimeState base n candidate s
  tape : WitnessTape base bytes (s₀.gpr .esp) ptr r s
  length : r.length = measure
  left : r.length ≤ startLen
  budget : i ≤ startLen - r.length + 1
  count : uniform ≤ i
  go : i ≤ 16 ∨ uniform < checks
  cursor : s.mem.readW (off base witnessCursor) 32 = ptr
  remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length
  index : s.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 i
  uniforms : s.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform
  spec : result = VG.Proof.Dsa.Generation.candidateLoop candidate checks i uniform r
  frame : SampleRoundFrame base (s₀.gpr .esp) len s₀ s
  regs : Keeps loopRegs s₀ s

theorem LoopReady.of_keeps {s₀ s t : State} {base : Addr} {bytes n len candidate checks startLen measure : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (K : Keeps loopRegs s t) (memory : t.mem = s.mem) :
    LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform t := by
  refine ⟨R.prime.of_keeps K (by decide) (by decide) memory,
    R.tape.of_keeps K.2.1 K.2.2 memory, R.length, R.left, R.budget, R.count, R.go,
    ?_, ?_, ?_, ?_, R.spec, ?_, R.regs.trans K⟩
  · rw [memory]; exact R.cursor
  · rw [memory]; exact R.remaining
  · rw [memory]; exact R.index
  · rw [memory]; exact R.uniforms
  · unfold SampleRoundFrame; rw [memory]; exact R.frame

theorem LoopReady.draw_bounds {s₀ s : State} {base : Addr} {bytes n len candidate checks startLen measure drawBytes : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (small : startLen < 2 ^ 32) (minimum : 2 ≤ drawBytes) (available : drawBytes ≤ r.length) :
    i + 1 < 2 ^ 32 ∧ uniform + 1 < 2 ^ 32 := by
  have budget := R.budget
  have left := R.left
  have count := R.count
  omega

theorem LoopReady.frame_step {s₀ s t : State} {base : Addr} {bytes n len candidate checks startLen measure : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (F : SampleRoundFrame base (s.gpr .esp) len s t) : SampleRoundFrame base (s₀.gpr .esp) len s₀ t := by
  rw [R.regs.1 .esp (by decide)] at F
  exact R.frame.trans F

theorem LoopReady.keep_tape {s₀ s t : State} {base : Addr} {bytes n len candidate checks startLen measure : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (F : SampleRoundFrame base (s.gpr .esp) len s t) (K : Keeps loopRegs s t)
    (capacity : 40960 ≤ bytes) (length : len ≤ 384) : WitnessTape base bytes (s₀.gpr .esp) ptr r t := by
  rw [R.regs.1 .esp (by decide)] at F
  exact R.tape.keep F capacity length K.2.1 K.2.2

def LoopAnswer (result : Option (Bool × List Byte)) (r : List Byte) (status : Nat) : Prop :=
  match result with
  | none => status = 0
  | some (b, rest) => r = rest ∧ status = if b then 1 else 3

structure LoopTerminal (s₀ : State) (base : Addr) (bytes n len candidate : Nat)
    (result : Option (Bool × List Byte)) (r : List Byte) (ptr : BitVec 32) (status : Nat) (s : State) : Prop where
  prime : PrimeState base n candidate s
  tape : WitnessTape base bytes (s₀.gpr .esp) ptr r s
  cursor : s.mem.readW (off base witnessCursor) 32 = ptr
  remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length
  value : s.mem.readW (off base primeStatus) 32 = BitVec.ofNat 32 status
  bound : status ≤ 4
  answer : LoopAnswer result r status
  frame : SampleRoundFrame base (s₀.gpr .esp) len s₀ s
  regs : Keeps loopRegs s₀ s

structure LoopResult (s₀ : State) (base : Addr) (bytes n len candidate : Nat)
    (result : Option (Bool × List Byte)) (r : List Byte) (ptr : BitVec 32) (s : State) : Prop where
  prime : PrimeState base n candidate s
  tape : WitnessTape base bytes (s₀.gpr .esp) ptr r s
  cursor : s.mem.readW (off base witnessCursor) 32 = ptr
  remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length
  answer : match result with
    | none => s.gpr .eax = 0#32
    | some (b, rest) => r = rest ∧ s.gpr .eax = BitVec.ofNat 32 (if b then 1 else 3)
  frame : SampleRoundFrame base (s₀.gpr .esp) len s₀ s
  regs : Keeps loopRegs s₀ s

theorem LoopResult.prefix {s₀ s t : State} {base : Addr} {bytes n len candidate : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32}
    (R : LoopResult s base bytes n len candidate result r ptr t)
    (F : SampleRoundFrame base (s₀.gpr .esp) len s₀ s) (K : Keeps loopRegs s₀ s) :
    LoopResult s₀ base bytes n len candidate result r ptr t := by
  have tape := R.tape
  have frame := R.frame
  rw [K.1 .esp (by decide)] at tape frame
  exact ⟨R.prime, tape, R.cursor, R.remaining, R.answer, F.trans frame, K.trans R.regs⟩

def LoopInvariant (s₀ : State) (base : Addr) (bytes n len candidate checks startLen : Nat)
    (result : Option (Bool × List Byte)) (measure : Nat) (s : State) : Prop :=
  ∃ r ptr i uniform, LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s

def LoopStepPost (s₀ : State) (base : Addr) (bytes n len candidate checks startLen : Nat)
    (result : Option (Bool × List Byte)) (measure : Nat) (s : State) : Prop :=
  (isa.eval .e s = some false ∧ ∃ r ptr, LoopResult s₀ base bytes n len candidate result r ptr s) ∨
    (isa.eval .e s = some true ∧ ∃ next < measure,
      LoopInvariant s₀ base bytes n len candidate checks startLen result next s)

theorem LoopTerminal.finish {s₀ s : State} {base : Addr} {bytes n len candidate : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32} {status : Nat}
    (T : LoopTerminal s₀ base bytes n len candidate result r ptr status s)
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) :
    WP isa (.block primeLoopEnd) s fun t =>
      isa.eval .e t = some false ∧ ∃ r ptr, LoopResult s₀ base bytes n len candidate result r ptr t := by
  refine WP.mono (prime_loop_end scr capacity T.bound T.value) fun t ⟨value, zf, memory, K⟩ => ?_
  have noContinue : status ≠ 4 := by
    have answer := T.answer
    unfold LoopAnswer at answer
    cases result with
    | none => simp only at answer; omega
    | some pair => cases pair with | mk b rest => cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at answer <;> omega
  refine ⟨by simpa only [eval, noContinue, decide_false] using zf,
    ⟨r, ptr, ⟨T.prime.of_keeps K (by decide) (by decide) memory,
      T.tape.of_keeps K.2.1 K.2.2 memory, ?_, ?_, ?_, ?_, T.regs.trans (K.mono (by decide))⟩⟩⟩
  · rw [memory]; exact T.cursor
  · rw [memory]; exact T.remaining
  · have answer := T.answer
    cases result with
    | none => rw [answer] at value; exact value
    | some pair => cases pair with | mk b rest => exact ⟨answer.1, by rw [answer.2] at value; exact value⟩
  · unfold SampleRoundFrame; rw [memory]; exact T.frame

end VG.Proof.Dsa.X86.Generation
