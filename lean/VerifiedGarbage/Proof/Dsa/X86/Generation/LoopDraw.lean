module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoopState
import VerifiedGarbage.Proof.Framework.Offset

/-! A full draw either completes the shared policy or strictly shortens the remaining tape. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.Generation (candidateLoop candidate_loop_step candidate_loop_done)

theorem loop_draw (v : RoundImpl) {s₀ s : State} {base : Addr}
    {bytes n len candidate checks startLen measure drawBytes : Nat} {result : Option (Bool × List Byte)}
    {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (stack : RoundRoom (s.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0) (padded : len ≤ drawBytes)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (width : Spec.RsaKeyGen.witnessBytes candidate = drawBytes)
    (checksBound : checks < 2 ^ 32) (startBound : startLen < 2 ^ 32) (available : drawBytes ≤ r.length) :
    WP isa (testedDraw v.name v.code n len drawBytes checks) s fun b => WP isa (.block primeLoopEnd) b
      (LoopStepPost s₀ base bytes n len candidate checks startLen result measure) := by
  have drawPositive : 0 < drawBytes := by omega
  have lenBound : len ≤ 384 := by omega
  have remainingBound : r.length < 2 ^ 32 := Nat.lt_of_le_of_lt R.left startBound
  have bounds := R.draw_bounds startBound (by omega) available
  obtain ⟨read, apart⟩ := R.tape.prefix drawPositive available
  let w := Spec.RsaKeyGen.witness (candidate - 1) (Spec.Rsa.os2ip (r.take drawBytes))
  have drawn : drawnWitness candidate s.mem ptr drawBytes = w := by
    have slice := VG.Proof.Dsa.bytesAt_slice s.mem (byteAddr ptr) (total := r.length)
      (offset := 0) (len := drawBytes) (by omega)
    simp only [List.drop_zero, BitVec.add_zero] at slice
    unfold drawnWitness
    rw [← slice, R.tape.data]
  have math := candidate_loop_step r R.go width drawPositive
  rw [ite_eq_left available] at math
  have root : result = if Spec.MillerRabin.round candidate w.1 then
      candidateLoop candidate checks (i + 1) (uniform + w.2.toNat) (r.drop drawBytes)
      else some (false, r.drop drawBytes) := R.spec.trans math
  have draw := draw_round v scr capacity R.prime stack positive upper lower length aligned padded bits
    R.cursor R.remaining available remainingBound (by have := R.tape.fit; omega) read apart
  refine WP.mono (tested_draw scr capacity draw R.index R.uniforms bounds.1 bounds.2 checksBound)
    fun b ⟨prime, _, _, status, index, uniforms, cursor, remaining, F, K⟩ => ?_
  rw [drawn] at status index uniforms
  have Sb := scr.of_keeps K (by decide)
  have tape := (R.keep_tape F K capacity lenBound).advance available
  have frame := R.frame_step F
  have regs := R.regs.trans K
  have remain : b.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 (r.drop drawBytes).length := by
    rw [List.length_drop]; exact remaining
  have finish : ∀ statusValue, statusValue ≤ 4 →
      b.mem.readW (off base primeStatus) 32 = BitVec.ofNat 32 statusValue →
      LoopAnswer result (r.drop drawBytes) statusValue →
      WP isa (.block primeLoopEnd) b (LoopStepPost s₀ base bytes n len candidate checks startLen result measure) := by
    intro statusValue statusBound value answer
    have T : LoopTerminal s₀ base bytes n len candidate result (r.drop drawBytes)
        (ptr + BitVec.ofNat 32 drawBytes) statusValue b :=
      ⟨prime, tape, cursor, remain, value, statusBound, answer, frame, regs⟩
    exact WP.mono (T.finish Sb capacity) fun _ h => Or.inl h
  cases passed : Spec.MillerRabin.round candidate w.1
  · have failed : result = some (false, r.drop drawBytes) := by
      simpa only [passed, Bool.false_eq_true, ite_false] using root
    apply finish 3 (by decide)
    · simpa only [passed, nextStatus, Bool.false_eq_true, ite_false] using status
    · rw [failed]; exact ⟨rfl, rfl⟩
  · by_cases go : i + 1 ≤ 16 ∨ uniform + w.2.toNat < checks
    · have lt : i + 1 < 17 ∨ uniform + w.2.toNat < checks := by omega
      have statusFour : b.mem.readW (off base primeStatus) 32 = 4#32 := by
        simpa only [passed, nextStatus, ite_true, ite_eq_left lt] using status
      have N : LoopReady s₀ base bytes n len candidate checks startLen result
          (r.drop drawBytes).length (r.drop drawBytes) (ptr + BitVec.ofNat 32 drawBytes)
          (i + 1) (uniform + w.2.toNat) b := by
        refine ⟨prime, tape, rfl, ?_, ?_, ?_, go, cursor, remain, ?_, ?_, ?_, frame, regs⟩
        · rw [List.length_drop]; have := R.left; omega
        · rw [List.length_drop]; have := R.left; have := R.budget; omega
        · have := R.count; have := Bool.toNat_le w.2; omega
        · simpa only [passed, ite_true] using index
        · simpa only [passed, ite_true] using uniforms
        · simpa only [passed, ite_true] using root
      refine WP.mono (prime_loop_end Sb capacity (by decide : 4 ≤ 4) statusFour)
        fun t ⟨_, zf, memory, Kt⟩ => Or.inr ⟨?_, (r.drop drawBytes).length, ?_, ?_⟩
      · simpa only [eval, decide_true] using zf
      · rw [List.length_drop]; have := R.length; omega
      · exact ⟨r.drop drawBytes, ptr + BitVec.ofNat 32 drawBytes, i + 1, uniform + w.2.toNat,
          N.of_keeps (Kt.mono (by decide)) memory⟩
    · have lt : ¬ (i + 1 < 17 ∨ uniform + w.2.toNat < checks) := by omega
      have after : result = candidateLoop candidate checks (i + 1) (uniform + w.2.toNat) (r.drop drawBytes) := by
        simpa only [passed, ite_true] using root
      have accepted := after.trans (candidate_loop_done (r.drop drawBytes) go)
      apply finish 1 (by decide)
      · simpa only [passed, nextStatus, ite_true, ite_eq_right lt] using status
      · rw [accepted]; exact ⟨rfl, rfl⟩

end VG.Proof.Dsa.X86.Generation
