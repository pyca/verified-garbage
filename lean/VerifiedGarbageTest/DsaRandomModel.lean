import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareState
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomTermination
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMask
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.RandomStructure
import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
import VerifiedGarbageTest.DsaModel
import VerifiedGarbage.Proof.Dsa.Random

/-! Differential execution of the scalar sampler in the x86-64 ISA model.
These are sampler boundary inputs, not cryptographic known-answer vectors.
This does not replace the whole-program verification required for emission. -/
namespace VG.Test.DsaRandomModel
open VG VG.X86_64
open DsaModel
open Impl.Dsa.X86_64.Random

def check (q qLen : Nat) (rand : List Byte) : Except String Unit := do
  let qb := Spec.Dsa.encodeBE qLen q
  let regions := [(0x2000, qb), (0x3000, rand)]
  let mem : Mem := fun a =>
    match regions.find? (fun (p, bs) => p ≤ a.toNat && a.toNat < p + bs.length) with
    | some (p, bs) => bs.getD (a.toNat - p) 0
    | none => 0
  let mut words : Words := {}
  for (p, bs) in regions do
    for i in [: (bs.length + 7) / 8] do
      words := words.insert ((p / 8) + i) (mem.readW (BitVec.ofNat 64 (p + 8 * i)) 64)
  for (slot, value) in [(oQ, 0x2000), (oQLen, qLen), (oRand, 0x3000),
      (oRandLen, rand.length), (oUsed, 0)] do
    words := words.insert ((0x1000 + slot) / 8) (BitVec.ofNat 64 value)
  let s : State := {
    gpr := fun r => if r = .rsp then 0x1000 else BitVec.ofNat 64 (0x5500 + r.ctorIdx)
    cf := none, zf := none, sf := none, of := none, mem := memory words
    rd := [⟨0x2000, qLen⟩, ⟨0x3000, rand.length⟩]
    wr := [⟨0x1000, frameBytes⟩] }
  let prog : Prog isa := .seq prepare (.seq (.block [.alu .cmp .rax (.imm 0)])
    (.ite .ne sample (.block [])))
  let after ← evaluate 10000 prog ⟨s, words, 0⟩
  let expected := Spec.Dsa.Random.sample q 128 rand
  let status := if expected.scalar.isSome then 1 else
    if expected.trace.getLast? == some 2 then 2 else 0
  unless after.state.gpr .rax == BitVec.ofNat 64 status do
    throw s!"status: q={q}, len={rand.length}"
  unless after.state.mem.readW (BitVec.ofNat 64 (0x1000 + oUsed)) 64 ==
      BitVec.ofNat 64 expected.used do throw s!"consumption: q={q}, len={rand.length}"
  if let some k := expected.scalar then
    unless Spec.Rsa.bytesAt after.state.mem (BitVec.ofNat 64 (0x1000 + oNonce)) qLen ==
        Spec.Dsa.encodeBE qLen k do throw s!"scalar: q={q}, len={rand.length}"
  for reg in [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp] do
    unless after.state.gpr reg == s.gpr reg do throw "callee-saved register changed"

def checks : Except String Nat := do
  let mut count := 0
  for q in [0, 1, 2, 3, 13, 127, 128, 129, 255, 256, 257, 65535,
      2 ^ 159 + 7, 2 ^ 223 + 9, 2 ^ 255 + 19] do
    let width := Spec.Dsa.Random.drawBytes q
    for qLen in [20, 28, 32] do
      if width ≤ qLen then
        let accepted := Spec.Dsa.encodeBE width (q - 1)
        for rand in [[], [0], accepted, Spec.Dsa.encodeBE width q ++ accepted,
            List.replicate width 0 ++ accepted,
            List.replicate (128 * width) 0 ++ accepted,
            List.replicate (127 * width) 0 ++ accepted,
            List.replicate width 255 ++ accepted,
            accepted ++ List.replicate width 255] do
          check q qLen rand
          count := count + 1
  -- Exhaustive one-byte candidates for several non-power-of-two domains.
  for q in [3, 13, 129, 255] do
    for b in [:256] do
      check q 20 [BitVec.ofNat 8 b]
      count := count + 1
  return count
end VG.Test.DsaRandomModel

run_cmd
  match VG.Test.DsaRandomModel.checks with
  | .ok _ => pure ()
  | .error e => Lean.throwError e

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_spSafe
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sample_spSafe
#assert_standard_axioms VG.Proof.Dsa.X86_64.randomSign_spSafe
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_baseline
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sample_baseline
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_byte_borrow
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_borrow_ok
#assert_no_compiler_overrides VG.Impl.Dsa.X86_64.RandomSign.code
#assert_spec_origin

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_significant_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_mask_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.randomMaskValue_eq
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copyLoop_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_rangeByte_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_rangeLoop_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_rangeFinish_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_rangeInit_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_inRange_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copyLoop_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_rangeBody_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_mask_ct
#assert_standard_axioms VG.Proof.Dsa.randomBorrow_eq
#assert_standard_axioms VG.Proof.Dsa.randomOr_zero
#assert_standard_axioms VG.Proof.Dsa.random_drawBytes_scan
#assert_standard_axioms VG.Proof.Dsa.random_mask_byte
#assert_standard_axioms VG.Proof.Dsa.random_mask_decode

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_clear_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_clear_outside
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_clear_byte
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copyInit_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copy_of_init
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copy_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepareFinish_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_valid
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_width
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_pointer
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_mask
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_outside
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_zero
#assert_standard_axioms VG.Proof.Dsa.random_candidate_mask
#assert_standard_axioms VG.Proof.Dsa.random_valid_scan
#assert_standard_axioms VG.Proof.Dsa.random_valid_scan_ge

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_drawHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_status_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_draw_short_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_used_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_drawFinish_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sampleLoop_rule

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copy_candidate_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_src_drop
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_src_take
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_nonce_addr
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_nonce_offset
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copy_outside
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copy_draw_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_check_candidate_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_draw_full_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_drawFinish_outside
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_drawFinish_status
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_drawFinish_draws
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_drawFinish_word
#assert_standard_axioms VG.Proof.Dsa.X86_64.RandomReady.congr
#assert_standard_axioms VG.Proof.Dsa.X86_64.RandomReady.after_draw
#assert_standard_axioms VG.Proof.Dsa.X86_64.RandomReady.after_status
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_draw_progress
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sampleLoop_terminates
#assert_standard_axioms VG.Proof.Dsa.random_significant_drop
#assert_standard_axioms VG.Proof.Dsa.random_significant_drop_length

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sampleLoop_correct
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sample_correct
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_sample_encoded
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_nonce_encoding
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_prepare_ready
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_copy_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_inRange_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.random_draw_full_result
#assert_standard_axioms VG.Proof.Dsa.Random.sample_trace_nonempty
#assert_standard_axioms VG.Proof.Dsa.Random.sampleStatus_reject
#assert_standard_axioms VG.Proof.Dsa.Random.sample_short
#assert_standard_axioms VG.Proof.Dsa.Random.sample_accept
#assert_standard_axioms VG.Proof.Dsa.Random.sample_reject

#assert_standard_axioms VG.Proof.Dsa.X86_64.random_statusLoop_rule
