import VerifiedGarbage.Proof.Dsa.AArch64.RandomRestore
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignArgs
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEntry
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetry
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbageTest.DsaArmModel
import VerifiedGarbage.Spec.Dsa.RandomSign

/-! Execute the wrapper, including actual call/frame semantics, against a
published NIST signing vector and failure paths. This is test evidence only. -/
namespace VG.Test.DsaArmRandomSignModel
open VG VG.AArch64 DsaArmModel
open Impl.Dsa.AArch64.Random

/-- The baseline model runner extended with stack allocation and calls. -/
def evaluate : Nat → Prog isa → Machine → Except String Machine
  | 0, _, _ => .error "wrapper model exhausted fuel"
  | _ + 1, .block is, m => block is m
  | fuel + 1, .seq a b, m => (evaluate fuel a m).bind (evaluate fuel b)
  | fuel + 1, .ite c a b, m => do
    let some taken := isa.eval c m.state | throw "undefined condition"
    evaluate fuel (if taken then a else b) m
  | fuel + 1, .loop body c, m => do
    let next ← evaluate fuel body m
    let some again := isa.eval c next.state | throw "undefined loop condition"
    if again then evaluate fuel (.loop body c) next else pure next
  | fuel + 1, .call _ body, m => do
    let some entered := isa.call m.state | throw "call fault"
    let next ← evaluate fuel body ⟨flatten entered m.words, m.words, m.instructions + 1⟩
    let some returned := isa.ret entered next.state | throw "return fault"
    return { next with state := returned }
  | _ + 1, .icall _, _ => throw "unexpected indirect call"
  | fuel + 1, .frame push body pop, m => do
    -- This runner supports allocation frames, which do not store registers.
    match push with
    | .alloc _ => pure ()
    | _ => throw "unsupported frame kind"
    let some entered := isa.push push m.state | throw "frame allocation fault"
    let next ← evaluate fuel body { m with state := entered }
    let some returned := isa.pop pop entered next.state | throw "frame restoration fault"
    return { next with state := returned }

def putBytes (words : Words) (p : Nat) (bs : List Byte) : Words := Id.run do
  let mut result := words
  for i in [:bs.length] do
    let a := p + i
    let old := result[a / 8]?.getD 0
    let shift := 8 * (a % 8)
    let mask := (255 : BitVec 64) <<< shift
    result := result.insert (a / 8) ((old &&& ~~~mask) ||| (bs[i]!.setWidth 64 <<< shift))
  return result

def wordBytes (n : Nat) : List Byte := (List.range 8).map fun i => BitVec.ofNat 8 (n >>> (8 * i))

def check (v : Dsa.Vector) (rand : List Byte) : Except String Unit := do
  let pLen := 128
  let qLen := 20
  let entrySp := 0x20000
  let digest ← Dsa.digest v
  let key := Spec.Dsa.encodeBE pLen v.params.p ++ Spec.Dsa.encodeBE qLen v.params.q ++
    Spec.Dsa.encodeBE pLen v.params.g ++ Spec.Dsa.encodeBE pLen v.y ++ Spec.Dsa.encodeBE qLen v.x
  let args := [digest.length, 0x4000, rand.length, 0x10000, 16 * pLen + 64]
  let words := putBytes (putBytes (putBytes (putBytes (putBytes {} 0x1000 key) 0x2200 digest)
    0x3000 (List.replicate 40 0xa5)) 0x4000 rand) entrySp (args.flatMap wordBytes)
  let s : State := {
    gpr := fun r => match r with
      | .x0 => 0x3000 | .x1 => 40 | .x2 => 0x3100 | .x3 => 0x1000
      | .x4 => BitVec.ofNat 64 key.length | .x5 => BitVec.ofNat 64 pLen
      | .x6 => BitVec.ofNat 64 qLen | .x7 => 0x2200 | _ => BitVec.ofNat 64 (0x123400 + r.ctorIdx)
    sp := BitVec.ofNat 64 entrySp
    v := fun r => BitVec.ofNat 128 (0x567800 + r.ctorIdx)
    mem := memory words
    rd := [⟨0x1000, key.length⟩, ⟨0x2200, digest.length⟩, ⟨0x4000, rand.length⟩, ⟨BitVec.ofNat 64 entrySp, 40⟩]
    wr := [⟨0x3000, 40⟩, ⟨0x3100, 8⟩, ⟨0x10000, 8 * (16 * pLen + 64)⟩] }
  let key := Spec.Rsa.bytesAt s.mem 0x1000 (3 * pLen + 2 * qLen)
  let expected := Spec.Dsa.randomSignBytes pLen qLen key digest rand
  let program := Impl.Dsa.AArch64.RandomSign.code "vg_dsa_sign"
    (Impl.Dsa.AArch64.SignVerify.sign Impl.Bignum.AArch64.ProductDispatch.mm)
  let after ← evaluate 30000 program ⟨s, words, 0⟩
  unless after.state.gpr .x0 == BitVec.ofNat 64 expected.status do throw "wrapper status"
  unless Spec.Rsa.bytesAt after.state.mem 0x3000 40 ==
      expected.signature.getD (List.replicate 40 0) do throw "wrapper signature"
  unless after.state.mem.readW 0x3100 64 == BitVec.ofNat 64 expected.used do throw "wrapper consumption"
  for r in preserved do
    unless after.state.gpr r == s.gpr r do throw "wrapper ABI"
  unless after.state.sp == s.sp do throw "wrapper stack pointer"
  for r in preservedV do
    unless (after.state.v r).extractLsb' 0 64 == (s.v r).extractLsb' 0 64 do throw "wrapper vector ABI"
  unless Spec.Rsa.bytesAt after.state.mem (BitVec.ofNat 64 (entrySp - frameBytes + oNonce)) 32 ==
      List.replicate 32 0 do throw "nonce not wiped"
end VG.Test.DsaArmRandomSignModel

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  let source ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "SigGen.txt")
  let vectors ← match VG.Test.Dsa.parse source true with
    | .ok vs => pure vs
    | .error e => throwError e
  let some v := vectors.find? (fun v => VG.Spec.Dsa.bitLength v.params.p == 1024 &&
      VG.Spec.Dsa.bitLength v.params.q == 160) | throwError "missing NIST vector"
  let nonce := VG.Spec.Dsa.encodeBE 20 v.k
  for rand in [nonce, List.replicate 20 0 ++ nonce, [], List.replicate 19 0,
      List.replicate (128 * 20) 0] do
    match VG.Test.DsaArmRandomSignModel.check v rand with
    | .ok () => pure ()
    | .error e => throwError e
  for q in [0, 1] do
    match VG.Test.DsaArmRandomSignModel.check { v with params := { v.params with q := q } } nonce with
    | .ok () => pure ()
    | .error e => throwError e
  let invalid := { v with params := { v.params with p := 0 } }
  for rand in [nonce, (List.replicate 9 nonce).flatten] do
    match VG.Test.DsaArmRandomSignModel.check invalid rand with
    | .ok () => pure ()
    | .error e => throwError e

#assert_standard_axioms VG.Proof.Dsa.AArch64.random_signCallArgs_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_signOutgoing_words
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_signOutgoing_frame
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_entry_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_publish_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_callFinish_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_signer_call
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_zeroOut_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_copySlots_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_slots_outside

#assert_standard_axioms VG.Proof.Dsa.AArch64.randomSignABI_of
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_frame_ok
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_incoming_read
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_finish_ok
#assert_standard_axioms VG.Proof.Dsa.randomSignLoop_sample_none
#assert_standard_axioms VG.Proof.Dsa.randomSignLoop_step_success
#assert_standard_axioms VG.Proof.Dsa.randomSignLoop_retry
#assert_standard_axioms VG.Proof.Dsa.randomSignLoop_status_le

#assert_standard_axioms VG.Proof.Dsa.AArch64.random_call_pre
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_call_covers
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_signer_outcome
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_call_frameBytes
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_call_inputBytes

#assert_standard_axioms VG.Proof.Dsa.AArch64.RandomReady.restore
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_entry_values
