import VerifiedGarbage.Proof.Dsa.X86.SharedCorrect
import VerifiedGarbage.Proof.Dsa.X86.InputBuffer
import VerifiedGarbageTest.DsaX86SignVerify
import VerifiedGarbage.Impl.Dsa.X86.Entry
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.CallerSlice
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.X86.WidthDispatch

/-! ISA-model checks of cdecl entry and public-shape rejection for every
supported external width. Zero-filled invalid domains exercise rejection
without reading uninitialized scalar scratch. -/

#assert_standard_axioms VG.Proof.Dsa.X86.widthDispatch_ok
#assert_standard_axioms VG.Proof.Dsa.X86.signFailure_ok
#assert_standard_axioms VG.Proof.Dsa.X86.verifyFailure_ok
#assert_standard_axioms VG.Proof.Dsa.X86.signingCorrect
#assert_standard_axioms VG.Proof.Dsa.X86.verifyingCorrect
#assert_standard_axioms VG.Proof.Dsa.X86.inputBuffer
#assert_standard_axioms VG.Proof.Dsa.X86.inputBytes_keep
#assert_standard_axioms VG.Proof.Dsa.X86.installArguments_ok
#assert_standard_axioms VG.Proof.Dsa.X86.shapeModuli_ok
#assert_standard_axioms VG.Proof.Dsa.X86.CallerBuffer.slice
#assert_standard_axioms VG.Proof.Dsa.X86.entrySave_ok
#assert_standard_axioms VG.Proof.Dsa.X86.entryRestore_ok

namespace VG.Test.DsaX86Entry
open VG VG.X86 VG.Test.DsaX86Mont VG.Test.DsaX86Core VG.Impl.Dsa.X86

def check (signing : Bool) (pLen qLen : Nat) : Except String Unit := do
  let base := 0x10000
  let key := 0x20000
  let output := 0x30000
  let stack := 0x40000
  let nonce := 0x50000
  let digest := 0x60000
  let keyLen := 3 * pLen + (if signing then 2 else 1) * qLen
  let args := if signing then [output, 2 * qLen, key, keyLen, pLen, nonce, qLen, digest, 0, base, 16 * pLen]
    else [key, keyLen, pLen, qLen, output, 2 * qLen, digest, 0, base, 16 * pLen]
  let ws := args.zipIdx.foldl (fun w (value, i) => put w (stack + 4 + 4 * i) 1 value) ({} : Words)
  let ws := putBE ws output (2 * qLen) (2 ^ (16 * qLen) - 1)
  let original : Reg → BitVec 32 := fun reg => match reg with
    | .esp => BitVec.ofNat 32 stack
    | .ebx => 0x12345678
    | .ebp => 0x87654321
    | .esi => 0xabcdef01
    | .edi => 0x10fedcba
    | _ => 0
  let st : State := {
    gpr := original, cf := none, zf := none, sf := none, of := none,
    mem := memory ws, rd := [⟨BitVec.ofNat 64 key, keyLen⟩, ⟨BitVec.ofNat 64 stack, 48⟩],
    wr := [⟨BitVec.ofNat 64 base, 128 * pLen⟩, ⟨BitVec.ofNat 64 output, 2 * qLen⟩] }
  let done ← evaluate fuel (Entry.operation signing) ⟨st, ws⟩
  unless done.state.gpr .eax == 0 do throw "invalid domain did not return failure"
  for reg in [.ebx, .ebp, .esi, .edi, .esp] do
    unless done.state.gpr reg == original reg do throw "cdecl register was not restored"
  if signing then
    unless getBE done.words output (2 * qLen) == 0 do throw "early signing failure did not zero output"
  else
    unless getBE done.words output (2 * qLen) == 2 ^ (16 * qLen) - 1 do throw "verification changed the signature"

def checks : Except String Unit := do
  for (pLen, qLen) in [(128, 20), (256, 20), (256, 28), (256, 32), (384, 32)] do
    check true pLen qLen
    check false pLen qLen

end VG.Test.DsaX86Entry

run_cmd
  match VG.Test.DsaX86Entry.checks with
  | .ok () => pure ()
  | .error msg => Lean.throwError msg
