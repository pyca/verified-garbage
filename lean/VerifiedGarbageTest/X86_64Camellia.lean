import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
import VerifiedGarbageTest.X86_64TripleDes
import VerifiedGarbageTest.Camellia

/-! Model-level smoke checks of the x86-64 Camellia ECB functions against
the specification, on keys and data derived from NTT's published vectors.
The functional proofs cover every input; this catches code-generation
mistakes during development. -/

namespace VG.Test.X86_64Camellia

open VG VG.X86_64 VG.Spec.Camellia
open VG.Test.X86_64TripleDes (evaluate)

def schedAt : Nat := 0x1000
def dataAt : Nat := 0x4000
def scratchAt : Nat := 0x8000

def initial (sched data : List Byte) (rounds n : Nat) : State where
  gpr r := if r = .rdi then BitVec.ofNat 64 schedAt else if r = .rsi then BitVec.ofNat 64 rounds
    else if r = .rdx then BitVec.ofNat 64 dataAt else if r = .rcx then BitVec.ofNat 64 n
    else if r = .r8 then BitVec.ofNat 64 scratchAt else if r = .rsp then 0xF000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if schedAt ≤ a.toNat ∧ a.toNat < schedAt + sched.length then
    sched.getD (a.toNat - schedAt) 0
    else if dataAt ≤ a.toNat ∧ a.toNat < dataAt + data.length then
    data.getD (a.toNat - dataAt) 0 else 0
  rd := [⟨BitVec.ofNat 64 schedAt, 272⟩]
  wr := [⟨BitVec.ofNat 64 dataAt, data.length⟩, ⟨BitVec.ofNat 64 scratchAt, 8 * Impl.Camellia.X86_64.slots⟩]

/-- Key expansion: the key at `0x1000`, the schedule written to `0x4000`. -/
def checkKey (key : List Byte) : Except String Unit := do
  let s : State :=
    { initial key [] 0 0 with
      gpr := fun r => if r = .rdi then BitVec.ofNat 64 schedAt else if r = .rsi then BitVec.ofNat 64 key.length
        else if r = .rdx then BitVec.ofNat 64 dataAt else if r = .rcx then BitVec.ofNat 64 scratchAt
        else if r = .rsp then 0xF000 else 0
      rd := [⟨BitVec.ofNat 64 schedAt, key.length⟩]
      wr := [⟨BitVec.ofNat 64 dataAt, 272⟩, ⟨BitVec.ofNat 64 scratchAt, 8 * Impl.Camellia.X86_64.slots⟩] }
  let some s := evaluate 100000 Impl.Camellia.X86_64.expandKey s
    | throw s!"{key.length}-byte key expansion faulted"
  let sk := expandKey key
  unless Spec.Camellia.bytesAt s.mem (BitVec.ofNat 64 dataAt) (scheduleBytes sk).length == scheduleBytes sk do
    throw s!"{key.length}-byte key expansion differs from the specification"

def checkCase (key : List Byte) (data : List Byte) : Except String Unit := do
  let sk := expandKey key
  let sched := scheduleBytes sk ++ List.replicate (272 - (scheduleBytes sk).length) 0
  let n := data.length / 16
  let blocks := (List.range n).map fun i => Vector.ofFn fun (j : Fin 16) => data.getD (16 * i + j) 0
  for (dir, d) in [(Impl.Camellia.X86_64.Dir.encrypt, Direction.encrypt), (.decrypt, .decrypt)] do
    let some s := evaluate 100000 (Impl.Camellia.X86_64.ecb dir) (initial sched data (rounds key.length) n)
      | throw s!"{key.length}-byte key, {n} blocks: faulted"
    unless blocksAt s.mem (BitVec.ofNat 64 dataAt) n == ecb sk d blocks do
      throw s!"{key.length}-byte key, {n} blocks, {repr d}: differs from the specification"
    unless (List.range 6).all (fun i => s.gpr (Impl.Camellia.X86_64.savedRegs.getD i (.rax, 0)).1 == 0) do
      throw "callee-saved registers not restored"

run_cmd do
  let file ← IO.FS.realPath (← Lean.getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root"
  let text ← IO.FS.readFile (root / "vectors" / "cryptography-camellia-128" / "camellia-128-ecb.txt")
  let bytes := (text.splitOn "\n").filterMap fun l => match l.splitOn " : " with
    | [_, h] => (Camellia.unhex h).toOption
    | _ => none
  let pool := bytes.flatten
  let result := do
    for klen in [16, 24, 32] do
      checkKey (pool.take klen)
      checkKey ((pool.drop 7).take klen)
    for (klen, n) in [(16, 1), (24, 9), (32, 0), (16, 8), (32, 17)] do
      checkCase (pool.take klen) ((pool.drop 100).take (16 * n))
  match result with
  | .ok () => pure ()
  | .error e => throwError "x86-64 Camellia: {e}"

end VG.Test.X86_64Camellia
