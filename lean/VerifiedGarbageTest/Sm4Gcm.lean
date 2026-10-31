module

import Lean.Elab.Command
meta import Lean.Elab.Command
import VerifiedGarbage.Spec.Sm4.Gcm
meta import VerifiedGarbage.Spec.Sm4.Gcm
import VerifiedGarbage.Spec.Sm4.Gcm.Contract
meta import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-!
# SM4-GCM specification tests

Read the byte-for-byte RFC 8998 file under `vectors/rfc8998/` (see its
`vectors/sources/` manifest) and check its one SM4-GCM example
(Appendix A.1) against `VG.Spec.Sm4.gcmEncrypt` and `gcmDecrypt`: the
ciphertext and tag, the decryption of the ciphertext, and the rejection of
the example with a byte of its tag, its ciphertext or its additional data
changed. The contract's memory layouts are checked on the example's key
schedule and blocks.
-/

namespace VG.Test.Sm4Gcm

open Lean Elab Command Spec

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

def isHex (s : String) : Bool :=
  !s.isEmpty && s.all fun c => ('0' ≤ c ∧ c ≤ '9') ∨ ('A' ≤ c ∧ c ≤ 'F') ∨ ('a' ≤ c ∧ c ≤ 'f')

/-- The text between `start` and the next `stop` after it. -/
def between (text start stop : String) : Except String String := do
  let some after := (text.splitOn start)[1]? | throw s!"missing {start}"
  return (after.splitOn stop).headD ""

/-- The hex value of the field `label` of an example: the rest of its line
and of each following line that holds nothing but hex digits. -/
def field (ex label : String) : Except String (List Byte) := do
  let some after := (ex.splitOn (label ++ ":"))[1]? | throw s!"missing {label}"
  let first :: rest := after.splitOn "\n" | throw s!"missing {label}"
  let more := rest.takeWhile fun l => isHex l.trimAscii.toString
  unhex (String.join ((first :: more).map (·.trimAscii.toString)))

/-- The byte at `i` of `xs` flipped in its lowest bit. -/
def flip (xs : List Byte) (i : Nat) : List Byte := xs.modify i (· ^^^ 1)

def checkExample (ex : String) : Except String Unit := do
  let iv ← field ex "Initialization Vector"
  let key ← field ex "Key"
  let pt ← field ex "Plaintext"
  let aad ← field ex "Associated Data"
  let ct ← field ex "CipherText"
  let tag ← field ex "Authentication Tag"
  unless iv.length == 12 && key.length == 16 && pt.length == 64 && aad.length == 20 &&
      ct.length == 64 && tag.length == 16 do
    throw "unexpected lengths"
  unless Sm4.gcmEncrypt key 16 iv pt aad == (ct, tag) do throw "encryption differs"
  unless Sm4.gcmDecrypt key 16 iv ct aad tag == some pt do throw "decryption differs"
  -- A truncated tag is the first bytes of the full one.
  unless Sm4.gcmEncrypt key 12 iv pt aad == (ct, tag.take 12) do throw "truncated tag differs"
  unless Sm4.gcmDecrypt key 12 iv ct aad (tag.take 12) == some pt do
    throw "truncated decryption differs"
  -- Any change is rejected.
  unless Sm4.gcmDecrypt key 16 iv ct aad (flip tag 15) == none do throw "accepted a changed tag"
  unless Sm4.gcmDecrypt key 16 iv (flip ct 0) aad tag == none do
    throw "accepted a changed ciphertext"
  unless Sm4.gcmDecrypt key 16 iv ct (flip aad 19) tag == none do
    throw "accepted changed additional data"
  -- The contract's layouts: the schedule `vg_sm4_expand_key` writes, and
  -- the blocks of GCM, the first byte the most significant.
  let k := Sm4.expandKey (Vector.ofFn fun i => key.getD i.val 0)
  let scheduleMem : Mem := fun p => ((k.getD (p.toNat / 4) 0) >>> (8 * (p.toNat % 4))).setWidth 8
  unless Sm4.scheduleAt scheduleMem 0 == k do throw "scheduleAt differs"
  let dataMem : Mem := fun p => pt.getD p.toNat 0
  unless Gcm.blocksAt dataMem 0 4 == Gcm.blocks pt do throw "blocksAt differs"
  -- The text is `ctr32` from `inc₃₂(J₀)` (§7.1 step 3), and `H` the
  -- encryption of the zero block (step 1).
  let ciph := Sm4.gcmCipher k
  let j := Gcm.j0 (ciph 0) iv
  unless Gcm.ctr32 ciph (Gcm.inc32 j) (Gcm.blocks pt) == Gcm.blocks ct do throw "ctr32 differs"
  unless Gcm.ctr32 ciph 0 [0] == [ciph 0] do throw "H differs"
  -- The key context `vg_sm4_gcm_init` writes: the schedule, then `H` in its
  -- last 16 bytes, from which GCM-AE and GCM-AD give the example.
  let hb := Gcm.toBytes (ciph 0)
  let ctxMem : Mem := fun p =>
    if p.toNat < 128 then scheduleMem p else if 240 ≤ p.toNat then hb.getD (p.toNat - 240) 0 else 0
  unless Sm4.scheduleAt ctxMem 0 == k && Gcm.ctxH ctxMem 0 == Sm4.gcmCipherOfKey key 0 do
    throw "key context differs"
  unless Gcm.encryptWith (Sm4.Gcm.ctxCiph ctxMem 0) (Gcm.ctxH ctxMem 0) 16 iv pt aad == (ct, tag) do
    throw "encryption with the key context differs"
  unless Gcm.openResult (Sm4.Gcm.ctxCiph ctxMem 0) (Gcm.ctxH ctxMem 0) 16 iv ct aad tag == some pt do
    throw "decryption with the key context differs"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc8998" / "rfc8998.txt")
  let result := do
    checkExample (← between text "\nA.1.  SM4-GCM Test Vectors\n" "\nA.2.  SM4-CCM Test Vectors\n")
  match result with
  | .ok () => pure ()
  | .error e => throwError "SM4-GCM: {e}"

#assert_standard_axioms VG.Spec.Sm4.ctr32Contract
#assert_standard_axioms VG.Spec.Sm4.gcmEncrypt
#assert_standard_axioms VG.Spec.Sm4.gcmDecrypt
#assert_standard_axioms VG.Spec.Sm4.Gcm.initContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.sealContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.openContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.streamEncryptContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.streamDecryptContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.streamFinishContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.streamVerifyContract
#assert_standard_axioms VG.Spec.Sm4.Gcm.encryptWith_ctx
#assert_standard_axioms VG.Spec.Sm4.Gcm.decryptWith_ctx

end VG.Test.Sm4Gcm
