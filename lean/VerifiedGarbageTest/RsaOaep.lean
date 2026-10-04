import Lean.Elab.Command
import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-!
# RSAES-OAEP specification tests

Known answers are parsed from the byte-for-byte RSA Laboratories PKCS #1
v2.1 RSAES-OAEP vectors (`vectors/pkcs1-v2.1-oaep/oaep-vect.txt`: ten keys
of 1024 to 1031, 1536 and 2048 bits, six messages each, SHA-1 and MGF1 with
SHA-1, the empty label); no vector values are embedded in this test. For
each message:

* `encrypt` with the vector's seed gives the vector's ciphertext;
* `decode` of `c^d mod n` (as `k` octets) gives the message back, and
  fails with another label, with the first octet set, and with the first
  or the last octet of the label's hash changed.
-/

namespace VG.Test.RsaOaep

open Lean Elab Command Spec Spec.RsaOaep Spec.Mgf1

/-- The octets of the hex pairs on `lines`. -/
def hexLine (s : String) : Except String (List Byte) :=
  (s.splitOn " ").filter (· ≠ "") |>.mapM fun w => do
    let digit (c : Char) : Except String Nat :=
      if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else throw s!"invalid hex digit {c}"
    match w.toList with
    | [a, b] => pure (BitVec.ofNat 8 (16 * (← digit a) + (← digit b)))
    | _ => throw s!"invalid hex octet {w}"

/-- The fields of the file in order: each `# Name:` line followed by lines of
hex octets. -/
def fields (text : String) : Except String (List (String × List Byte)) := do
  let mut out : Array (String × List Byte) := #[]
  let mut cur : Option (String × List Byte) := none
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "# " && line.endsWith ":" then
      if let some f := cur then out := out.push f
      cur := some ((line.drop 2).dropEnd 1 |>.toString, [])
    else if line.isEmpty || line.startsWith "#" || line.startsWith "=" then
      if let some f := cur then out := out.push f
      cur := none
    else if let some (name, bs) := cur then
      match hexLine line with
      | .ok more => cur := some (name, bs ++ more)
      | .error _ =>
        out := out.push (name, bs)
        cur := none
  if let some f := cur then out := out.push f
  return out.toList

structure Key where
  n : List Byte := []
  e : List Byte := []
  d : List Byte := []

/-- Checks one message. -/
def check (key : Key) (msg seed c : List Byte) : Except String Unit := do
  let k := key.n.length
  unless encrypt sha1 sha1 key.n key.e [] msg seed == some c do throw "encrypt"
  let n := Rsa.os2ip key.n
  let em := Rsa.i2osp (Rsa.powMod (Rsa.os2ip c) (Rsa.os2ip key.d) n) k
  unless decode sha1 sha1 [] em == some msg do throw "decode"
  unless decode sha1 sha1 [0] em == none do throw "decoded with another label"
  unless decode sha1 sha1 [] (1 :: em.drop 1) == none do throw "decoded with Y = 1"
  -- The label's hash is octets 0–19 of `DB`: change the first and the last.
  let some x := encode sha1 sha1 [] msg seed k | throw "encode"
  unless x == em do throw "encode is not c^d"
  let maskedDB := em.drop 21
  for i in [0, 19] do
    let lh := (sha1.hash []).set i ((sha1.hash [])[i]! ^^^ 1)
    let db := lh ++ ((xorBytes maskedDB (mgf1 sha1 seed (k - 21))).drop 20)
    let maskedDB' := xorBytes db (mgf1 sha1 seed (k - 21))
    let em' := 0 :: xorBytes seed (mgf1 sha1 maskedDB' 20) ++ maskedDB'
    unless decode sha1 sha1 [] em' == none do throw s!"decoded with lHash octet {i} changed"

#assert_standard_axioms Spec.RsaOaep.encrypt
#assert_standard_axioms Spec.RsaOaep.decode
#assert_no_compiler_overrides Spec.RsaOaep.encrypt Spec.RsaOaep.decode
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  let text ← IO.FS.readFile (root / "vectors" / "pkcs1-v2.1-oaep" / "oaep-vect.txt")
  let result : Except String Nat := do
    let fs ← fields text
    let mut key : Key := {}
    let mut msg : List Byte := []
    let mut seed : List Byte := []
    let mut count := 0
    let mut inPrivate := false
    for (name, bs) in fs do
      match name with
      | "Modulus" => key := { key with n := bs }
      | "Exponent" => if inPrivate then key := { key with d := bs } else key := { key with e := bs }
      | "Public exponent" => inPrivate := true
      | "Message" => msg := bs
      | "Seed" => seed := bs
      | "Encryption" =>
        match check key msg seed bs with
        | .ok () => count := count + 1
        | .error e => throw s!"vector {count} ({key.n.length} octets): {e}"
        inPrivate := false
      | _ => pure ()
    return count
  match result with
  | .ok 60 => pure ()
  | .ok n => throwError "oaep-vect.txt: {n} vectors"
  | .error e => throwError "oaep-vect.txt: {e}"

end VG.Test.RsaOaep
