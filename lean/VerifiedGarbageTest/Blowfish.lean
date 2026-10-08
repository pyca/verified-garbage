import Lean.Elab.Command
import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.TCB.Axioms

/-!
# Blowfish specification tests

Reads the unmodified files Schneier publishes under `vectors/`:

* `schneier-blowfish-constants/constants.txt`, the P-array and S-boxes,
  which must be `initP` and `initS`; and both must be the hexadecimal
  digits of π after the initial 3, computed here from Machin's formula
  π = 16 arctan(1/5) − 4 arctan(1/239);
* `schneier-blowfish-vectors/vectors-2.txt`, Eric Young's test vectors: all
  34 ECB records in both directions, all 24 set-key records (keys of 1–24
  bytes) in both directions, and the CBC record, whose ciphertext gives
  four ECB blocks under a 16-byte key (the block encrypted is the plaintext
  block XORed with the previous ciphertext block, or the IV). That ECB
  record also exercises every stream split, byte-at-a-time updates, empty
  updates and incomplete final blocks.

Synthetic inputs test key-length rejection; they are not known-answer
vectors.
-/

namespace VG.Test.Blowfish

open Lean Elab Command Spec.Blowfish

def unhex (s : String) : Except String (List Byte) := do
  let cs := s.toLower.toList.filter (!·.isWhitespace)
  unless cs.length % 2 == 0 do throw "odd number of hex digits"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error s!"not a hex digit: {c}"
  (List.range (cs.length / 2)).mapM fun i => do
    return BitVec.ofNat 8 (16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!))

def block (bs : List Byte) : Except String Block := do
  unless bs.length == 8 do throw s!"not an 8-byte block: {bs.length}"
  return Vector.ofFn fun i => bs.getD i 0

def lines (text : String) : List String :=
  (text.replace "\r" "").splitOn "\n" |>.map (·.trimAscii.toString)

def words (line : String) : List String :=
  (line.splitOn " ").filter (!·.isEmpty)

/-! ## The constants -/

/-- The hexadecimal digits of π after the initial 3, as 32-bit words. -/
def piWords (n : Nat) : List Word :=
  let bits := 32 * n + 64
  let one : Int := 2 ^ bits
  -- arctan(1/x) · 2^bits, to within the number of terms
  let arctanInv (x : Int) (terms : Nat) : Int := Id.run do
    let mut power := one / x
    let mut sum : Int := 0
    for k in List.range terms do
      let term := power / (2 * k + 1)
      sum := if k % 2 == 0 then sum + term else sum - term
      power := power / (x * x)
    return sum
  let pi := 16 * arctanInv 5 (bits / 4 + 10) - 4 * arctanInv 239 (bits / 15 + 10)
  let fraction := (pi.toNat >>> 64) % 2 ^ (32 * n)
  (List.range n).map fun i => BitVec.ofNat 32 (fraction >>> (32 * (n - 1 - i)))

/-- The arrays of `constants.txt`, in the order they appear there:
`unsigned long <name>[] = { 0x…L, … };`. -/
def cArrays (text : String) : Except String (List (String × List Word)) := do
  let mut out : List (String × List Word) := []
  for chunk in (text.splitOn "unsigned long ").drop 1 do
    let name := (chunk.splitOn "[").headD ""
    let some body := ((chunk.splitOn "{").getD 1 "").splitOn "}" |>.head?
      | throw s!"no body for {name}"
    let mut values : List Word := []
    for item in body.splitOn "," do
      let item := item.trimAscii.toString
      unless item.startsWith "0x" && item.endsWith "L" && item.length == 11 do
        throw s!"{name}: not a constant: {item}"
      let bs ← unhex ((item.drop 2).take 8).toString
      values := values ++ [bs.foldl (fun (w : Word) (b : Byte) => (w <<< 8) ||| b.zeroExtend 32) 0]
    out := out ++ [(name, values)]
  return out

def checkConstants (text : String) : Except String Unit := do
  let arrays ← cArrays text
  let names := arrays.map (·.1)
  unless names == ["sbox0", "sbox1", "sbox2", "sbox3", "parray"] do
    throw s!"unexpected arrays {names}"
  let get (name : String) := (arrays.lookup name).getD []
  unless get "parray" == initP.toList do throw "initP differs from constants.txt"
  for j in List.range 4 do
    unless get s!"sbox{j}" == (initS.getD j (Vector.replicate 256 0)).toList do
      throw s!"initS[{j}] differs from constants.txt"
  unless piWords 1042 == initial.toList do throw "the initial schedule is not the digits of π"

/-! ## Known answers -/

def check (key : List Byte) (pt ct : Block) (what : String) : Except String Unit := do
  let k := expandKey key
  unless encryptBlock k pt == ct do throw s!"{what}: encryption failed"
  unless decryptBlock k ct == pt do throw s!"{what}: decryption failed"

def finalized (ctx : Spec.Blowfish.Context) : Bool :=
  match finalize ctx with | .ok bs => bs.isEmpty | .error _ => false

def incomplete (ctx : Spec.Blowfish.Context) : Bool :=
  match finalize ctx with | .error .incompleteBlock => true | _ => false

def context (key : List Byte) (direction : Direction) : Except String Spec.Blowfish.Context :=
  (init key direction).mapError (fun e => s!"initialization: {repr e}")

def checkStream (ctx : Spec.Blowfish.Context) (input expected : List Byte) :
    Except String Unit := do
  let empty := update ctx []
  unless empty.2.isEmpty && empty.1.pending.isEmpty && finalized empty.1 do
    throw "empty initial update changed the context"
  unless (update ctx input).2 == expected && finalized (update ctx input).1 do
    throw "one-shot update failed"
  for split in List.range (input.length + 1) do
    let (first, a) := update ctx (input.take split)
    unless a.length == 8 * (split / 8) && first.pending.length == split % 8 do
      throw s!"wrong buffering at split {split}"
    if split % 8 != 0 then
      unless incomplete first do throw "accepted a partial block"
    let (same, noOutput) := update first []
    unless noOutput.isEmpty && same.pending == first.pending do
      throw "empty intermediate update changed the context"
    let (last, b) := update same (input.drop split)
    unless a ++ b == expected && finalized last do throw s!"wrong output at split {split}"
  let mut ctx := ctx
  let mut output := []
  for byte in input do
    let (next, out) := update ctx [byte]
    ctx := next
    output := output ++ out
  unless output == expected && finalized ctx do throw "byte-at-a-time streaming failed"

/-- `field = value` after a prefix such as `key[16]   = `. -/
def valueOf (ls : List String) (pre : String) : Except String String :=
  match ls.find? (·.startsWith pre) with
  | some l => pure ((l.splitOn "=").getD 1 "").trimAscii.toString
  | none => throw s!"missing {pre}"

def xorBytes (a b : List Byte) : List Byte := (a.zip b).map fun (x, y) => x ^^^ y

/-- Returns the numbers of ECB and set-key records. -/
def checkVectors (text : String) : Except String (Nat × Nat) := do
  let ls := lines text
  let ecbStart := (ls.findIdx? (·.startsWith "key bytes")).getD ls.length
  let setKeyStart := (ls.findIdx? (· == "set_key test data")).getD ls.length
  let mut ecbCount := 0
  for line in (ls.drop (ecbStart + 1)).take (setKeyStart - ecbStart - 1) do
    let [k, p, c] := words line | throw s!"bad ECB line: {line}"
    check (← unhex k) (← block (← unhex p)) (← block (← unhex c)) s!"ECB record {ecbCount}"
    ecbCount := ecbCount + 1
  let pt ← block (← unhex (← valueOf ls "data[8]="))
  let mut setKeyCount := 0
  for line in ls.drop setKeyStart do
    unless line.startsWith "c=" do continue
    let c ← block (← unhex (((line.drop 2).take 16).toString))
    let key ← unhex ((line.splitOn "]=").getD 1 "")
    unless key.length == setKeyCount + 1 do throw s!"bad set-key line: {line}"
    check key pt c s!"set-key record {setKeyCount}"
    setKeyCount := setKeyCount + 1
  -- CBC: Eric Young's `des_cbc_encrypt` pads the 29 bytes with zeros.
  let key ← unhex (← valueOf ls "key[16]")
  let iv ← unhex (← valueOf ls "iv[8]")
  -- The second `data[29]` line is the hex form of the first.
  let some dataLine := (ls.filter (·.startsWith "data[29]")).getLast? | throw "no CBC data"
  let data ← unhex ((dataLine.splitOn "=").getD 1 "")
  let cbcLine := (ls.findIdx? (· == "cbc cipher text")).getD ls.length
  let cipher ← unhex (((ls.getD (cbcLine + 1) "").splitOn "=").getD 1 "")
  unless key.length == 16 && iv.length == 8 && data.length == 29 && cipher.length == 32 do
    throw "bad CBC record"
  let padded := data ++ List.replicate 3 0
  let chained := (List.range 4).flatMap fun i =>
    xorBytes ((padded.drop (8 * i)).take 8) (if i == 0 then iv else (cipher.drop (8 * (i - 1))).take 8)
  checkStream (← context key .encrypt) chained cipher
  checkStream (← context key .decrypt) cipher chained
  return (ecbCount, setKeyCount)

def checkLimits : Except String Unit := do
  for len in List.range 61 do
    let key := (List.range len).map (fun i => BitVec.ofNat 8 (17 * i + 3))
    for direction in [Direction.encrypt, .decrypt] do
      match init key direction with
      | .error .invalidKeyLength =>
        if 4 ≤ len && len ≤ 56 then throw "rejected a valid key length"
      | .error _ => throw "wrong key-length error"
      | .ok ctx =>
        unless 4 ≤ len && len ≤ 56 do throw "accepted an invalid key length"
        unless ctx.schedule == expandKey key && ctx.direction == direction do
          throw "wrong initial context"
        for n in List.range 8 do
          let (next, out) := update ctx (List.replicate n 0)
          unless out.isEmpty && next.pending.length == n do throw "wrong partial-block buffering"
          unless (if n == 0 then finalized next else incomplete next) do
            throw "wrong partial-block finalization"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let constants ← IO.FS.readFile (root / "vectors" / "schneier-blowfish-constants" / "constants.txt")
  match checkConstants constants with
  | .ok () => pure ()
  | .error e => throwError "Blowfish constants: {e}"
  let vectors ← IO.FS.readFile (root / "vectors" / "schneier-blowfish-vectors" / "vectors-2.txt")
  match checkVectors vectors with
  | .error e => throwError "Blowfish vectors: {e}"
  | .ok counts => unless counts == (34, 24) do
      throwError "Blowfish vectors: expected (34, 24) records, got {counts}"
  match checkLimits with
  | .ok () => pure ()
  | .error e => throwError "Blowfish: {e}"

#assert_standard_axioms VG.Spec.Blowfish.expandKeyContract
#assert_standard_axioms VG.Spec.Blowfish.ecbEncryptContract
#assert_standard_axioms VG.Spec.Blowfish.ecbDecryptContract

end VG.Test.Blowfish
