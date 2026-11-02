module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public import VerifiedGarbage.Spec.Dsa.SignVerify
public meta import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Spec.Sha512
public meta import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.Axioms
public meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.TCB.Audit
public meta import VerifiedGarbage.TCB.Audit
public import VerifiedGarbageTest.Memo
public meta import VerifiedGarbageTest.Memo

/-! # DSA specification regression tests
Known answers are parsed from the byte-for-byte NIST CAVP files, including
published nonces for signing. No vector values are embedded in this test.
Primality is not recomputed: CAVP supplies the validated domain parameters.
-/

@[expose] public section
namespace VG.Test.Dsa
open Lean Elab Command Spec.Dsa

def hex (s : String) : Except String (List Byte) := do
  let cs := s.toList
  if cs.length % 2 != 0 then throw "odd hex length"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw "invalid hex digit"
  let rec loop : List Char → Except String (List Byte)
    | [] => pure []
    | h :: l :: rest => do return BitVec.ofNat 8 (16 * (← digit h) + (← digit l)) :: (← loop rest)
    | _ => throw "odd hex length"
  loop cs

structure Vector where
  params : Params := ⟨0, 0, 0⟩
  hash : String := ""
  msg : List Byte := []
  x : Nat := 0
  y : Nat := 0
  k : Nat := 0
  sig : Signature := ⟨0, 0⟩
  pass : Bool := true

def parse (text : String) (signing : Bool) : Except String (List Vector) := do
  let mut v : Vector := {}
  let mut vs := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "[mod = " then
      let some h := (line.splitOn ", ").getLast? | throw "missing hash header"
      v := { v with hash := h.replace "]" "" }
    else
      match line.splitOn " = " with
      | [field, value] =>
        if field == "Result" then
          v := { v with pass := value.startsWith "P" }
          vs := v :: vs
        else
          let bytes ← hex value
          let n := decodeBE bytes
          match field with
          | "P" => v := { v with params := { v.params with p := n } }
          | "Q" => v := { v with params := { v.params with q := n } }
          | "G" => v := { v with params := { v.params with g := n } }
          | "Msg" => v := { v with msg := bytes }
          | "X" => v := { v with x := n }
          | "Y" => v := { v with y := n }
          | "K" => v := { v with k := n }
          | "R" => v := { v with sig := { v.sig with r := n } }
          | "S" =>
            v := { v with sig := { v.sig with s := n } }
            if signing then vs := v :: vs
          | _ => throw s!"unknown field {field}"
      | _ => pure ()
  return vs.reverse

def digest (v : Vector) : Except String (List Byte) :=
  match v.hash with
  | "SHA-1" => pure (Spec.Sha1.hash v.msg)
  | "SHA-224" => pure (Spec.Sha256.sha224 v.msg)
  | "SHA-256" => pure (Spec.Sha256.hash v.msg)
  | "SHA-384" => pure (Spec.Sha512.sha384 v.msg)
  | "SHA-512" => pure (Spec.Sha512.sha512 v.msg)
  | h => throw s!"unknown hash {h}"

/-! The checks of a signing vector compute the same exponentiations modulo
`p` again (`g^q`, `y^q` and `g^x` validating the domain and the key in
every function, `g^k` signing, `g^u₁` and `y^u₂` verifying): they evaluate
copies of the functions with `pm` for those exponentiations
(`signBytes_eq`, …), and `pm` looks up the ones computed once
(`Test.memo_tableOf`). -/

section
variable (pm : Nat × Nat × Nat → Nat)

/-- `parametersValid`. -/
def parametersValidP (a : Params) : Prop :=
  supportedSizes (bitLength a.p) (bitLength a.q) ∧ a.p % 2 = 1 ∧ a.q % 2 = 1 ∧
    a.q < a.p ∧ (a.p - 1) % a.q = 0 ∧ 1 < a.g ∧ a.g < a.p ∧ pm (a.g, a.q, a.p) = 1

instance (a : Params) : Decidable (parametersValidP pm a) := by
  unfold parametersValidP
  infer_instance

/-- `keyValid`. -/
def keyValidP (key : Key) : Bool :=
  let a := key.params
  1 < key.y && key.y < a.p && pm (key.y, a.q, a.p) == 1 &&
    match key.x with
    | none => true
    | some x => 0 < x && x < a.q && pm (a.g, x, a.p) == key.y

/-- `fromComponents`. -/
def fromComponentsP (p q g y : Nat) (x : Option Nat) : Option Key :=
  let key : Key := ⟨⟨p, q, g⟩, y, x⟩
  if parametersValidP pm key.params && keyValidP pm key then some key else none

/-- `generate`. -/
def generateP (a : Params) (candidates : List Nat) : Option Key := do
  let x ← sampleScalar a.q candidates
  return ⟨a, pm (a.g, x, a.p), some x⟩

/-- `signWithNonce`. -/
def signWithNonceP (key : Key) (digest : List Byte) (k : Nat) : Option Signature := do
  let x ← key.x
  if !keyValidP pm key || !(0 < k && k < key.params.q) then none else do
    let a := key.params
    let r := pm (a.g, k, a.p) % a.q
    let s := powMod k (a.q - 2) a.q * (digestScalar a.q digest + x * r) % a.q
    if r == 0 || s == 0 then none else some ⟨r, s⟩

/-- `sign`. -/
def signP (key : Key) (digest : List Byte) : List Nat → Option Signature
  | [] => none
  | k :: ks => match signWithNonceP pm key digest k with
    | some sig => some sig
    | none => signP key digest ks

/-- `verify`. -/
def verifyP (key : Key) (sig : Signature) (digest : List Byte) : Bool :=
  let a := key.params
  let publicKey := { key with x := none }
  if !keyValidP pm publicKey || !(0 < sig.r && sig.r < a.q && 0 < sig.s && sig.s < a.q) then false
  else
    let w := powMod sig.s (a.q - 2) a.q
    let u1 := digestScalar a.q digest * w % a.q
    let u2 := sig.r * w % a.q
    (pm (a.g, u1, a.p) * pm (key.y, u2, a.p) % a.p) % a.q == sig.r

/-- `signBytes`. -/
def signBytesP (pLen qLen : Nat) (key nonce digest : List Byte) : Option (List Byte) := do
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + 2 * qLen ||
      nonce.length != qLen then none else do
    let k := privateKeyBytes pLen qLen key
    if !parametersValidP pm k.params then none else do
      let sig ← signWithNonceP pm k digest (decodeBE nonce)
      return encodeBE qLen sig.r ++ encodeBE qLen sig.s

/-- `verifyBytes`. -/
def verifyBytesP (pLen qLen : Nat) (key signature digest : List Byte) : Bool :=
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + qLen ||
      signature.length != 2 * qLen then false else
    let k := publicKeyBytes pLen qLen key
    decide (parametersValidP pm k.params) &&
      verifyP pm k ⟨decodeBE (signature.take qLen), decodeBE (signature.drop qLen)⟩ digest

end

/-- `powMod`, of one argument. -/
def powMod' (x : Nat × Nat × Nat) : Nat := powMod x.1 x.2.1 x.2.2

theorem fromComponents_eq (p q g y : Nat) (x : Option Nat) :
    fromComponents p q g y x = fromComponentsP powMod' p q g y x := rfl
theorem generate_eq (a : Params) (candidates : List Nat) :
    generate a candidates = generateP powMod' a candidates := rfl
theorem signWithNonce_eq (key : Key) (digest : List Byte) (k : Nat) :
    signWithNonce key digest k = signWithNonceP powMod' key digest k := rfl
theorem sign_eq (key : Key) (digest : List Byte) (ks : List Nat) :
    sign key digest ks = signP powMod' key digest ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [sign, signP, ih]; rfl
theorem verify_eq (key : Key) (sig : Signature) (digest : List Byte) :
    verify key sig digest = verifyP powMod' key sig digest := rfl
theorem signBytes_eq (pLen qLen : Nat) (key nonce digest : List Byte) :
    signBytes pLen qLen key nonce digest = signBytesP powMod' pLen qLen key nonce digest := rfl
theorem verifyBytes_eq (pLen qLen : Nat) (key signature digest : List Byte) :
    verifyBytes pLen qLen key signature digest =
      verifyBytesP powMod' pLen qLen key signature digest := rfl

def check (v : Vector) (signing : Bool) : Except String Unit := do
  let d ← digest v
  let key : Key := ⟨v.params, v.y, some v.x⟩
  let a := v.params
  -- The exponentiations a signing vector's checks compute (see above),
  -- computed once: `pm` is `powMod'`.
  let w := powMod v.sig.s (a.q - 2) a.q
  let table := if signing then
      Test.tableOf powMod' [(a.g, a.q, a.p), (v.y, a.q, a.p), (a.g, v.x, a.p), (a.g, v.k, a.p),
        (a.g, digestScalar a.q d * w % a.q, a.p), (v.y, v.sig.r * w % a.q, a.p),
        (a.g, v.x + 1, a.p)]
    else []
  let pm := Test.memo table powMod'
  unless verifyP pm key v.sig d == v.pass do throw "verification mismatch"
  if signing then
    unless signWithNonceP pm key d v.k == some v.sig do throw "signature mismatch"
    unless signP pm key d [0, v.params.q, v.k] == some v.sig do throw "nonce rejection failed"
    unless generateP pm v.params [0, v.params.q, v.x] == some key do throw "key generation mismatch"
    let pLen := bitLength v.params.p / 8
    let qLen := bitLength v.params.q / 8
    let publicBytes := encodeBE pLen v.params.p ++ encodeBE qLen v.params.q ++
      encodeBE pLen v.params.g ++ encodeBE pLen v.y
    let privateBytes := publicBytes ++ encodeBE qLen v.x
    let signature := encodeBE qLen v.sig.r ++ encodeBE qLen v.sig.s
    unless signBytesP pm pLen qLen privateBytes (encodeBE qLen v.k) d == some signature do
      throw "packed signing mismatch"
    unless verifyBytesP pm pLen qLen publicBytes signature d do throw "packed verification mismatch"
    unless signBytesP pm pLen qLen privateBytes (encodeBE qLen 0) d == none do
      throw "packed signing accepted zero nonce"
    unless signBytesP pm pLen qLen publicBytes (encodeBE qLen v.k) d == none do
      throw "packed signing accepted public-only key"
    if verifyBytesP pm pLen qLen privateBytes signature d then throw "packed public key length accepted"
    if verifyBytesP pm pLen qLen publicBytes (signature ++ [0]) d then throw "oversized signature accepted"
    if verifyBytesP pm pLen qLen publicBytes (List.replicate (2 * qLen) 0) d then
      throw "packed zero signature accepted"
    unless fromComponentsP pm v.params.p v.params.q v.params.g v.y (some v.x) == some key do
      throw "component import mismatch"
    unless toComponents key == (v.params.p, v.params.q, v.params.g, v.y, some v.x) do
      throw "component export mismatch"
    unless signWithNonceP pm { key with x := none } d v.k == none do throw "signed with public key"
    unless signWithNonceP pm { key with x := some (v.x + 1) } d v.k == none do
      throw "accepted inconsistent private key"
    for bad in [⟨0, v.sig.s⟩, ⟨v.params.q, v.sig.s⟩, ⟨v.sig.r, 0⟩, ⟨v.sig.r, v.params.q⟩] do
      if verifyP pm key bad d then throw "accepted out-of-range signature"
    if verifyP pm { key with y := 1 } v.sig d then throw "accepted identity public key"
    -- Truncation discards low digest bits; extending a long digest by a
    -- byte must not change z. An empty digest represents zero.
    unless digestScalar v.params.q (d ++ [0]) == digestScalar v.params.q d ||
      8 * d.length < bitLength v.params.q do throw "digest truncation mismatch"
    unless digestScalar v.params.q [] == 0 do throw "empty digest mismatch"

def checkParameterCandidates (text : String) : Except String Unit := do
  let mut hash := ""
  let mut p := 0
  let mut q := 0
  let mut seed := []
  let mut checked := 0
  for raw in (text.splitOn "\n").takeWhile (!·.startsWith "[A.1.2") do
    if raw.startsWith "\t" then continue
    let line := raw.trimAscii.toString
    if line.startsWith "[mod = " then
      let some h := (line.splitOn ", ").getLast? | throw "missing parameter hash"
      hash := h.replace "]" ""
    else
      match line.splitOn " = " with
      | ["P", value] => p := decodeBE (← hex value)
      | ["Q", value] => q := decodeBE (← hex value)
      | ["domain_parameter_seed", value] => seed := ← hex value
      | ["counter", value] =>
        let some counter := value.toNat? | throw "invalid counter"
        let l := bitLength p
        let n := bitLength q
        if (l == 1024 && n == 160 && hash == "SHA-1") ||
            ((l == 2048 || l == 3072) && n == 256 && hash == "SHA-256") then
          unless qCandidate n seed == q do throw "q candidate mismatch"
          unless pCandidate l n q seed (1 + counter * ((l - 1) / n + 1)) == p do
            throw "p candidate mismatch"
          checked := checked + 1
      | _ => pure ()
  unless checked == 15 do throw s!"unexpected parameter candidate count {checked}"

/-- Synthetic small-group properties test the rare zero-component retry
paths. These are arithmetic inputs, not cryptographic known-answer vectors;
production imports reject their unsupported bit lengths. -/
def checkEdges : Except String Unit := do
  let a : Params := ⟨11, 5, powMod 2 2 11⟩
  let mut retries := 0
  let mut successes := 0
  for x in List.range a.q do
    if x == 0 then continue
    let some key := generate a [x] | throw "small-group key generation failed"
    for k in List.range a.q do
      if k == 0 then continue
      for z in List.range 8 do
        let d := [BitVec.ofNat 8 (z * 32)]
        match signWithNonce key d k with
        | none => retries := retries + 1
        | some sig =>
          successes := successes + 1
          unless verify key sig d do throw "small-group signature did not verify"
  unless retries > 0 && successes > 0 do throw "zero-component retry path not exercised"
  unless fromComponents a.p a.q a.g 4 (some 1) == none do
    throw "import accepted unsupported parameter sizes"
  unless sampleScalar a.q [0, a.q, a.q + 1] == none do throw "invalid scalar accepted"
  unless generate a [] == none do throw "empty randomness tape accepted"
  for bits in [0, 512, 1024, 2048, 3072, 4096] do
    unless generateParameters bits [] [] [] == none do throw "empty seed tape accepted"
  for n in List.range 4 do
    for x in List.range 512 do
      unless decodeBE (encodeBE n x) == x % 2 ^ (8 * n) do throw "big-endian wrap failed"

/-- Arithmetic regression inputs, not cryptographic known-answer vectors.
Fixed tapes make consumption and rejection deterministic in these tests;
production callers must supply independent random bytes. -/
def checkPrimality : Except String Unit := do
  let witness := encodeBE 8 2
  let tape := (List.replicate 64 witness).flatten
  let suffix : List Byte := [17, 23]
  unless primeChecks 2048 == 64 && primeChecks 2049 == 128 do
    throw "round policy boundary changed"
  for n in [0, 1, 4, 9, 25, 561] do
    unless probablePrime n suffix == some (false, suffix) do
      throw "small composite was not rejected without witnesses"
  for n in [2, 3] do
    unless probablePrime n suffix == some (true, suffix) do
      throw "small prime handling changed"
  unless probablePrime 5 (tape ++ suffix) == some (true, suffix) do
    throw "prime did not consume exactly 64 uniform witnesses"
  unless probablePrime 5 (tape.take (tape.length - 1)) == none do
    throw "short witness tape accepted"
  -- An out-of-range draw is mapped to a witness but does not count as
  -- uniform. It must not replace one of the 64 required uniform draws.
  unless probablePrime 5 (encodeBE 8 0 ++ tape ++ suffix) == some (true, suffix) do
    throw "nonuniform witness accounting changed"
  unless probablePrime 5 (List.replicate 512 0) == none do
    throw "nonuniform witnesses satisfied the round requirement"
  -- Both factors exceed the trial-division table, so this exercises MR.
  unless probablePrime (10007 * 10009) (witness ++ suffix) == some (false, suffix) do
    throw "Miller-Rabin composite rejection failed"
  -- Construct composite, supported-size parameters with an element of
  -- order three. Import checks the algebraic relations, not primality.
  let q := 3 * (2 ^ 158 + 1)
  let some j := (List.range 7).find? (fun j => q * (2 ^ 352 + j) % 7 == 2)
    | throw "composite-domain construction failed"
  let g := q * (2 ^ 352 + j)
  let p := g * g + g + 1
  unless p % 7 == 0 && q % 3 == 0 && bitLength p == 1024 && bitLength q == 160 do
    throw "composite-domain arithmetic changed"
  unless fromComponents p q g g (some 1) == some ⟨⟨p, q, g⟩, g, some 1⟩ do
    throw "import unexpectedly requires primality certification"
  unless primeFromSeed 0 160 5 [] suffix == some (none, suffix) do
    throw "empty parameter search consumed witnesses"

#assert_standard_axioms Spec.Dsa.signContract
#assert_standard_axioms Spec.Dsa.verifyContract
#assert_standard_axioms Spec.Dsa.generateParameters
#assert_standard_axioms Spec.Dsa.probablePrime
#assert_standard_axioms Spec.Dsa.fromComponents
#assert_standard_axioms Spec.Dsa.sign
#assert_standard_axioms Spec.Dsa.verify
#assert_no_compiler_overrides Spec.Dsa.generateParameters Spec.Dsa.fromComponents Spec.Dsa.sign Spec.Dsa.verify
#assert_no_compiler_overrides Spec.Dsa.verifyApi
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  match checkPrimality with
  | .ok () => pure ()
  | .error e => throwError "DSA primality: {e}"
  match checkEdges with
  | .ok () => pure ()
  | .error e => throwError "DSA edges: {e}"
  let params ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / "PQGGen.txt")
  match checkParameterCandidates params with
  | .ok () => pure ()
  | .error e => throwError "PQGGen.txt: {e}"
  for (name, signing) in [("SigGen.txt", true), ("SigVer.rsp", false)] do
    let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-dsa" / name)
    let result := do
      let vs ← parse text signing
      unless vs.length == 300 do throw s!"unexpected vector count {vs.length}"
      for (v, i) in vs.zipIdx do
        match check v signing with
        | .ok () => pure ()
        | .error e => throw s!"vector {i}, {v.hash}, L={bitLength v.params.p}: {e}"
    match result with
    | .ok () => pure ()
    | .error e => throwError "{name}: {e}"

end VG.Test.Dsa
