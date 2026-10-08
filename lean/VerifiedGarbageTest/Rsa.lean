import Lean.Elab.Command
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-!
# RSA primitive specification tests

Known answers are parsed from the byte-for-byte NIST CAVP RSADP component
vectors (`vectors/nist-cavp-rsadp/`, SP 800-56B, 1024- and 2048-bit
moduli). Each gives `n`, `e`, `d` and `c`, and either the result `k` or the
failure for `c ≥ n`; no vector values are embedded in this test. For each:

* `primesKey` recovers the factors of `n` (Appendix C.1), as `k` octets
  each, as `recoverPrimes` does.
* The recovered `p > q` multiply to `n`; `crtKey` gives their CRT values
  (`crtValues`), with which `privateCrt` gives `k`, or fails for `c ≥ n`,
  also with `p`, `dP` and `qInv` one octet longer (a leading zero).
* `publicOp` with `e` takes `k` back to `c`.
* Inconsistent keys fail: `qInv + p`, and `q + 2` (so `p q ≠ n`), in
  `privateCrt` and `crtKey`.
* BoringSSL's checks: these vectors' exponents exceed its limits, so
  `publicOpChecked`, `privateChecked` and `checkKey` refuse them. The same
  factors with `e = 65537` and `d = e⁻¹ mod λ(n)` (computed, when it exists)
  make a key `checkKey` accepts, with `p` and `q` either way round and with
  leading zeros, and refuses when any one of its checks fails, and so does
  `checkCrtKey` (but for those of `d`); with it `privateChecked` gives 0
  for 0, and `c^d mod n` for `c`, which `publicOpChecked` takes back to
  `c`, and faults for a wrong `dP`, `dQ` or `e`.
* `publicPrecompute` gives `w = ⌈k / 8⌉` words of `n`, which make up `n`,
  then `w` words of `R² mod n`, which equal `(R mod n)² mod n`, with
  `R = 2^(64 w)` reduced by doubling; and nothing for the invalid moduli
  below.

The rest checks the edges on arithmetic inputs, not known answers: the
bounds of `modulusValid`, OS2IP and I2OSP, and that `inverse` finds every
inverse modulo small moduli.
-/

namespace VG.Test.Rsa

open Lean Elab Command Spec.Rsa

/-- A hexadecimal integer (the file prints integers without leading zeros, so
some have an odd number of digits). -/
def hexNat (s : String) : Except String Nat :=
  s.toList.foldlM (init := 0) fun x c =>
    if '0' ≤ c && c ≤ '9' then pure (16 * x + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then pure (16 * x + (c.toNat - 'a'.toNat + 10))
    else throw "invalid hex digit"

structure Vector where
  n : Nat := 0
  e : Nat := 0
  d : Nat := 0
  c : Nat := 0
  pass : Bool := false
  k : Nat := 0

/-- The vectors of `RSADPComponent800_56B.txt`: each starts at `COUNT`. -/
def parse (text : String) : Except String (List Vector) := do
  let mut v : Option Vector := none
  let mut vs := []
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "[" || line.startsWith "#" then continue
    match line.splitOn " = " with
    | [field, value] =>
      let value := value.trimAscii.toString
      if field == "COUNT" then
        if let some w := v then vs := w :: vs
        v := some {}
      else
        let some w := v | throw s!"{field} before COUNT"
        match field with
        | "n" => v := some { w with n := ← hexNat value }
        | "e" => v := some { w with e := ← hexNat value }
        | "d" => v := some { w with d := ← hexNat value }
        | "c" => v := some { w with c := ← hexNat value }
        | "k" => v := some { w with k := ← hexNat value }
        | "Result" => v := some { w with pass := value == "Pass" }
        | "c^d" | "k^e" => pure ()
        | _ => throw s!"unknown field {field}"
    | _ => pure ()
  if let some w := v then vs := w :: vs
  return vs.reverse

/-- `x` as octets, most significant first, with no leading zero. -/
def bytes (x : Nat) : List Byte := i2osp x ((Nat.log2 x) / 8 + 1)

/-- The words `ws`, least significant first, as an integer. -/
def ofWords (ws : List (BitVec 64)) : Nat := ws.foldr (fun x acc => x.toNat + 2 ^ 64 * acc) 0

/-- `2^b mod n`, by `b` doublings. -/
def powTwoMod (b n : Nat) : Nat := (List.range b).foldl (fun x _ => 2 * x % n) (1 % n)

/-- Checks one vector; returns the number of candidates the factor recovery
tried. -/
def check (v : Vector) : Except String Nat := do
  let n := v.n
  let e := v.e
  let d := v.d
  let nB := bytes n
  let len := nB.length
  unless len * 8 == Nat.log2 n + 1 do throw "modulus not a whole number of octets"
  let eB := bytes e
  let dB := bytes d
  let cB := i2osp v.c len
  let kB := i2osp v.k len
  unless modulusValid n len do throw "modulus rejected"
  let expected : Option (List Byte) := if v.pass then some kB else none
  if v.pass then
    unless v.k < n do throw "result not below n"
    unless publicOp nB eB kB == some cB do throw "RSAEP mismatch"
  else
    unless v.c ≥ n && v.c < 256 ^ len do throw "failing vector's input not in [n, 256^k)"
    unless publicOp nB eB cB == none do throw "RSAEP accepted an input not below n"
  let (some (p, q), tries) := recoverPrimes n e d | throw "factors not found"
  unless 1 ≤ tries && tries ≤ recoverTries do throw s!"{tries} tries"
  unless primesKey nB eB dB == (some (i2osp p len, i2osp q len), tries) do
    throw "primesKey mismatch"
  -- The `i`-th candidate is `g = i + 1`: those before the last tried fail.
  let (t, r) := splitTwos (d * e - 1)
  unless (List.range tries).all (fun i => (recoverStep n t r (i + 2)).isSome == (i + 1 == tries)) do
    throw "candidates tried"
  unless p * q == n && p > q && q > 1 do throw "factors wrong"
  let some (dP, dQ, qInv) := crtValues p q d | throw "no CRT values"
  unless (q * qInv) % p == 1 && dP < p - 1 && dQ < q - 1 do throw "CRT values wrong"
  let pLen := (bytes p).length
  let qLen := (bytes q).length
  unless crtKey nB (bytes p) (bytes q) dB == some (i2osp dP pLen, i2osp dQ qLen, i2osp qInv pLen) do
    throw "crtKey mismatch"
  -- The input `n` itself is not below `n`.
  unless publicOp nB eB nB == none &&
      privateCrt nB nB (bytes p) (bytes q) (i2osp dP pLen) (i2osp dQ qLen) (i2osp qInv pLen) == none do
    throw "accepted the input n"
  unless privateCrt nB cB (bytes p) (bytes q) (i2osp dP pLen) (i2osp dQ qLen)
      (i2osp qInv pLen) == expected do
    throw "privateCrt mismatch"
  unless privateCrt nB cB (i2osp p (pLen + 1)) (bytes q) (i2osp dP (pLen + 1))
      (i2osp dQ qLen) (i2osp qInv (pLen + 1)) == expected do
    throw "privateCrt mismatch with unbalanced lengths"
  unless privateCrt nB cB (i2osp p (pLen + 1)) (bytes q) (i2osp dP (pLen + 1))
      (i2osp dQ qLen) (i2osp (qInv + p) (pLen + 1)) == none do
    throw "privateCrt accepted qInv ≥ p"
  unless privateCrt nB cB (bytes p) (i2osp (q + 2) qLen) (i2osp dP pLen) (i2osp dQ qLen)
      (i2osp qInv pLen) == none do
    throw "privateCrt accepted p q ≠ n"
  unless crtKey nB (bytes p) (i2osp (q + 2) qLen) dB == none do
    throw "crtKey accepted p q ≠ n"
  let w := modulusWords len
  let some ws := publicPrecompute nB | throw "publicPrecompute rejected the modulus"
  unless ws.length == 2 * w do throw "publicPrecompute length"
  unless ofWords (ws.take w) == n do throw "publicPrecompute: n"
  let rr := powTwoMod (64 * w) n
  unless ofWords (ws.drop w) == rr * rr % n do throw "publicPrecompute: R² mod n"
  unless publicPrecompute (0 :: nB) == none && publicPrecompute (i2osp (n + 1) len) == none do
    throw "publicPrecompute accepted an invalid modulus"
  -- BoringSSL's checks. These vectors' exponents are above `2^33`, beyond
  -- BoringSSL's limits, so every checked function refuses them.
  let pB := bytes p
  let qB := bytes q
  let crt (dP dQ qInv : Nat) := (i2osp dP pLen, i2osp dQ qLen, i2osp qInv pLen)
  let (dPB, dQB, qInvB) := crt dP dQ qInv
  unless !exponentValid e do throw "exponent within BoringSSL's limits"
  unless publicOpChecked nB eB kB == none do throw "publicOpChecked accepted a large exponent"
  unless privateChecked nB eB cB pB qB dPB dQB qInvB == .invalid do
    throw "privateChecked accepted a large exponent"
  unless !checkKey nB eB dB pB qB dPB dQB qInvB do throw "checkKey accepted a large exponent"
  -- The same factors with `e = 65537` and `d = e⁻¹ mod λ(n)`, computed here.
  let e' := 65537
  let eB' := bytes e'
  let lam := (p - 1) * (q - 1) / Nat.gcd (p - 1) (q - 1)
  if let some d' := inverse e' lam then
    let dB' := bytes d'
    let some (dP', dQ', qInv') := crtValues p q d' | throw "no CRT values for e = 65537"
    let (dPB', dQB', qInvB') := crt dP' dQ' qInv'
    unless checkKey nB eB' dB' pB qB dPB' dQB' qInvB' do throw "checkKey rejected a valid key"
    -- With the factors' lengths unbalanced (a leading zero), as given.
    unless checkKey nB eB' (0 :: dB') (0 :: pB) qB (0 :: dPB') dQB' (0 :: qInvB') do
      throw "checkKey rejected a valid key with leading zeros"
    -- Each check of `RSA_check_key` fails alone.
    let rejects : List (String × Bool) := [
      ("an even modulus", checkKey (i2osp (n + 1) len) eB' dB' pB qB dPB' dQB' qInvB'),
      ("e = 65536", checkKey nB (bytes 65536) dB' pB qB dPB' dQB' qInvB'),
      ("e = 2^33 + 1", checkKey nB (bytes (2 ^ 33 + 1)) dB' pB qB dPB' dQB' qInvB'),
      ("d ≥ n", checkKey nB eB' (bytes (d' + n)) pB qB dPB' dQB' qInvB'),
      ("p q ≠ n", checkKey nB eB' dB' pB (bytes (q + 2)) dPB' dQB' qInvB'),
      ("d e ≢ 1", checkKey nB eB' (bytes (d' + 1)) pB qB dPB' dQB' qInvB'),
      ("dP ≥ p - 1", checkKey nB eB' dB' pB qB (i2osp (dP' + (p - 1)) (pLen + 1)) dQB' qInvB'),
      ("e dP ≢ 1", checkKey nB eB' dB' pB qB (i2osp (dP' + 1) pLen) dQB' qInvB'),
      ("dQ ≥ q - 1", checkKey nB eB' dB' pB qB dPB' (i2osp (dQ' + (q - 1)) (qLen + 1)) qInvB'),
      ("e dQ ≢ 1", checkKey nB eB' dB' pB qB dPB' (i2osp (dQ' + 1) qLen) qInvB'),
      ("qInv ≥ p", checkKey nB eB' dB' pB qB dPB' dQB' (i2osp (qInv' + p) (pLen + 1))),
      ("q qInv ≢ 1", checkKey nB eB' dB' pB qB dPB' dQB' (i2osp (qInv' + 1) pLen))]
    for (what, accepted) in rejects do
      if accepted then throw s!"checkKey accepted {what}"
    -- `p` and `q` swapped make another valid key, with its own CRT values.
    let some (dQ'', dP'', pInv) := crtValues q p d' | throw "no CRT values, swapped"
    unless checkKey nB eB' dB' qB pB (i2osp dQ'' qLen) (i2osp dP'' pLen) (i2osp pInv qLen) do
      throw "checkKey rejected the key with p and q swapped"
    -- `checkCrtKey`: the same checks without `d`.
    unless checkCrtKey nB eB' pB qB dPB' dQB' qInvB' do throw "checkCrtKey rejected a valid key"
    unless checkCrtKey nB eB' (0 :: pB) qB (0 :: dPB') dQB' (0 :: qInvB') do
      throw "checkCrtKey rejected a valid key with leading zeros"
    unless checkCrtKey nB eB' qB pB (i2osp dQ'' qLen) (i2osp dP'' pLen) (i2osp pInv qLen) do
      throw "checkCrtKey rejected the key with p and q swapped"
    let crtRejects : List (String × Bool) := [
      ("an even modulus", checkCrtKey (i2osp (n + 1) len) eB' pB qB dPB' dQB' qInvB'),
      ("e = 65536", checkCrtKey nB (bytes 65536) pB qB dPB' dQB' qInvB'),
      ("e = 2^33 + 1", checkCrtKey nB (bytes (2 ^ 33 + 1)) pB qB dPB' dQB' qInvB'),
      ("p q ≠ n", checkCrtKey nB eB' pB (bytes (q + 2)) dPB' dQB' qInvB'),
      ("dP ≥ p - 1", checkCrtKey nB eB' pB qB (i2osp (dP' + (p - 1)) (pLen + 1)) dQB' qInvB'),
      ("e dP ≢ 1", checkCrtKey nB eB' pB qB (i2osp (dP' + 1) pLen) dQB' qInvB'),
      ("dQ ≥ q - 1", checkCrtKey nB eB' pB qB dPB' (i2osp (dQ' + (q - 1)) (qLen + 1)) qInvB'),
      ("e dQ ≢ 1", checkCrtKey nB eB' pB qB dPB' (i2osp (dQ' + 1) qLen) qInvB'),
      ("qInv ≥ p", checkCrtKey nB eB' pB qB dPB' dQB' (i2osp (qInv' + p) (pLen + 1))),
      ("q qInv ≢ 1", checkCrtKey nB eB' pB qB dPB' dQB' (i2osp (qInv' + 1) pLen)),
      ("p = 1", checkCrtKey nB eB' [1] nB [0] (i2osp 0 len) [0])]
    for (what, accepted) in crtRejects do
      if accepted then throw s!"checkCrtKey accepted {what}"
    -- A key it accepts gives a result for 0, which is 0.
    unless privateChecked nB eB' (i2osp 0 len) pB qB dPB' dQB' qInvB' == .ok (i2osp 0 len) do
      throw "privateChecked refused 0 with a key checkCrtKey accepts"
    if v.pass then
      let m := powMod v.c d' n
      unless privateChecked nB eB' cB pB qB dPB' dQB' qInvB' == .ok (i2osp m len) do
        throw "privateChecked mismatch"
      unless publicOpChecked nB eB' (i2osp m len) == some cB do
        throw "publicOpChecked mismatch"
      -- A wrong `dP` or `dQ` (which `checkKey` refuses) faults rather than
      -- releasing a result that reveals a factor.
      unless privateChecked nB eB' cB pB qB (i2osp (dP' + 1) pLen) dQB' qInvB' == .fault do
        throw "privateChecked released a result with a wrong dP"
      unless privateChecked nB eB' cB pB qB dPB' (i2osp (dQ' + 1) qLen) qInvB' == .fault do
        throw "privateChecked released a result with a wrong dQ"
      -- So does a wrong exponent.
      unless privateChecked nB (bytes (e' + 2)) cB pB qB dPB' dQB' qInvB' == .fault do
        throw "privateChecked released a result for the wrong e"
      unless privateChecked nB (bytes 65536) cB pB qB dPB' dQB' qInvB' == .invalid do
        throw "privateChecked accepted an even exponent"
      unless privateChecked nB eB' cB pB qB dPB' dQB' (i2osp (qInv' + p) (pLen + 1)) ==
          .invalid do
        throw "privateChecked accepted qInv ≥ p"
    else
      unless privateChecked nB eB' cB pB qB dPB' dQB' qInvB' == .invalid do
        throw "privateChecked accepted an input not below n"
      unless publicOpChecked nB eB' cB == none do
        throw "publicOpChecked accepted an input not below n"
  -- A modulus with a leading zero octet, or an even one, is not valid.
  unless publicOp (0 :: nB) eB (0 :: kB) == none do throw "accepted a leading zero"
  unless publicOp (i2osp (n + 1) len) eB kB == none do throw "accepted an even modulus"
  unless primesKey (i2osp (n + 1) len) eB dB == (none, 0) do
    throw "primesKey accepted an even modulus"
  unless crtKey (i2osp (n + 1) len) (bytes p) (bytes q) dB == none do
    throw "crtKey accepted an even modulus"
  return tries

/-- Edges on arithmetic inputs. -/
def checkEdges : Except String Unit := do
  for (n, k, ok) in [(2 ^ 511 + 1, 64, true), (2 ^ 511 - 1, 64, false), (2 ^ 512 - 1, 64, true),
      (2 ^ 512 - 2, 64, false), (2 ^ 8192 - 1, 1024, true), (2 ^ 8192 + 1, 1025, false),
      (2 ^ 520 + 1, 66, true), (2 ^ 520 + 1, 67, false)] do
    unless modulusValid n k == ok do
      throw s!"modulusValid of a {k}-octet modulus"
  for (k, w) in [(64, 8), (65, 9), (71, 9), (72, 9), (73, 10), (1024, 128)] do
    unless modulusWords k == w do throw s!"modulusWords {k}"
  unless toWords (2 ^ 64 + 5) 3 == [5, 1, 0] do throw "toWords"
  for (e, ok) in [(0, false), (1, false), (2, false), (3, true), (4, false), (65537, true),
      (2 ^ 33 - 1, true), (2 ^ 33, false), (2 ^ 33 + 1, false)] do
    unless exponentValid e == ok do throw s!"exponentValid {e}"
  for x in List.range 70000 do
    unless os2ip (i2osp x 3) == x % 2 ^ 24 do throw "I2OSP/OS2IP"
  for m in List.range 120 do
    if m < 2 then continue
    for a in List.range (2 * m) do
      let brute := (List.range m).find? fun x => a * x % m == 1
      unless inverse a m == brute do throw s!"inverse {a} mod {m}"
  -- `d e - 1` odd, or `d e < 2`: no factors, and no candidate tried.
  unless recoverPrimes (2 ^ 511 + 1) 3 2 == (none, 0) do throw "odd de - 1"
  unless recoverPrimes (2 ^ 511 + 1) 3 0 == (none, 0) do throw "zero d"
  unless recoverPrimes (2 ^ 511 + 1) 1 1 == (none, 0) do throw "de = 1"

#assert_standard_axioms Spec.Rsa.publicOp
#assert_standard_axioms Spec.Rsa.privateCrt
#assert_standard_axioms Spec.Rsa.crtKey
#assert_standard_axioms Spec.Rsa.primesKey
#assert_standard_axioms Spec.Rsa.publicPrecompute
#assert_standard_axioms Spec.Rsa.publicOpChecked
#assert_standard_axioms Spec.Rsa.privateChecked
#assert_standard_axioms Spec.Rsa.checkKey
#assert_no_compiler_overrides Spec.Rsa.publicPrecompute Spec.Rsa.publicOp Spec.Rsa.privateCrt Spec.Rsa.crtKey Spec.Rsa.primesKey
#assert_no_compiler_overrides Spec.Rsa.publicOpChecked Spec.Rsa.privateChecked Spec.Rsa.checkKey
#assert_spec_origin

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent) | throwError "no repository root"
  match checkEdges with
  | .ok () => pure ()
  | .error e => throwError "RSA edges: {e}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-rsadp" / "RSADPComponent800_56B.txt")
  let result : Except String Unit := do
    let vs ← parse text
    unless vs.length == 60 do throw s!"unexpected vector count {vs.length}"
    unless (vs.filter (·.pass)).length == 40 do throw "unexpected passing vector count"
    for (v, i) in vs.zipIdx do
      match check v with
      | .ok _ => pure ()
      | .error e => throw s!"vector {i} ({Nat.log2 v.n + 1} bits): {e}"
  match result with
  | .ok () => pure ()
  | .error e => throwError "RSADPComponent800_56B.txt: {e}"

end VG.Test.Rsa
