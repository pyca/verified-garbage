import Lean.Elab.Command
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384
import VerifiedGarbageTest.Ec.Rfc6979
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# Deterministic ECDSA (RFC 6979) specification tests

From the byte-for-byte vendored RFC:

* The detailed example of §A.1.2 (the curve K-163, whose order `q` has 163
  bits, and HMAC-SHA-256): `int2octets(x)`, `bits2octets(h1)`, `K` and `V`
  after steps b to g, and the three candidates `T` and `k`, the first two
  rejected (above `q - 1`), with `K` and `V` after each rejection. Only `q`
  of K-163 matters to the generation of `k`; the rest of the curve here is
  a placeholder.
* The ten signatures of §A.2.5 (P-256; "sample" and "test" with SHA-1,
  SHA-224, SHA-256, SHA-384 and SHA-512), with the checks of
  `Ec/Rfc6979.lean`: the contracts' instances are `P256Sha256.inst` and
  `P256Sha384.inst`.
-/

namespace VG.Test.EcdsaRfc6979

open Spec.Weierstrass Spec.Ecdsa Spec.Ecdsa.Rfc6979 VG.Test.Ec

/-- The octets listed under the line `label`: the following lines of
space-separated pairs of hexadecimal digits. -/
def octets (lines : List String) (label : String) : Except String (List Byte) := do
  let rest := (lines.dropWhile (trim · != label)).drop 1
  if rest.isEmpty then throw s!"no {label}"
  let rows := rest.takeWhile fun l =>
    let ws := (trim l).splitOn " " |>.filter (· ≠ "")
    !ws.isEmpty && ws.all (·.length == 2)
  let ws := rows.flatMap fun l => (trim l).splitOn " " |>.filter (· ≠ "")
  if ws.isEmpty then throw s!"no octets under {label}"
  ws.mapM fun w => do return BitVec.ofNat 8 (← hexNat w)

/-- K-163's order `q`, and a placeholder for the rest of the curve. -/
def k163 (q : Nat) (h : q ≠ 0) : Curve :=
  @Curve.mk 2 0 0 0 0 q 21 ⟨by decide⟩ ⟨h⟩

def H := Spec.Hmac.sha256

/-- §A.1.2. -/
def checkDetailed (text : String) : Except String Unit := do
  let keys := sectionOf text "A.1.1.  Key Pair" "A.1.2."
  let q ← one keys "q"
  let x ← one keys "x"
  let lines := sectionOf text "A.1.2.  Generation of k" "A.1.3."
  if h : q = 0 then throw "q = 0" else
  let C := k163 q h
  unless nBits C == 163 do throw s!"qlen = {nBits C}"
  let h1 ← octets lines "h1"
  unless Spec.Sha256.hash (utf8 "sample") == h1 do throw "h1"
  unless int2octets C x == (← octets lines "int2octets(x)") do throw "int2octets(x)"
  unless bits2octets C h1 == (← octets lines "bits2octets(h1)") do throw "bits2octets(h1)"
  let (K, V) := init C H 32 x h1
  unless K == (← octets lines "K after step f:") do throw "K after step f"
  unless V == (← octets lines "V after step g:") do throw "V after step g"
  unless blocks C 32 == 1 do throw "blocks"
  -- The first two candidates are above `q - 1`; the third is suitable.
  let (T, V) := genT H K 1 V
  unless T == (← octets lines "T (first try)") do throw "T (first try)"
  let k1 := bits2int C T
  unless k1 == 0x4982D236F3FFC758838CA6F5E9FEA455106AF3B2B && q ≤ k1 do throw "k1"
  let (K, V) := next H K V
  unless K == (← octets lines "new K") && V == (← octets lines "new V") do throw "new K, V"
  let (T, V) := genT H K 1 V
  unless T == (← octets lines "T (second try)") do throw "T (second try)"
  let k2 := bits2int C T
  unless k2 == 0x63863C30451DADF4944DF4877B740D4F160A8B6AB && q ≤ k2 do throw "k2"
  let (K, V) := next H K V
  unless K == (← octets lines "new K (2)") && V == (← octets lines "new V (2)") do
    throw "new K (2), V (2)"
  let (T, _) := genT H K 1 V
  unless T == (← octets lines "T (third try)") do throw "T (third try)"
  let k3 := bits2int C T
  unless k3 == (← one lines "k") && k3 < q do throw "k3"

open Lean Elab Command in
run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc6979" / "rfc6979.txt")
  let result := do
    checkDetailed text
    VG.Test.Ec.Rfc6979.check Spec.P256.curve
      [("SHA-256", Spec.Ecdsa.Rfc6979.P256Sha256.inst), ("SHA-384", Spec.Ecdsa.Rfc6979.P256Sha384.inst)]
      "A.2.5.  ECDSA, 256 Bits" "A.2.6." text
  match result with
  | .ok () => pure ()
  | .error e => throwError "rfc6979.txt: {e}"

end VG.Test.EcdsaRfc6979
