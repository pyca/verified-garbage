import VerifiedGarbage.Spec.Weierstrass

/-!
# Helpers for the elliptic-curve specification tests

Parsing the vendored vector files: hexadecimal in either case, and RFC
6979's values that wrap onto further lines.
-/

namespace VG.Test.Ec

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexNat (s : String) : Except String Nat :=
  s.toList.foldlM (fun acc c => match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"invalid hexadecimal digit {c}") 0

def hexBytes (s : String) : Except String (List Byte) := do
  let cs := s.toList
  unless cs.length % 2 == 0 do throw s!"odd hexadecimal string {s}"
  (List.range (cs.length / 2)).mapM fun i => do
    let some hi := hexDigit cs[2 * i]! | throw s!"invalid hexadecimal digit in {s}"
    let some lo := hexDigit cs[2 * i + 1]! | throw s!"invalid hexadecimal digit in {s}"
    return BitVec.ofNat 8 (16 * hi + lo)

def trim (line : String) : String := String.ofList (line.toList.dropWhile (· == ' '))

/-- The lines of `text`, without carriage returns. -/
def lines (text : String) : List String :=
  (text.splitOn "\n").map fun l => String.ofList (l.toList.filter (· != '\r'))

/-- The lines from the one starting with `start` (excluded) to the next one
starting with `stop` (excluded). -/
def sectionOf (text start stop : String) : List String :=
  (((lines text).dropWhile (!·.startsWith start)).drop 1).takeWhile (!·.startsWith stop)

/-- Each `name = HEX` line followed by the indented lines of hexadecimal
digits it wraps onto (RFC 6979's values above 256 bits), as one line. -/
def joinWrapped (ls : List String) : List String :=
  ls.foldl (fun acc l =>
    let t := trim l
    match acc with
    | prev :: rest =>
      if !t.isEmpty && t.length < l.length && t.all (hexDigit · |>.isSome) &&
          (prev.splitOn " = ").length == 2 then (prev ++ t) :: rest
      else l :: acc
    | [] => [l]) [] |>.reverse

/-- `name = HEX` (or `name = 0xHEX`) on a line of its own, indented. -/
def field (name : String) (line : String) : Option String :=
  let t := trim line
  if t.startsWith (name ++ " = ") then
    let v := String.ofList (t.toList.drop (name.length + 3))
    some (if v.startsWith "0x" then String.ofList (v.toList.drop 2) else v)
  else none

def one (ls : List String) (name : String) : Except String Nat := do
  match ls.filterMap (field name) with
  | [v] => hexNat v
  | vs => throw s!"expected one {name}, got {vs.length}"

def utf8 (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- `04 ‖ x ‖ y` (SEC 1 §2.3.3), from the integers, for `len`-octet
coordinates. -/
def point (len x y : Nat) : List Byte := 4 :: (Spec.Weierstrass.toBytes len x ++ Spec.Weierstrass.toBytes len y)

end VG.Test.Ec
