module
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.TCB.PPC64LE.Isa


/-!
# Ed25519 on PPC64LE: elements to and from bytes

An element's eight words are its 32 bytes, little-endian, so packing it is
a copy of its words to the bytes at `r14` (plus a constant), and unpacking
the reverse; a point is its four coordinates, consecutive.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

def packStep (a dst k : Nat) : List Instr :=
  [.load .w .r7 .r6 (a + 4 * k), .store .w .r7 .r14 (dst + 4 * k)]

def packField (a dst : Nat) : List Instr := (List.range 8).flatMap (packStep a dst)

def unpackSrc (src k : Nat) : List Instr := [.load .w .r7 .r14 (src + 4 * k)]

def unpackField (o src : Nat) : List Instr :=
  (List.range 8).flatMap fun k => unpackSrc src k ++ [.store .w .r7 .r6 (o + 4 * k)]

def pointToTable : List Instr :=
  (List.range 4).flatMap fun j => packField (64 + 32 * j) (32 * j)

def pointFromTable : List Instr :=
  (List.range 4).flatMap fun j => unpackField (64 + 32 * j) (32 * j)

end VG.Impl.Ed25519.PPC64LE
