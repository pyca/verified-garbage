module

public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Spec.TripleDes

/-!
# DES's S-boxes, packed for evaluation

`sboxOut i x` is the output of S-box `i` on the six-bit input `x`, read from
a packed copy of the specification's tables (`Spec.TripleDes.sBoxes`,
reordered by input). The targets' S-box constants are built from it: the
kernel evaluates them from a few `Nat` shifts rather than from the
specification's vectors of `BitVec` numerals. Nothing is trusted here: every
target's proof checks the constants against the specification's S-boxes
(`Proof.TripleDes.outputTable`), and the `#guard` below checks the table
when the file is compiled.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes

/-- Box `i`'s 64 outputs, four bits each, output `x` at bit `4 x`. -/
def sboxRows : List Nat := [
  0xd0650aa3e739bc5f7b12964d288ec1f487305995bcc66aa318db2fe2417df40e,
  0x9fe25309c67c68b5214df43a1ba78ed05ab5906cad1207c9e4832bf67e48d13f,
  0xc72e5ab53ce2f14b70839f6809d4a61d18f2b4cbe75c8d21a56f43369e0970da,
  0xe42872c5be53419f8dd71bac6009f63a9fe4ac1bc52872413a09f66053be8dd7,
  0x3e5043a6950cf96fd827ed1a7bc182b4698e903daff3055816db7a47c124bce2,
  0xd68b0d617a14e0b7a3fc5892c52f3e498b35b70ee4d31d605896c2792f4af1ac,
  0xc23925e0f8065f9a7ea7431c8ddbb4616186fa25c7593ce3ad18904f7eb20bd4,
  0xb865533f0d9ac6f0d28eac4971e41b27279ce005be6359ca417b3fa684d8f21d]

/-- The output of S-box `i` on the input `x < 64`. -/
def sboxOut (i x : Nat) : Nat := (sboxRows.getD i 0 >>> (4 * x)) % 16

#guard (List.range 8).all fun i => (List.range 64).all fun x =>
  sboxOut i x == (Spec.TripleDes.sBox i (BitVec.ofNat 6 x)).toNat

end VG.Impl.CmacTripleDes
