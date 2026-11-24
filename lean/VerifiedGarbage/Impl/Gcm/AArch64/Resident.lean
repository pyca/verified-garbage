module

public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
public import VerifiedGarbage.Impl.Gcm.AArch64.Xor3

@[expose] public section
namespace VG.Impl.Gcm.AArch64.Stitch
open VG.AArch64

/-- Previous batch of ciphertext, reversed within each doubleword for GHASH. -/
def cipherReg : Nat → VReg
  | 0 => .v8 | 1 => .v9 | 2 => .v10 | 3 => .v11
  | 4 => .v12 | 5 => .v13 | 6 => .v14 | _ => .v15

/-- Multiply both resident ciphertext operands without copying them into
the product destinations. The last pair mixes the old GHASH accumulator
into the right operand before multiplication. -/
def residentPair (p : Nat) : List Instr :=
  let a := cipherReg (pa p)
  let b := cipherReg (pb p)
  let r := if p = 3 then A₂ else b
  (if p = 3 then [.vop (.logic .eor A₂ b Y)] else []) ++
  [.ldrq S₁ .x19 (sOff (pk p)), .ldrq S₂ .x19 (sOff (pl p)), .ldrq KP .x19 (kOff p),
   .vop (.perm .trn1 .d2 T a r), .vop (.perm .trn2 .d2 U a r), .vop (.logic .eor T T U),
   .vop (.pmull false X₁ a S₁), .vop (.pmull true A₁ a S₁),
   .vop (.pmull false X₂ r S₂), .vop (.pmull true A₂ r S₂),
   .vop (.pmull false U T KP), .vop (.pmull true T T KP)]

def residentGroup (p : Nat) := residentPair p ++ (if p = 0 then addFirst else addNext)

def residentHash := residentGroup 0 ++ (residentGroup 1 ++ (residentGroup 2 ++ (residentGroup 3 ++ reduce)))

/-- Preserve the interleaving positions of the two eliminated load/move pairs. -/
def residentSlots : List (List Instr) :=
  (List.range 4).flatMap (fun p => [[],[],[],[]] ++ (residentGroup p).map List.singleton) ++
    reduce.map List.singleton

def residentParts (nr : Nat) :=
  (VG.Impl.Weave.weaveG (fuse (aesPart nr 128 .x15)) residentSlots).flatMap lowerXor3

end VG.Impl.Gcm.AArch64.Stitch
