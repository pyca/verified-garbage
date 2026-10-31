module

public import VerifiedGarbage.TCB.VectorCrypto

/-!
# POWER8 vector cryptography values

**Trusted.** Power ISA v3.1C, Book I §§6.9.1.1 (modular adds), 6.9.4
(logical), 6.8.5/6.8.7 (permute/shift), 6.11.1 (AES), 6.11.2 (SHA sigma), 6.11.3
(polynomial multiply). All were available on POWER8 / ISA 2.07.
https://openpower.foundation/specifications/isa/
https://www.ibm.com/support/pages/power8-cryptography-core-instructions

Architectural element 0 is the most significant element, independently of
memory endianness. AES uses that byte order for FIPS 197's state array.
Reuse the existing FIPS transformations and polynomial product from
`VectorCrypto`; those are pure values, not Arm instruction semantics. Its
AES helpers number bytes from the least significant end, so reverse bytes
at that boundary. In particular, inverse cipher adds the round key BEFORE
InvMixColumns, unlike AESDEC's equivalent-inverse round.

Only volatile vector registers v0–v19 (VSR32–VSR51) are operands. ELFv2
§2.2.2.1, Table 2.21 preserves v20–v31; leaving those and VSR0–VSR31 out
prevents code from modifying them, including the nonvolatile FPR aliases.
-/

@[expose] public section

namespace VG.PPC64LE

inductive VReg
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 | v8 | v9
  | v10 | v11 | v12 | v13 | v14 | v15 | v16 | v17 | v18 | v19
  deriving DecidableEq, Repr, Inhabited

def vbyte (x : BitVec 128) (i : Nat) : BitVec 8 := x.extractLsb' (8 * (15 - i)) 8
def vword (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * (3 - i)) 32
def vdword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * (1 - i)) 64

def ofVBytes (f : Nat → BitVec 8) : BitVec 128 :=
  (List.range 16).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (8 * (15 - i)))) 0

def rev128 (x : BitVec 128) : BitVec 128 := ofVBytes fun i => vbyte x (15 - i)

/-- Book I §6.11.1: SubBytes, ShiftRows, optionally MixColumns, AddRoundKey;
inverse: InvShiftRows, InvSubBytes, AddRoundKey, optionally InvMixColumns. -/
def vcipher (inverse last : Bool) (x k : BitVec 128) : BitVec 128 :=
  let x := rev128 x
  let k := rev128 k
  rev128 (if inverse then
    let y := VectorCrypto.aesMapBytes VectorCrypto.aesInvSbox (VectorCrypto.aesInvShiftRows x) ^^^ k
    if last then y else VectorCrypto.aesInvMixColumns y
  else
    let y := VectorCrypto.aesShiftRows (VectorCrypto.aesMapBytes VectorCrypto.aesSbox x)
    (if last then y else VectorCrypto.aesMixColumns y) ^^^ k)

/-- Book I §6.11.2, four SHA-256 functions; `st` selects upper-case Σ. -/
def sigma256 (st one : Bool) (x : BitVec 32) : BitVec 32 :=
  if st then
    if one then x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
    else x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
  else
    if one then x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)
    else x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- Book I §6.11.2, four SHA-512 functions. -/
def sigma512 (st one : Bool) (x : BitVec 64) : BitVec 64 :=
  if st then
    if one then x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
    else x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
  else
    if one then x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)
    else x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)

inductive VLogic | and | or | xor
  deriving DecidableEq, Repr

/-- Non-saturating vector instructions: none modifies VSCR or CR. -/
inductive VOp
  | cipher (inverse last : Bool) (d n m : VReg)
  | sbox (d n : VReg)
  | sha256 (d n : VReg) (st : Bool) (six : Nat)
  | sha512 (d n : VReg) (st : Bool) (six : Nat)
  | pmsumd (d n m : VReg)
  | logic (op : VLogic) (d n m : VReg)
  /-- `vsel`: mask bit zero selects VA, mask bit one selects VB.
  NXP AltiVec Programming Environments Manual (06/2014), p. 6-163,
  Figure 6-124; no other registers are changed. Baseline AltiVec.
  https://www.nxp.com/docs/en/reference-manual/ALTIVECPOWERISAPEM.pdf#page=257 -/
  | sel (d n m mask : VReg)
  /-- `vadduwm` / `vaddudm`: add modulo 2^32 / 2^64 per element. -/
  | add (doubleword : Bool) (d n m : VReg)
  /-- `vperm`: each byte selects the low five bits of its control byte. -/
  | perm (d n m c : VReg)
  /-- `vsldoi`: concatenate VA||VB and select bytes SHB through SHB+15. -/
  | sldoi (d n m : VReg) (sh : Nat)
  deriving DecidableEq, Repr

/-- The destination and result; reject unencodable and reserved immediates.
SHA SIX is numbered from its MSB: word i uses bit i, doubleword i bit 2i;
for the doubleword instruction the other two SIX bits are reserved. -/
def VOp.eval (v : VReg → BitVec 128) : VOp → Option (VReg × BitVec 128)
  | .cipher inv last d n m => some (d, vcipher inv last (v n) (v m))
  | .sbox d n => some (d, ofVBytes fun i => VectorCrypto.aesSbox (vbyte (v n) i))
  | .sha256 d n st six => if six < 16 then
      some (d, (List.range 4).foldl (fun x i => x |||
        ((sigma256 st (six.testBit (3 - i)) (vword (v n) i)).setWidth 128 <<< (32 * (3 - i)))) 0)
    else none
  | .sha512 d n st six => if six < 16 ∧ six &&& 5 = 0 then
      some (d, sigma512 st (six.testBit 3) (vdword (v n) 0) ++
        sigma512 st (six.testBit 1) (vdword (v n) 1))
    else none
  | .pmsumd d n m => some (d,
      VectorCrypto.polyMul (vdword (v n) 0) (vdword (v m) 0) ^^^
      VectorCrypto.polyMul (vdword (v n) 1) (vdword (v m) 1))
  | .logic op d n m => some (d, match op with
      | .and => v n &&& v m | .or => v n ||| v m | .xor => v n ^^^ v m)
  | .sel d n m mask => some (d, (v n &&& ~~~v mask) ||| (v m &&& v mask))
  | .add dw d n m => some (d, if dw then
      (vdword (v n) 0 + vdword (v m) 0) ++ (vdword (v n) 1 + vdword (v m) 1)
    else (List.range 4).foldl (fun x i => x |||
      ((vword (v n) i + vword (v m) i).setWidth 128 <<< (32 * (3 - i)))) 0)
  | .perm d n m c => some (d, ofVBytes fun i =>
      let j := (vbyte (v c) i).toNat % 32
      if j < 16 then vbyte (v n) j else vbyte (v m) (j - 16))
  | .sldoi d n m sh => if sh < 16 then
      some (d, ((v n ++ v m) <<< (8 * sh)).extractLsb' 128 128)
    else none

end VG.PPC64LE
