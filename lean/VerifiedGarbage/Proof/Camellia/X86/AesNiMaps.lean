module

public import VerifiedGarbage.Impl.Camellia.X86.AesNi
meta import VerifiedGarbage.Impl.Camellia.X86.AesNi
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
public import VerifiedGarbage.Spec.Camellia
meta import VerifiedGarbage.Spec.Camellia
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia's S-boxes by the AES S-box: the byte maps

The byte maps of `Impl/Camellia/X86/AesNi.lean`, as functions of a byte read
from its table of constants, and what they are of Camellia's S-boxes
(RFC 3713 §2.4.2, `Spec.Camellia.sbox1` … `sbox4`), each a fact about the
256 bytes that the kernel evaluates:

* `qT a` (into the rounds' form: `L1 ∘ rot^a`, where `a` holds at the two
  positions of s4) and `qI a` (out of it) are inverse and linear;
* `sbox_ok`: at a position of kind `j` (s1, s2, s3 or s4), whose byte goes
  to a position where `a` is `ai`, `qT ai (s_j b) = nmap k (AES (qT a_j b ⊕ c5))
  ⊕ mc ai j`, with `k` the map after the S-box for the two positions, and
  `mc` a constant.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNi

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNi

/-- The 16 bytes at `off` of the table of constants. -/
def tblAt (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

/-- `pshufb`'s look-up in the constant at `off`. -/
def lk (off : Nat) (b : Byte) : Byte := Fn.eval (.look (tblAt off)) b

/-- The byte map at `t` (`oT` or `oI`), with its difference at a position
of s4 (`a`). -/
def bmap (t : Nat) (a : Bool) (b : Byte) : Byte :=
  lk t (b &&& 0x0f#8) ^^^ lk (t + 16) (b >>> 4) ^^^
    (if a = true then lk (t + 32) (b &&& 0x0f#8) ^^^ lk (t + 48) (b >>> 4) else 0#8)

/-- Into the rounds' form. -/
def qT (a : Bool) (b : Byte) : Byte := bmap oT a b
/-- Out of it. -/
def qI (a : Bool) (b : Byte) : Byte := bmap oI a b

/-- Map `k` after the AES S-box, whose key is the mask `0x0f`. -/
def nmap (k : Nat) (z : Byte) : Byte := lk (oN k) ((z &&& 0x0f#8) ^^^ 0x0f#8) ^^^ lk (oN k + 16) (z >>> 4)

/-- The constant of the map before the AES S-box. -/
def c5 : Byte := qT false 0xc5#8

/-- Camellia's S-box of kind `j`: s1, s2, s3, s4. -/
def sb : Nat → Byte → Byte
  | 0 => Spec.Camellia.sbox1
  | 1 => Spec.Camellia.sbox2
  | 2 => Spec.Camellia.sbox3
  | _ => Spec.Camellia.sbox4

/-- The map after the AES S-box, for the S-box of kind `j` and a position
where `a` is `ai`. -/
def kOf : Bool → Nat → Nat
  | false, 0 => 0 | false, 1 => 1 | false, 2 => 2 | false, _ => 0
  | true, 0 => 1 | true, 1 => 3 | true, 2 => 0 | true, _ => 1

/-- The constant of `sbox_ok`. -/
def mc (ai : Bool) (j : Nat) : Byte := qT ai (sb j 0#8) ^^^ nmap (kOf ai j) (aesSbox (qT (j == 3) 0#8 ^^^ c5))

theorem sbox_all : ((List.range 256).all fun n => [false, true].all fun ai => (List.range 4).all fun j =>
    qT ai (sb j (BitVec.ofNat 8 n)) ==
      nmap (kOf ai j) (aesSbox (qT (j == 3) (BitVec.ofNat 8 n) ^^^ c5)) ^^^ mc ai j) = true := by
  lit_decide

theorem inv_all : ((List.range 256).all fun n => [false, true].all fun a =>
    qI a (qT a (BitVec.ofNat 8 n)) == BitVec.ofNat 8 n && qT a (qI a (BitVec.ofNat 8 n)) == BitVec.ofNat 8 n) = true := by
  lit_decide

/-- The nibble tables of the two byte maps are linear. -/
theorem lin16_all : ((List.range 16).all fun x => (List.range 16).all fun y =>
    [oT, oT + 16, oT + 32, oT + 48, oI, oI + 16, oI + 32, oI + 48].all fun t =>
      lk t (BitVec.ofNat 8 (x ^^^ y)) == lk t (BitVec.ofNat 8 x) ^^^ lk t (BitVec.ofNat 8 y)) = true := by
  lit_decide

/-! ## The positions

A half's bytes are numbered from the least significant, `j < 8`; the byte
`j` is in slot `(j + 4) % 8` of a register (a 32-bit word of the half is a
little-endian lane), and again eight slots on in a spread register. -/

/-- The S-box at byte `j` of F's input: s1, s4, s3, s2, s4, s3, s2, s1 from
the least significant byte (§2.4.1). -/
def kind (j : Nat) : Nat := [0, 3, 2, 1, 3, 2, 1, 0].getD j 0

/-- Whether byte `j` is at a position of s4. -/
def isA (j : Nat) : Bool := kind j == 3

/-- The bytes of the S-boxes' output that make byte `j` of F's (§2.4.1's P). -/
def sets (j : Nat) : List Nat :=
  [[7, 4, 3, 2, 1], [5, 4, 3, 2, 0], [6, 5, 3, 1, 0], [7, 6, 2, 1, 0],
   [6, 5, 4, 3, 2, 1], [7, 6, 5, 3, 2, 0], [7, 6, 4, 3, 1, 0], [7, 5, 4, 2, 1, 0]].getD j []

/-- The slot of byte `j`. -/
def slot (j : Nat) : Nat := (j + 4) % 8

/-- The code's parameters: the table at `ebx`, the keys of a group at `esi`. -/
def params : Params := { tb := tbr, name := tableName, kreg := kr, klen := 128 }

/-- The registers on entry to a part of the code: the mask in `xmm7`. -/
def regs₀ : Regs := Regs.init.set m0 ⟨false, bytes fun _ => .cst 0x0f#8⟩

/-- The input bytes of slot `q` of register `r`, and of its spread half. -/
def var (r : XReg) (q : Nat) : Nat := 2 ^ (16 * r.ctorIdx + q)
def fold (r : XReg) (q : Nat) : Nat := var r q ^^^ var r (q + 8)

/-- A round's output byte in slot `q` of `y` (the two quadwords folded), as
the code leaves it: `y`'s own, and for each byte of the S-boxes' output that
P takes, its map by the two look-ups. -/
def roundRef (xr y : XReg) (q : Nat) : BV :=
  let j := slot q
  ⟨fold y q, (sets j).flatMap (fun i =>
    let k := kOf (isA j) (kind i)
    [⟨[.look (tblAt (oN k)), .xorc 0x0f#8, .and 0x0f#8, .aes], fold xr (slot i)⟩,
     ⟨[.look (tblAt (oN k + 16)), .hi4, .aes], fold xr (slot i)⟩]), 0#8⟩

/-- Round `i` of a group leaves `xr` with its eight key bytes added, `y` as
`roundRef`, and the mask. -/
def roundOk (xr y : XReg) (i : Nat) : Bool :=
  match run params regs₀ (round xr y i) with
  | none => false
  | some ρ =>
    !(ρ.get xr).sh && !(ρ.get y).sh && !(ρ.get m0).sh &&
    ((List.range 8).all fun q =>
      ((get (ρ.get y).bs q).xor (get (ρ.get y).bs (q + 8))).same (roundRef xr y q)) &&
    ((List.range 16).all fun q => (get (ρ.get xr).bs q).same
      ⟨var xr q ^^^ (if q < 8 then 2 ^ (128 + 16 + 8 * i + q) else 0), [], 0#8⟩) &&
    ((List.range 16).all fun q => (get (ρ.get m0).bs q).same (.cst 0x0f#8))

theorem round_all : ([0, 2, 4].all fun i => roundOk .xmm0 .xmm1 i) = true ∧
    ([1, 3, 5].all fun i => roundOk .xmm1 .xmm0 i) = true := by
  constructor <;> lit_decide

/-! ## The conversions -/

/-- The byte of a block, or of a pair of subkeys, that `BSW` puts in slot `q`. -/
def bswq (q : Nat) : Nat := if q < 4 then 3 - q else if q < 8 then 11 - q else if q < 12 then 19 - q else 27 - q

/-- The slot `OUTC` puts in byte `q` of the block. -/
def outq (q : Nat) : Nat := if q < 8 then 8 + bswq q else bswq (q - 8)

/-- The four look-ups of the byte map at `t`, of the input bytes `v`, in slot `q`. -/
def cterms (t q v : Nat) : List Term :=
  let m := byte (tblAt oM4) q
  [⟨[.look (tblAt t), .and 0x0f#8], v⟩, ⟨[.look (tblAt (t + 16)), .hi4], v⟩,
   ⟨[.look (tblAt (t + 32)), .and m, .and 0x0f#8], v⟩, ⟨[.look (tblAt (t + 48)), .and m, .hi4], v⟩]

/-- `xmm0` and `xmm1` hold the two quadwords `w`, each under a zero quadword. -/
def unpackOk (ρ : Regs) (w : Nat → BV) : Bool :=
  !(ρ.get .xmm0).sh && !(ρ.get .xmm1).sh &&
  (List.range 16).all fun q =>
    (get (ρ.get .xmm0).bs q).same (if q < 8 then w q else .zero) &&
      (get (ρ.get .xmm1).bs q).same (if q < 8 then w (q + 8) else .zero)

def maskOk (ρ : Regs) : Bool :=
  !(ρ.get m0).sh && (List.range 16).all fun q => (get (ρ.get m0).bs q).same (.cst 0x0f#8)

/-- The halves of the two registers, packed. -/
def pk (q : Nat) : Nat := if q < 8 then fold .xmm0 q else fold .xmm1 (q - 8)

def headOk : Bool :=
  match run params Regs.init headX with
  | none => false
  | some ρ => unpackOk ρ (fun q => ⟨2 ^ (128 + q), cterms oT q (var .xmm0 (bswq q)), 0#8⟩) && maskOk ρ

def layerInOk : Bool :=
  match run params regs₀ layerIn with
  | none => false
  | some ρ => !(ρ.get .xmm4).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm4).bs q).same ⟨0, cterms oI q (pk q), 0#8⟩) && maskOk ρ

def layerOutOk : Bool :=
  match run params regs₀ layerOut with
  | none => false
  | some ρ => unpackOk ρ (fun q => ⟨2 ^ (128 + 112 + q), cterms oT q (var .xmm4 q), 0#8⟩) && maskOk ρ

def tailOk : Bool :=
  match run params regs₀ tailX with
  | none => false
  | some ρ => !(ρ.get .xmm6).sh && (List.range 16).all fun q =>
    (get (ρ.get .xmm6).bs q).same ⟨2 ^ (128 + 64 + q), cterms oI (outq q) (pk (outq q)), 0#8⟩

theorem conv_all : headOk = true ∧ layerInOk = true ∧ layerOutOk = true ∧ tailOk = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> lit_decide

/-- The mask of the positions of s4, and the nibble tables at zero. -/
theorem m4_all : ((List.range 16).all fun q =>
    byte (tblAt oM4) q == (if isA (slot (q % 8)) = true then 0x0f#8 else 0#8)) = true := by
  lit_decide

/-! ## `prepare`'s code -/

/-- The constant a round adds at byte `j`. -/
def gc (j : Nat) : Byte := (sets j).foldr (fun i acc => mc (isA j) (kind i) ^^^ acc) 0#8

/-- `prepare` reads the schedule at `eax`, 80 bytes at a time, and stores
the keys of a group at `esi`. -/
def pparams : Params := { tb := tbr, name := tableName, kreg := .eax, klen := 80 }
def oparams : OParams := { oreg := kr, olen := 128 }

/-- Byte `q` of the two subkeys at byte `off` of the schedule, in the rounds'
form. -/
def pT (off q : Nat) : BV := ⟨0, cterms oT q (2 ^ (128 + (off + bswq q))), 0#8⟩

/-- Byte `q` of the constant at `t`. -/
def cb (t q : Nat) : BV := .cst (byte (tblAt t) q)

def prepHeadOk : Bool :=
  match run pparams Regs.init prepHeadX with
  | none => false
  | some ρ => !(ρ.get .xmm6).sh && ((List.range 16).all fun q => (get (ρ.get .xmm6).bs q).same (pT 0 q)) && maskOk ρ

def prepGroupOk : Bool :=
  match runS pparams oparams (regs₀, []) prepGroupX with
  | none => false
  | some σ =>
    outOk σ.2 0 (fun q => ((pT 16 q).xor (.var (16 * 6 + q))).xor (cb oCK q)) &&
    outOk σ.2 16 (fun q => ((pT 16 q).xor (pT 32 q)).xor (cb oGG q)) &&
    outOk σ.2 32 (fun q => ((pT 32 q).xor (pT 48 q)).xor (cb oGG q)) &&
    outOk σ.2 48 (fun q => (pT 48 q).xor (cb oCW2 q)) &&
    outsIn σ.2 0 64 &&
    !(σ.1.get .xmm6).sh && ((List.range 16).all fun q => (get (σ.1.get .xmm6).bs q).same .zero) && maskOk σ.1

/-- A mask of the FL layer: the subkeys' byte, with the constant at `n`,
under the mask at `m`. -/
def pM (n m q : Nat) : BV :=
  ⟨0, [⟨[.and (byte (tblAt m) q)], 2 ^ (128 + (64 + bswq q))⟩], byte (tblAt n) q &&& byte (tblAt m) q⟩

def prepMasksOk : Bool :=
  match runS pparams oparams (regs₀, []) prepMasksX with
  | none => false
  | some σ =>
    outOk σ.2 64 (pM oN1 oM1) && outOk σ.2 80 (pM oN2 oM2) &&
    outOk σ.2 96 (fun q => if q % 8 < 4 then .var (128 + (64 + bswq (q + 4))) else .zero) &&
    outsIn σ.2 64 112 &&
    !(σ.1.get .xmm6).sh && ((List.range 16).all fun q => (get (σ.1.get .xmm6).bs q).same (.var (16 * 6 + q))) &&
    maskOk σ.1

def prepTailOk : Bool :=
  match runS pparams oparams (regs₀, []) prepTail with
  | none => false
  | some σ => outOk σ.2 64 (fun q => .var (128 + (64 + q))) && outsIn σ.2 64 80 && maskOk σ.1

theorem prep_all : prepHeadOk = true ∧ prepGroupOk = true ∧ prepMasksOk = true ∧ prepTailOk = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> lit_decide

/-- The constants of the keys. -/
theorem pconst_all : ((List.range 8).all fun j =>
    byte (tblAt oCK) (slot j) == c5 && byte (tblAt oCK) (slot j + 8) == c5 ^^^ gc j &&
    byte (tblAt oGG) (slot j) == gc j && byte (tblAt oGG) (slot j + 8) == gc j &&
    byte (tblAt oCW2) (slot j) == gc j ^^^ c5 && byte (tblAt oCW2) (slot j + 8) == c5) = true := by
  lit_decide

/-- The constants of the FL layer's masks, by doublewords. -/
theorem pmask_all :
    (dword (tblAt oN1) 0 == 0#32 && dword (tblAt oN1) 1 == 0#32 && dword (tblAt oN1) 2 == 0#32 &&
     dword (tblAt oN1) 3 == BitVec.allOnes 32 &&
     dword (tblAt oM1) 0 == BitVec.allOnes 32 && dword (tblAt oM1) 1 == 0#32 && dword (tblAt oM1) 2 == 0#32 &&
     dword (tblAt oM1) 3 == BitVec.allOnes 32 &&
     dword (tblAt oN2) 0 == 0#32 && dword (tblAt oN2) 1 == BitVec.allOnes 32 && dword (tblAt oN2) 2 == 0#32 &&
     dword (tblAt oN2) 3 == 0#32 &&
     dword (tblAt oM2) 0 == 0#32 && dword (tblAt oM2) 1 == BitVec.allOnes 32 &&
     dword (tblAt oM2) 2 == BitVec.allOnes 32 && dword (tblAt oM2) 3 == 0#32) = true := by
  lit_decide

end VG.Proof.Camellia.X86.AesNi
