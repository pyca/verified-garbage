module

public import VerifiedGarbage.Impl.Camellia.X86.AesNi
meta import VerifiedGarbage.Impl.Camellia.X86.AesNi
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
public import VerifiedGarbage.Spec.Camellia
meta import VerifiedGarbage.Spec.Camellia
import VerifiedGarbage.Proof.Aes.X86.AesNi.Sbox
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Sbox
import VerifiedGarbage.Proof.Camellia.SboxTable
meta import VerifiedGarbage.Proof.Camellia.SboxTable
import VerifiedGarbage.Proof.Framework.AllBelow
meta import VerifiedGarbage.Proof.Framework.AllBelow
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

And what the straight-line parts of the code leave in the registers and
store, as expressions of the bytes they start with
(`Proof/Framework/X86/ByteMap.lean`), each compared by the kernel with the
expression the proofs use: the six rounds of a group (`round_all`), the
conversions at the two ends and around the FL layer (`conv_all`), and the
blocks of `prepare` (`prep_all`), with the constants the keys take
(`pconst_all`, `pmask_all`).
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

/-! ### The maps as numbers

`sbox_all` and `inv_all` are checked on tables of the maps, packed in
numbers: evaluating the maps (and the AES S-box) as functions of bytes at
each of the cases took the kernel a minute and a half. -/

/-- The constant at `16 u` of the table, as a number. -/
private def tN (u : Nat) : Nat := (tblAt (16 * u)).toNat

/-- `qT a` (row `a`) and `qI a` (row `2 + a`) at byte `n`. -/
private def qN (r n : Nat) : Nat :=
  Nat.xor (nibs (tN (4 * Nat.div r 2 + 4)) (tN (4 * Nat.div r 2 + 5)) n)
    (Nat.mul (Nat.mod r 2) (nibs (tN (4 * Nat.div r 2 + 6)) (tN (4 * Nat.div r 2 + 7)) n))

/-- `nmap k` at byte `n`. -/
private def nN (k n : Nat) : Nat := nibs (tN (2 * k + 12)) (tN (2 * k + 13)) (Nat.xor 15 n)

/-- `SBOX1` at byte `n`, from its truth tables. -/
private def s1N (n : Nat) : Nat := (Aes.row ((List.range 8).map Camellia.sbox1T) n).toNat

/-- `sb j` at byte `n`. -/
private def sN : Nat → Nat → Nat
  | 0, n => s1N n
  | 1, n => ((BitVec.ofNat 8 (s1N n)).rotateLeft 1).toNat
  | 2, n => ((BitVec.ofNat 8 (s1N n)).rotateLeft 7).toNat
  | _, n => s1N ((BitVec.ofNat 8 n).rotateLeft 1).toNat

private theorem sbox1_eq (b : Byte) : Spec.Camellia.sbox1 b = BitVec.ofNat 8 (s1N b.toNat) := by
  rw [s1N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (Aes.row_ext fun j hj => ?_).symm
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some,
    Camellia.testBit_sbox1T b.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem s1N_lt (n : Nat) : s1N n < 256 := BitVec.isLt _

private theorem sb_eq {j : Nat} (hj : j < 4) (b : Byte) : sb j b = BitVec.ofNat 8 (sN j b.toNat) := by
  have h (x : Byte) : BitVec.ofNat 8 x.toNat = x := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  match j, hj with
  | 0, _ => exact sbox1_eq b
  | 1, _ => rw [sN, h, ← sbox1_eq]; rfl
  | 2, _ => rw [sN, h, ← sbox1_eq]; rfl
  | 3, _ =>
    show Spec.Camellia.sbox1 _ = BitVec.ofNat 8 (s1N ((BitVec.ofNat 8 b.toNat).rotateLeft 1).toNat)
    rw [h, ← sbox1_eq]

private theorem sN_lt (j n : Nat) : sN j n < 256 := by
  unfold sN; split <;> exact BitVec.isLt _

private theorem qN_lt (r n : Nat) : qN r n < 256 := by
  refine Nat.xor_lt_two_pow (n := 8) (nibs_lt ..) ?_
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · rw [show Nat.mod r 2 = 0 from h, show Nat.mul 0 _ = 0 from Nat.zero_mul _]; decide
  · rw [show Nat.mod r 2 = 1 from h, show Nat.mul 1 _ = _ from Nat.one_mul _]; exact nibs_lt ..

private theorem qT_eq (a : Bool) (b : Byte) : qT a b = BitVec.ofNat 8 (qN a.toNat b.toNat) := by
  cases a
  · rw [qT, bmap, lk, lk, look_nibs, ite_eq_right Bool.false_ne_true, BitVec.xor_zero, qN]
    exact congrArg _ ((Nat.xor_zero _).symm.trans (congrArg _ (Nat.zero_mul _).symm))
  · rw [qT, bmap, lk, lk, look_nibs, ite_eq_left rfl, lk, lk, look_nibs, ← BitVec.ofNat_xor, qN]
    exact congrArg _ (congrArg _ (Nat.one_mul _).symm)

private theorem qI_eq (a : Bool) (b : Byte) : qI a b = BitVec.ofNat 8 (qN (2 + a.toNat) b.toNat) := by
  cases a
  · rw [qI, bmap, lk, lk, look_nibs, ite_eq_right Bool.false_ne_true, BitVec.xor_zero, qN]
    exact congrArg _ ((Nat.xor_zero _).symm.trans (congrArg _ (Nat.zero_mul _).symm))
  · rw [qI, bmap, lk, lk, look_nibs, ite_eq_left rfl, lk, lk, look_nibs, ← BitVec.ofNat_xor, qN]
    exact congrArg _ (congrArg _ (Nat.one_mul _).symm)

private theorem nmap_eq (k : Nat) (b : Byte) : nmap k b = BitVec.ofNat 8 (nN k b.toNat) := by
  rw [nmap, lk, lk, look_nibs_flip, nN, tN, tN, oN, show 16 * (2 * k + 12) = 192 + 32 * k by omega_arith,
    show 16 * (2 * k + 13) = 192 + 32 * k + 16 by omega_arith]
  rfl

materialize_table tN 20
materialize_table s1N 256
materialize_table sN 4 256
materialize_table qN 4 256
materialize_table nN 4 256

/-- The map after the AES S-box of `sbox_all`, at byte `n`. -/
private def fN (a j n : Nat) : Nat :=
  nN (kOf (Nat.beq a 1) j) (Aes.sboxN (Nat.xor (qN (cond (Nat.beq j 3) 1 0) n) (qN 0 0xc5)))

private theorem sbox_chk : allBelow (fun n => allBelow (fun a => allBelow (fun j =>
    Nat.beq (Nat.xor (qN a (sN j n)) (fN a j n)) (Nat.xor (qN a (sN j 0)) (fN a j 0))) 4) 2) 256 = true := by
  lit_decide

private theorem inv_chk : allBelow (fun n => allBelow (fun a =>
    Nat.beq (qN (2 + a) (qN a n)) n && Nat.beq (qN a (qN (2 + a) n)) n) 2) 256 = true := by
  lit_decide

theorem sbox_all : ((List.range 256).all fun n => [false, true].all fun ai => (List.range 4).all fun j =>
    qT ai (sb j (BitVec.ofNat 8 n)) ==
      nmap (kOf ai j) (aesSbox (qT (j == 3) (BitVec.ofNat 8 n) ^^^ c5)) ^^^ mc ai j) = true := by
  have h8 {n : Nat} (hn : n < 256) : (BitVec.ofNat 8 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hf (ai : Bool) {j n : Nat} (hj : j < 4) (hn : n < 256) :
      nmap (kOf ai j) (aesSbox (qT (j == 3) (BitVec.ofNat 8 n) ^^^ c5)) = BitVec.ofNat 8 (fN ai.toNat j n) := by
    have e₁ : (j == 3).toNat = cond (Nat.beq j 3) 1 0 := by
      revert j; decide
    have e₂ : kOf (Nat.beq ai.toNat 1) j = kOf ai j := by cases ai <;> rfl
    rw [c5, qT_eq, qT_eq, ← BitVec.ofNat_xor, Aes.X86.AesNi.aesSbox_eq_sboxN, nmap_eq, h8 hn, e₁,
      h8 (Nat.xor_lt_two_pow (n := 8) (qN_lt ..) (qN_lt ..)), h8 (Aes.sboxN_lt _), fN, e₂]
    rfl
  have hs (ai : Bool) {j n : Nat} (hj : j < 4) (hn : n < 256) :
      qT ai (sb j (BitVec.ofNat 8 n)) = BitVec.ofNat 8 (qN ai.toNat (sN j n)) := by
    rw [sb_eq hj, qT_eq, h8 hn, h8 (sN_lt ..)]
  refine List.all_eq_true.mpr fun n hn => List.all_eq_true.mpr fun ai _ => List.all_eq_true.mpr fun j hj => ?_
  have hn := List.mem_range.mp hn
  have hj := List.mem_range.mp hj
  have h := of_allBelow (of_allBelow (of_allBelow sbox_chk n hn) ai.toNat (by cases ai <;> decide)) j hj
  have h : BitVec.ofNat 8 (qN ai.toNat (sN j n) ^^^ fN ai.toNat j n) =
      BitVec.ofNat 8 (qN ai.toNat (sN j 0) ^^^ fN ai.toNat j 0) :=
    congrArg (BitVec.ofNat 8) (Nat.eq_of_beq_eq_true h)
  rw [mc, hs ai hj hn, hf ai hj hn, hs ai hj (by decide : 0 < 256), hf ai hj (by decide : 0 < 256), beq_iff_eq]
  rw [BitVec.ofNat_xor, BitVec.ofNat_xor] at h
  rw [← h, BitVec.xor_comm, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem inv_all : ((List.range 256).all fun n => [false, true].all fun a =>
    qI a (qT a (BitVec.ofNat 8 n)) == BitVec.ofNat 8 n && qT a (qI a (BitVec.ofNat 8 n)) == BitVec.ofNat 8 n) = true := by
  have h8 {n : Nat} (hn : n < 256) : (BitVec.ofNat 8 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine List.all_eq_true.mpr fun n hn => List.all_eq_true.mpr fun a _ => ?_
  have hn := List.mem_range.mp hn
  have h := of_allBelow (of_allBelow inv_chk n hn) a.toNat (by cases a <;> decide)
  rw [Bool.and_eq_true] at h
  rw [qT_eq, qI_eq, qI_eq, qT_eq, h8 hn, h8 (qN_lt ..), h8 (qN_lt ..), Nat.eq_of_beq_eq_true h.1,
    Nat.eq_of_beq_eq_true h.2, beq_self_eq_true, Bool.and_self]

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
