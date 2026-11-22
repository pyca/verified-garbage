module

public import VerifiedGarbage.Impl.Sm4.X86.AesNi
meta import VerifiedGarbage.Impl.Sm4.X86.AesNi
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
public import VerifiedGarbage.Proof.Sm4.SboxTable
meta import VerifiedGarbage.Proof.Sm4.SboxTable
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SM4's S-box by the AES S-box: the byte maps

The byte maps of `Impl/Sm4/X86/AesNi.lean`, as functions of a byte read
from its table of constants, and what they are of SM4's S-box (GB/T
32907-2016 §6.2, `Spec.Sm4.sbox`) and of the bytes of `L` (`lm1`, `lm3`),
each a fact about the 256 bytes that the kernel evaluates:

* `pl` (into the rounds' form) and `pv` (out of it) are inverse and linear,
  and `pk` is `pl` and a constant;
* `sbox_all`: the two maps after the AES S-box, of the AES S-box of `pk b`,
  are `pl (lm1 (S b))`, and `pl (lm3 (S b))` and a constant.

And what the straight-line parts of the code leave in the registers and
store, as expressions of the bytes they start with
(`Proof/Framework/X86/ByteMap.lean`), each compared by the kernel with the
expression the proofs use: the two rounds of a turn (`round_all`), the
conversions at the two ends (`conv_all`), and a group of `prepare`
(`prep_all`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNi

open VG VG.X86 VG.X86.ByteMap VG.Impl.Sm4.X86.AesNi

/-- The 16 bytes at `off` of the table of constants. -/
def tblAt (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

/-- `pshufb`'s look-up in the constant at `off`. -/
def lk (off : Nat) (b : Byte) : Byte := Fn.eval (.look (tblAt off)) b

/-- The byte map at `t`: the look-ups of the two nibbles. -/
def nm (t : Nat) (b : Byte) : Byte := lk t (b &&& 0x0f#8) ^^^ lk (t + 16) (b >>> 4)

/-- Into the rounds' form. -/
def pl (b : Byte) : Byte := nm oCV b
/-- Out of it. -/
def pv (b : Byte) : Byte := nm oIV b
/-- A round key's byte: `pl` and the constant of the map before the S-box. -/
def pk (b : Byte) : Byte := nm oK b

/-- The map at `t` (`oE` or `oH`) after the AES S-box, whose key is the
mask `0x0f`. -/
def am (t : Nat) (z : Byte) : Byte := lk t ((z &&& 0x0f#8) ^^^ 0x0f#8) ^^^ lk (t + 16) (z >>> 4)

/-- The bytes of `L` (§6.2): of a byte and of the two after it, and of the
third after it; a byte's own is their exclusive-or. -/
def lm1 (b : Byte) : Byte := (b >>> 6) ^^^ (b <<< 2)
def lm3 (b : Byte) : Byte := (b >>> 6) ^^^ b

/-- A byte's own: `lm1 ⊕ lm3` (`lm_all`). -/
def lm0 (b : Byte) : Byte := b ^^^ (b <<< 2)

/-- The bits of the three, and `lm0` as the two. -/
theorem lm_all : ((List.range 256).all fun n => (List.range 8).all fun j =>
    lm0 (BitVec.ofNat 8 n) == lm1 (BitVec.ofNat 8 n) ^^^ lm3 (BitVec.ofNat 8 n) &&
    (lm0 (BitVec.ofNat 8 n)).getLsbD j ==
      ((BitVec.ofNat 8 n).getLsbD j ^^ (decide (2 ≤ j) && (BitVec.ofNat 8 n).getLsbD (j - 2))) &&
    (lm1 (BitVec.ofNat 8 n)).getLsbD j ==
      ((decide (j < 2) && (BitVec.ofNat 8 n).getLsbD (j + 6)) ^^ (decide (2 ≤ j) && (BitVec.ofNat 8 n).getLsbD (j - 2))) &&
    (lm3 (BitVec.ofNat 8 n)).getLsbD j ==
      ((decide (j < 2) && (BitVec.ofNat 8 n).getLsbD (j + 6)) ^^ (BitVec.ofNat 8 n).getLsbD j)) = true := by
  lit_decide

/-- The constant of `H`. -/
def ch : Byte := am oH (aesSbox (pk 0#8)) ^^^ pl (lm3 (Proof.Sm4.sboxB 0#8))

theorem sbox_all : ((List.range 256).all fun n =>
    am oE (aesSbox (pk (BitVec.ofNat 8 n))) == pl (lm1 (Proof.Sm4.sboxB (BitVec.ofNat 8 n))) &&
    am oH (aesSbox (pk (BitVec.ofNat 8 n))) == pl (lm3 (Proof.Sm4.sboxB (BitVec.ofNat 8 n))) ^^^ ch) = true := by
  lit_decide

theorem inv_all : ((List.range 256).all fun n =>
    pv (pl (BitVec.ofNat 8 n)) == BitVec.ofNat 8 n && pk (BitVec.ofNat 8 n) == pl (BitVec.ofNat 8 n) ^^^ pk 0#8) = true := by
  lit_decide

/-- The nibble tables of the byte maps are linear. -/
theorem lin16_all : ((List.range 16).all fun x => (List.range 16).all fun y =>
    [oCV, oCV + 16, oIV, oIV + 16].all fun t =>
      lk t (BitVec.ofNat 8 (x ^^^ y)) == lk t (BitVec.ofNat 8 x) ^^^ lk t (BitVec.ofNat 8 y)) = true := by
  lit_decide

/-! ## A round -/

/-- A round's code: the table at `ebx`, the entries at `esi`, of which it
reads the 128 bytes of four, and its word's place at `ecx`. -/
def params : Params := { tb := tbr, name := tableName, kreg := kr, klen := 128 }
def oparams : OParams := { oreg := kw, olen := 48 }

/-- The registers on entry to a part of the code: the mask in `xmm7`. -/
def regs₀ : Regs := Regs.init.set m0 ⟨false, bytes fun _ => .cst 0x0f#8⟩

/-- The input byte `q` of register `r`, and the input byte at `o` of the entries. -/
def var (r : XReg) (q : Nat) : Nat := 2 ^ (16 * r.ctorIdx + q)
def kv (o : Nat) : Nat := 2 ^ (128 + o)

/-- The byte that the rotation by `k` bytes puts at `q`. -/
def br (k q : Nat) : Nat := 4 * (q / 4) + (q % 4 + k) % 4

/-- The map at `t` of `aesenclast`'s byte at `p`, of the register `a`. -/
def aT (t : Nat) (a : XReg) (p : Nat) : List Term :=
  [⟨[.look (tblAt t), .xorc 0x0f#8, .and 0x0f#8, .aes], var a (srow p)⟩,
   ⟨[.look (tblAt (t + 16)), .hi4, .aes], var a (srow p)⟩]

/-- A round's sum at byte `q`: `E ⊕ H ⊕ rot¹ E ⊕ rot² E ⊕ rot³ H`. -/
def sigma (a : XReg) (q : Nat) : List Term :=
  aT oE a q ++ aT oH a q ++ aT oE a (br 1 q) ++ aT oE a (br 2 q) ++ aT oH a (br 3 q)

def maskOk (ρ : Regs) : Bool :=
  !(ρ.get m0).sh && (List.range 16).all fun q => (get (ρ.get m0).bs q).same (.cst 0x0f#8)

/-- Round `r` of a turn leaves, in `c`, its word and sum with the next
round's key and the two words after its own that it read or had; in `e`
and at its word's place, its word and sum; and the mask. -/
def roundOk (a c n e : XReg) (r : Nat) : Bool :=
  match runS params oparams (regs₀, []) (round a c n e r) with
  | none => false
  | some σ =>
    !(σ.1.get c).sh && !(σ.1.get e).sh &&
    ((List.range 16).all fun q => (get (σ.1.get c).bs q).same
      ⟨kv (32 * r + 16 + q) ^^^ kv (32 * r + 32 + q) ^^^ kv (32 * r + 80 + q) ^^^ var n q, sigma a q, 0#8⟩) &&
    ((List.range 16).all fun q => (get (σ.1.get e).bs q).same ⟨kv (32 * r + 16 + q), sigma a q, 0#8⟩) &&
    outOk σ.2 (32 * r) (fun q => ⟨kv (32 * r + 16 + q), sigma a q, 0#8⟩) && outsIn σ.2 (32 * r) (32 * r + 16) &&
    maskOk σ.1

theorem round_all : roundOk .xmm0 .xmm4 .xmm1 .xmm2 0 = true ∧ roundOk .xmm4 .xmm0 .xmm2 .xmm1 1 = true := by
  constructor <;> lit_decide

/-! ## The conversions -/

/-- The two look-ups of the byte map at `t`, of the input bytes `v`. -/
def cterms (t v : Nat) : List Term :=
  [⟨[.look (tblAt t), .and 0x0f#8], v⟩, ⟨[.look (tblAt (t + 16)), .hi4], v⟩]

/-- `headX` reads nothing but the table, and stores the block's four words
at `esi`. -/
def hparams : Params := { tb := tbr, name := tableName, kreg := kr, klen := 0 }
def hoparams : OParams := { oreg := kr, olen := 128 }

/-- Byte `q` of word `w` of the block in `xmm0`, in the rounds' form. -/
def hw (w q : Nat) : BV := ⟨0, cterms oCV (var .xmm0 (4 * w + q % 4)), 0#8⟩

def headOk : Bool :=
  match runS hparams hoparams (Regs.init, []) headX with
  | none => false
  | some σ =>
    outOk σ.2 16 (hw 0) && outOk σ.2 48 (hw 1) && outOk σ.2 80 (hw 2) && outOk σ.2 112 (hw 3) &&
    (σ.2.map fun e => e.1) == [112, 80, 48, 16] &&
    !(σ.1.get .xmm0).sh && !(σ.1.get .xmm1).sh &&
    ((List.range 16).all fun q => (get (σ.1.get .xmm0).bs q).same (((hw 1 q).xor (hw 2 q)).xor (hw 3 q)) &&
      (get (σ.1.get .xmm1).bs q).same (hw 3 q)) && maskOk σ.1

/-- The block's byte `q` from the last four entries: word `35 - q / 4`, out
of the rounds' form. -/
def tailOk : Bool :=
  match run params regs₀ tailX with
  | none => false
  | some ρ => !(ρ.get .xmm2).sh && (List.range 16).all fun q =>
    (get (ρ.get .xmm2).bs q).same ⟨0, cterms oIV (kv (32 * (3 - q / 4) + 16 + q % 4)), 0#8⟩

theorem conv_all : headOk = true ∧ tailOk = true := by
  constructor <;> lit_decide

/-! ## `prepare`'s code -/

/-- `prepare` reads the schedule at `eax`, 16 bytes at a time, and stores
four round keys in the entries at `esi`. -/
def pparams : Params := { tb := tbr, name := tableName, kreg := .eax, klen := 16 }
def poparams : OParams := { oreg := kr, olen := 112 }

/-- Byte `q` of round key `w` of the four: the schedule's words are
little-endian. -/
def pw (w q : Nat) : BV := ⟨0, cterms oK (kv (4 * w + (3 - q % 4))), 0#8⟩

def prepGroupOk : Bool :=
  match runS pparams poparams (regs₀, []) prepGroupX with
  | none => false
  | some σ =>
    outOk σ.2 0 (pw 0) && outOk σ.2 32 (pw 1) && outOk σ.2 64 (pw 2) && outOk σ.2 96 (pw 3) &&
    outsIn σ.2 0 112 && maskOk σ.1

/-- The mask's load. -/
def prepMaskOk : Bool :=
  match run pparams Regs.init [tb m0 oM0] with
  | none => false
  | some ρ => maskOk ρ

theorem prep_all : prepGroupOk = true ∧ prepMaskOk = true := by
  constructor <;> lit_decide

end VG.Proof.Sm4.X86.AesNi
