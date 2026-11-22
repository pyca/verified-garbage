module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiKey
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiKey
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
public import VerifiedGarbage.Proof.Sm4.SboxTable
meta import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Proof.Sm4.Bitsliced
meta import VerifiedGarbage.Proof.Sm4.Bitsliced
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The SM4 key schedule by the AES S-box: the byte maps

The byte maps of `Impl/Sm4/X86/AesNiKey.lean`, as functions of a byte read
from its table of constants, and what they are of SM4's S-box (GB/T
32907-2016 §6.2, `Spec.Sm4.sbox`), of the bytes of `L'` (`kn`), and of the
constants `FK` and `CK` (§7.3), each a fact about bytes that the kernel
evaluates:

* `pl` (into the rounds' form) is linear and `pv` (out of it) its inverse;
  `pk` is `pl` and a constant;
* `sbox_all`: the map `r` after the AES S-box, of the AES S-box of `pk b`,
  is `pl (kn r (S b))`;
* `consts_all`: the table's rows of `FK` and `CK` are `pl` of `FK`'s bytes
  and `pk` of `CK`'s.

And what the straight-line parts of the code leave in the registers and
store, as expressions of the bytes they start with
(`Proof/Framework/X86/ByteMap.lean`), each compared by the kernel with the
expression the proofs use: the copy of the constants (`stage_ok`), the
key's words (`head_ok`), the two halves of each of a turn's four rounds
(`round_all`), and the turn's round keys (`out_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNiKey

open VG VG.X86 VG.X86.ByteMap VG.Impl.Sm4.X86.AesNiKey
open VG.Proof.Sm4 (sboxB byteAt)

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
/-- The constant of the map before the S-box: the table's `CK₀` starts with
that map of zero. -/
def c0 : Byte := byte (tblAt oCK) 0
/-- The map before the S-box: `pl` and its constant. -/
def pk (b : Byte) : Byte := pl b ^^^ c0

/-- The map at `t` after the AES S-box, whose key is the mask `0x0f`. -/
def am (t : Nat) (z : Byte) : Byte := lk t ((z &&& 0x0f#8) ^^^ 0x0f#8) ^^^ lk (t + 16) (z >>> 4)

/-- The bytes of `L'` (§7.3): byte `j` of `L'(B)` is the exclusive-or of
`kn r` of the byte `r` places on, `r` from 0 to 3. -/
def kn : Nat → Byte → Byte
  | 0, b => b
  | 1, b => b <<< 5
  | 2, b => (b >>> 3) ^^^ (b <<< 7)
  | _, b => b >>> 1

/-- Their bits. -/
theorem kn_all : ((List.range 256).all fun n => (List.range 8).all fun j =>
    (kn 1 (BitVec.ofNat 8 n)).getLsbD j == (decide (5 ≤ j) && (BitVec.ofNat 8 n).getLsbD (j - 5)) &&
    (kn 2 (BitVec.ofNat 8 n)).getLsbD j ==
      ((decide (j < 5) && (BitVec.ofNat 8 n).getLsbD (j + 3)) ^^ (decide (j = 7) && (BitVec.ofNat 8 n).getLsbD 0)) &&
    (kn 3 (BitVec.ofNat 8 n)).getLsbD j == (decide (j < 7) && (BitVec.ofNat 8 n).getLsbD (j + 1))) = true := by
  lit_decide

theorem sbox_all : ((List.range 256).all fun n => (List.range 4).all fun r =>
    am (oQ + 32 * r) (aesSbox (pk (BitVec.ofNat 8 n))) == pl (kn r (sboxB (BitVec.ofNat 8 n)))) = true := by
  lit_decide

theorem inv_all : ((List.range 256).all fun n => pv (pl (BitVec.ofNat 8 n)) == BitVec.ofNat 8 n) = true := by
  lit_decide

/-- The nibble tables of `pl` are linear. -/
theorem lin16_all : ((List.range 16).all fun x => (List.range 16).all fun y =>
    [oCV, oCV + 16].all fun t =>
      lk t (BitVec.ofNat 8 (x ^^^ y)) == lk t (BitVec.ofNat 8 x) ^^^ lk t (BitVec.ofNat 8 y)) = true := by
  lit_decide

/-- The rows of `FK` and of `CK`. -/
theorem consts_all :
    ((List.range 4).all fun w => (List.range 4).all fun j =>
      byte (tblAt oFK) (4 * w + j) == pl (byteAt (Spec.Sm4.fk.getD w 0) j)) = true ∧
    ((List.range 32).all fun i => (List.range 4).all fun j =>
      byte (tblAt (oCK + 16 * (i / 4))) (4 * (i % 4) + j) == pk (byteAt (Spec.Sm4.ck i) j)) = true := by
  constructor <;> lit_decide

/-! ## The code -/

/-- The registers on entry to a part of the code: the mask in `xmm7`. -/
def regs₀ : Regs := Regs.init.set m0 ⟨false, bytes fun _ => .cst 0x0f#8⟩

/-- The input byte `q` of register `r`, and the input byte at `o` of the keys' region. -/
def var (r : XReg) (q : Nat) : Nat := 2 ^ (16 * r.ctorIdx + q)
def kv (o : Nat) : Nat := 2 ^ (128 + o)

def maskOk (ρ : Regs) : Bool :=
  !(ρ.get m0).sh && (List.range 16).all fun q => (get (ρ.get m0).bs q).same (.cst 0x0f#8)

/-- Register `r` is as on entry. -/
def keeps (ρ : Regs) (r : XReg) : Bool :=
  !(ρ.get r).sh && (List.range 16).all fun q => (get (ρ.get r).bs q).same ⟨var r q, [], 0#8⟩

/-- The two look-ups of the byte map at `t`, of the input bytes `v`. -/
def cterms (t v : Nat) : List Term :=
  [⟨[.look (tblAt t), .and 0x0f#8], v⟩, ⟨[.look (tblAt (t + 16)), .hi4], v⟩]

/-- The map at `t` of `aesenclast`'s byte at `p`, of the register `a`. -/
def aT (t : Nat) (a : XReg) (p : Nat) : List Term :=
  [⟨[.look (tblAt t), .xorc 0x0f#8, .and 0x0f#8, .aes], var a (srow p)⟩,
   ⟨[.look (tblAt (t + 16)), .hi4, .aes], var a (srow p)⟩]

/-- The copy of the constants reads nothing but the table, and stores its
eight rows at `edx`. -/
def sparams : Params := { tb := tbr, name := tableName, kreg := .ecx, klen := 0 }
def soparams : OParams := { oreg := kp, olen := 128 }

def stageOk : Bool :=
  match runS sparams soparams (Regs.init, []) stage with
  | none => false
  | some σ =>
    ((List.range 8).all fun m => outOk σ.2 (16 * m) fun q => .cst (byte (tblAt (oCK + 16 * m)) q)) &&
      outsIn σ.2 0 128

theorem stage_ok : stageOk = true := by lit_decide

/-- `headX` reads the key at `ecx`. -/
def hparams : Params := { tb := tbr, name := tableName, kreg := .ecx, klen := 16 }

/-- Byte `q` of word `w` of the key with `FK`, in the rounds' form. -/
def hw (w q : Nat) : BV := ⟨0, cterms oCV (kv (4 * w + q % 4)), byte (tblAt oFK) (4 * w + q % 4)⟩

def headOk : Bool :=
  match run hparams Regs.init headX with
  | none => false
  | some ρ =>
    ((List.range 4).all fun w => !(ρ.get (xreg w)).sh &&
      (List.range 16).all fun q => (get (ρ.get (xreg w)).bs q).same (hw w q)) && maskOk ρ

theorem head_ok : headOk = true := by lit_decide

/-- A round's first half reads the turn's row at `edx`. -/
def pparams : Params := { tb := tbr, name := tableName, kreg := kp, klen := 16 }
/-- Its second half, and the turn's round keys, read nothing but the table. -/
def rparams : Params := { tb := tbr, name := tableName, kreg := kp, klen := 0 }

/-- The words' registers: word `i mod 4`'s. -/
def vr (i : Nat) : XReg := xreg (i % 4)

/-- The first half of round `w` of a turn leaves in `xmm4`, in every byte
of lane `l`, byte `l` of the exclusive-or of constant `w` of the row and of
the first lanes of `v1`, `v2` and `v3`; and the words and the mask as they
were. -/
def prepOk (v1 v2 v3 : XReg) (w : Nat) : Bool :=
  match run pparams regs₀ (prepX v1 v2 v3 w) with
  | none => false
  | some ρ =>
    !(ρ.get .xmm4).sh && ((List.range 16).all fun i => (get (ρ.get .xmm4).bs i).same
      ⟨kv (4 * w + i / 4) ^^^ var v1 (i / 4) ^^^ var v2 (i / 4) ^^^ var v3 (i / 4), [], 0#8⟩) &&
    keeps ρ .xmm0 && keeps ρ .xmm1 && keeps ρ .xmm2 && keeps ρ .xmm3 && maskOk ρ

/-- The second half adds to the first lane of `v0`, at byte `q`, the map
`r` of the S-box of `xmm4`'s byte `q` of lane `r`, as ShiftRows moves it,
for `r` from 0 to 3; and leaves the other words and the mask as they were. -/
def roundOk (v0 : XReg) : Bool :=
  match run rparams regs₀ (roundX v0) with
  | none => false
  | some ρ =>
    !(ρ.get v0).sh && ((List.range 4).all fun q => (get (ρ.get v0).bs q).same
      ⟨var v0 q, (List.range 4).flatMap fun r => aT (oQ + 32 * r) .xmm4 (4 * r + q), 0#8⟩) &&
    ([XReg.xmm0, .xmm1, .xmm2, .xmm3].all fun u => u == v0 || keeps ρ u) && maskOk ρ

/-- The four rounds of a turn, with their registers. -/
theorem round_all : ∀ w < 4, prepOk (vr (w + 1)) (vr (w + 2)) (vr (w + 3)) w = true ∧ roundOk (vr w) = true := by
  lit_decide

/-- The turn's round keys in `xmm4`: byte `q` is byte `3 - q mod 4` of word
`q / 4`, out of the rounds' form. -/
def outOk' : Bool :=
  match run rparams regs₀ outX with
  | none => false
  | some ρ => !(ρ.get .xmm4).sh && ((List.range 16).all fun q => (get (ρ.get .xmm4).bs q).same
      ⟨0, cterms oIV (var (xreg (q / 4)) (3 - q % 4)), 0#8⟩) &&
    keeps ρ .xmm0 && keeps ρ .xmm1 && keeps ρ .xmm2 && keeps ρ .xmm3 && maskOk ρ

theorem out_ok : outOk' = true := by lit_decide

end VG.Proof.Sm4.X86.AesNiKey
