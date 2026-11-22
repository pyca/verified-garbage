module

public import VerifiedGarbage.Impl.Seed.X86.AesNi
meta import VerifiedGarbage.Impl.Seed.X86.AesNi
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
public import VerifiedGarbage.Proof.Seed.G
meta import VerifiedGarbage.Proof.Seed.G
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SEED's S-boxes by the AES S-box: the byte maps

The byte maps of `Impl/Seed/X86/AesNi.lean`, as functions of a byte read
from its table of constants, and what they are of SEED's S-boxes (RFC 4269
Appendix A.1, `Spec.Seed.s0` and `s1`) and of G's masks (§2.2), each a fact
that the kernel evaluates:

* `sbox_all`: the map after the AES S-box for `S0`, and the one for `S1`,
  of the AES S-box of the map before it of a byte, are `S0` and `S1` of the
  byte, for the 256 bytes;
* `ka_all`: the masks by position keep, at byte `i` of lane `c`, the bytes
  of the S-box of the word's byte `(c + i) mod 4`, under the mask `m` of
  that byte for the output byte `i`.

And what the straight-line parts of the code leave in the registers and
store, as expressions of the bytes they start with
(`Proof/Framework/X86/ByteMap.lean`), each compared by the kernel with the
expression the proofs use: the two parts of G (`g_all`), the start and the
end of the two rounds of a turn (`round_all`), the block's words at the two
ends (`ends_all`), and a group of `prepare` (`prep_ok`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNi

open VG VG.X86 VG.X86.ByteMap VG.Impl.Seed.X86.AesNi
open VG.Proof.Seed (sNat maskOf)

/-- The 16 bytes at `off` of the table of constants. -/
def tblAt (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

/-- `pshufb`'s look-up in the constant at `off`. -/
def lk (off : Nat) (b : Byte) : Byte := Fn.eval (.look (tblAt off)) b

/-- The map before the S-box: the look-ups of the two nibbles. -/
def pre (b : Byte) : Byte := lk oPRE (b &&& 0x0f#8) ^^^ lk (oPRE + 16) (b >>> 4)

/-- The map at `t` (`oP0` or `oP1`) after the AES S-box, whose key is the
mask `0x0f`. -/
def am (t : Nat) (z : Byte) : Byte := lk t ((z &&& 0x0f#8) ^^^ 0x0f#8) ^^^ lk (t + 16) (z >>> 4)

/-- The mask at byte `p` of the masks by position at `t` (`oKA` or `oKA + 16`). -/
def ka (t p : Nat) : Byte := byte (tblAt t) p

theorem sbox_all : ((List.range 256).all fun n =>
    am oP0 (aesSbox (pre (BitVec.ofNat 8 n))) == BitVec.ofNat 8 (sNat false n) &&
    am oP1 (aesSbox (pre (BitVec.ofNat 8 n))) == BitVec.ofNat 8 (sNat true n)) = true := by
  lit_decide

theorem ka_all : ((List.range 16).all fun p =>
    ka oKA p == (if (p / 4 + p % 4) % 2 = 0 then maskOf ((2 * (p % 4) + p / 4) % 4) else 0#8) &&
    ka (oKA + 16) p == (if (p / 4 + p % 4) % 2 = 1 then maskOf ((2 * (p % 4) + p / 4) % 4) else 0#8)) = true := by
  lit_decide

/-! ## G -/

/-- The code of the rounds reads the table at `ebx`, and the scratch buffer
at `edi`, whose first 96 bytes end with the four places of the state's
halves. -/
def params : Params := { tb := tbr, name := tableName, kreg := Impl.Modes.X86.sb, klen := 96 }

/-- The registers on entry to a part of the code: the mask in `xmm7`. -/
def regs₀ : Regs := Regs.init.set m0 ⟨false, bytes fun _ => .cst 0x0f#8⟩

/-- The input byte `q` of register `r`, and the input byte at `o` of the keys' region. -/
def var (r : XReg) (q : Nat) : Nat := 2 ^ (16 * r.ctorIdx + q)
def kv (o : Nat) : Nat := 2 ^ (128 + o)

def maskOk (ρ : Regs) : Bool :=
  !(ρ.get m0).sh && (List.range 16).all fun q => (get (ρ.get m0).bs q).same (.cst 0x0f#8)

/-- The register `r` holds what it started with. -/
def keeps (ρ : Regs) (r : XReg) : Bool :=
  !(ρ.get r).sh && (List.range 16).all fun q => (get (ρ.get r).bs q).same ⟨var r q, [], 0#8⟩

/-- The two look-ups of the map before the S-box, of the input bytes `v`. -/
def cterms (v : Nat) : List Term :=
  [⟨[.look (tblAt oPRE), .and 0x0f#8], v⟩, ⟨[.look (tblAt (oPRE + 16)), .hi4], v⟩]

/-- `gPre` leaves in byte `q` of `xmm2` the map before the S-box of byte
`q / 4` of `xmm0`, and keeps `xmm5`, `xmm6` and the mask. -/
def gPreOk : Bool :=
  match run params regs₀ gPre with
  | none => false
  | some ρ =>
    !(ρ.get .xmm2).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm2).bs q).same ⟨0, cterms (var .xmm0 (q / 4)), 0#8⟩) &&
    keeps ρ .xmm5 && keeps ρ .xmm6 && maskOk ρ

/-- The map at `t` after the S-box of `aesenclast`'s byte at `p`, of
`xmm2`, under the mask `c`. -/
def aT (t : Nat) (c : Byte) (p : Nat) : List Term :=
  [⟨[.and c, .look (tblAt t), .xorc 0x0f#8, .and 0x0f#8, .aes], var .xmm2 (srow p)⟩,
   ⟨[.and c, .look (tblAt (t + 16)), .hi4, .aes], var .xmm2 (srow p)⟩]

/-- Lane `c`'s byte for the output byte `q`: both maps, each under its mask
of the position. -/
def laneT (c q : Nat) : List Term :=
  aT oP0 (ka oKA (4 * c + q % 4)) (4 * c + q % 4) ++ aT oP1 (ka (oKA + 16) (4 * c + q % 4)) (4 * c + q % 4)

/-- G's output byte `q`: the four lanes. -/
def gT (q : Nat) : List Term := laneT 0 q ++ laneT 1 q ++ laneT 2 q ++ laneT 3 q

/-- `gPost` leaves `gT` of `xmm2` in `xmm0`, and keeps `xmm5`, `xmm6` and
the mask. -/
def gPostOk : Bool :=
  match run params regs₀ gPost with
  | none => false
  | some ρ =>
    !(ρ.get .xmm0).sh && ((List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same ⟨0, gT q, 0#8⟩) &&
    keeps ρ .xmm5 && keeps ρ .xmm6 && maskOk ρ

theorem g_all : gPreOk = true ∧ gPostOk = true := by
  constructor <;> lit_decide

/-! ## A round's start and end -/

/-- A round's start reads its keys at `esi`, and stores the right half in
the scratch buffer. -/
def kparams : Params := { tb := tbr, name := tableName, kreg := kr, klen := 64 }
def koparams : OParams := { oreg := Impl.Modes.X86.sb, olen := 96 }

/-- Round `h`'s start stores `xmm5` and `xmm0` at the places `2 - 2 h` and
`3 - 2 h`, and adds the keys at `32 h` and `32 h + 16` to them. -/
def keyOk (h : Nat) : Bool :=
  match runS kparams koparams (regs₀, []) (keyX h) with
  | none => false
  | some σ =>
    outOk σ.2 (oR + 16 * (2 - 2 * h)) (fun q => ⟨var .xmm5 q, [], 0#8⟩) &&
    outOk σ.2 (oR + 16 * (3 - 2 * h)) (fun q => ⟨var .xmm0 q, [], 0#8⟩) &&
    (σ.2.map fun e => e.1) == [oR + 16 * (3 - 2 * h), oR + 16 * (2 - 2 * h)] &&
    !(σ.1.get .xmm5).sh && !(σ.1.get .xmm0).sh &&
    ((List.range 16).all fun q =>
      (get (σ.1.get .xmm5).bs q).same ⟨var .xmm5 q ^^^ kv (32 * h + q), [], 0#8⟩ &&
      (get (σ.1.get .xmm0).bs q).same ⟨var .xmm0 q ^^^ kv (32 * h + 16 + q), [], 0#8⟩) && maskOk σ.1

/-- Round `h`'s end adds the places `2 h` and `2 h + 1` to `xmm5` and `xmm0`. -/
def leftOk (h : Nat) : Bool :=
  match run params regs₀ (leftX h) with
  | none => false
  | some ρ =>
    !(ρ.get .xmm5).sh && !(ρ.get .xmm0).sh &&
    ((List.range 16).all fun q =>
      (get (ρ.get .xmm5).bs q).same ⟨var .xmm5 q ^^^ kv (oR + 32 * h + q), [], 0#8⟩ &&
      (get (ρ.get .xmm0).bs q).same ⟨var .xmm0 q ^^^ kv (oR + 32 * h + 16 + q), [], 0#8⟩) && maskOk ρ

theorem round_all : ∀ h < 2, keyOk h = true ∧ leftOk h = true := by
  lit_decide

/-! ## The block's words -/

/-- `headX` reads nothing but the table, and stores the block's first two
words in their places. -/
def hparams : Params := { tb := tbr, name := tableName, kreg := kr, klen := 0 }

/-- Byte `q` of a register that holds word `w` of the block in `xmm0` in
every lane: the block's words are big-endian. -/
def hw (w q : Nat) : BV := ⟨var .xmm0 (4 * w + (3 - q % 4)), [], 0#8⟩

def headOk : Bool :=
  match runS hparams koparams (Regs.init, []) headX with
  | none => false
  | some σ =>
    outOk σ.2 oR (hw 0) && outOk σ.2 (oR + 16) (hw 1) && (σ.2.map fun e => e.1) == [oR + 16, oR] &&
    !(σ.1.get .xmm5).sh && !(σ.1.get .xmm0).sh &&
    ((List.range 16).all fun q => (get (σ.1.get .xmm5).bs q).same (hw 2 q) &&
      (get (σ.1.get .xmm0).bs q).same (hw 3 q)) && maskOk σ.1

/-- The block's byte `q` at the end: of `xmm5`, of `xmm0`, and of the first
two places, a word each, the most significant byte first. -/
def tw (q : Nat) : Nat :=
  if q / 4 = 0 then var .xmm5 (3 - q % 4) else if q / 4 = 1 then var .xmm0 (3 - q % 4)
  else kv (oR + 16 * (q / 4 - 2) + (3 - q % 4))

def tailOk : Bool :=
  match run params regs₀ tailX with
  | none => false
  | some ρ => !(ρ.get .xmm5).sh && (List.range 16).all fun q => (get (ρ.get .xmm5).bs q).same ⟨tw q, [], 0#8⟩

theorem ends_all : headOk = true ∧ tailOk = true := by
  constructor <;> lit_decide

/-! ## `prepare`'s code -/

/-- `prepare` reads the schedule at `eax`, 16 bytes at a time, and stores
four round keys in their places at `esi`. -/
def pparams : Params := { tb := tbr, name := tableName, kreg := .eax, klen := 16 }
def poparams : OParams := { oreg := kr, olen := 64 }

/-- Byte `q` of round key `w` of the four, in every lane. -/
def pw (w q : Nat) : BV := ⟨kv (4 * w + q % 4), [], 0#8⟩

def prepGroupOk : Bool :=
  match runS pparams poparams (Regs.init, []) prepGroupX with
  | none => false
  | some σ =>
    outOk σ.2 0 (pw 0) && outOk σ.2 16 (pw 1) && outOk σ.2 32 (pw 2) && outOk σ.2 48 (pw 3) && outsIn σ.2 0 64

theorem prep_ok : prepGroupOk = true := by
  lit_decide

end VG.Proof.Seed.X86.AesNi
