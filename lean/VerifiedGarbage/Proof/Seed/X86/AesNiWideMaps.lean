module

public import VerifiedGarbage.Impl.Seed.X86.AesNiWide
public import VerifiedGarbage.Proof.Seed.X86.AesNiMaps
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Seed.X86.AesNiWide
meta import VerifiedGarbage.Proof.Seed.X86.AesNiMaps
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED's S-boxes by the AES S-box, four blocks at a time: what the code computes of each byte

The byte maps of `Impl/Seed/X86/AesNiWide.lean`, as functions of a byte
read from its table of constants, and what they are of SEED's S-boxes
(`sbox_all`: the map after the AES S-box for `S0`, and that map with the
difference of the two, of the AES S-box of the map before it of a byte,
are `S0` and `S1` of the byte, for the 256 bytes).

And what the straight-line parts of the code leave in the registers and
store, as expressions of the bytes they start with
(`Proof/Framework/X86/ByteMap.lean`), each compared by the kernel with the
expression the proofs use: the two parts of G (`g_all`: at byte `i` of a
lane, the S-boxes of the lane's four bytes, each under its mask `m` for the
output byte `i`), the start and the end of the two rounds of a turn
(`round_all`), the four blocks' words at the two ends (`ends_all`), and a
group of `prepare` in each direction (`prep_all`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNiWide

open VG VG.X86 VG.X86.ByteMap VG.Impl.Seed.X86.AesNiWide
open VG.Impl.Seed.X86.AesNi (tbr kr m0)
open VG.Spec.Seed (Direction)
open VG.Proof.Seed (sNat maskOf)
open VG.Proof.Seed.X86.AesNi (var kv maskOk keeps regs₀)

/-- The 16 bytes at `off` of the table of constants. -/
def tblAt (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

/-- `pshufb`'s look-up in the constant at `off`. -/
def lk (off : Nat) (b : Byte) : Byte := Fn.eval (.look (tblAt off)) b

/-- The map before the S-box: the look-ups of the two nibbles. -/
def pre (b : Byte) : Byte := lk oPRE (b &&& 0x0f#8) ^^^ lk (oPRE + 16) (b >>> 4)

/-- The map at `t` (`oP0` or `oD`) after the AES S-box, whose key is the
mask `0x0f`. -/
def am (t : Nat) (z : Byte) : Byte := lk t ((z &&& 0x0f#8) ^^^ 0x0f#8) ^^^ lk (t + 16) (z >>> 4)

theorem sbox_all : ((List.range 256).all fun n =>
    am oP0 (aesSbox (pre (BitVec.ofNat 8 n))) == BitVec.ofNat 8 (sNat false n) &&
    (am oP0 (aesSbox (pre (BitVec.ofNat 8 n))) ^^^ am oD (aesSbox (pre (BitVec.ofNat 8 n)))) ==
      BitVec.ofNat 8 (sNat true n)) = true := by
  lit_decide

/-! ## G -/

/-- The code of the rounds reads the table at `ebx`, and the scratch buffer
at `edi`, whose first 96 bytes end with the five places. -/
def params : Params := { tb := tbr, name := tableName, kreg := Impl.Modes.X86.sb, klen := 96 }

/-- The two look-ups of the map before the S-box, of the input bytes `v`. -/
def cterms (v : Nat) : List Term :=
  [⟨[.look (tblAt oPRE), .and 0x0f#8], v⟩, ⟨[.look (tblAt (oPRE + 16)), .hi4], v⟩]

/-- `gPre` leaves in byte `q` of `xmm1` the map before the S-box of byte
`q` of `xmm0`, and keeps `xmm5` and the mask. -/
def gPreOk : Bool :=
  match run params regs₀ gPre with
  | none => false
  | some ρ =>
    !(ρ.get .xmm1).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm1).bs q).same ⟨0, cterms (var .xmm0 q), 0#8⟩) &&
    keeps ρ .xmm5 && maskOk ρ

/-- The map at `t` after the S-box of byte `q` of `xmm1`, under the mask `c`. -/
def aT (t : Nat) (c : Byte) (q : Nat) : List Term :=
  [⟨[.and c, .look (tblAt t), .xorc 0x0f#8, .and 0x0f#8, .aes], var .xmm1 q⟩,
   ⟨[.and c, .look (tblAt (t + 16)), .hi4, .aes], var .xmm1 q⟩]

/-- The difference of the two maps after the S-box of byte `q` of `xmm1`,
under the mask `e` of the odd places, then under the mask `c`. -/
def dT (c e : Byte) (q : Nat) : List Term :=
  [⟨[.and c, .and e, .look (tblAt oD), .xorc 0x0f#8, .and 0x0f#8, .aes], var .xmm1 q⟩,
   ⟨[.and c, .and e, .look (tblAt (oD + 16)), .hi4, .aes], var .xmm1 q⟩]

/-- The mask of the odd places, at byte `k` of a word. -/
def e1 (k : Nat) : Byte := if k % 2 = 1 then 0xff#8 else 0#8

/-- The S-box of byte `k` of the lane of `p`, under its mask for the output
byte `p`: `S0`'s map, and the difference to `S1`'s under the mask of the
odd places. -/
def kT (p k : Nat) : List Term :=
  aT oP0 (maskOf ((k + p % 4) % 4)) (4 * (p / 4) + k) ++ dT (maskOf ((k + p % 4) % 4)) (e1 k) (4 * (p / 4) + k)

/-- G's output byte `p`: of the four bytes of its lane. -/
def gT (p : Nat) : List Term := kT p 0 ++ kT p 1 ++ kT p 2 ++ kT p 3

/-- `gPost` leaves `gT` of `xmm1` in `xmm0`, and keeps `xmm5` and the mask. -/
def gPostOk : Bool :=
  match run params regs₀ gPost with
  | none => false
  | some ρ =>
    !(ρ.get .xmm0).sh && ((List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same ⟨0, gT q, 0#8⟩) &&
    keeps ρ .xmm5 && maskOk ρ

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

/-! ## The four blocks' words -/

/-- `headX` reads the four blocks of the scratch buffer. -/
def hparams : Params := { tb := tbr, name := tableName, kreg := Impl.Modes.X86.sb, klen := 672 }

/-- Byte `q` of a register that holds word `w` of the four blocks: lane
`q / 4` is block `q / 4`'s, and the blocks' words are big-endian. -/
def hw (w q : Nat) : BV := ⟨kv (oB + 16 * (q / 4) + 4 * w + (3 - q % 4)), [], 0#8⟩

/-- The four words in `xmm0`, `xmm3`, `xmm4` and `xmm1`, and the mask. -/
def headOk : Bool :=
  match run hparams Regs.init headX with
  | none => false
  | some ρ =>
    !(ρ.get .xmm0).sh && !(ρ.get .xmm3).sh && !(ρ.get .xmm4).sh && !(ρ.get .xmm1).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same (hw 0 q) &&
      (get (ρ.get .xmm3).bs q).same (hw 1 q) && (get (ρ.get .xmm4).bs q).same (hw 2 q) &&
      (get (ρ.get .xmm1).bs q).same (hw 3 q)) && maskOk ρ

/-- Byte `q` of block `l` at the end: lane `l` of `xmm5`, of `xmm0`, and of
the first two places, a word each, the most significant byte first. -/
def tw (l q : Nat) : Nat :=
  if q / 4 = 0 then var .xmm5 (4 * l + (3 - q % 4)) else if q / 4 = 1 then var .xmm0 (4 * l + (3 - q % 4))
  else kv (oR + 16 * (q / 4 - 2) + 4 * l + (3 - q % 4))

/-- The four blocks in `xmm0`, `xmm3`, `xmm4` and `xmm1`. -/
def tailOk : Bool :=
  match run params regs₀ tailX with
  | none => false
  | some ρ =>
    !(ρ.get .xmm0).sh && !(ρ.get .xmm3).sh && !(ρ.get .xmm4).sh && !(ρ.get .xmm1).sh &&
    (List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same ⟨tw 0 q, [], 0#8⟩ &&
      (get (ρ.get .xmm3).bs q).same ⟨tw 1 q, [], 0#8⟩ && (get (ρ.get .xmm4).bs q).same ⟨tw 2 q, [], 0#8⟩ &&
      (get (ρ.get .xmm1).bs q).same ⟨tw 3 q, [], 0#8⟩

theorem ends_all : headOk = true ∧ tailOk = true := by
  constructor <;> lit_decide

/-! ## `prepare`'s code -/

/-- `prepare` reads the schedule at `eax`, 16 bytes at a time, and stores
four round keys in their places at `esi`. -/
def pparams : Params := { tb := tbr, name := tableName, kreg := .eax, klen := 16 }
def poparams : OParams := { oreg := kr, olen := 64 }

/-- The key of a group of the schedule's four (two rounds' two) that goes
to the place at `kr + 16 w`. -/
def keyIdx : Direction → Nat → Nat
  | .encrypt, w => w
  | .decrypt, w => (w + 2) % 4

/-- Byte `q` of the round key at `kr + 16 w`, in every lane. -/
def pw (d : Direction) (w q : Nat) : BV := ⟨kv (4 * keyIdx d w + q % 4), [], 0#8⟩

def prepGroupOk (d : Direction) : Bool :=
  match runS pparams poparams (Regs.init, []) (prepGroupX d) with
  | none => false
  | some σ =>
    outOk σ.2 0 (pw d 0) && outOk σ.2 16 (pw d 1) && outOk σ.2 32 (pw d 2) && outOk σ.2 48 (pw d 3) && outsIn σ.2 0 64

theorem prep_all : prepGroupOk .encrypt = true ∧ prepGroupOk .decrypt = true := by
  constructor <;> lit_decide

end VG.Proof.Seed.X86.AesNiWide
