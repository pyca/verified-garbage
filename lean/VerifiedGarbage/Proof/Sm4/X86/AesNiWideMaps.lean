module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiWide
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiWide
public import VerifiedGarbage.Proof.Sm4.X86.AesNiMaps
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiMaps
public import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4's S-box by the AES S-box, four blocks at a time: what the code computes of each byte

What the straight-line parts of `Impl/Sm4/X86/AesNiWide.lean` leave in the
registers and store, as expressions of the bytes they start with
(`Proof/Framework/X86/ByteMap.lean`), each compared by the kernel with the
expression the proofs use: the four rounds of a turn, each but its key's
load and its word's store (`round_all`), the conversions and transposes at
the two ends (`conv_all`), and a group of `prepare` in each direction
(`prep_all`). The byte maps are those of the one-block core
(`AesNiMaps.lean`), whose table's rows this code's table starts with.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNiWide

open VG VG.X86 VG.X86.ByteMap VG.Impl.Sm4.X86.AesNiWide
open VG.Impl.Sm4.X86 (Dir)
open VG.Impl.Sm4.X86.AesNi (oE oH oCV oIV oK oM0 oR tbr kr m0)
open VG.Proof.Sm4.X86.AesNi (tblAt var kv br cterms maskOk regs₀)

/-! ## A round -/

/-- A round's code but its key's load and its word's store, and the code
that takes the last four words: the table at `ebx`, and the scratch buffer
at `edi`, of which they read the ring's four places. -/
def params : Params := { tb := tbr, name := tableName, kreg := Impl.Modes.X86.sb, klen := 96 }

/-- The map at `t` of `aesenclast`'s byte at `p`, of the register `a`: the
shuffle before `aesenclast` undoes its ShiftRows. -/
def aT (t : Nat) (a : XReg) (p : Nat) : List Term :=
  [⟨[.look (tblAt t), .xorc 0x0f#8, .and 0x0f#8, .aes], var a p⟩,
   ⟨[.look (tblAt (t + 16)), .hi4, .aes], var a p⟩]

/-- A round's sum at byte `q`: `E ⊕ H ⊕ rot¹ E ⊕ rot² E ⊕ rot³ H`. -/
def sigma (a : XReg) (q : Nat) : List Term :=
  aT oE a q ++ aT oH a q ++ aT oE a (br 1 q) ++ aT oE a (br 2 q) ++ aT oH a (br 3 q)

/-- A round but its key's load and its word's store, with the next round's
key in `e`, its oldest word at `s0` of the scratch buffer and its third at
`s2`, leaves, in `c`, its word and sum with that key and the two words
after its own that it read or had; in `e`, its word and sum; and the mask. -/
def roundOk (a c n e : XReg) (s0 s2 : Nat) : Bool :=
  match run params regs₀ (roundX a c n e s0 s2) with
  | none => false
  | some ρ =>
    !(ρ.get c).sh && !(ρ.get e).sh &&
    ((List.range 16).all fun q => (get (ρ.get c).bs q).same
      ⟨kv (s0 + q) ^^^ var e q ^^^ kv (s2 + q) ^^^ var n q, sigma a q, 0#8⟩) &&
    ((List.range 16).all fun q => (get (ρ.get e).bs q).same ⟨kv (s0 + q), sigma a q, 0#8⟩) &&
    maskOk ρ

/-- The four rounds of a turn: the registers of its first and third, and of
its second and fourth, with each round's places in the ring. -/
theorem round_all : ∀ j < 4, roundOk (if j % 2 = 0 then .xmm0 else .xmm4) (if j % 2 = 0 then .xmm4 else .xmm0)
    (if j % 2 = 0 then .xmm1 else .xmm2) (if j % 2 = 0 then .xmm2 else .xmm1) (oR + 16 * j)
    (oR + 16 * ((j + 2) % 4)) = true := by
  lit_decide

/-! ## The conversions -/

/-- `headX` reads the four blocks of the scratch buffer. -/
def hparams : Params := { tb := tbr, name := tableName, kreg := Impl.Modes.X86.sb, klen := 688 }

/-- Byte `q` of word `w` of the four blocks, in the rounds' form: lane
`q / 4` is block `q / 4`'s. -/
def hw (w q : Nat) : BV := ⟨0, cterms oCV (kv (oB + 16 * (q / 4) + 4 * w + q % 4)), 0#8⟩

/-- The four words in `xmm0`, `xmm3`, `xmm4` and `xmm1`, the exclusive-or of
the last three in `xmm2`, and the mask. -/
def headOk : Bool :=
  match run hparams Regs.init headX with
  | none => false
  | some ρ =>
    !(ρ.get .xmm0).sh && !(ρ.get .xmm3).sh && !(ρ.get .xmm4).sh && !(ρ.get .xmm1).sh && !(ρ.get .xmm2).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same (hw 0 q) &&
      (get (ρ.get .xmm3).bs q).same (hw 1 q) && (get (ρ.get .xmm4).bs q).same (hw 2 q) &&
      (get (ρ.get .xmm1).bs q).same (hw 3 q) &&
      (get (ρ.get .xmm2).bs q).same (((hw 1 q).xor (hw 2 q)).xor (hw 3 q))) && maskOk ρ

/-- Byte `q` of block `l` from the ring: lane `l` of the word in place
`3 - q / 4`, out of the rounds' form. -/
def tw (l q : Nat) : BV := ⟨0, cterms oIV (kv (oR + 16 * (3 - q / 4) + 4 * l + q % 4)), 0#8⟩

/-- The four blocks in `xmm0`, `xmm3`, `xmm4` and `xmm1`. -/
def tailOk : Bool :=
  match run params regs₀ tailX with
  | none => false
  | some ρ =>
    !(ρ.get .xmm0).sh && !(ρ.get .xmm3).sh && !(ρ.get .xmm4).sh && !(ρ.get .xmm1).sh &&
    (List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same (tw 0 q) &&
      (get (ρ.get .xmm3).bs q).same (tw 1 q) && (get (ρ.get .xmm4).bs q).same (tw 2 q) &&
      (get (ρ.get .xmm1).bs q).same (tw 3 q)

theorem conv_all : headOk = true ∧ tailOk = true := by
  constructor <;> lit_decide

/-! ## `prepare`'s code -/

/-- `prepare` reads the schedule at `eax`, 16 bytes at a time, and stores
four round keys in their places at `esi`. -/
def pparams : Params := { tb := tbr, name := tableName, kreg := .eax, klen := 16 }
def poparams : OParams := { oreg := kr, olen := 64 }

/-- The key of a group of the schedule's four that goes to the place at
`kr + 16 w`. -/
def keyIdx : Dir → Nat → Nat
  | .encrypt, w => w
  | .decrypt, w => 3 - w

/-- Byte `q` of the round key at `kr + 16 w`: the schedule's words are
little-endian. -/
def pw (d : Dir) (w q : Nat) : BV := ⟨0, cterms oK (kv (4 * keyIdx d w + (3 - q % 4))), 0#8⟩

def prepGroupOk (d : Dir) : Bool :=
  match runS pparams poparams (regs₀, []) (prepGroupX d) with
  | none => false
  | some σ =>
    outOk σ.2 0 (pw d 0) && outOk σ.2 16 (pw d 1) && outOk σ.2 32 (pw d 2) && outOk σ.2 48 (pw d 3) &&
    outsIn σ.2 0 64 && maskOk σ.1

/-- The mask's load. -/
def prepMaskOk : Bool :=
  match run pparams Regs.init [tb m0 oM0] with
  | none => false
  | some ρ => maskOk ρ

theorem prep_all : prepGroupOk .encrypt = true ∧ prepGroupOk .decrypt = true ∧ prepMaskOk = true := by
  refine ⟨?_, ?_, ?_⟩ <;> lit_decide

end VG.Proof.Sm4.X86.AesNiWide
