module

public import VerifiedGarbage.Impl.RsaOaep.Arm
public import VerifiedGarbage.Impl.Md5.Arm.Stream
public import VerifiedGarbage.Impl.Sha1.Arm.Stream
public import VerifiedGarbage.Impl.Sha256.Arm.Stream
public import VerifiedGarbage.Impl.Sha512.Arm.Stream

/-!
# RSASSA-PSS on ARMv7, with its hash functions as tables

`sign` and `verifyPrecomputed` (`vg_rsa_pss_sign`,
`vg_rsa_pss_verify_precomputed`) with the pieces of `Impl/RsaPss/Arm.lean`,
the hash function `H` given as a table of the interface `MdHash`
(`Spec/MdHashTable.lean`) and MGF1's as a table of `Hash`
(`Spec/HashTable.lean`), their last two arguments.

`ctHash` calls `H`'s streaming `init`, compression function and digest of a
hash value, the table's functions 0, 3 and 4, through the table
(`Impl.RsaOaep.Arm.tcall`: the table's address is copied to the slot
`sTab` first). MGF1 is RSAES-OAEP's (`Impl.RsaOaep.Arm.mgfXor`), over the
table `mgf1`: its source is `H` at `DB + dbLen` and its destination `DB`.

Everything else depends on `H` through its shape (`Sh`: its block size,
digest size, the sizes of its hash value and length field, and its length
field's code), which the functions choose by the index of `H` in
`Spec.Mgf1.hashes`, the table's word 5 (`ofIdx`, among `idxs`, by
`Impl.RsaOaep.Arm.byLen`), before anything else.
-/

@[expose] public section

namespace VG.Impl.RsaPss.Arm

open VG.Arm
open VG.Impl.RsaPkcs1Sig.Arm (wrap)
open VG.Impl.Bignum.Arm (copyBytes maskBytes compareBytes)
open VG.Impl.RsaOaep.Arm (tcall tabSlot byLen sSrc sSrcLen sDst sDstLen)

/-- The functions an indirect call of each of the functions of a table of
`MdHash` that the code calls may reach: for each of `init`, the compression
function and the digest, that function of every table of the interface. -/
structure MdFns where
  init : List (String × Prog isa)
  comp : List (String × Prog isa)
  dig : List (String × Prog isa)

variable (f : MdFns) (g : Impl.RsaOaep.Arm.Fns) (H : Sh)

/-! ## `ctHash` -/

/-- The table that is our argument `j` to `sTab`, and the hash value set to
the initial one. -/
def initPart (j : Nat) : Prog isa := .seq (.block (tabSlot j ++ initArgs)) (tcall 0 f.init)

/-- One compression of the block at `r6` into the hash value at `r0`, with
the working space `r3`. -/
def compCall : Prog isa := .seq (.block [.mov .r1 (.reg .r6), .mov .r2 (.imm 1)]) (tcall 3 f.comp)

def compBody : Prog isa :=
  seqs [.block (compSet H), compCall f, .block (selSet H), countLoop selBody, .block compNext]

/-- Every block compressed, the last one's hash value selected. -/
def compLoop : Prog isa := .seq (.block compInit) (.loop (compBody f H) .ne)

/-- The digest of the selected hash value. -/
def outPart : Prog isa := .seq (.block outSet) (tcall 4 f.dig)

/-- The digest of the first `ℓ` bytes of `Y`, padded in `nbm` blocks, to
`scratch + oDig`, without revealing `ℓ`, with the hash function of the table
that is our argument `j`. -/
def ctHash (j : Nat) : Prog isa := seqs [initPart f j, lenPart H, padPart H, compLoop f H, outPart f]

/-! ## MGF1 -/

/-- MGF1's slots: its source `H` (`hLen` bytes at `DB + dbLen`), its
destination `DB` (`dbLen` bytes). -/
def mgfSlots : List Instr :=
  sp0 :: (atDb .r0 ++ [ld .r1 sDb, .dp .add .r2 .r0 (.reg .r1), mw .r3 (dig H), st .r0 sDst, st .r1 sDstLen,
    st .r2 sSrc, st .r3 sSrcLen])

/-- `DB ⊕= MGF1(H, dbLen)`, with the hash function of the table that is our
argument `j`. -/
def mgfPart (j : Nat) : Prog isa := .seq (.block (mgfSlots H)) (Impl.RsaOaep.Arm.mgfXor g j)

/-! ## The hash function of the table -/

/-- The indices in `Mgf1.hashes` of the hash functions whose tables of
`MdHash` the functions take: MD5, SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. -/
def idxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The shape of the hash function of index `i`. -/
def ofIdx : Nat → Sh
  | 0 => ⟨64, 16, 16, 8, Impl.Md5.Arm.Stream.params.len⟩
  | 1 => ⟨64, 20, 20, 8, Impl.Sha1.Arm.Stream.params.len⟩
  | 2 => ⟨64, 28, 32, 8, Impl.Sha256.Arm.Stream.params.len⟩
  | 3 => ⟨64, 32, 32, 8, Impl.Sha256.Arm.Stream.params.len⟩
  | 4 => ⟨128, 48, 64, 16, Impl.Sha512.Arm.Stream.params.len⟩
  | 5 => ⟨128, 64, 64, 16, Impl.Sha512.Arm.Stream.params.len⟩
  | 6 => ⟨128, 28, 64, 16, Impl.Sha512.Arm.Stream.params.len⟩
  | _ => ⟨128, 32, 64, 16, Impl.Sha512.Arm.Stream.params.len⟩

/-- The index of the hash function of the table that is our argument `j`
(its word 5), to `r1`. -/
def idxLoad (j : Nat) : List Instr := [ld .r1 (arg j), .ldr .r1 .r1 20]

/-! ## Signing -/

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEnc : Prog isa :=
  seqs [yDig H 16, .block (cpSalt H), .ite .eq (.block []) copyBytes, .block (lenSet H 19), ctHash f H 22,
    .block clrEm, maskBytes, .block saltPos, .block put1, .ite .eq (.block []) copyBytes, .block (putH H), copyBytes,
    .block bcSet, .block bcPut, mgfPart g H 23, .block topSet, .block topAnd]

variable (privN : String) (privC : Prog isa)

/-- The inner frame's body, for the hash function of shape `H`. -/
def signBody : Prog isa :=
  seqs [.block (signChk H), .block (params ++ saltFits),
    .ite .ne signFail (seqs [signEnc f g H, .block privArgs, .call privN privC])]

/-- The body for the hash function of the table `hash`. -/
def signTab : Prog isa := .seq (.block (idxLoad 22)) (byLen (fun i => signBody f g (ofIdx i) privN privC) idxs)

/-- `vg_rsa_pss_sign`, calling a checked private operation by its name. -/
def sign : Prog isa := wrap frameBytes (signTab f g privN privC)

/-! ## Verifying -/

/-- A salt of the expected length: copied from the end of `DB`. -/
def fixedPath : Prog isa :=
  seqs [yDig H 4, .block (fxSalt H), .ite .eq (.block []) copyBytes, .block (lenSet H 8), ctHash f H 14, cmpH H]

/-- A salt of any length: `DB` shifted into place, hashed over the blocks of
the longest salt. -/
def anyPath : Prog isa :=
  seqs [yDig H 4, .block (cpDb H), copyBytes, shift H, .block (anyLen H), ctHash f H 14, cmpH H]

variable (pubN : String) (pubC : Prog isa)

/-- After the public checks. -/
def verifyMain : Prog isa :=
  seqs [.block pubArgs, .call pubN pubC, .block accSet, .block acc0, mgfPart g H 15, .block topSet, .block topAnd,
    .block scanSet, countLoop scanBody, .block posSet, .block posChk, .block anySet,
    .ite .eq (fixedPath f H) (anyPath f H)]

/-- The inner frame's body, for the hash function of shape `H`. -/
def verifyBody : Prog isa :=
  seqs [.block (verifyChk H), .block (params ++ expLen ++ saltFits),
    .ite .ne (.block [mw .r0 0]) (verifyMain f g H pubN pubC)]

/-- The body for the hash function of the table `hash`. -/
def verifyTab : Prog isa :=
  .seq (.block (idxLoad 14)) (byLen (fun i => verifyBody f g (ofIdx i) pubN pubC) idxs)

/-- `vg_rsa_pss_verify_precomputed`, calling a precomputed public operation
by its name. -/
def verifyPrecomputed : Prog isa := wrap frameBytes (verifyTab f g pubN pubC)

end VG.Impl.RsaPss.Arm
