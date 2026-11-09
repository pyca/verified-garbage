module

public import VerifiedGarbage.Impl.RsaOaep.X86

/-!
# RSASSA-PSS on x86 (32-bit), with the hash functions as tables

`sign` and `verifyPrecomputed` take the hash function `H` as a table of the
interface `MdHash` (`Spec/MdHashTable.lean`), their argument `hash`, and
MGF1's `G` as a table of `Hash` (`Spec/HashTable.lean`), their argument
`mgf1`, the last two. They run the pieces of `Impl/RsaPss/X86.lean` in its
frames and slots, with these differences:

* `ctHashT` hashes in constant time, with `H`'s streaming `init`, its
  compression function and its digest (`Impl/MdHashTable/X86.lean`) the
  table's functions 0, 3 and 4, each called indirectly through the table,
  whose address it first copies to the slot `sTab`
  (`Impl.RsaOaep.X86.tcall`, in the frames `H.callInit` and
  `Impl.MdStream.X86.compressAt` push);
* `DB ⊕= MGF1(H, dbLen)` is RSAES-OAEP's MGF1 with the table `mgf1`
  (`Impl.RsaOaep.X86.mgfXor`), with `H` (`hLen` bytes at `DB + dbLen`) as
  its source and `DB` as its destination, in its slots (`mgfArgsT`);
* the code that depends on `H`'s sizes (its block, hash value, length field
  and digest) is chosen by the index of `H` in `Mgf1.hashes`, the table's
  word 5 (`idxLoad`), by comparisons with each of `idxs` (`byLen`): `ofIdx i`
  has the sizes of the hash function of index `i`, all the code reads of it.

Only the table's address and its index decide a branch or an address beyond
what `Impl/RsaPss/X86.lean` lets decide one; which tables are passed is
public.
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86

open VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap stk at_)
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Impl.RsaOaep.X86 (Fns tcall sTab sSrc sSrcLen sDst sDstLen byLen)

/-- The functions an indirect call of each of the functions of a table of
`MdHash` that the code calls may reach: for each of `init`, the compression
function and the digest, that function of every table of the interface. -/
structure MdFns where
  init : List (String × Prog isa)
  comp : List (String × Prog isa)
  dig : List (String × Prog isa)

variable (f : MdFns) (H : Hash)

/-! ## Constant-time hashing through the table of `MdHash` -/

/-- The table that is our argument `j` to `sTab`. -/
def hTab (j : Nat) : List Instr := [ld .eax (arg j), st .eax sTab]

/-- The hash value set to the initial one: the table's function 0. -/
def initPartT : Prog isa := .seq (.block initArgs) (tcall 0 f.init [.ebx])

/-- One compression of the block at `eax` into the hash value at `ebx`,
with the scratch space at `ebp`: the table's function 3, in the frame
`Impl.MdStream.X86.compressAt` pushes. -/
def cmpT : Prog isa := .seq (.block [.mov .ecx (.imm 1)]) (tcall 3 f.comp [.ebp, .ecx, .eax, .ebx])

def compBodyT : Prog isa :=
  seqs [.block (blkSet H), Impl.Bignum.X86.copyBytes, .block (cmpSet H), cmpT f, .block (selSet H),
    countLoop selBody, .block compNext]

/-- Every block compressed, the last one's hash value selected. -/
def compLoopT : Prog isa := .seq (.block compInit) (.loop (compBodyT f H) .ne)

/-- The digest of the selected hash value: the table's function 4, with the
hash value at `ebx` and the digest's place at `eax`. -/
def outPartT : Prog isa := .seq (.block outSet) (tcall 4 f.dig [.ebx])

/-- Constant-time hashing, with the hash function of the table that is our
argument `j`. -/
def ctHashT (j : Nat) : Prog isa :=
  seqs [.block (hTab j), initPartT f, lenPart H, padPart H, compLoopT f H, outPartT f]

/-! ## MGF1 through the table of `Hash` -/

/-- MGF1's slots: `H` (`hLen` bytes at `DB + dbLen`) its source, `DB`
(`dbLen` bytes) its destination. -/
def mgfArgsT : List Instr :=
  atDb .eax ++ [st .eax sDst, ld .ecx sDb, st .ecx sDstLen, .alu .add .eax (.reg .ecx), st .eax sSrc, mi .eax H.D,
    st .eax sSrcLen]

/-! ## The hash function of the table -/

/-- The indices in `Mgf1.hashes` of the hash functions whose tables of
`MdHash` the functions take: MD5, SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. -/
def idxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The block size, the sizes of the hash value, of the length field and of
the digest, and the byte order of the hash function of index `i`. -/
def sizesOf : Nat → Nat × Nat × Nat × Nat × Bool
  | 0 => (64, 16, 8, 16, false)
  | 1 => (64, 20, 8, 20, true)
  | 2 => (64, 32, 8, 28, true)
  | 3 => (64, 32, 8, 32, true)
  | 4 => (128, 64, 16, 48, true)
  | 5 => (128, 64, 16, 64, true)
  | 6 => (128, 64, 16, 28, true)
  | _ => (128, 64, 16, 32, true)

/-- A hash function's sizes, in the order of `sizesOf`. -/
def sizes (H : Hash) : Nat × Nat × Nat × Nat × Bool := (H.B, H.N, H.L, H.D, H.be)

/-- A hash function with the sizes `z` and no code: all that the pieces of
code chosen by the index read of it. -/
def ofSizes (z : Nat × Nat × Nat × Nat × Bool) : Hash :=
  ⟨⟨z.1, 0, z.2.2.2.1, 0, 0, "", .block [], "", .block [], "", .block []⟩, z.2.1, z.2.2.1, z.2.2.2.2, 0, "",
    .block [], []⟩

/-- The hash function of index `i`, as the code sees it. -/
def ofIdx (i : Nat) : Hash := ofSizes (sizesOf i)

/-- The index of the hash function of the table that is our argument `j`
(its word 5), to `edx`. -/
def idxLoad (j : Nat) : List Instr := [ld .edx (arg j), .mov .edx (.mem (at_ .edx 20))]

variable (g : Fns)

/-! ## Signing -/

/-- After the checks: `EM` at `scratch + oEm`. -/
def signEncT : Prog isa :=
  seqs [yDig H 16, .block (cpSalt H), .ite .e (.block []) Impl.Bignum.X86.copyBytes, .block (lenArgs H 19),
    ctHashT f H 22, .block clrEm, zeroLoop, .block oneSet, .block put1, .ite .e (.block []) Impl.Bignum.X86.copyBytes,
    .block (putH H), Impl.Bignum.X86.copyBytes, .block bcSet, .block putBc, .block (mgfArgsT H), Impl.RsaOaep.X86.mgfXor g 23,
    .block topSet, .block topAnd]

variable (privN : String) (privC : Prog isa)

/-- The checks, the encoding and the private-key operation, for the hash
function `H`. -/
def signTail : Prog isa :=
  seqs [.block (signChk ++ params H),
    .ite .ne signFail (seqs [signEncT f H g, .block privArgs, .call privN privC])]

/-- The inner frame's body: the tail for the table's hash function. -/
def signBodyT : Prog isa := .seq (.block (idxLoad 22)) (byLen (fun i => signTail f (ofIdx i) g privN privC) idxs)

/-- `vg_rsa_pss_sign`, calling a checked private operation by its name. -/
def sign : Prog isa := wrap frameBytes (signBodyT f g privN privC)

/-! ## Verifying -/

/-- A salt of the expected length: copied from the end of `DB`. -/
def fixedPathT : Prog isa :=
  seqs [yDig H 4, .block (fxSalt H), .ite .e (.block []) Impl.Bignum.X86.copyBytes, .block (lenArgs H 8),
    ctHashT f H 14, cmpH H]

/-- A salt of any length: `DB` shifted into place, hashed over the blocks of
the longest salt. -/
def anyPathT : Prog isa :=
  seqs [yDig H 4, .block (cpDb H), Impl.Bignum.X86.copyBytes, shift H, .block (anyLen H), ctHashT f H 14, cmpH H]

variable (pubN : String) (pubC : Prog isa)

/-- After the public checks. -/
def verifyMainT : Prog isa :=
  seqs [.block pubArgs, .call pubN pubC, .block accSet, .block acc0, .block (mgfArgsT H), Impl.RsaOaep.X86.mgfXor g 15,
    .block topSet, .block topAnd, .block scanSet, countLoop scanBody, .block posChk,
    .ite .e (fixedPathT f H) (anyPathT f H)]

/-- The checks and the verification, for the hash function `H`. -/
def verifyTail : Prog isa :=
  seqs [.block (verifyChk ++ params H), .ite .ne (.block [mi .eax 0]) (verifyMainT f H g pubN pubC)]

/-- The inner frame's body: the tail for the table's hash function. -/
def verifyBodyT : Prog isa :=
  .seq (.block (idxLoad 14)) (byLen (fun i => verifyTail f (ofIdx i) g pubN pubC) idxs)

/-- `vg_rsa_pss_verify_precomputed`, calling a precomputed public operation
by its name. -/
def verifyPrecomputed : Prog isa := wrap frameBytes (verifyBodyT f g pubN pubC)

end VG.Impl.RsaPss.X86
