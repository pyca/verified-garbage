module

public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Impl.Dispatch.X86_64

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments

`sign` and `verify` (with cached public-key values) of `Impl/RsaPss/X86_64.lean`,
but taking the digest's hash function and MGF1's as the arguments `hash` and
`mgf1_hash` (their numbers, `Spec/HashId.lean`): of the hash functions `hs`,
the `i`th is the one numbered `i`. Each selector is stored in a slot of the
frame (`sHsel`, `sMsel`) zero-extended from its 32 bits, and the digest's
length (`digest_len`, which the contract makes `hLen`) in `sHd`.

What depends on the digest's hash function `H`:

* the checks of the encoding's length, which compare with `hLen + 2` from
  `sHd` (`emLenAny`, `saltFitsAny`);
* when signing, `M'` and its hash, and `H` and `0xbc` in `EM` (`signPre`),
  and when verifying, everything after `DB`'s first nonzero byte is found
  (`verifyTail`): the code of `Impl/RsaPss/X86_64.lean` for `H`, chosen by a
  dispatch on `hash` (`Dispatch.X86_64.chain`);
* MGF1's seed, `H`, of `hLen` bytes from `sHd` (`seedPart`).

What depends on MGF1's hash function `G` is chosen by a dispatch on
`mgf1_hash` for each counter (`gPart`): the hash of `H ‖ C` and its digest
XORed into `DB`. Its padding is written at the offset `hLen + 4` from the
slot `sL` (`slotPad80`), and its blocks are compressed directly when
`hLen + 4` and the length field fit one block (`sFb`, the last block's
index, is 0); otherwise in two blocks, as `ctHash` does (`genericRest`).
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86_64.AnyHash

open VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-! ## The new slots -/

/-- `hLen`, the digest's length (the argument `digest_len`). -/
def sHd : Nat := 120
/-- The digest's hash function's number. -/
def sHsel : Nat := 376
/-- MGF1's hash function's number. -/
def sMsel : Nat := 384

/-- The cases of a dispatch on the hash functions `hs`: `f` of the `i`th for
the number `i`. -/
def cases (f : Hash → Prog isa) (hs : List Hash) : List (Nat × Prog isa) :=
  hs.mapIdx fun i h => (i, f h)

/-- `f` of the hash function the selector in the slot `d` names. -/
def dispatch (d : Nat) (f : Hash → Prog isa) (hs : List Hash) : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp d))]) (Dispatch.X86_64.chain (cases f hs))

/-! ## The checks -/

/-- `emLen`, the mask and `lo`, as `emLen`, with `hLen + 2` from `sHd`. -/
def emLenAny : Prog isa :=
  .seq (.ite .e (.block [.mov32 .rdx (.imm 0xFF), .mov32 .r8 (.imm 1)]) (.block [.mov32 .r8 (.imm 0)]))
    (.block [.store (sp sC) .rdx, .store (sp sLo) .r8, .mov .rax (.mem (sp sK)), .alu .sub .rax (.reg .r8),
      .mov .r9 (.mem (sp sHd)), .alu .add .r9 (.imm 2), .alu .cmp .rax (.reg .r9)])

/-- `saltFits`, with `hLen` from `sHd`. -/
def saltFitsAny : List Instr :=
  [.alu .sub .rax (.mem (sp sHd)), .alu .sub .rax (.imm 2), .alu .cmp .rax (.reg .rdx)]

/-! ## MGF1 -/

/-- `Y`'s first 256 bytes (two blocks of any hash function here) cleared,
and `rcx` = `Y`. -/
def clearSeedBlocks : Prog isa :=
  .seq (.block (scr .rcx oY ++ ([.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)] : List Instr)))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 256)]) .ne)

/-- `H`, the `hLen` bytes at `DB + dbLen`, to `Y` (in `rcx`). -/
def copySeed : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sp sEb)), .mov .r8 (.mem (sp sDb)), .alu .add .rsi (.reg .r8),
      .mov .r10 (.mem (sp sHd)), .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- The counter, big-endian, after `H` in `Y` (in `rcx`); the message's
length, `hLen + 4`, and two blocks. -/
def counterAny : List Instr :=
  [.mov .r9 (.mem (sp sHd)), .mov .rdi (.reg .rcx), .alu .add .rdi (.reg .r9), .mov .rax (.mem (sp sCtr)),
    .store8 (at_ .rdi 3) .rax, .shift .shr .rax 8, .store8 (at_ .rdi 2) .rax, .shift .shr .rax 8,
    .store8 (at_ .rdi 1) .rax, .shift .shr .rax 8, .store8 (at_ .rdi) .rax,
    .mov .rax (.reg .r9), .alu .add .rax (.imm 4), .store (sp sL) .rax,
    .mov32 .rax (.imm 2), .store (sp sNb) .rax]

/-- `H ‖ C` in `Y`. -/
def seedPart : Prog isa := seqs [clearSeedBlocks, copySeed, .block counterAny]

/-- `0x80` ORed into byte `ℓ` (`sL`, public here) of `Y`. -/
def slotPad80 : Prog isa :=
  .seq (.block (scr .rcx oY ++ ([.mov .rdx (.mem (sp sL))] : List Instr)))
    (.block [.movzx8 .rax (ix .rcx .rdx), .alu .or .rax (.imm 0x80), .store8 (ix .rcx .rdx) .rax])

/-- The one block compressed into the state `init` set, and its digest. -/
def directRest (G : Hash) : Prog isa :=
  seqs [directLen G, .block [.mov32 .rax (.imm 0), .store (sp sB) .rax],
    .seq (.block (compArgs G)) (.call G.compN G.compC), .block (digestAt G oSt)]

/-- The length field into the last of the `nbm` blocks, every block
compressed and the last one's hash value selected, and its digest. -/
def genericRest (G : Hash) : Prog isa :=
  seqs [lenLoop G, compLoop G, .block (digestOut G)]

/-- The digest of `H ‖ C` (`hLen + 4` bytes) to `scratch + oDig`. -/
def mgfHashAny (G : Hash) : Prog isa :=
  seqs [ctInit G, slotPad80, .block (lenField G), .block [.mov .rax (.mem (sp sFb)), .alu .test .rax (.reg .rax)],
    .ite .e (directRest G) (genericRest G)]

/-- What MGF1's hash function decides for one counter: the digest of
`H ‖ C`, XORed into `DB`, and the next counter. -/
def gPart (G : Hash) : Prog isa := seqs [mgfHashAny G, xorOut G, .block (nextCtr G)]

/-- `DB ⊕= MGF1(G, H, dbLen)`, `G` the hash function `mgf1_hash` names. -/
def mgfXorAny (hs : List Hash) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax])
    (.loop (.seq seedPart (dispatch sMsel gPart hs)) .b)

/-! ## Signing

`sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, digest,
digest_len, salt, salt_len, scratch, scratch_len, hash, mgf1_hash)`, the
last eighteen on the stack. -/

def signPrologue : List Instr :=
  saveRegs ++ ([.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8,
    .store (sp sEl) .r9, .mov .rax (.mem (arg 10)), .store (sp sDig) .rax, .mov .rax (.mem (arg 11)),
    .store (sp sHd) .rax, .mov .rax (.mem (arg 12)), .store (sp sSalt) .rax, .mov .rax (.mem (arg 13)),
    .store (sp sSaltLen) .rax, .mov .rax (.mem (arg 14)), .store (sp sScr) .rax, .mov .rax (.mem (arg 15)),
    .store (sp sScrLen) .rax, .mov32 .rax (.mem (arg 16)), .store (sp sHsel) .rax, .mov32 .rax (.mem (arg 17)),
    .store (sp sMsel) .rax] : List Instr)

/-- What the digest's hash function decides of the encoding: `M'` in `Y`
and its hash `H`, `EM` cleared, `0x01` and the salt, `H` and `0xbc`. -/
def signPre (H : Hash) : Prog isa :=
  seqs [clearY, copyDigest H, copySaltY H, .block (signLen H), ctHash H, clearEm, putSalt, putH H]

variable (hs : List Hash)

def signEnc : Prog isa :=
  seqs [.block dbSlots, dispatch sHsel signPre hs, mgfXorAny hs, .block clearTop]

variable (privN : String) (privC : Prog isa)

def signMain : Prog isa := seqs [signEnc hs, .block privArgs, .call privN privC]

def signBody : Prog isa :=
  seqs [.block (signPrologue ++ n0),
    .ite .e signFail (seqs [.block smear, emLenAny,
      .ite .b signFail (seqs [.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFitsAny),
        .ite .b signFail (signMain hs privN privC)])]),
    .block restoreRegs]

/-- `vg_rsa_pss_sign`. -/
def sign : Prog isa := .frame (.alloc frameBytes) (signBody hs privN privC) (.free frameBytes)

/-! ## Verifying

`verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx, digest = r8,
digest_len = r9, sig, sig_len, salt_len, any_salt_len, scratch, scratch_len,
pre, pre_len, hash, mgf1_hash)`, the last ten on the stack. -/

def verifyPrologue : List Instr :=
  saveRegs ++ ([.store (sp sN) .rdi, .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx,
    .store (sp sDig) .r8, .store (sp sHd) .r9, .mov .rax (.mem (arg 0)), .store (sp sSig) .rax,
    .mov .rax (.mem (arg 4)), .store (sp sScr) .rax, .mov .rax (.mem (arg 5)), .store (sp sScrLen) .rax,
    .mov32 .rax (.mem (arg 8)), .store (sp sHsel) .rax, .mov32 .rax (.mem (arg 9)),
    .store (sp sMsel) .rax] : List Instr)

/-- `anyArgs`, from `salt_len` and `any_salt_len` here. -/
def anyArgs : Prog isa :=
  .seq (.block [.mov .rax (.mem (arg 2)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 3)),
      .alu .test .rax (.reg .rax)])
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]))

/-- The public operation's arguments, with the cached values `pre`. -/
def pubArgs : List Instr := X86_64.pubArgs ++
  ([.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))] : List Instr)

/-- What the digest's hash function decides of verification, after `DB`'s
first nonzero byte is found. -/
def verifyTail (H : Hash) : Prog isa := .seq (posCheck H) (saltBack H)

variable (pubN : String) (pubC : Prog isa)

def verifyMain : Prog isa :=
  seqs [.block dbSlots, .block pubArgs, .call pubN pubC, .block acc0, mgfXorAny hs, .block clearTop,
    posScan, dispatch sHsel verifyTail hs]

def verifyBody : Prog isa :=
  seqs [.block (verifyPrologue ++ n0),
    .ite .e verifyFail (seqs [.block smear, emLenAny,
      .ite .b verifyFail (seqs [anyArgs, .block (([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
          .alu .sub .rax (.reg .r8)] : List Instr) ++ saltFitsAny),
        .ite .b verifyFail (verifyMain hs pubN pubC)])]),
    .block restoreRegs]

/-- `vg_rsa_pss_verify_precomputed`. -/
def verify : Prog isa := .frame (.alloc frameBytes) (verifyBody hs pubN pubC) (.free frameBytes)

end VG.Impl.RsaPss.X86_64.AnyHash
