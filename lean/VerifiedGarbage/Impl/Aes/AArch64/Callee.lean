module

public import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-!
# The implementations of `vg_aes_ctr32` on AArch64

A function that calls `vg_aes_ctr32` (AES-CMAC's) takes the implementation it
calls, a `Ctr32`, and is emitted once for each (`Generic/AesCtr32/AArch64/`).
One that also expands the key (streaming AES-CMAC's `init`) calls the
implementation of `vg_aes_expand_key_scratch` that goes with it, an `ExpandKey`.
A function that encrypts or decrypts whole blocks (AES-OCB's) calls an
implementation of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, a
pair of `Blocks`.

Each states the registers its code writes, of those the calling convention
does not preserve (`clear`): what a function that calls it clears for it
before returning, with those its own instructions write
(`Impl.Scrub.AArch64.Clear.union`). The proofs hold each to its code
(`Proof.Aes.AArch64.Ctr32Impl`, `BlocksImpl`).
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64

open VG.AArch64

/-- An implementation of `vg_aes_ctr32` to call: its symbol and its code. -/
structure Ctr32 where
  name : String
  code : Prog isa
  /-- The registers its code writes, of those the calling convention does not
  preserve (`Proof.Aes.AArch64.Ctr32Impl.scrub`, `toScrub`). -/
  clear : Impl.Scrub.AArch64.Clear
  /-- The bytes of `scratch` it needs, none or 2048: a function that calls it
  has only these in its frame (`Proof.Aes.AArch64.Ctr32Impl.scratch_eq`). -/
  scratch : Nat

def Ctr32.scalar : Ctr32 where
  name := "vg_aes_ctr32"
  code := ctr32N
  clear := ⟨[.x1, .x3, .x4, .x6, .x8, .x9, .x10],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
     .v27, .v28, .v29, .v30, .v31],
    []⟩
  scratch := 2048

def Ctr32.aese : Ctr32 where
  name := "vg_aes_ctr32_aes"
  code := Aese.ctr32
  clear := ⟨[.x3, .x4, .x6, .x7, .x9, .x10, .x12, .x13],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30, .v31],
    []⟩
  scratch := 0

/-! Their out-of-place forms, internal functions (`ctr32ToN`, `Aese.ctr32To`), which
`vg_aes_gcm_open_to` calls to decrypt into `dst` as it reads `src`. -/

def Ctr32.scalarTo : Ctr32 where
  name := "vg_aes_ctr32_to"
  code := ctr32ToN
  clear := ⟨[.x1, .x3, .x4, .x6, .x8, .x9, .x10],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
     .v27, .v28, .v29, .v30, .v31],
    []⟩
  scratch := 2048

def Ctr32.aeseTo : Ctr32 where
  name := "vg_aes_ctr32_to_aes"
  code := Aese.ctr32To
  clear := ⟨[.x3, .x4, .x6, .x7, .x9, .x10, .x12, .x13, .x14],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30, .v31],
    []⟩
  scratch := 0

/-- An implementation of `vg_aes_expand_key_scratch` to call: its symbol and its code. -/
structure ExpandKey where
  name : String
  code : Prog isa
  /-- The registers its code writes, of those the calling convention does not
  preserve (`Proof.Aes.AArch64.Ctr32Impl.expandScrub`). -/
  clear : Impl.Scrub.AArch64.Clear

def ExpandKey.scalar : ExpandKey where
  name := "vg_aes_expand_key_scratch"
  code := expandKey
  clear := ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30, .v31],
    []⟩

def ExpandKey.aese : ExpandKey where
  name := "vg_aes_expand_key_scratch_aes"
  code := Aese.expandKey
  clear := ⟨[.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13], [.v0, .v1], []⟩

/-- An implementation of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`
to call: its symbol and its code. -/
structure Blocks where
  name : String
  code : Prog isa
  /-- The registers its code writes, of those the calling convention does not
  preserve (`Proof.Aes.AArch64.BlocksImpl.encScrub`, `decScrub`). -/
  clear : Impl.Scrub.AArch64.Clear
  /-- The bytes of `scratch` it needs, none or 2048: a function that calls it
  has only these in its frame (`Proof.Aes.AArch64.BlocksImpl.encScratch_eq`,
  `decScratch_eq`). -/
  scratch : Nat

def Blocks.encScalar : Blocks where
  name := "vg_aes_encrypt_blocks"
  code := encryptBlocksN
  clear := ⟨[.x1, .x2, .x3, .x6, .x9, .x10],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
     .v27, .v28, .v29, .v30, .v31],
    []⟩
  scratch := 2048

def Blocks.decScalar : Blocks where
  name := "vg_aes_decrypt_blocks"
  code := decryptBlocksN
  clear := ⟨[.x1, .x2, .x3, .x6, .x9, .x10],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30],
    []⟩
  scratch := 2048

def Blocks.encAese : Blocks where
  name := "vg_aes_encrypt_blocks_aes"
  code := Aese.encryptBlocks
  clear := ⟨[.x2, .x3, .x6, .x7, .x9, .x13],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30],
    []⟩
  scratch := 0

def Blocks.decAese : Blocks where
  name := "vg_aes_decrypt_blocks_aes"
  code := Aese.decryptBlocks
  clear := ⟨[.x2, .x3, .x6, .x7, .x9, .x13],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30],
    []⟩
  scratch := 0

end VG.Impl.Aes.AArch64
