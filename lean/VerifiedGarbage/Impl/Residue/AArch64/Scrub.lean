module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Clearing the stack a function used before returning (AArch64)

`withScrub W c` runs `c`, then zeroes the `W` bytes below the stack pointer,
where `c`'s frames were: it opens a frame of `W` bytes (`sub sp, sp, #W`),
zeroes it 16 bytes at a time (`str q31, [x9, #16k]`, `x9` its base and `q31`
zero), and releases it. What `c`'s frames held is then gone from the stack
below the stack pointer, where its caller cannot clear it. `W` is a multiple
of 16, below 4096, and at most what the contract lets the function use of
the stack.
-/

@[expose] public section

namespace VG.Impl.Residue.AArch64

open VG.AArch64

/-- `str q31, [x9, #16k]` for each `k < n`. -/
def scrubStores (n : Nat) : List Instr := (List.range n).map fun k => .strq .v31 .x9 (16 * k)

/-- `movi v31.2d, #0`, `add x9, sp, #0`, then the stores of the `W` bytes from `x9`. -/
def scrubBlock (W : Nat) : List Instr := .vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStores (W / 16)

/-- The frame of `W` bytes, zeroed. -/
def scrubTail (W : Nat) : Prog isa := .frame (.alloc W) (.block (scrubBlock W)) (.free W)

/-- What clears the bits of `x0` above an `rb`-bit result: all of it (`movz x0, #0`)
for no result, its upper half (`add w0, w0, #0`) for a 32-bit one. -/
def retFix : Nat → List Instr
  | 0 => [.movz .x .x0 0 0]
  | 32 => [.addImm .w .x0 .x0 0]
  | _ => []

/-- `c`, then the bits of `x0` above an `rb`-bit result cleared. -/
def withRet (rb : Nat) (c : Prog isa) : Prog isa := .seq c (.block (retFix rb))

/-- `c`, then the `W` bytes below the stack pointer zeroed. -/
def withScrub (W : Nat) (c : Prog isa) : Prog isa := .seq c (scrubTail W)

/-- `str q31, [x9, #16k]` for each `k` of `ks`. -/
def scrubStoresL (ks : List Nat) : List Instr := ks.map fun k => .strq .v31 .x9 (16 * k)

/-- The frame of `W` bytes, with its 16-byte granules `ks` zeroed. -/
def scrubTailG (W : Nat) (ks : List Nat) : Prog isa :=
  .frame (.alloc W) (.block (.vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStoresL ks)) (.free W)

/-- The frame of `W` bytes, `4080 < W < 8176`, with all its 16-byte granules
zeroed: as two frames, one of `W - 4080` bytes and below it one of 4080, since
an `alloc` takes less than 4096 bytes; the stores, from the inner frame's
base, reach the outer one too. -/
def scrubTailL (W : Nat) : Prog isa :=
  .frame (.alloc (W - 4080))
    (.frame (.alloc 4080) (.block (.vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStoresL (List.range (W / 16))))
      (.free 4080))
    (.free (W - 4080))

/-- `c`, then the granules `ks` of the `W` bytes below the stack pointer
zeroed; nothing if there are none. -/
def withScrubG (W : Nat) (ks : List Nat) (c : Prog isa) : Prog isa :=
  match ks with
  | [] => c
  | _ => .seq c (scrubTailG W ks)

/-- The general-purpose registers the calling convention does not preserve, but `x0`. -/
def allGprs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The vector registers the calling convention does not preserve at all. -/
def allVecs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
   .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- The vector registers whose low halves the calling convention preserves. -/
def hiVecs : List VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]

/-- What the tail clears: the general-purpose registers `gprs` (of
`allGprs`), the vector registers `vecs` (of `allVecs`), and the high halves
of `his` (of `hiVecs`). `Proof/Framework/AArch64/Writes.lean` computes it from
the code (`Clear.of`): the registers the code may write. -/
structure Clear where
  gprs : List Reg
  vecs : List VReg
  his : List VReg

/-- Every register the calling convention does not preserve. -/
def Clear.all : Clear := ⟨allGprs, allVecs, hiVecs⟩

/-- `movz` of each of `gprs`, `movi` of each of `vecs`, the flags from `x1`
(`tst x1, x1`), and the high halves of `his` from `x1` (`mov v.d[1], x1`).
`x1` is either cleared or holds what it held on entry, the same in two runs
that agree on what is public. -/
def clearsOf (cl : Clear) : List Instr :=
  cl.gprs.map (fun r => .movz .x r 0 0) ++ cl.vecs.map (fun v => .vop (.movi0 v)) ++
    [.tst .x .x1 .x1] ++ cl.his.map (fun v => .vop (.ins .d2 v 1 .x1))

/-- `clearsOf Clear.all`. -/
abbrev clearsAll : List Instr := clearsOf Clear.all

/-- `c`, then the registers of `cl` cleared but the result's `rb` bits of
`x0`, and the `W` bytes below the stack pointer zeroed: what returns without
secret residue whatever `c` leaves, for code whose frames stay within those
`W` bytes and that writes no register `cl` leaves (`ScrubAll.noResidue_scrubAll`). -/
def scrubAll (W rb : Nat) (cl : Clear) (c : Prog isa) : Prog isa :=
  withScrubG W (List.range (W / 16)) (withRet rb (.seq c (.block (clearsOf cl))))

/-- `scrubAll` for `4080 < W < 8176` bytes of stack, zeroed by `scrubTailL`. -/
def scrubAllL (W rb : Nat) (cl : Clear) (c : Prog isa) : Prog isa :=
  .seq (withRet rb (.seq c (.block (clearsOf cl)))) (scrubTailL W)

end VG.Impl.Residue.AArch64
