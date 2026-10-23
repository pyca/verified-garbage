module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Gathering a list of slices: PPC64LE

`gather` copies the `r8` slices that the descriptors at `r7` list (each an
address and a length, 16 bytes), one after the other, to `r9`, as the
functions encrypting out of place from a list of slices do before encrypting
in place (`seal_gather`). With `r3` the slice's address and `r4` its length,
it copies its whole doublewords through `r0`, `r5` counting them
(`copyWords`), then its last `len mod 8` bytes one at a time through `r0`
(`copyBytes`). It writes only `r0` and `r3`–`r9`, all caller-saved, and its
branches are on the number of slices and their lengths alone.
-/

@[expose] public section

namespace VG.Impl.Gather.PPC64LE

open VG.PPC64LE

/-- Copies the `r5` (at least 1) doublewords at `r3` to `r9`, advancing both. -/
def copyWords : Prog isa :=
  .loop (.block [.load .d .r0 .r3 0, .store .d .r0 .r9 0, .addi .r3 .r3 8, .addi .r9 .r9 8,
    .subi .r5 .r5 1]) (.nonzero .d .r5)

/-- Copies the `r4` (at least 1) bytes at `r3` to `r9`, advancing both. -/
def copyBytes : Prog isa :=
  .loop (.block [.lbz .r0 .r3 0, .stb .r0 .r9 0, .addi .r3 .r3 1, .addi .r9 .r9 1,
    .subi .r4 .r4 1]) (.nonzero .d .r4)

/-- The number of whole doublewords of the slice, in `r5`. -/
def wordsArg : List Instr := [.lsr .d .r5 .r4 3]

/-- The number of its last bytes, in `r4`. -/
def bytesArg : List Instr := [.li .r6 7, .logic .and .r4 .r4 .r6]

/-- Copies the `r4` bytes at `r3` to `r9`, advancing `r9` past them. -/
def copySlice : Prog isa :=
  .seq (.block wordsArg)
  (.seq (.ite (.zero .d .r5) (.block []) copyWords)
  (.seq (.block bytesArg)
    (.ite (.zero .d .r4) (.block []) copyBytes)))

/-- The next descriptor: the slice's address in `r3` and length in `r4`. -/
def next : List Instr := [.load .d .r3 .r7 0, .load .d .r4 .r7 8, .addi .r7 .r7 16]

/-- Copies the `r8` (at least 1) slices that the descriptors at `r7` list to
`r9`, one after the other. -/
def gatherLoop : Prog isa :=
  .loop (.seq (.block next) (.seq copySlice (.block [.subi .r8 .r8 1]))) (.nonzero .d .r8)

/-- Copies the `r8` slices that the descriptors at `r7` list to `r9`. -/
def gather : Prog isa := .ite (.zero .d .r8) (.block []) gatherLoop

end VG.Impl.Gather.PPC64LE
