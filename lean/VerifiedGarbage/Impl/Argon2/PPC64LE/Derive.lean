module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.Fill
public import VerifiedGarbage.Impl.Argon2.PPC64LE.MemoryInit

/-!
# Argon2 on PPC64LE: the derivation

`vg_argon2(kind = r3, password = r4, password_len = r5, salt = r6,
salt_len = r7, iterations = r8, memory_cost = r9, lanes = r10, threads,
secret, secret_len, associated_data, ad_len, memory, blocks, scratch, out,
out_len)`, the last ten in the caller's Parameter Save Area.

The derivation allocates its frame (`Impl/Argon2/PPC64LE/Layout.lean`),
saves the return address and the caller's `r28`–`r31` and its register
arguments there, and points `r30` to the frame and `r31` to `scratch`
throughout. It computes the parameters and H₀, initializes the memory, fills
it, XORs the last block of every lane into the first block of the memory,
and writes H′ of it to `out`. The lanes are evaluated serially, which every
positive `threads` permits.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Derive

open VG.PPC64LE

/-! ## The final block and the tag -/

/-- Zero the memory's first block. -/
def reduceClear : List Instr :=
  [lda .r6 memoryArg, .li .r3 0] ++ (List.range 128).map fun k => .store .d .r3 .r6 (8 * k)

/-- XOR the last block of lane `[r30 + laneOff]` into the first block. -/
def reduceLane : List Instr :=
  [ld .r3 laneOff, ld .r4 laneLenOff, .subi .r4 .r4 1] ++ blockAddr ++
    ([HPrime.mov .r4 .r3, lda .r6 memoryArg] : List Instr) ++ writeBlock true

def reduce : Prog isa :=
  .seq (.block (reduceClear ++ setLocal laneOff 0))
    (.loop (.block (reduceLane ++ advanceBy laneOff (ldw .r4 lanesArg))) (.nonzero .d .r4))

/-- `hprime(memory, 1024, out, out_len, scratch)`. -/
def finalOutput : Prog isa :=
  .seq (.block [lda .r3 memoryArg, .li .r4 1024, lda .r5 outArg, lda .r6 outLenArg,
      HPrime.mov .r7 .r31])
    hPrimeCall

/-! ## The whole function -/

/-- The caller's registers, and where they are saved. -/
def savedSlots : List (Reg × Nat) := [(.r28, 112), (.r29, 120), (.r30, 128), (.r31, 136)]

/-- The register arguments, `r3`–`r10`, and where they are saved. -/
def argSlots : List (Reg × Nat) :=
  [(.r3, 144), (.r4, 152), (.r5, 160), (.r6, 168), (.r7, 176), (.r8, 184), (.r9, 192), (.r10, 200)]

/-- Save the return address, the caller's registers and the register
arguments, and point `r30` to the frame and `r31` to `scratch`. -/
def setup : List Instr :=
  [.addSp .r12 0, .mflr .r0, .store .d .r0 .r12 lrOff] ++
  (savedSlots ++ argSlots).map (fun (r, d) => .store .d r .r12 d) ++
  [HPrime.mov .r30 .r12, lda .r31 scratchArg]

/-- The caller's registers, in the order they are restored: `r30`, the
frame's pointer, last. -/
def restoreSlots : List (Reg × Nat) := [(.r28, 112), (.r29, 120), (.r31, 136), (.r30, 128)]

/-- Restore the return address and the caller's registers. -/
def restore : List Instr :=
  [ld .r0 lrOff, .mtlr .r0] ++ restoreSlots.map (fun (r, d) => .load .d r .r30 d)

def body : Prog isa :=
  .seq (.block (setup ++ parameters))
  (.seq code
  (.seq memoryInit
  (.seq passesLoop
  (.seq reduce
  (.seq finalOutput (.block restore))))))

def derive : Prog isa := .frame (.alloc locals) body (.free locals)

end VG.Impl.Argon2.PPC64LE.Derive
