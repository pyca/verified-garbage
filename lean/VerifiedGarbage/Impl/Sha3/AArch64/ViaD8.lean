module

public import VerifiedGarbage.Impl.Sha3.AArch64.Callee
public import VerifiedGarbage.Impl.ICall
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# Calling a Keccak permutation by the address in `d8`

A function that is the same code for every Keccak permutation it calls
calls the permutation by its address, which its caller leaves in the low 64
bits of `v8` (`d8`, which the calling convention preserves across calls):
`umov x16, v8.d[0]`, then `blr x16`, an indirect call of `c`
(`Code.icalls`), whose printed code does not name `c`. `entryD8 n name body`
is the function that calls such a function, `name`, whose code is `body`,
with the address of `n` in `d8`, in a frame of 16 bytes: its return address
at `sp`, and its caller's `d8` at `sp + 8`, which it restores.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64

open VG.AArch64

/-- The call of `c` by the address in `v8`'s low 64 bits. -/
def Callee.viaD8 (c : Callee) : Prog isa :=
  .seq (.block [.umov .x .x16 .v8 0]) (Code.icalls (.blr .x16) [(c.name, c.code)])

/-- `umov x16, v8.d[0]; str x30, [sp]; str x16, [sp, #8]; adrp/add x16, n;
ins v8.d[0], x16`: save the return address and `d8`, and put `n`'s address
in `d8`. -/
def enterD8 (n : String) : List Instr :=
  [.umov .x .x16 .v8 0, .strSp .x30 0, .strSp .x16 8, .adrSym .x16 n, .vop (.ins .d2 .v8 0 .x16)]

/-- `ldr x16, [sp, #8]; ins v8.d[0], x16; ldr x30, [sp]`: restore `d8` and
the return address. -/
def leaveD8 : List Instr := [.ldrSp .x16 8, .vop (.ins .d2 .v8 0 .x16), .ldrSp .x30 0]

/-- A call of `name`, whose code is `body`, with `n`'s address in `d8`. -/
def entryD8 (n name : String) (body : Prog isa) : Prog isa :=
  .frame (.alloc 16) (.seq (.block (enterD8 n)) (.seq (.call name body) (.block leaveD8))) (.free 16)

/-- Where `entryD8S` saves the return address and `d8`, above the copies of
`k` stack words, rounded up to 16 bytes. -/
def saveOff (k : Nat) : Nat := 8 * (k + k % 2)

/-- The frame of `entryD8S` for `k` stack words. -/
def frameS (k : Nat) : Nat := saveOff k + 16

/-- `enterD8` after copying the caller's `k` stack words into the bottom of
the frame (`copyArg`, as `withStackArgScratch` does): save the return address and
`d8` above them, and put `n`'s address in `d8`. -/
def enterD8S (n : String) (k : Nat) : List Instr :=
  .addSp .x16 0 :: (List.range k).flatMap (Impl.StackScratch.AArch64.copyArg (frameS k)) ++
    [.umov .x .x16 .v8 0, .strSp .x30 (saveOff k), .strSp .x16 (saveOff k + 8), .adrSym .x16 n,
      .vop (.ins .d2 .v8 0 .x16)]

/-- `leaveD8`, from above the copies of `k` stack words. -/
def leaveD8S (k : Nat) : List Instr :=
  [.ldrSp .x16 (saveOff k + 8), .vop (.ins .d2 .v8 0 .x16), .ldrSp .x30 (saveOff k)]

/-- `entryD8` for a function with `k` stack words: the call of `name`, whose
code is `body`, with `n`'s address in `d8`, from a frame that holds a copy of
the caller's stack words at its bottom, where `body` finds its own, then the
return address and the caller's `d8`. -/
def entryD8S (n name : String) (k : Nat) (body : Prog isa) : Prog isa :=
  .frame (.alloc (frameS k))
    (.seq (.block (enterD8S n k)) (.seq (.call name body) (.block (leaveD8S k)))) (.free (frameS k))

/-- For each function `n` and register `v` that `L` lists, the `i`-th from
`i`: save `v`'s low 64 bits at `sp + o + 8 + 8i` and put `n`'s address there. -/
def saveRegs (o : Nat) : Nat → List (String × VReg) → List Instr
  | _, [] => []
  | i, (n, v) :: L =>
    [.umov .x .x16 v 0, .strSp .x16 (o + 8 + 8 * i), .adrSym .x16 n, .vop (.ins .d2 v 0 .x16)] ++
      saveRegs o (i + 1) L

/-- Restore the low 64 bits of each register `L` lists, saved by `saveRegs`. -/
def restoreRegs (o : Nat) : Nat → List (String × VReg) → List Instr
  | _, [] => []
  | i, (_, v) :: L => [.ldrSp .x16 (o + 8 + 8 * i), .vop (.ins .d2 v 0 .x16)] ++ restoreRegs o (i + 1) L

/-- The frame of `entryDS` for `k` stack words and `j` registers: the copies
of the stack words, then the return address and the registers' low halves,
in 16-byte units. -/
def frameDS (k j : Nat) : Nat := saveOff k + 8 * ((j + 1) + (j + 1) % 2)

/-- Copy the caller's `k` stack words into the bottom of the frame (as
`withStackArgScratch` does), save the return address above them, then each
register `L` lists, putting in it the address of the function `L` pairs it
with. -/
def enterDS (L : List (String × VReg)) (k : Nat) : List Instr :=
  .addSp .x16 0 :: (List.range k).flatMap (Impl.StackScratch.AArch64.copyArg (frameDS k L.length)) ++
    .strSp .x30 (saveOff k) :: saveRegs (saveOff k) 0 L

/-- Restore the registers and the return address. -/
def leaveDS (L : List (String × VReg)) (k : Nat) : List Instr :=
  restoreRegs (saveOff k) 0 L ++ [.ldrSp .x30 (saveOff k)]

/-- The call of `name`, whose code is `body`, with the address of each
function `L` lists in the register it pairs it with, from a frame that holds
a copy of the caller's `k` stack words at its bottom, where `body` finds its
own, then the return address and the caller's registers. -/
def entryDS (L : List (String × VReg)) (name : String) (k : Nat) (body : Prog isa) : Prog isa :=
  .frame (.alloc (frameDS k L.length))
    (.seq (.block (enterDS L k)) (.seq (.call name body) (.block (leaveDS L k)))) (.free (frameDS k L.length))

/-- What the cleanup of a function that calls code made so by `entryDS L`
clears: every general-purpose and vector register the calling convention
does not preserve, and the high halves of the registers `L` gives, which
`entryDS` writes the low halves of. -/
def clearDL (L : List (String × VReg)) : Impl.Scrub.AArch64.Clear :=
  ⟨Impl.Scrub.AArch64.allGprs, Impl.Scrub.AArch64.allVecs, L.map (·.2)⟩

/-- `umov x16, v.d[0]; blr x16`: the call of `n`, whose code is `b`, by the
address in the low 64 bits of `v`. -/
def callDV (v : VReg) (n : String) (b : Prog isa) : Prog isa :=
  .seq (.block [.umov .x .x16 v 0]) (.icall (.blr .x16) n b (.block []))

/-- `c` with each call of a function `L` names made a call by the address in
the register `L` gives it, in the bodies of the functions it calls too: code
that is the same for every implementation of those functions it calls. -/
def Code.viaDAt (L : List (String × VReg)) : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (viaDAt L a) (viaDAt L b)
  | .ite cd a b => .ite cd (viaDAt L a) (viaDAt L b)
  | .loop b cd => .loop (viaDAt L b) cd
  | .call m b => match L.lookup m with
    | some v => callDV v m (viaDAt L b)
    | none => .call m (viaDAt L b)
  | .frame i b j => .frame i (viaDAt L b) j
  | .icall i m b nx => .icall i m b nx

/-- `callDV` by `d8`. -/
abbrev callD8 (n : String) (b : Prog isa) : Prog isa := callDV .v8 n b

/-- `Code.viaDAt` of one function, by `d8`. -/
abbrev Code.viaD8At (n : String) (c : Prog isa) : Prog isa := Code.viaDAt [(n, .v8)] c

/-- What the cleanup of a function that calls code made so by `entryD8`
clears: every general-purpose and vector register the calling convention
does not preserve, and the high half of `v8`, which `entryD8` writes the low
half of. -/
def clearD8 : Impl.Scrub.AArch64.Clear :=
  ⟨Impl.Scrub.AArch64.allGprs, Impl.Scrub.AArch64.allVecs, [.v8]⟩

end VG.Impl.Sha3.AArch64
