module

public import VerifiedGarbage.Impl.Scrub.X86_64

/-!
# The cleanup as part of the code (x86-64)

A function's code as emitted, its body and then its cleanup, is a named
definition in `Impl/` (`Impl.<Alg>.X86_64.Fn.<f>`), written with the
cleanup's literals: the level of its vector registers, the result's bits it
keeps, the bytes of stack its frames and calls use and, where only some of
them may hold secrets, the runs of 16-byte granules it zeroes:

    def Fn.cbcInit : Prog isa := scrubSel .sse 32 600 [(552, 3)] (…)

Both cleanups clear every SSE register (and at the level `evex`
`zmm16`–`zmm31`), every caller-saved general-purpose register but the
result's `rb` bits, and wipe the stack below the stack pointer in
`chunksA n`, whose 16-byte stores are aligned. Neither writes MXCSR: the
code they follow leaves it as two runs found it. `scrubAll` wipes every
granule of the `n` bytes; `scrubSel` only the runs the residue analysis
(`X86_64.RTaint`) finds may differ between two runs.
-/

@[expose] public section

namespace VG.Impl.Scrub.X86_64

open VG.X86_64

/-- `n` bytes of stack in chunks whose 16-byte granules are aligned: 8 bytes
at the top (the stack pointer on entry is 8 off 16), then `chunks`. -/
def chunksA (n : Nat) : List Nat := if n ≤ 8 then chunks n else 8 :: chunks (n - 8)

/-- The granules of the runs `rs`, each `(off, k)`: `k` granules from the
offset `off` (from the bottom of the wiped stack) up. -/
def runKs : List (Nat × Nat) → List Nat
  | [] => []
  | (off, k) :: rs => (List.range k).map (fun t => off + 16 * t) ++ runKs rs

/-- Every granule of the chunks `cs` (from the top), each chunk's 16-byte
granules ending at its top and an 8-byte one at its bottom if its size is
not a multiple of 16. -/
def wipeKs : List Nat → List Nat
  | [] => []
  | b :: bs => bs.sum :: ((List.range (b / 16)).map fun t => bs.sum + b % 16 + 16 * t) ++ wipeKs bs

/-- The caller-saved registers the tail clears after the wipe of the
granules `ks`: all of them, but `r11`, which the wipe stores and so clears
before, if it stores any. -/
def gsAll (ks : List Nat) : List Reg := if ks = [] then scratchRegs else scratchRegs.erase .r11

/-- `c`, then the clearing of every vector register at the level `v`, of
the granules `ks` of the `n` bytes below the stack pointer (`chunksA n`),
and of every caller-saved register but the `rb` bits of the result. -/
def scrubKs (v : VecLevel) (rb n : Nat) (ks : List Nat) (c : Prog isa) : Prog isa :=
  scrub v rb xregs (psOf ks) (gsAll ks) ks (chunksA n) c .avx

/-- `scrubKs`, wiping only the runs of granules `rs`. -/
def scrubSel (v : VecLevel) (rb n : Nat) (rs : List (Nat × Nat)) (c : Prog isa) : Prog isa :=
  scrubKs v rb n (runKs rs) c

/-- `scrubKs`, wiping every granule of the `n` bytes. -/
def scrubAll (v : VecLevel) (rb n : Nat) (c : Prog isa) : Prog isa :=
  scrubKs v rb n (wipeKs (chunksA n)) c

end VG.Impl.Scrub.X86_64
