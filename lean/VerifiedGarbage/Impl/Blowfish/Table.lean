module

public import VerifiedGarbage.Spec.Blowfish

/-!
# The initial schedule, as a table of constants

Key expansion starts from `Spec.Blowfish.initial` in the memory layout of
`scheduleAt`: the S-boxes in byte planes, then the P-array. `initWords` is
that image, 4168 bytes, as 521 little-endian 64-bit words, for a `static`.
-/

@[expose] public section

namespace VG.Impl.Blowfish

open VG VG.Spec.Blowfish

/-- Byte `o` of the initial schedule in the layout of `scheduleAt`. -/
def initByte (o : Nat) : Byte :=
  if o < 4096 then
    (initial.getD (18 + 256 * (o / 1024) + o % 256) 0 >>> (8 * (o % 1024 / 256))).setWidth 8
  else (initial.getD ((o - 4096) / 4) 0 >>> (8 * ((o - 4096) % 4))).setWidth 8

/-- Word `i` of the table: bytes `8 i`…`8 i + 7`, little-endian. -/
def initWord (i : Nat) : BitVec 64 :=
  (List.range 8).foldl (fun w b => w ||| (initByte (8 * i + b)).zeroExtend 64 <<< (8 * b)) 0

def initWords : List (BitVec 64) := (List.range 521).map initWord

end VG.Impl.Blowfish
