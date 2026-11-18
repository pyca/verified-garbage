module

public import VerifiedGarbage.Impl.Camellia.Arm.Ecb
public import VerifiedGarbage.Impl.Modes.Arm.SeqKeyed

/-!
# Camellia ECB on ARMv7 from a table built once

`ecb dir` (`Ecb.lean`) bitslices the subkeys into its table at every call.
A mode that enciphers its blocks one at a time, each depending on the one
before, has the table built once in the working space it gives every call
(`ecbKeys`), and each block enciphered from it (`ecbKeyed`): the two halves
of `ecb dir`, with the same working space and layout (`Layers.lean`).

`scrCore dir` is `ecb dir` as the modes of `Impl/Modes/Arm/Seq.lean` see a
core that takes its working space as a stack argument, and `keyed dir` the
two functions that split it (`Impl/Modes/Arm/SeqKeyed.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Modes.Arm

/-- `vg_camellia_ecb_encrypt_keys` (or `vg_camellia_ecb_decrypt_keys`)
`(schedule = r0, rounds = r1, scratch = r2)`: the table of `ecb dir` for 18
or 24 rounds, in the scratch buffer, where `ecb dir` builds it; the
callee-saved registers wait in their slots meanwhile. -/
def ecbKeys (dir : Dir) : Prog isa :=
  .seq (.block (([movR .r12 .r2] : List Instr) ++ saveRegs .r12 ++
      ([movR sb .r12, movR .r12 .r0, .cmp .r1 (.imm 18)] : List Instr)))
    (.seq (keys dir) (.block (([movR .r12 sb] : List Instr) ++ restoreRegs .r12)))

/-- The address of the postwhitening's entry of the table for `g` groups, to
`lr`, as `keys` leaves it. -/
def endOf (g : Nat) : List Instr := [.dp .add .lr sb (.imm (BitVec.ofNat 32 (4 * keySlot + 512 * g)))]

/-- `vg_camellia_ecb_keyed(schedule = r0, rounds = r1, data = r2, n = r3,
scratch = [sp])`: `ecb` in either direction without its table's
construction, from the table `ecbKeys` left in the scratch buffer for that
direction, which it leaves as it is. It does not read `schedule`. -/
def ecbKeyed : Prog isa :=
  .seq (.block (([.ldrSp .r12 0] : List Instr) ++ saveRegs .r12 ++
      ([movR sb .r12, .cmp .r1 (.imm 18), movR .r1 .r2, movR .r2 .r3] : List Instr)))
    (.seq (.ite .eq (.block (endOf 3)) (.block (endOf 4)))
      (.seq (.block [.cmp .r2 (.imm 0)])
        (.seq (.ite .eq (.block []) (.loop group .ne))
          (.block (([movR .r12 sb] : List Instr) ++ restoreRegs .r12)))))

/-- `ecb dir` with its working space as a stack argument, as a mode's core:
the function the two of `keyed dir` split, which gives a mode its layout
(the working space at the end of its scratch buffer) and the cipher. No code
calls it by this name: the modes call the two of `keyed dir` instead. -/
def scrCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => "vg_camellia_ecb_encrypt_scratch"
    | .decrypt => "vg_camellia_ecb_decrypt_scratch"
  code := ecb dir
  bw := 4
  rounds := true
  stackScratch := 4 * slots

/-- The functions that build the table of a direction, and encipher with it. -/
def keyed (dir : Dir) : Keyed where
  keysName := match dir with
    | .encrypt => "vg_camellia_ecb_encrypt_keys"
    | .decrypt => "vg_camellia_ecb_decrypt_keys"
  keysCode := ecbKeys dir
  name := "vg_camellia_ecb_keyed"
  code := ecbKeyed

end VG.Impl.Camellia.Arm
