module

public import VerifiedGarbage.Proof.Camellia.Arm.Linear
public import VerifiedGarbage.Impl.Camellia.Arm.ExpandKey
import Mathlib.Tactic.SplitIfs

/-!
# Camellia's key schedule on ARMv7: the transposes of one value

`pairPlain` runs the bitsliced rounds on eight copies of the running value:
`bcast_check`, each of its four words (at `wSlot`) in all eight lanes,
transposed into the planes of the halves (input words `0 … 3`); and
`unbcast_check`, lane 0's words back from the planes (input words
`0 … 31`, the planes at `d1Slot`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Bitslice VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR ldS stS ortho)
open VG.Proof.Sm4.Arm (linEnvG linPostG)

/-- The value's words to the planes. -/
def bcast : List Instr :=
  (List.range 4).flatMap fun w =>
    [ldS (q 0) (wSlot + w)] ++ (List.range 7).map (fun i => movR (q (i + 1)) (q 0)) ++ ortho ++
      (List.range 8).map (fun j => stS (stateSlot w j) (q j))

/-- Lane 0's words back from the planes. -/
def unbcast : List Instr :=
  (List.range 4).flatMap fun w =>
    (List.range 8).map (fun j => ldS (q j) (stateSlot w j)) ++ ortho ++ [stS (wSlot + w) (q 0)]

theorem pairPlain_eq : pairPlain = bcast ++ (round 0 d1Slot d2Slot ++ round 16 d2Slot d1Slot) ++
    (unbcast ++ ([.dp .add kp kp (.imm 128)] : List Instr)) := by
  simp only [pairPlain, bcast, unbcast, List.append_assoc]

def bcastEnv : Env (Nat × Nat) := linEnvG [] ((List.range 4).map fun w => (wSlot + w, w)) []

/-- Plane `j` of the state's word `w`, at `8 i + b`: bit `8 i + j` of the value's word `w`. -/
def bcastG (w j p : Nat) : List Nat := [32 * w + 8 * (p / 8) + j]

def bcastOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 32).map fun k => (d1Slot + k, bcastG (k / 8) (k % 8))

theorem bcast_check :
    check (lanes 32 7) fromBsCfg (linExt 0) bcast bcastEnv (linPostG 7 [] bcastOuts [] bcastEnv) = true := by
  decide +kernel

def unbcastEnv : Env (Nat × Nat) := linEnvG [] ((List.range 32).map fun k => (d1Slot + k, k)) []

/-- Bit `8 i + j` of the value's word `w`: plane `j` of the state's word `w`, at `8 i` (lane 0). -/
def unbcastG (w t : Nat) : List Nat := [32 * (8 * w + t % 8) + 8 * (t / 8)]

def unbcastOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 4).map fun w => (wSlot + w, unbcastG w)

theorem unbcast_check :
    check (lanes 32 10) fromBsCfg (linExt 0) unbcast unbcastEnv
      (linPostG 10 [] unbcastOuts [] unbcastEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.Arm
