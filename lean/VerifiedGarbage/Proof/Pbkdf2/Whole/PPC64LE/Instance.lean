module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: an instance

The functions `pbkdf2` calls for each hash function `H` of instance `I`
(`fnsOf`): HMAC's `init` for a key of any length (`initCode`, its working
space in a frame of `hmacFrame I` bytes, which uses `hmacFrame I + 96` bytes
of stack, `sdepth_initCode`) and `finalize`, and `iterate`; the facts the
proofs need of them (`okOf`); and a state satisfying `pbkdf2`'s shared
precondition, at each instance's sizes (`pbkSat`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK finG hmacFrame longFrame initCode)
open VG.Proof.Pbkdf2.Stream.PPC64LE (iterG)

/-- The functions `pbkdf2` calls, for hash function `H` of instance `I`, with
blocks of `2 ^ b` bytes, and `iterate`'s code `itC`, with `itW` bytes of
working space. -/
def fnsOf (H : Hash) (I : Spec.Hmac.Instance) (b : Nat) (itC : Prog isa) (itW : Nat) : Fns where
  H := H
  Wc := 8 * I.scratch
  hiN := I.initAnyKeyApi.name
  hiC := initCode H I b
  hfN := s!"vg_hmac_{I.rust}_finalize_scratch"
  itN := s!"vg_pbkdf2_hmac_{I.rust}_iterate"
  itC := itC
  itW := itW

/-- HMAC's `init` uses its frame and the 96 bytes its callees use below it. -/
theorem sdepth_initCode {H : Hash} (hH : HashOK H) (I : Spec.Hmac.Instance) (b : Nat) (h48 : 48 ≤ hmacFrame I) :
    sdepth (initCode H I b) ≤ hmacFrame I + 96 := by
  have hi := sdepth_le_fdepth _ (Proof.Hmac.Stream.PPC64LE.InitLong.init_pf hH)
  have hid := Proof.Hmac.Stream.PPC64LE.InitLong.init_fdepth hH
  have hl := sdepth_le_fdepth H.initLong (by
    simp [Hash.initLong, pushFrames, Instr.isPush, Proof.Hmac.Stream.PPC64LE.InitLong.initLongMain_pf hH])
  have hld : H.initLong.fdepth ≤ 3 := by
    have := Proof.Hmac.Stream.PPC64LE.InitLong.initLongMain_fdepth hH
    simp only [Hash.initLong, Code.fdepth]; omega
  simp only [initCode, Hash.initEntry, Code.iteCold, Impl.StackScratch.PPC64LE.withStackScratchWiped,
    Impl.StackScratch.PPC64LE.withStackScratch, sdepth, Instr.frameBytes, longFrame, Nat.max_le] at *
  omega

/-- The facts about the functions `pbkdf2` calls, from their proofs. -/
def okOf {H : Hash} (hH : HashOK H) {I : Spec.Hmac.Instance} {b : Nat} {itC : Prog isa} {itW : Nat}
    (hSH : hH.SH = I.S)
    (hi : Verified PPC64LE.target (initCode H I b) (I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame I)))
    (hf : ConstantTime isa (finG hH.SH (H.W + 48 + H.FD) 96).pre (finG hH.SH (H.W + 48 + H.FD) 96).pub
      H.finalize)
    (itOk : ∀ s, (iterG hH.SH itW 96).pre s →
      ∃ t s', Exec isa itC s t s' ∧ abiPreserved s s' ∧ (iterG hH.SH itW 96).post s s')
    (it : ConstantTime isa (iterG hH.SH itW 96).pre (iterG hH.SH itW 96).pub itC)
    (itFd : itC.fdepth ≤ 2) (itPf : pushFrames itC = true)
    (hWc : H.W + 48 + H.S + H.FD + H.FD ≤ 8 * I.scratch) (hIt : itW ≤ 8 * I.scratch) (hX : hmacFrame I ≤ 4096)
    (h48 : 48 ≤ hmacFrame I) (reach : (fnsOf H I b itC itW).bytes ≤ 4096) : FnsOK (fnsOf H I b itC itW) where
  hH := hH
  X := hmacFrame I
  hi := by
    have e : hiK hH.SH (hmacFrame I) = I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame I) := by
      rw [hiK, Nat.add_comm, hSH]; rfl
    rw [e]; exact hi.1
  hiCt := by
    have e : hiK hH.SH (hmacFrame I) = I.initAnyKeyContract PPC64LE.abi (96 + hmacFrame I) := by
      rw [hiK, Nat.add_comm, hSH]; rfl
    rw [e]; exact hi.2.1
  hiSd := sdepth_initCode hH I b h48
  hfCt := hf
  itOk := itOk
  itCt := it
  itFd := itFd
  itPf := itPf
  hWc := hWc
  hIt := hIt
  hX := hX
  reach := reach

/-- A state satisfying `pbkdf2`'s precondition, with `sc` bytes of scratch
space (none: the frame holds it): an empty password, salt and output, and
`c = 1`. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r5 => 0x20000 | .r7 => 1 | .r8 => 0x30000 | .r10 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩]
  wr := [⟨0x30000, 0⟩, ⟨0x40000, sc⟩]

/-- `pbkSat` without the working space: a state satisfying the precondition
of `pbkdf2` with its working space on the stack. -/
def pbkSat0 : State := { pbkSat 0 with wr := [⟨0x30000, 0⟩] }

end VG.Proof.Pbkdf2.Whole.PPC64LE
