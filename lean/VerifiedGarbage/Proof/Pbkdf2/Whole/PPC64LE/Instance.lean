module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.CT
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Correct
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Instance
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common

/-! ### `Pbkdf2.Whole.PPC64LE.Shared`, which only this module used -/

section

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the shared contracts

`pbkdf2`'s generic proof (`correct`, `ct`) is written against `pbkG`, with
the `F.bytes` bytes of scratch space the code uses. It is widened to the
working space of the shared contract (`Verified.widen`) and moved to it
(`generic_implies`), for any instance `I` of the hash function whose
`pbkdf2Scratch` holds `F.bytes` (`scratch`). The function without the
working space as an argument runs it in a frame of `pbkFrame I` bytes
(`Verified.stackScratch`, `framed`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)

variable {F : Fns}

theorem pbkImp (S : Spec.Hmac.StreamingHash) (n X : Nat)
    (hs : ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract S n PPC64LE.abi (X + 144)).pre s) :
    (pbkG S (8 * n) (X + 144)).Implies (Proof.Pbkdf2.pbkdf2ScratchContract S n PPC64LE.abi (X + 144)) := by
  generic_implies [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, pbkG, PPC64LE.abi, PPC64LE.argRegs] using hs

/-- `pbkdf2` with its working space as an argument, against the shared contract. -/
theorem scratch (hF : FnsOK F) (hc : Checks F) {I : Spec.Hmac.Instance} (hSH : hF.hH.SH = I.S)
    (hfit : F.bytes ≤ 8 * I.pbkdf2Scratch)
    (hs : ∃ s, (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I PPC64LE.abi (hF.X + 144)).pre s) :
    Verified PPC64LE.target F.pbkdf2 (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I PPC64LE.abi (hF.X + 144)) := by
  have imp : (pbkG I.S (8 * I.pbkdf2Scratch) (hF.X + 144)).Implies
      (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I PPC64LE.abi (hF.X + 144)) := pbkImp I.S I.pbkdf2Scratch hF.X hs
  rw [← hSH] at imp
  have wide : ∀ s, (pbkG hF.hH.SH (8 * I.pbkdf2Scratch) (hF.X + 144)).pre s →
      (pbkG hF.hH.SH F.bytes (hF.X + 144)).pre (s.withRegions s.rd [⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
        ⟨s.gpr .r10, F.bytes⟩]) := by
    intro s ⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    exact ⟨h1, rfl, h3, h4.sub_right (Region.sub_prefix hfit), h5, h6.sub_right (Region.sub_prefix hfit),
      h7.sub_right (Region.sub_prefix hfit), h8, h9, h10, h11, h12.sub_right (Region.sub_prefix hfit), h13, h14,
      h15, by show (s.gpr .r10).toNat + F.bytes ≤ 2 ^ 64; omega_using [hfit, h16], h17, h18⟩
  have v : Verified PPC64LE.target F.pbkdf2 (pbkG hF.hH.SH F.bytes (hF.X + 144)) :=
    ⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := correct hF hs; exact ⟨t, s', he, h₁, h₂⟩, ct hF hc,
      imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨s.gpr .r10, F.bytes⟩]) wide
      (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) imp.sat_left).of_implies imp
  obtain ⟨_, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil)

/-- The bytes of `pbkdf2`'s frame: the working space, above the frame's
32-byte header, rounded up to a multiple of 16. -/
def pbkFrame (I : Spec.Hmac.Instance) : Nat := (8 * I.pbkdf2Scratch + 32 + 15) / 16 * 16

/-- `pbkdf2` with its working space in a frame of `bytes` bytes. -/
theorem framed {I : Spec.Hmac.Instance} {c : Prog isa} {stack bytes : Nat}
    (h : Verified PPC64LE.target c (Proof.Pbkdf2.Instance.pbkdf2ScratchContract I PPC64LE.abi stack))
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ I.pbkdf2Scratch * 8 + 32 ≤ bytes)
    (hsat : ∃ s, (I.pbkdf2Contract PPC64LE.abi (stack + bytes)).pre s) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch bytes .r10 c)
      (I.pbkdf2Contract PPC64LE.abi (stack + bytes)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S PPC64LE.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S PPC64LE.abi.ptrBits) (wa := true) (stack := stack) (bytes := bytes) h
    (by decide) hb (Pbkdf2.pbkdf2Pre_local I.S _) (Pbkdf2.pbkdf2Post_local I.S _)
    (fun vs m m₁ m₂ r hl _ => Pbkdf2.pbkdf2PostOut_local I.S _ vs m m₁ m₂ r hl) hsat rfl

end VG.Proof.Pbkdf2.Whole.PPC64LE

end

end


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
  hiN := I.initAnyKeyApi.name ++ "_core"
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
  omega_using [h48, hi, hid, hl, hld]

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
