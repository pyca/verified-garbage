module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.CT
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Correct

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
      h15, by show (s.gpr .r10).toNat + F.bytes ≤ 2 ^ 64; omega, h17, h18⟩
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
    (by decide) hb (Pbkdf2.pbkdf2Pre_local I.S _) (Pbkdf2.pbkdf2Post_local I.S _) hsat rfl

end VG.Proof.Pbkdf2.Whole.PPC64LE
