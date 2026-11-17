module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.Arm.Groups
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesCbc.Arm.GroupsCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesCbc.Rounds
meta import VerifiedGarbage.Impl.AesCbc.Arm.Groups
meta import VerifiedGarbage.Spec.Cbc.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.AesCbc.Arm.GroupsCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-CBC on ARMv7: `Verified`

Correctness and constant time, a state satisfying the precondition, and the
shared contracts of `Spec/Cbc/Contract.lean`, with 8 bytes of stack: each
call of a block function pushes its stack argument and `lr`.

Decryption takes the blocks in groups of 4 and of 2 (`decryptG`,
`Impl/AesCbc/Arm/Groups.lean`): a group of `cbcDecG` leaves the data and the
chaining value as CBC decryption of its blocks does (`cbcDecG_sim`), which
evaluating both on any blocks shows.
-/

@[expose] public section

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Proof.AesOcb.Arm (decF)

/-- A state satisfying the precondition: the schedule at `0x1000`, 10
rounds, the chaining value at `0x2000`, no blocks at `0x3000` and the scratch
buffer at 0 (the stack arguments, at `0x8000`, are zeros). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0, 2176⟩]

theorem encrypt_verified : Verified Arm.target encrypt (Proof.AesCbc.encryptRoundsContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => wholeK_wp encBody_ok hs) (wholeK_ct encBody_ok encBody_ct) (by
    sig_implies [Proof.AesCbc.encryptRoundsContract, Spec.Cbc.aesSig, cbcArm, modeArm, cbcMode,
      ciphOf, cbc, cts, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

/-! ## Decryption, in groups -/

private theorem decrypt_append (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs ys : List (List Byte)) :
    Spec.Cbc.decrypt ciph iv (xs ++ ys) =
      Spec.Cbc.decrypt ciph iv xs ++ Spec.Cbc.decrypt ciph (Spec.Cbc.next iv xs) ys := by
  induction xs generalizing iv with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, Spec.Cbc.decrypt, ih, next_cons]

/-- A group of `cbcDecG` computes CBC decryption of its blocks. -/
private theorem cbcDecG_sim : ∀ lg ∈ groupLevels, GSim (cbcMode false) (ciphOf false) cbcDecG (2 ^ lg) := by
  intro lg h R w iv xs ys b hy hiv hd
  simp only [groupLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [cbcMode, cbc, cts, Bool.false_eq_true, ↓reduceIte, decrypt_append, next_append] at hiv ⊢
  rcases h with rfl | rfl
  · match ys, hy with
    | [y0, y1, y2, y3], _ =>
      have h0 := hd 0 (by decide)
      have h1 := hd 1 (by decide)
      have h2 := hd 2 (by decide)
      have h3 := hd 3 (by decide)
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3
      simp [gstep, cbcDecG, grunOps, grunOp, gset, gciph, gtgt, List.range_succ, Spec.Cbc.decrypt, Spec.Cbc.next,
        ← h0, ← h1, ← h2, ← h3, hiv]
  · match ys, hy with
    | [y0, y1], _ =>
      have h0 := hd 0 (by decide)
      have h1 := hd 1 (by decide)
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
      simp [gstep, cbcDecG, grunOps, grunOp, gset, gciph, gtgt, List.range_succ, Spec.Cbc.decrypt, Spec.Cbc.next,
        ← h0, ← h1, hiv]

private theorem cbcDecG_levels : ∀ lg ∈ groupLevels, LevelOk (cbcMode false) decF (ciphOf false) cbcDecG lg :=
  levels_of (by decide) (by decide) cbcDecG_sim fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

private theorem cbcDecG_taint : ∀ lg ∈ groupLevels, LevelTaint cbcDecG lg := by
  intro lg h
  simp only [groupLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

private theorem decryptG_eq : decryptG = wholeG (VG.Proof.AesOcb.Arm.blkFrame decF) cbcDecG groupLevels decBody := rfl

theorem decrypt_verified : Verified Arm.target decryptG (Proof.AesCbc.decryptRoundsContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => by rw [decryptG_eq]; exact wholeG_wp cbcDecG_levels decBody_ok hs)
    (by rw [decryptG_eq]; exact wholeG_ct cbcDecG_levels cbcDecG_taint decBody_ok decBody_ct) (by
    sig_implies [Proof.AesCbc.decryptRoundsContract, Spec.Cbc.aesSig, cbcArm, modeArm, cbcMode,
      ciphOf, cbc, cts, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sat)

end VG.Proof.AesCbc.Arm
