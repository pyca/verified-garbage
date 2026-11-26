module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Gcm.AArch64.Resident
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Gcm.AArch64.Xor3
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Impl.Gcm.AArch64.Forward
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave

-- separate module: The straight-line GHASH equivalence is independent of the seal loop invariant and the public ABI.
@[expose] public section
namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch Pmull

/-- Reference copy of a GHASH operand, used to compare the preexisting pair proof. -/
def forwardLd (d : VReg) (j : Nat) : List Instr :=
  [.vop (.logic .orr d (cipherReg j) (cipherReg j))]

private theorem swLoad {s : State} (h : GhIn s) (v : VReg) {k : Nat} (lo : 1 ≤ k) (hi : k ≤ 8) :
    exec (.ldrq v .x19 (sOff k)) s =
      some (s.setV v (s.mem.read (s.gpr .x19 + BitVec.ofNat 64 (sOff k)) 16)) :=
  exec_ldrq (sOff_ok k hi).1 (sOff_ok k hi).2 (h.sw k lo hi)

private theorem packedLoad {s : State} (h : GhIn s) (v : VReg) {p : Nat} (hp : p < 4) :
    exec (.ldrq v .x19 (kOff p)) s =
      some (s.setV v (s.mem.read (s.gpr .x19 + BitVec.ofNat 64 (kOff p)) 16)) :=
  exec_ldrq (kOff_ok p hp).1 (kOff_ok p hp).2 (h.key p hp)

private theorem orSelf (s : State) (d a : VReg) :
    exec (.vop (.logic .orr d a a)) s = some (s.setV d (s.v a)) := by
  change some (s.setV d (_ ||| _)) = _
  rw [BitVec.or_self]

private def withoutV (s : State) : State := {s with v := fun _ => 0}

private theorem withoutV_set (s : State) (r : VReg) (x : BitVec 128) :
    withoutV (s.setV r x) = withoutV s := rfl

private theorem stateEq {s t : State} (rest : withoutV s = withoutV t) (vec : s.v = t.v) : s = t :=
  calc s = {withoutV s with v := s.v} := rfl
       _ = {withoutV t with v := t.v} := by rw [rest, vec]
       _ = t := rfl

private def writes (s : State) (a b c d e f g h i j k l : BitVec 128) : State :=
  ((((((((((((s.setV S₁ a).setV S₂ b).setV KP c).setV T d).setV U e).setV T f).setV X₁ g).setV A₁ h).setV X₂ i).setV A₂ j).setV U k).setV T l)

private theorem writes_eq (base s t : State) (a b c d e f g h i j k l : BitVec 128)
    (hs : s = {base with v := s.v}) (ht : t = {base with v := t.v})
    (hv : ∀ r, r ≠ A₁ → r ≠ A₂ → s.v r = t.v r) :
    writes s a b c d e f g h i j k l = writes t a b c d e f g h i j k l := by
  apply stateEq
  · simp only [writes, withoutV_set]
    exact (congrArg withoutV hs).trans (congrArg withoutV ht).symm
  · funext r
    by_cases h1 : r = A₁
    · subst r; simp only [writes, v_setV, reduceCtorEq, ↓reduceIte]
    by_cases h2 : r = A₂
    · subst r; simp only [writes, v_setV, reduceCtorEq, ↓reduceIte]
    simp only [writes, v_setV, hv r h1 h2]

private theorem ghIn_setV (s : State) (r : VReg) (x : BitVec 128) : GhIn (s.setV r x) ↔ GhIn s :=
  ⟨fun h => h.of (gpr_setV ..).symm (rd_setV ..).symm (wr_setV ..).symm,
    fun h => h.of (gpr_setV ..) (rd_setV ..) (wr_setV ..)⟩

private theorem withoutV_base {base : State} (s : State) (h : withoutV s = withoutV base) :
    s = {base with v := s.v} :=
  stateEq h rfl

local macro "prove_resident_pair" s:ident h:ident : tactic => `(tactic| (
    dsimp only [residentPair, pairWith, forwardLd, pa, pb, pk, pl, cipherReg]
    simp (disch := first | simp only [ghIn_setV, $h:ident] | decide) only [show decide True = true by rfl, show ¬ (1:Nat) = 3 by decide, show ¬ (2:Nat) = 3 by decide, ↓reduceIte,
      List.nil_append, List.cons_append, runBlock_cons, runStep_some, runBlock_nil, orSelf, swLoad, packedLoad,
      exec_trn, exec_eor, exec_pmull0, exec_pmull1, v_setV, gpr_setV, mem_setV, reduceCtorEq,
      Option.some.injEq]
    apply writes_eq ($s) _ _ _ _ _ _ _ _ _ _ _ _ _ _ (withoutV_base _ (by simp only [withoutV_set]))
      (withoutV_base _ (by simp only [withoutV_set]))
    intro r ha hb
    simp only [v_setV, ha, hb, ↓reduceIte]))

private theorem pair0_eq (s : State) (h : GhIn s) :
    runBlock isa (residentPair 0) s =
      runBlock isa (pairWith forwardLd 0 (pa 0) (pk 0) (pb 0) (pl 0) (decide (0 = 3))) s := by
  prove_resident_pair s h

private theorem pair1_eq (s : State) (h : GhIn s) :
    runBlock isa (residentPair 1) s =
      runBlock isa (pairWith forwardLd 1 (pa 1) (pk 1) (pb 1) (pl 1) (decide (1 = 3))) s := by
  prove_resident_pair s h

private theorem pair2_eq (s : State) (h : GhIn s) :
    runBlock isa (residentPair 2) s =
      runBlock isa (pairWith forwardLd 2 (pa 2) (pk 2) (pb 2) (pl 2) (decide (2 = 3))) s := by
  prove_resident_pair s h

private theorem pair3_eq (s : State) (h : GhIn s) :
    runBlock isa (residentPair 3) s =
      runBlock isa (pairWith forwardLd 3 (pa 3) (pk 3) (pb 3) (pl 3) (decide (3 = 3))) s := by
  prove_resident_pair s h

/-- Both temporary registers receive their respective products before the
consumer uses them. Replacing the copies preserves every register and memory. -/
theorem residentPair_eq (p : Nat) (hp : p < 4) (s : State) (h : GhIn s) :
    runBlock isa (residentPair p) s =
      runBlock isa (pairWith forwardLd p (pa p) (pk p) (pb p) (pl p) (decide (p = 3))) s := by
  have casesP : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases casesP with rfl|rfl|rfl|rfl
  exacts [pair0_eq s h,pair1_eq s h,pair2_eq s h,pair3_eq s h]

end VG.Proof.Gcm.AArch64.Stitch

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Aes.AArch64.Aese (setV_setV setV_v_self setV_v_of_ne)

/-- Lowering preserves the entire machine state, including aliased operands. -/
theorem run_xor3Base (d a b c : VReg) (s : State) :
    runBlock isa (xor3Base d a b c) s = exec (.vop (.eor3 d a b c)) s := by
  by_cases hc : c = d
  · subst c
    by_cases hb : b = d
    · subst b
      simp only [xor3Base, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      change some (s.setV d (s.v a ||| s.v a)) = some (s.setV d (s.v a ^^^ s.v d ^^^ s.v d))
      simp [BitVec.xor_assoc]
    · simp [xor3Base, hb]
      change some ((s.setV d (s.v d ^^^ s.v a)).setV d _) = some (s.setV d _)
      rw [setV_v_self, setV_v_of_ne _ _ hb, setV_setV]
      simp [BitVec.xor_comm, BitVec.xor_assoc]
  · simp [xor3Base, hc]
    change some ((s.setV d (s.v a ^^^ s.v b)).setV d _) = some (s.setV d _)
    rw [setV_v_self, setV_v_of_ne _ _ hc, setV_setV]

theorem run_lowerXor3 (i : Instr) (s : State) :
    runBlock isa (lowerXor3 i) s = exec i s := by
  unfold lowerXor3
  split
  · exact run_xor3Base _ _ _ _ _
  · change (exec _ s).bind some = exec _ s
    cases exec i s <;> rfl

theorem run_lowerXor3_block (code : List Instr) (s : State) :
    runBlock isa (code.flatMap lowerXor3) s = runBlock isa code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [List.flatMap_cons, VG.AArch64.Interleave.runBlock_append, run_lowerXor3]
    change (exec i s).bind _ = (exec i s).bind _
    exact congrArg ((exec i s).bind ·) (funext ih)

end VG.Proof.Gcm.AArch64.Stitch

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Aes.AArch64.Aese (setV_setV setV_v_self setV_v_of_ne)

def CipherBatch (s : State) : Prop := ∀ j < 8, s.v (cipherReg j) = blkV s j

/-- A forwarded ciphertext block gives the exact state of the old load and reverse. -/
theorem run_forwardLd (d : VReg) {j : Nat} (hj : j < 8) {s : State}
    (hc : CipherBatch s) (hin : GhIn s) :
    runBlock isa (forwardLd d j) s = runBlock isa (ld d j) s := by
  have he := VG.Proof.Gcm.AArch64.Pmull.exec_ldrq (t := d) (n := .x9)
    (off := 16*j) (s := s) (Nat.mul_mod_right 16 j) (by omega) (hin.blk j hj)
  unfold ld
  rw [runBlock_cons, he, runStep_some, runBlock_cons, VG.Proof.Gcm.AArch64.Pmull.exec_rev64b,
    runStep_some, runBlock_nil, setV_v_self, setV_setV]
  change some (s.setV d (s.v (cipherReg j) ||| s.v (cipherReg j))) = _
  rw [BitVec.or_self, hc j hj]
  rfl

private theorem run_forwardLd_value (d : VReg) {j : Nat} (hj : j < 8) {s : State}
    (hc : CipherBatch s) :
    runBlock isa (forwardLd d j) s = some (s.setV d (blkV s j)) := by
  change some (s.setV d (_ ||| _)) = _
  rw [BitVec.or_self, hc j hj]

private theorem batch_setA₁ {s : State} (hc : CipherBatch s) (x : BitVec 128) :
    CipherBatch (s.setV A₁ x) := by
  intro j hj
  have hn : cipherReg j ≠ A₁ := by unfold cipherReg; split <;> decide
  rw [setV_v_of_ne _ _ hn, hc j hj]
  rfl

/-- Forward both ciphertext operands of a Karatsuba pair; all product and
reduction instructions remain shared. -/
theorem run_forwardPair (p a k b l : Nat) (y : Bool) {s : State}
    (ha : a < 8) (hb : b < 8) (hc : CipherBatch s) (hin : GhIn s) :
    runBlock isa (pairWith forwardLd p a k b l y) s = runBlock isa (pair p a k b l y) s := by
  let t := s.setV A₁ (blkV s a)
  have f₁ : runBlock isa (forwardLd A₁ a) s = some t := run_forwardLd_value A₁ ha hc
  have o₁ := (run_forwardLd A₁ ha hc hin).symm.trans f₁
  have h₂ := run_forwardLd A₂ hb (batch_setA₁ hc (blkV s a)) (hin.of (s' := t) rfl rfl rfl)
  change runBlock isa (forwardLd A₂ b) t = runBlock isa (ld A₂ b) t at h₂
  simp only [pair, pairWith, List.append_assoc, VG.AArch64.Interleave.runBlock_append, f₁, o₁,
    Option.bind_some, h₂]

private def group (load : VReg → Nat → List Instr) (p : Nat) :=
  pairWith load p (pa p) (pk p) (pb p) (pl p) (decide (p = 3)) ++ (if p = 0 then addFirst else addNext)

private theorem group_cons {s : State} {p : Nat} {f g : List Instr}
    (hp : p < 4) (hc : CipherBatch s) (hi : GhIn s)
    (h : ∀ t, CipherBatch t → GhIn t → runBlock isa f t = runBlock isa g t) :
    runBlock isa (residentGroup p ++ f) s = runBlock isa (group ld p ++ g) s := by
  have ha : pa p < 8 := by unfold pa; split <;> decide
  have hb : pb p < 8 := by unfold pb; split <;> decide
  have same : runBlock isa (residentGroup p) s = runBlock isa (group ld p) s := by
    unfold group residentGroup
    rw [VG.AArch64.Interleave.runBlock_append, VG.AArch64.Interleave.runBlock_append, residentPair_eq p hp s hi,
      run_forwardPair _ _ _ _ _ _ ha hb hc hi]
  obtain ⟨t, hr, _, fr⟩ := VG.AArch64.Interleave.runBlock_of_WP
    (pairAdd_ok p hp (decide (p = 0)) s s hi rfl rfl rfl rfl rfl)
  have hr' : runBlock isa (group ld p) s = some t := by simpa [group] using hr
  rw [VG.AArch64.Interleave.runBlock_append, VG.AArch64.Interleave.runBlock_append, same, hr',
    Option.bind_some, Option.bind_some]
  refine h t (fun j hj => ?_) (hi.of fr.gpr fr.rd fr.wr)
  have hn : cipherReg j ∉ pairV := by unfold cipherReg; split <;> decide
  rw [fr.v _ hn, hc j hj]
  simp only [blkV, fr.mem, fr.gpr]

private theorem ghWith_groups (load : VReg → Nat → List Instr) :
    ghWith load = group load 0 ++ (group load 1 ++ (group load 2 ++ (group load 3 ++
        Impl.Gcm.AArch64.Stitch.reduce))) := by
  simp only [ghWith, group, List.append_assoc]
  rfl

/-- Forwarded GHASH gives the same state as hashing the output buffer. -/
theorem run_forwardGh {s : State} (hc : CipherBatch s) (hi : GhIn s) :
    runBlock isa residentHash s = runBlock isa ghPart s := by
  rw [residentHash, ghPart, ghWith_groups]
  exact group_cons (by decide) hc hi fun _ h₁ i₁ =>
    group_cons (by decide) h₁ i₁ fun _ h₂ i₂ =>
    group_cons (by decide) h₂ i₂ fun _ h₃ i₃ =>
    group_cons (by decide) h₃ i₃ fun _ _ _ => rfl

private theorem residentFlatten : residentSlots.flatten = residentHash := by decide +kernel

private theorem forward_check : ∀ nr ∈ [10, 12, 14],
    ((fps.blockFp (aesPart nr 128 .x15)).bind fun A =>
      (fps.blockFp residentHash).map fun B => fps.indep A B) = some true := by
  decide +kernel

theorem run_forwardParts_eq_seq {nr : Nat} (hn : nr = 10 ∨ nr = 12 ∨ nr = 14) (s : State) :
    runBlock isa (residentParts nr) s = runBlock isa (aesPart nr 128 .x15 ++ residentHash) s := by
  unfold residentParts
  rw [run_lowerXor3_block]
  have hm := VG.Interleave.weaveG_merge (fuse (aesPart nr 128 .x15)) residentSlots
  rw [fuse_flatten, residentFlatten] at hm
  exact VG.Interleave.run_merge hm
    (fps.indeps_of_check (forward_check nr (by rcases hn with rfl | rfl | rfl <;> decide))) trivial

end VG.Proof.Gcm.AArch64.Stitch
