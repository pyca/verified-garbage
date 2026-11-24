module

public import VerifiedGarbage.Impl.Gcm.AArch64.Forward
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Xor3
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
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
    runBlock isa (group forwardLd p ++ f) s = runBlock isa (group ld p ++ g) s := by
  have ha : pa p < 8 := by unfold pa; split <;> decide
  have hb : pb p < 8 := by unfold pb; split <;> decide
  have same : runBlock isa (group forwardLd p) s = runBlock isa (group ld p) s := by
    unfold group
    rw [VG.AArch64.Interleave.runBlock_append, VG.AArch64.Interleave.runBlock_append,
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
    runBlock isa (ghWith forwardLd) s = runBlock isa ghPart s := by
  rw [ghWith_groups, ghPart, ghWith_groups]
  exact group_cons (by decide) hc hi fun _ h₁ i₁ =>
    group_cons (by decide) h₁ i₁ fun _ h₂ i₂ =>
    group_cons (by decide) h₂ i₂ fun _ h₃ i₃ =>
    group_cons (by decide) h₃ i₃ fun _ _ _ => rfl

private theorem forwardGroups_flatten (xs : List Instr) : (xs.flatMap forwardGroup).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.flatMap_cons, List.flatten_append, ih]
    unfold forwardGroup
    split <;> rfl

private theorem forward_check : ∀ nr ∈ [10, 12, 14],
    ((fps.blockFp (aesPart nr 128 .x15)).bind fun A =>
      (fps.blockFp (ghWith forwardLd)).map fun B => fps.indep A B) = some true := by
  decide +kernel

theorem wp_lowerXor3 {code : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block code) s Q) :
    WP isa (.block (code.flatMap lowerXor3)) s Q := by
  apply WP.of_runBlock
  rw [run_lowerXor3_block]
  exact VG.AArch64.Interleave.runBlock_of_WP h

/-- AES on the next batch and GHASH on the retained ciphertext may be woven
while retaining all register, memory and permission obligations. -/
theorem forwardParts_ok {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {s : State} {Q : State → Prop}
    (h : WP isa (.block (aesPart nr 128 .x15)) s fun t => CipherBatch t ∧ GhIn t ∧ WP isa (.block ghPart) t Q) :
    WP isa (.block (forwardParts nr)) s Q := by
  apply wp_lowerXor3
  refine VG.Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [fuse_flatten, forwardGroups_flatten]
    exact fps.indeps_of_check (forward_check nr (by rcases hnr with rfl | rfl | rfl <;> decide))
  · rw [fuse_flatten, forwardGroups_flatten]
    refine WP.mono h fun t ⟨hc, hi, hg⟩ => ?_
    apply WP.of_runBlock
    rw [run_forwardGh hc hi]
    exact VG.AArch64.Interleave.runBlock_of_WP hg

end VG.Proof.Gcm.AArch64.Stitch
