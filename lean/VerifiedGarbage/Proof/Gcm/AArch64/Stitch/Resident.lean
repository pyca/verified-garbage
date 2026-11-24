module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Gcm.AArch64.Resident
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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

local macro "prove_resident_pair" s:ident h:ident : tactic => `(tactic| (
    have gh {t : State} (g : t.gpr = ($s).gpr) (rd : t.rd = ($s).rd) (wr : t.wr = ($s).wr) : GhIn t :=
      ($h).of g rd wr
    dsimp only [residentPair, pairWith, forwardLd, pa, pb, pk, pl, cipherReg]
    simp (config := { decide := true }) (disch := first | exact gh rfl rfl rfl | decide) only [↓reduceIte,
      List.nil_append, List.cons_append, runBlock_cons, runStep_some, runBlock_nil, orSelf, swLoad, packedLoad,
      exec_trn, exec_eor, exec_pmull0, exec_pmull1, v_setV, gpr_setV, mem_setV, reduceCtorEq,
      Option.some.injEq]
    apply writes_eq ($s) _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
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
