import VerifiedGarbage.Impl.Cast5.Arm
import VerifiedGarbage.Proof.Cast5.KeyMem

/-!
# CAST5 key expansion on ARMv7: the steps of a half

The implementation runs each half of §2.4 as 40 steps (`halfSteps`): for each
group of four lines, its extra lookups, then its lines, each with its extra
lookup from those (`lineE`). Run on the arrays, the subkeys so far and the
extra lookups (`KSt`), the steps of a half compute `halfImpl`
(`runSteps_half`).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

/-- What the steps of key expansion work on: the arrays, the subkeys so far
and the group's extra lookups (`S8, S7, S6, S5` of its extra bytes). -/
structure KSt where
  xz : XZ
  ws : List Spec.Cast5.Word
  ex : Nat → Spec.Cast5.Word

/-- A line's value, its extra lookup taken from `ex`. -/
def lineE (xz : XZ) (ex : Nat → Spec.Cast5.Word) (l : Line) : Spec.Cast5.Word :=
  let v := Spec.Cast5.S8 (xz.get l.main.2.2.2) ^^^ Spec.Cast5.S7 (xz.get l.main.2.2.1) ^^^
    Spec.Cast5.S6 (xz.get l.main.2.1) ^^^ Spec.Cast5.S5 (xz.get l.main.1) ^^^ ex (8 - l.extra.1)
  match l.word with
  | some (a, q) => v ^^^ quadOf (xz.arr a) q
  | none => v

theorem lineE_eq {xz : XZ} {ex : Nat → Spec.Cast5.Word} {l : Line}
    (h : ex (8 - l.extra.1) = sbox l.extra.1 (xz.get l.extra.2)) : lineE xz ex l = lineVal xz l := by
  simp only [lineE, lineVal]
  rcases hw : l.word with _ | ⟨a, q⟩ <;> simp only [h]

/-- A step on the state of key expansion. -/
def stepRun : Step → KSt → KSt
  | .extras a b c d, k => { k with ex := exVal k.xz a b c d }
  | .line l (.quad a q), k => { k with xz := k.xz.put a q (lineE k.xz k.ex l) }
  | .line l (.key _), k => { k with ws := k.ws ++ [lineE k.xz k.ex l] }

/-- Steps in order. -/
def runSteps (ss : List Step) (k : KSt) : KSt := ss.foldl (fun k s => stepRun s k) k

theorem runSteps_append (a b : List Step) (k : KSt) : runSteps (a ++ b) k = runSteps b (runSteps a k) := by
  simp only [runSteps, List.foldl_append]

theorem runSteps_cons (s : Step) (ss : List Step) (k : KSt) : runSteps (s :: ss) k = runSteps ss (stepRun s k) := rfl

theorem runSteps_nil (k : KSt) : runSteps [] k = k := rfl

theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

/-- The extra lookups of a group. -/
def exOf (xz : XZ) (ls : List Line) : Nat → Spec.Cast5.Word :=
  exVal xz (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)

theorem lineQ_run (a : Arr) {ls : List Line} (hg : GroupOk (some a) ls) (xz : XZ) (ws : List Spec.Cast5.Word)
    {j : Nat} (hj : j < 4) :
    stepRun (.line (ls.getD j default) (.quad a j)) ⟨runQ a ls j xz, ws, exOf xz ls⟩ =
      ⟨runQ a ls (j + 1) xz, ws, exOf xz ls⟩ := by
  obtain ⟨hok, hex, hna⟩ := hg.1 j hj
  have he := hok
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  simp only [stepRun, runQ_succ]
  rw [lineE_eq]
  rw [exOf, exVal_sbox _ _ he.1.1.2 he.1.2, hex, get_runQ _ _ _ _ fun e => hna (by rw [e])]

theorem lineK_run {ls : List Line} (hg : GroupOk none ls) (xz : XZ) (ws : List Spec.Cast5.Word) (b : Nat)
    {j : Nat} (hj : j < 4) :
    stepRun (.line (ls.getD j default) (.key (b + j))) ⟨xz, ws ++ (keys4 ls xz).take j, exOf xz ls⟩ =
      ⟨xz, ws ++ (keys4 ls xz).take (j + 1), exOf xz ls⟩ := by
  obtain ⟨hok, hex, _⟩ := hg.1 j hj
  have he := hok
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  simp only [stepRun]
  rw [lineE_eq (by rw [exOf, exVal_sbox _ _ he.1.1.2 he.1.2, hex]), take_keys4 _ _ hj, List.append_assoc]

theorem groupQ_run (a : Arr) {ls : List Line} (hg : GroupOk (some a) ls) (k : KSt) :
    runSteps (groupSteps ls (.quad a)) k = ⟨runQ a ls 4 k.xz, k.ws, exOf k.xz ls⟩ := by
  obtain ⟨xz, ws, ex⟩ := k
  simp only [groupSteps, range4, List.map_cons, List.map_nil, runSteps_cons, runSteps_nil]
  have e0 : stepRun (.extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ⟨xz, ws, ex⟩ =
      ⟨runQ a ls 0 xz, ws, exOf xz ls⟩ := rfl
  rw [e0, lineQ_run a hg xz ws (by decide), lineQ_run a hg xz ws (by decide), lineQ_run a hg xz ws (by decide),
    lineQ_run a hg xz ws (by decide)]

theorem groupK_run {ls : List Line} (hg : GroupOk none ls) (b : Nat) (k : KSt) :
    runSteps (groupSteps ls fun j => .key (b + j)) k = ⟨k.xz, k.ws ++ keys4 ls k.xz, exOf k.xz ls⟩ := by
  obtain ⟨xz, ws, ex⟩ := k
  simp only [groupSteps, range4, List.map_cons, List.map_nil, runSteps_cons, runSteps_nil]
  have e0 : stepRun (.extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ⟨xz, ws, ex⟩ =
      ⟨xz, ws ++ (keys4 ls xz).take 0, exOf xz ls⟩ := by
    simp only [stepRun, exOf, List.take_zero, List.append_nil]
  rw [e0, lineK_run hg xz ws b (j := 0) (by decide), lineK_run hg xz ws b (j := 1) (by decide),
    lineK_run hg xz ws b (j := 2) (by decide), lineK_run hg xz ws b (j := 3) (by decide)]
  rfl

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem key_zero : groupSteps aLines Store.key = groupSteps aLines fun j => .key (0 + j) := by
  simp only [Nat.zero_add]

/-- The steps of a half compute `halfImpl`. -/
theorem runSteps_half (k : KSt) :
    (runSteps halfSteps k).xz = (halfImpl k.xz).2 ∧ (runSteps halfSteps k).ws = k.ws ++ (halfImpl k.xz).1 := by
  unfold halfSteps
  rw [key_zero]
  simp only [runSteps_append, groupQ_run _ gZ, groupQ_run _ gX, groupK_run gA, groupK_run gB, groupK_run gC,
    groupK_run gD, runQ_z, runQ_x]
  exact ⟨rfl, by simp only [halfImpl, List.append_assoc]⟩

end VG.Proof.Cast5.Arm
