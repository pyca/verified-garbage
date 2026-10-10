import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Ops
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds

/-! The row permutations and six-block schedule implement ChaCha's double round. -/
namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word innerBlock qround)
namespace Symbolic
abbrev E := VG.Proof.ChaCha20.AArch64.Neon4.E
abbrev ES := VG.Proof.ChaCha20.AArch64.Neon4.ES
open VG.Proof.ChaCha20.AArch64.Neon4 (qroundE)

def eval (env : Nat → Word) : E → Word
  | .var k => env k
  | .add a b => eval env a + eval env b
  | .xor a b => eval env a ^^^ eval env b
  | .rol a n => (eval env a).rotateLeft n

abbrev ER := Nat → Nat → E

def stepE (f : ER) : Op → ER
  | .add d a b => fun j k => if k = d.val then .add (f j a) (f j b) else f j k
  | .xorRol d a b n => fun j k =>
      if k = d.val then .rol (.xor (f j a) (f j b)) n else f j k
  | .permute d n => fun j k => if k = d.val then f ((j + n.val) % 4) d else f j k

def Rel (env : Nat → Word) (f : ER) (vs : Nat → Rows) : Prop :=
  ∀ k : Fin 24, ∀ j, j < 4 → eval env (f j k) = (vs j)[k]

theorem Rel.step {env : Nat → Word} {f : ER} {vs : Nat → Rows} (h : Rel env f vs) (op : Op) :
    Rel env (stepE f op) (VG.Proof.ChaCha20.AArch64.Rows6.step vs op) := by
  intro k j hj
  cases op with
  | add d a b =>
    simp only [stepE, VG.Proof.ChaCha20.AArch64.Rows6.step, get_set, Fin.ext_iff]
    split
    · simp only [eval, h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    simp only [stepE, VG.Proof.ChaCha20.AArch64.Rows6.step, get_set, Fin.ext_iff]
    split
    · simp only [eval, h a j hj, h b j hj]
    · exact h k j hj
  | permute d n =>
    simp only [stepE, VG.Proof.ChaCha20.AArch64.Rows6.step, get_set, Fin.ext_iff]
    split
    · exact h d _ (Nat.mod_lt _ (by decide))
    · exact h k j hj

theorem Rel.foldl {env : Nat → Word} {f : ER} {vs : Nat → Rows} (h : Rel env f vs) :
    ∀ ops : List Op, Rel env (ops.foldl stepE f) (ops.foldl VG.Proof.ChaCha20.AArch64.Rows6.step vs)
  | [] => h
  | op :: ops => (h.step op).foldl ops

def roundE (f : ES) : ES :=
  qroundE (qroundE (qroundE (qroundE
    (qroundE (qroundE (qroundE (qroundE f 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15)
    0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

def vars : ER := fun j k => .var (16 * (k / 4) + 4 * (k % 4) + j)
def target : ER := fun j k => roundE (fun w => .var (16 * (k / 4) + w)) (4 * (k % 4) + j)

/-! The schedule is checked by the kernel on a concrete state, a list of the
24 rows of 4 terms (`EL`), which it builds once per operation: on the
functions `ER`, every read at the end would run the whole schedule again. -/

/-- Structural equality of terms, which the kernel evaluates faster than
the derived `DecidableEq`. -/
def E.beq : E → E → Bool
  | .var a, .var b => a == b
  | .add a b, .add c d => E.beq a c && E.beq b d
  | .xor a b, .xor c d => E.beq a c && E.beq b d
  | .rol a n, .rol b m => n == m && E.beq a b
  | _, _ => false

theorem E.eq_of_beq : ∀ {a b : E}, E.beq a b = true → a = b
  | .var _, .var _, h => by simp only [E.beq, beq_iff_eq] at h; rw [h]
  | .add _ _, .add _ _, h => by
    simp only [E.beq, Bool.and_eq_true] at h; rw [E.eq_of_beq h.1, E.eq_of_beq h.2]
  | .xor _ _, .xor _ _, h => by
    simp only [E.beq, Bool.and_eq_true] at h; rw [E.eq_of_beq h.1, E.eq_of_beq h.2]
  | .rol _ _, .rol _ _, h => by
    simp only [E.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, E.eq_of_beq h.2]
  | .var _, .add _ _, h | .var _, .xor _ _, h | .var _, .rol _ _, h | .add _ _, .var _, h
  | .add _ _, .xor _ _, h | .add _ _, .rol _ _, h | .xor _ _, .var _, h | .xor _ _, .add _ _, h
  | .xor _ _, .rol _ _, h | .rol _ _, .var _, h | .rol _ _, .add _ _, h | .rol _ _, .xor _ _, h => by
    simp [E.beq] at h

/-- A state of terms as rows: `L[k][j]` is word `j` of row `k`. -/
abbrev EL := List (List E)

def look (L : EL) (j k : Nat) : E := (L.getD k []).getD j (.var 0)

def stepL (L : EL) : Op → EL
  | .add d a b => L.modify d.val fun _ => (List.range 4).map fun j => .add (look L j a) (look L j b)
  | .xorRol d a b n => L.modify d.val fun _ =>
      (List.range 4).map fun j => .rol (.xor (look L j a) (look L j b)) n
  | .permute d n => L.modify d.val fun _ => (List.range 4).map fun j => look L ((j + n.val) % 4) d

/-- The function `f` and the rows `L` agree on the 24 rows. -/
def Agree (f : ER) (L : EL) : Prop := L.length = 24 ∧ ∀ k : Fin 24, ∀ j, j < 4 → f j k = look L j k

theorem look_modify {L : EL} {d : Fin 24} (hl : L.length = 24) (g : List E → List E) (j k : Nat) :
    look (L.modify d.val g) j k = if k = d.val then (g (L.getD k [])).getD j (.var 0) else look L j k := by
  simp only [look, List.getD_eq_getElem?_getD, List.getElem?_modify]
  split
  · rename_i h; subst h
    have : d.val < L.length := by rw [hl]; exact d.isLt
    simp [List.getElem?_eq_getElem this]
  · rename_i h; simp [Ne.symm h]

theorem getD_range_map (g : Nat → E) {j : Nat} (hj : j < 4) :
    ((List.range 4).map g).getD j (.var 0) = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem Agree.step {f : ER} {L : EL} (h : Agree f L) (op : Op) : Agree (stepE f op) (stepL L op) := by
  obtain ⟨hl, h⟩ := h
  cases op with
  | add d a b =>
    refine ⟨by simp [stepL, hl], fun k j hj => ?_⟩
    simp only [stepE, stepL, look_modify hl, getD_range_map _ hj]
    split
    · rw [h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    refine ⟨by simp [stepL, hl], fun k j hj => ?_⟩
    simp only [stepE, stepL, look_modify hl, getD_range_map _ hj]
    split
    · rw [h a j hj, h b j hj]
    · exact h k j hj
  | permute d n =>
    refine ⟨by simp [stepL, hl], fun k j hj => ?_⟩
    simp only [stepE, stepL, look_modify hl, getD_range_map _ hj]
    split
    · exact h d _ (Nat.mod_lt _ (by decide))
    · exact h k j hj

theorem Agree.foldl {f : ER} {L : EL} (h : Agree f L) :
    ∀ ops : List Op, Agree (ops.foldl stepE f) (ops.foldl stepL L)
  | [] => h
  | op :: ops => (h.step op).foldl ops

def varsL : EL := (List.range 24).map fun k => (List.range 4).map fun j => .var (16 * (k / 4) + 4 * (k % 4) + j)

theorem agree_vars : Agree vars varsL :=
  ⟨by decide, by decide⟩

def equal (L : EL) (g : ER) : Bool := (List.finRange 24).all fun k =>
  (List.finRange 4).all fun j => E.beq (look L j k) (g j k)

theorem schedule_equalL : equal (roundOps.foldl stepL varsL) target = true := by decide +kernel

theorem schedule_equal (k : Fin 24) (j : Nat) (hj : j < 4) :
    roundOps.foldl stepE vars j k = target j k := by
  have he := schedule_equalL
  simp only [equal, List.all_eq_true, List.mem_finRange, true_implies] at he
  rw [(agree_vars.foldl roundOps).2 k j hj]
  exact E.eq_of_beq (he k ⟨j, hj⟩)

def LocalRel (env : Nat → Word) (f : ES) (v : CState) : Prop :=
  ∀ k (hk : k < 16), eval env (f k) = v[k]

theorem LocalRel.set {env : Nat → Word} {f : ES} {v : CState} (h : LocalRel env f v)
    {i : Nat} (hi : i < 16) {x : E} {y : Word} (hx : eval env x = y) :
    LocalRel env (VG.Proof.ChaCha20.AArch64.Neon4.ES.set f i x) (v.set i y hi) := by
  intro k hk
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem LocalRel.qround {env : Nat → Word} {f : ES} {v : CState} (h : LocalRel env f v)
    (x y z w : Fin 16) : LocalRel env (qroundE f x y z w) (qround v x y z w) := by
  simp only [qroundE]
  refine (((h.set x.isLt ?_).set y.isLt ?_).set z.isLt ?_).set w.isLt ?_ <;>
    simp only [eval, h _ x.isLt, h _ y.isLt, h _ z.isLt, h _ w.isLt, Fin.getElem_fin]

theorem LocalRel.round {env : Nat → Word} {f : ES} {v : CState} (h : LocalRel env f v) :
    LocalRel env (roundE f) (innerBlock v) :=
  (((((((h.qround 0 4 8 12).qround 1 5 9 13).qround 2 6 10 14).qround 3 7 11 15)
    |>.qround 0 5 10 15).qround 1 6 11 12).qround 2 7 8 13).qround 3 4 9 14
end Symbolic

def pack (blocks : Nat → CState) : Nat → Rows := fun j => Vector.ofFn fun k : Fin 24 =>
  (blocks (k.val / 4))[4 * (k.val % 4) + j % 4]'(by omega)

theorem pack_get (blocks : Nat → CState) (j : Nat) (k : Fin 24) :
    (pack blocks j)[k] = (blocks (k.val / 4))[4 * (k.val % 4) + j % 4]'(by omega) := by
  simp only [pack, Fin.getElem_fin, Vector.getElem_ofFn]

def env (blocks : Nat → CState) (k : Nat) : Word :=
  (blocks (k / 16))[k % 16]'(Nat.mod_lt _ (by decide))

theorem env_block (blocks : Nat → CState) (b w : Nat) (hw : w < 16) :
    env blocks (16 * b + w) = (blocks b)[w]'hw := by
  have hd : (16 * b + w) / 16 = b := by omega
  have hm : (16 * b + w) % 16 = w := by omega
  simp only [env, hd, hm]

theorem vars_rel (blocks : Nat → CState) : Symbolic.Rel (env blocks) Symbolic.vars (pack blocks) := by
  intro k j hj
  simp only [Symbolic.vars, Symbolic.eval, pack_get]
  rw [show 16 * (k.val / 4) + 4 * (k.val % 4) + j =
    16 * (k.val / 4) + (4 * (k.val % 4) + j) by omega,
    env_block blocks _ _ (by omega)]
  simp only [Nat.mod_eq_of_lt hj]

theorem target_rel (blocks : Nat → CState) :
    Symbolic.Rel (env blocks) Symbolic.target (pack (fun b => innerBlock (blocks b))) := by
  intro k j hj
  have h : Symbolic.LocalRel (env blocks) (fun w => .var (16 * (k.val / 4) + w))
      (blocks (k.val / 4)) := fun w hw => env_block blocks _ w hw
  have hr := h.round (4 * (k.val % 4) + j) (by omega)
  simp only [Symbolic.target, pack_get, Nat.mod_eq_of_lt hj]
  exact hr

theorem round_eq (blocks : Nat → CState) (k : Fin 24) (j : Nat) (hj : j < 4) :
    (roundOps.foldl step (pack blocks) j)[k] = (pack (fun b => innerBlock (blocks b)) j)[k] := by
  have h := ((vars_rel blocks).foldl roundOps) k j hj
  rw [Symbolic.schedule_equal k j hj] at h
  exact h.symm.trans (target_rel blocks k j hj)

theorem doubleRound_ok {blocks : Nat → CState} {s : State} (h : Holds (pack blocks) s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block doubleRound) s fun u =>
      Holds (pack (fun b => innerBlock (blocks b))) u ∧ RoundSame s u := by
  refine (ops_ok roundOps h ht).mono fun u ⟨hu,hs⟩ => ⟨?_,hs⟩
  intro k j hj
  exact (hu k j hj).trans (round_eq blocks k j hj)
theorem rounds_ok {blocks : Nat → CState} {s : State} (h : Holds (pack blocks) s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    ∀ n, WP isa (rounds n) s fun u =>
      Holds (pack (fun b => Nat.repeat innerBlock n (blocks b))) u ∧ RoundSame s u
  | 0 => WP.block_nil ⟨h, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩⟩
  | n + 1 => WP.seq ((rounds_ok h ht n).mono fun _ ⟨h',hs⟩ =>
      (doubleRound_ok h' (hs.v30.trans ht)).mono fun _ ⟨h'',hs'⟩ => ⟨h'',hs.trans hs'⟩)

end VG.Proof.ChaCha20.AArch64.Rows6
