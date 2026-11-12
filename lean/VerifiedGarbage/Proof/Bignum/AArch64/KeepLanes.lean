module

public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Registers kept through vector lanes, on AArch64

`WP.keep` frames the registers no instruction of a program writes. Code that
borrows callee-saved registers, saving each in a 64-bit lane of a vector
register (`ins vd.d[l], r`) and restoring it from there (`umov r, vd.d[l]`)
before it returns, writes them, but keeps them all the same: `WP.keepLanes`
frames them too.

`check` follows, through the program's blocks, branches and loops, where the
values the registers `T` started with are: in which registers and lanes
(`Facts`). An `ins` copies a register's facts to a lane, a `umov` a lane's to
a register, and any other instruction drops the facts of what it writes. A
branch keeps the facts both arms keep, and a loop those of the facts it is
entered with that its body keeps (`loopInv`). `keeps T c` is that every
register of `T` holds its own value at the end; the kernel evaluates it
(`decide +kernel`), and `Exec.keepsLanes` says it is sound. Calls and frames
are not followed.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.KeepLanes

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Where a value is: a register, or lane `i` (64 bits) of a vector register. -/
inductive Loc where
  | g (r : Reg)
  | l (v : VReg) (i : Nat)
  deriving DecidableEq

/-- Which locations hold the initial value of which register. -/
abbrev Facts := List (Reg × Loc)

/-- The value at a location. -/
def read (s : State) : Loc → BitVec 64
  | .g r => s.gpr r
  | .l v i => laneOf s v i

/-- Every fact of `A` holds in `s` of the registers of `s₀`. -/
def Holds (s₀ s : State) (A : Facts) : Prop := ∀ p ∈ A, read s p.2 = s₀.gpr p.1

/-- Whether instruction `i` keeps the value at a location: it writes neither
the register nor the vector register. -/
def keepP (i : Instr) : Loc → Bool
  | .g x => !clobbers i x
  | .l v _ => vdstOf i != some v

/-- `ins vd.d[k], n` keeps the other registers, and the other lane of `vd`. -/
def insKeep (d : VReg) (k : Nat) : Loc → Bool
  | .g _ => true
  | .l v j => v != d || (decide (j < 2) && j != k)

/-- `ins vd.d[k], n` copies `n`'s facts to the lane. -/
def insNew (d : VReg) (k : Nat) (n : Reg) (p : Reg × Loc) : Option (Reg × Loc) :=
  if p.2 = .g n then some (p.1, .l d k) else none

/-- `umov d, vn.d[k]` copies the lane's facts to `d`. -/
def umovNew (d : Reg) (n : VReg) (k : Nat) (p : Reg × Loc) : Option (Reg × Loc) :=
  if p.2 = .l n k then some (p.1, .g d) else none

/-- `ins vd.d[k], n` as `(d, k, n)`. -/
def insView : Instr → Option (VReg × Nat × Reg)
  | .vop (.ins .d2 d k n) => some (d, k, n)
  | _ => none

/-- `umov d, vn.d[k]` (64 bits) as `(d, n, k)`. -/
def umovView : Instr → Option (Reg × VReg × Nat)
  | .umov .x d n k => some (d, n, k)
  | _ => none

/-- The facts after an instruction. -/
def step (A : Facts) (i : Instr) : Facts :=
  match insView i with
  | some (d, k, n) =>
    if k < 2 then A.filter (fun p => insKeep d k p.2) ++ A.filterMap (insNew d k n) else A.filter (fun p => keepP i p.2)
  | none =>
    match umovView i with
    | some (d, n, k) =>
      if k < 2 then A.filter (fun p => p.2 != .g d) ++ A.filterMap (umovNew d n k)
      else A.filter (fun p => keepP i p.2)
    | none => A.filter (fun p => keepP i p.2)

/-- A loop's invariant, for its body's analysis `f`: the facts `I` the body
keeps, starting from those it is entered with and dropping those the body
does not keep, each round at least one (`n` rounds). -/
def loopInv (f : Facts → Option Facts) : Nat → Facts → Option Facts
  | 0, _ => none
  | n + 1, I => (f I).bind fun B => if I.all (· ∈ B) then some I else loopInv f n (I.filter (· ∈ B))

/-- The facts after a program, if it has no calls or frames. -/
def check : Facts → Prog isa → Option Facts
  | A, .block is => some (is.foldl step A)
  | A, .seq a b => (check A a).bind (check · b)
  | A, .ite _ t e => (check A t).bind fun B => (check A e).map fun C => B.filter (· ∈ C)
  | A, .loop body _ => loopInv (fun I => check I body) (A.length + 1) A
  | _, _ => none

/-- Every register of `T` ends with the value it started with. -/
def keeps (T : List Reg) (c : Prog isa) : Bool :=
  match check (T.map fun r => (r, .g r)) c with
  | some B => T.all fun r => B.contains (r, .g r)
  | none => false

theorem insView_eq {i : Instr} {d : VReg} {k : Nat} {n : Reg} (h : insView i = some (d, k, n)) :
    i = .vop (.ins .d2 d k n) := by
  unfold insView at h
  split at h <;> cases h; rfl

theorem umovView_eq {i : Instr} {d : Reg} {n : VReg} {k : Nat} (h : umovView i = some (d, n, k)) :
    i = .umov .x d n k := by
  unfold umovView at h
  split at h <;> cases h; rfl

/-- What an instruction writes neither of keeps its value. -/
theorem keepP_ok {i : Instr} {s s' : State} (he : exec i s = some s') {x : Loc} (h : keepP i x = true) :
    read s' x = read s x := by
  cases x with
  | g r =>
    simp only [keepP, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact exec_gpr h he
  | l v j =>
    simp only [keepP, bne_iff_ne, ne_eq] at h
    simp only [read, laneOf, exec_vec h he]

theorem filter_keepP {A : Facts} {i : Instr} {s₀ s s' : State} (he : exec i s = some s') (h : Holds s₀ s A) :
    Holds s₀ s' (A.filter fun p => keepP i p.2) := fun p hp => by
  obtain ⟨hp, hk⟩ := List.mem_filter.mp hp
  rw [keepP_ok he hk]; exact h p hp

/-- The facts after an instruction hold after it. -/
theorem step_ok {A : Facts} {i : Instr} {s₀ s s' : State} (he : exec i s = some s') (h : Holds s₀ s A) :
    Holds s₀ s' (step A i) := by
  unfold step
  split
  · rename_i d k n hv
    obtain rfl := insView_eq hv
    split
    · rename_i hk
      rw [exec_ins hk] at he
      obtain rfl := Option.some.inj he
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨hp, hk'⟩ := List.mem_filter.mp hp
        rw [← h p hp]
        revert hk'
        cases p.2 with
        | g x => intro _; simp only [read, RegUpd.gpr_setV]
        | l v j =>
          simp only [insKeep, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq]
          intro hk'
          simp only [read, laneOf_setV]
          split
          · rename_i hvd
            subst hvd
            rcases hk' with hk' | ⟨hj, hjk⟩
            · exact absurd rfl hk'
            · simp [extract_setLane64 _ _ hk hj, Ne.symm hjk]
          · rfl
      · obtain ⟨q, hq, hq'⟩ := List.mem_filterMap.mp hp
        unfold insNew at hq'
        split at hq' <;> [skip; cases hq']
        rename_i hg
        obtain rfl := Option.some.inj hq'
        rw [← h q hq, hg]
        simp only [read, laneOf_setV, ite_true, extract_setLane64 _ _ hk hk]
    · exact filter_keepP he h
  · split
    · rename_i _ d n k hv
      obtain rfl := umovView_eq hv
      split
      · rename_i hk
        rw [exec_umov hk] at he
        obtain rfl := Option.some.inj he
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨hp, hk'⟩ := List.mem_filter.mp hp
          rw [← h p hp]
          revert hk'
          cases p.2 with
          | g x =>
            simp only [bne_iff_ne, ne_eq, Loc.g.injEq]
            intro hx
            simp [read, State.write, hx]
          | l v j => intro _; simp only [read, laneOf, RegUpd.v_write]
        · obtain ⟨q, hq, hq'⟩ := List.mem_filterMap.mp hp
          unfold umovNew at hq'
          split at hq' <;> [skip; cases hq']
          rename_i hl
          obtain rfl := Option.some.inj hq'
          rw [← h q hq, hl]
          simp [read, State.write, laneOf]
      · exact filter_keepP he h
    · exact filter_keepP he h

theorem block_ok : ∀ {is : List Instr} {A : Facts} {s₀ s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → Holds s₀ s A → Holds s₀ s' (is.foldl step A)
  | [], _, _, _, _, _, e, h => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]; exact h
  | i :: is, A, s₀, s, s', t, e, h => by
    simp only [execBlock] at e
    split at e <;> [cases e; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at e
    obtain ⟨⟨s₂, t₂⟩, e₂, heq⟩ := e
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact block_ok (is := is) e₂ (step_ok he h)

/-- A loop's invariant is among the facts it is entered with, and the body
keeps it. -/
theorem loopInv_ok {f : Facts → Option Facts} : ∀ {n : Nat} {A I : Facts}, loopInv f n A = some I →
    (∀ p ∈ I, p ∈ A) ∧ ∃ B, f I = some B ∧ ∀ p ∈ I, p ∈ B
  | 0, _, _, h => by simp only [loopInv, reduceCtorEq] at h
  | n + 1, A, I, h => by
    simp only [loopInv, Option.bind_eq_some_iff] at h
    obtain ⟨B, hB, h⟩ := h
    split at h
    · rename_i hall
      obtain rfl := Option.some.inj h
      exact ⟨fun p hp => hp, B, hB, fun p hp => by simpa using List.all_eq_true.mp hall p hp⟩
    · obtain ⟨h₁, h₂⟩ := loopInv_ok h
      exact ⟨fun p hp => (List.mem_filter.mp (h₁ p hp)).1, h₂⟩

/-- The invariant is its own. -/
theorem loopInv_self {f : Facts → Option Facts} {I B : Facts} (hB : f I = some B) (hI : ∀ p ∈ I, p ∈ B) :
    loopInv f (I.length + 1) I = some I := by
  have hall : I.all (· ∈ B) = true := List.all_eq_true.mpr fun p hp => by simpa using hI p hp
  simp only [loopInv, hB, Option.bind_some, hall, ↓reduceIte]

/-- The facts `check` gives hold after the program. -/
theorem check_ok {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s') :
    ∀ {s₀ : State} {A B : Facts}, check A c = some B → Holds s₀ s A → Holds s₀ s' B := by
  induction he with
  | block e => intro s₀ A B hc h; simp only [check, Option.some.injEq] at hc; subst hc; exact block_ok e h
  | seq _ _ ih₁ ih₂ =>
    intro s₀ A B hc h
    simp only [check, Option.bind_eq_some_iff] at hc
    obtain ⟨C, h₁, h₂⟩ := hc
    exact ih₂ h₂ (ih₁ h₁ h)
  | iteT _ _ ih =>
    intro s₀ A B hc h
    simp only [check, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨B₁, h₁, C, -, rfl⟩ := hc
    intro p hp
    exact ih h₁ h p (List.mem_filter.mp hp).1
  | iteF _ _ ih =>
    intro s₀ A B hc h
    simp only [check, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨B₁, -, C, h₂, rfl⟩ := hc
    intro p hp
    exact ih h₂ h p (by simpa using (List.mem_filter.mp hp).2)
  | loopExit _ _ ih =>
    intro s₀ A B hc h
    simp only [check] at hc
    obtain ⟨hIA, C, h₁, hIC⟩ := loopInv_ok hc
    exact fun p hp => ih h₁ (fun q hq => h q (hIA q hq)) p (hIC p hp)
  | loopNext _ _ _ ih₁ ih₂ =>
    intro s₀ A B hc h
    simp only [check] at hc
    obtain ⟨hIA, C, h₁, hIC⟩ := loopInv_ok hc
    refine ih₂ (A := B) (by simp only [check]; exact loopInv_self h₁ hIC) fun p hp =>
      ih₁ h₁ (fun q hq => h q (hIA q hq)) p (hIC p hp)
  | call => intro _ _ _ hc; simp only [check, reduceCtorEq] at hc
  | frame => intro _ _ _ hc; simp only [check, reduceCtorEq] at hc
  | icall => intro _ _ _ hc; simp only [check, reduceCtorEq] at hc
  | icallNext => intro _ _ _ hc; simp only [check, reduceCtorEq] at hc

/-- The registers `keeps` accepts end with their initial values. -/
theorem Exec.keepsLanes {T : List Reg} {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hk : keeps T c = true) : ∀ r ∈ T, s'.gpr r = s.gpr r := by
  unfold keeps at hk
  split at hk <;> [skip; cases hk]
  rename_i B hB
  have hh := check_ok he (s₀ := s) hB fun p hp => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
    rfl
  intro r hr
  exact hh (r, .g r) (by simpa using List.all_eq_true.mp hk r hr)

end KeepLanes

open VG VG.AArch64 KeepLanes
open VG.Proof.MlKem.AArch64 (Keep)


/-- `WP.keep` for code that also writes the registers `T`, but restores them
(`KeepLanes.keeps`): it keeps all but `rs`. -/
theorem WP.keepLanes {c : Prog isa} {s : State} {Q : State → Prop} (rs T : List Reg) (h : WP isa c s Q)
    (hc : writesOnly (rs ++ T) c = true) (hT : keeps T c = true) (hn : c.noCalls = true := by first | rfl | decide)
    (hv : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq, kk⟩ := WP.keep (rs ++ T) h hc hn hv
  refine ⟨t, s', he, hq, ⟨fun r hr => ?_, kk.rd, kk.wr, kk.sp, kk.vcs⟩⟩
  by_cases hrT : r ∈ T
  · exact Exec.keepsLanes he hT r hrT
  · exact kk.gpr r (by simp [hr, hrT])

end VG.Proof.Bignum.AArch64
