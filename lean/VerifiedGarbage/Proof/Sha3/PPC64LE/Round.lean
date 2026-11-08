module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.Sha3.Compl
public import VerifiedGarbage.Impl.Sha3.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
meta import VerifiedGarbage.Proof.Sha3.Compl
meta import VerifiedGarbage.Impl.Sha3.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Keccak-f[1600] on PPC64LE: a round, by evaluation

A round's θ, ρ, π and χ (`core`) are checked by evaluating their code over
the ANF domain (`Bitslice.Anf`, with `Straight.eval`): the lanes of the
state, as kept (complemented, `Compl.cmpl`), are atoms `0–24` in their
registers (`lane`), and the scratch space is four slots, the three spilled
lanes and all ones (the constant `one`). `check` compares the registers'
values after it with the round computed from the specification
(`Compl.specP`), lane 0 before ι, whose round constant is atom `25`; and
`core_ok` turns that into a statement about the machine. ι (`iota`), the
round constant built from immediates, is run symbolically (`round_ok`).

The prologue's and the epilogue's loads and stores of the lanes, with the
lanes `complLanes` complemented, are checked the same way (`load_ok`,
`store_ok`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Round

open VG VG.PPC64LE VG.PPC64LE.Straight VG.Bitslice.Anf VG.Impl.Sha3.PPC64LE
open VG.Proof.Sha3.Compl (specP cmpl msk maskP eval_specP)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-- The lane a register holds (`lane`, inverted). -/
def laneOf : Reg → Option Nat
  | .r2 => some 0 | .r7 => some 1 | .r8 => some 2 | .r9 => some 3 | .r10 => some 4
  | .r11 => some 5 | .r12 => some 6 | .r14 => some 7 | .r15 => some 8 | .r16 => some 9
  | .r17 => some 10 | .r18 => some 11 | .r19 => some 12 | .r20 => some 13 | .r21 => some 14
  | .r22 => some 15 | .r23 => some 16 | .r24 => some 17 | .r25 => some 18 | .r26 => some 19
  | .r27 => some 20 | .r28 => some 21 | .r29 => some 22 | .r30 => some 23 | .r31 => some 24
  | _ => none

theorem laneOf_lane : ∀ i < 25, laneOf (lane i) = some i := by decide

theorem laneOf_some {r : Reg} {i : Nat} (h : laneOf r = some i) : r = lane i ∧ i < 25 := by
  cases r <;> simp only [laneOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact ⟨rfl, by decide⟩

/-- The lanes are in distinct registers, none of them a pointer or a temporary. -/
theorem lane_inj : ∀ i < 25, ∀ j < 25, lane i = lane j → i = j := by decide

theorem lane_ne : ∀ i < 25, lane i ≠ .r0 ∧ lane i ≠ .r3 ∧ lane i ≠ .r4 ∧ lane i ≠ .r5 ∧ lane i ≠ .r6 := by
  decide

/-! ## θ, ρ, π and χ -/

/-- The scratch space: slots 0–2 the spilled lanes, slot 3 all ones. -/
def cfg : Cfg := { base := .r4, slots := 4, ext := .r3, exts := 0 }

/-- The lanes, as kept, in their registers, and all ones in slot 3. -/
def env₀ : Straight.Env Poly :=
  { reg := fun r => (laneOf r).map atom
    slot := fun k => if k = 3 then some one else none }

/-- The round's output in the lanes' registers, lane 0 before ι, and slot 3
unchanged. -/
def post (e : Straight.Env Poly) : Bool :=
  (match e.reg (lane 0) with
    | some a => pxor a (atom 25) == specP 0
    | none => false) &&
  (List.range 24).all (fun j => e.reg (lane (j + 1)) == some (specP (j + 1))) &&
  e.slot 3 == some one

def check : Bool := Straight.check anf cfg (fun _ => none) core env₀ post

deriving instance Lean.ToExpr for Poly

/- `specP` reads the tables of `sD` and `sB`, so that the kernel evaluates each of their
values once, not once for each lane that uses it. -/
materialize_table Compl.sD 5
materialize_table Compl.sB 5 5
materialize_table specP 25

theorem check_eq : check = true := by lit_decide

theorem cmpl_get (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] = A[i] ^^^ msk i := by
  simp [cmpl]

/-- What `core` leaves in the registers and the scratch space. -/
structure CoreOut (A : KState) (rc : Lane) (P : Addr) (s s' : State) : Prop where
  lanes : ∀ i (hi : i < 25), i ≠ 0 → s'.gpr (lane i) = (cmpl (Proof.Sha3.outState A rc))[i]
  lane0 : s'.gpr (lane 0) ^^^ rc = (cmpl (Proof.Sha3.outState A rc))[0]
  ones : s'.mem.readW (P + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64
  frame : Frame [⟨P, 32⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  r3 : s'.gpr .r3 = s.gpr .r3
  r4 : s'.gpr .r4 = s.gpr .r4

/-- θ, ρ, π and χ, on the lanes kept complemented (`cmpl`) in their registers,
with the scratch space at `P` (all ones at `P + 24`). -/
theorem core_ok {s : State} {A : KState} {P : Addr} (rc : Lane) (hP : s.gpr .r4 = P)
    (hin : ∀ k < 4, InRegions s.wr (P + BitVec.ofNat 64 (8 * k)) 8)
    (hones : s.mem.readW (P + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64)
    (hA : ∀ i (hi : i < 25), s.gpr (lane i) = (cmpl A)[i]) :
    ∃ s', runBlock isa core s = some s' ∧ CoreOut A rc P s s' := by
  obtain ⟨e', he', hpost⟩ := Straight.of_check _ _ _ check_eq
  let V : Nat → Lane := fun i => if i = 25 then rc else s.gpr (lane i)
  have hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i := fun i hi => by
    simp only [V, show i ≠ 25 by omega, ite_false]
    rw [← cmpl_get A hi]; exact hA i hi
  have hV25 : V 25 = rc := by simp [V]
  have hok : Ok cfg s :=
    { slotIn := fun k hk => by simp only [cfg] at hk ⊢; rw [hP]; exact hin k hk
      extIn := fun k hk => by simp [cfg] at hk
      slots := by simp only [cfg]; decide
      sep := fun _ _ j hj => by simp [cfg] at hj }
  have hrel : Rel (AnfRel V) cfg (fun _ => none) env₀ s :=
    { reg := fun r a h => by
        simp only [env₀, Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        obtain ⟨rfl, hi25⟩ := laneOf_some hi
        simp only [AnfRel, eval_atom, V, show i ≠ 25 by omega, ite_false]
      slot := fun k a _ h => by
        simp only [env₀] at h
        split at h
        · rename_i hk; subst hk; cases h
          simp only [AnfRel, eval_one, cfg, hP]; exact hones.symm
        · cases h
      ext := fun _ _ _ h => by cases h }
  obtain ⟨s', hs', p⟩ := Straight.run (anf_sound V) hok hrel he'
  simp only [post, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  obtain ⟨⟨h0, hl⟩, h3⟩ := hpost
  have hb : s'.gpr .r4 = P := by have := p.base; simp only [cfg] at this; rw [this, hP]
  refine ⟨s', hs', ⟨fun i hi hi0 => ?_, ?_, ?_, ?_, p.rd, p.wr, p.sp, p.lr,
    by have := p.ext; simpa [cfg] using this, by have := p.base; simpa [cfg] using this⟩⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h := p.rel.reg _ _ (hl j (by omega))
    simp only [AnfRel, eval_specP hV hV25 hi] at h
    exact h.symm
  · split at h0
    · rename_i a ha
      have h := p.rel.reg _ _ ha
      simp only [beq_iff_eq] at h0
      have e := congrArg (eval V) h0
      rw [eval_pxor, eval_atom, hV25, eval_specP hV hV25 (by decide), h] at e
      exact e
    · cases h0
  · have h := p.rel.slot 3 _ (by decide) h3
    simp only [AnfRel, eval_one, cfg, hb] at h
    exact h.symm
  · have f := p.frame
    simp only [slotRegion, cfg, hP] at f
    exact f

/-! ## ι -/

/-- ι of round `r`: lane 0 XORed with its round constant, `T1` overwritten. -/
theorem iota_ok (r : Nat) {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ i, i < 25 → i ≠ 0 → s'.gpr (lane i) = s.gpr (lane i)) →
      s'.gpr (lane 0) = s.gpr (lane 0) ^^^ Spec.Sha3.RC r → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → s'.lr = s.lr → s'.gpr .r3 = s.gpr .r3 →
      s'.gpr .r4 = s.gpr .r4 → Q s') :
    WP isa (.block (iota r)) s Q := by
  simp only [iota, movImm64, List.cons_append, List.nil_append]
  refine MdStream.PPC64LE.WP.cons exec_lis (MdStream.PPC64LE.WP.cons exec_ori
    (MdStream.PPC64LE.WP.cons (exec_lsl (by decide)) (MdStream.PPC64LE.WP.cons exec_oris
    (MdStream.PPC64LE.WP.cons exec_ori (MdStream.PPC64LE.WP.cons exec_logic (WP.block_nil ?_))))))
  have l0 : lane 0 ≠ T1 := (lane_ne 0 (by decide)).2.2.2.1
  refine k _ (fun i hi hi0 => ?_) ?_ rfl rfl rfl rfl rfl ?_ ?_
  · have hne : lane i ≠ lane 0 := fun h => hi0 (lane_inj i hi 0 (by decide) h)
    have h5 : lane i ≠ T1 := (lane_ne i hi).2.2.2.1
    simp only [RegUpd.gpr_write_of_ne _ _ hne, RegUpd.gpr_write_of_ne _ _ h5]
  · simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ l0]
    rw [movImm64_eq]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r3 ≠ lane 0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.r3 ≠ T1 by decide)]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ lane 0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ T1 by decide)]

/-- Round `r`, on the lanes kept complemented (`cmpl`) in their registers. -/
theorem round_ok (r : Nat) {s : State} {A : KState} {P : Addr} (hP : s.gpr .r4 = P)
    (hin : ∀ k < 4, InRegions s.wr (P + BitVec.ofNat 64 (8 * k)) 8)
    (hones : s.mem.readW (P + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64)
    (hA : ∀ i (hi : i < 25), s.gpr (lane i) = (cmpl A)[i]) :
    WP isa (.block (round r)) s fun s' =>
      (∀ i (hi : i < 25), s'.gpr (lane i) = (cmpl (Spec.Sha3.rnd A r))[i]) ∧
      s'.mem.readW (P + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64 ∧
      Frame [⟨P, 32⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r4 = s.gpr .r4 := by
  obtain ⟨s₁, hs₁, c⟩ := core_ok (Spec.Sha3.RC r) hP hin hones hA
  rw [← Proof.Sha3.outState_eq]
  unfold round
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, iota_ok r fun s' hl hl0 hm hrd hwr hsp hlr h3 h4 => ?_⟩
  refine ⟨fun i hi => ?_, by rw [hm]; exact c.ones, by rw [hm]; exact c.frame,
    by rw [hrd, c.rd], by rw [hwr, c.wr], by rw [hsp, c.sp], by rw [hlr, c.lr],
    by rw [h3, c.r3], by rw [h4, c.r4]⟩
  by_cases hi0 : i = 0
  · subst hi0; rw [hl0]; exact c.lane0
  · rw [hl i hi hi0]; exact c.lanes i hi hi0

/-! ## Loading and storing the lanes -/

open VG.Proof.Sha3 (Lanes laneAddr)

/-- Loading the lanes from the state at `r3`, with all ones in `T0`. -/
def lCfg : Cfg := { base := .r4, slots := 0, ext := .r3, exts := 25 }

def lEnv : Straight.Env Poly := { reg := fun r => if r = T0 then some one else none, slot := fun _ => none }

def lPost (e : Straight.Env Poly) : Bool :=
  (List.range 25).all fun i => e.reg (lane i) == some (pxor (atom i) (maskP i))

theorem load_check : Straight.check anf lCfg (fun k => some (atom k)) loadLanes lEnv lPost = true := by
  lit_decide

/-- Storing the lanes to the state at `r3`, with all ones at scratch offset
24 (external word 3). -/
def sCfg : Cfg := { base := .r3, slots := 25, ext := .r4, exts := 4 }

def sEnv : Straight.Env Poly := { reg := fun r => (laneOf r).map atom, slot := fun _ => none }

def sExt (k : Nat) : Option Poly := if k = 3 then some one else none

def sPost (e : Straight.Env Poly) : Bool :=
  (List.range 25).all fun i => e.slot i == some (pxor (atom i) (maskP i))

theorem store_check : Straight.check anf sCfg sExt storeLanes sEnv sPost = true := by
  lit_decide

theorem eval_compl (V : Nat → Lane) (M : KState) (hV : ∀ i (hi : i < 25), V i = M[i]) {i : Nat} (hi : i < 25) :
    Bitslice.Anf.eval V (pxor (atom i) (maskP i)) = (cmpl M)[i] := by
  rw [eval_pxor, eval_atom, Compl.eval_maskP, cmpl_get M hi, hV i hi]

theorem cmpl_cmpl (A : KState) : cmpl (cmpl A) = A := by
  apply Vector.ext; intro i hi
  rw [cmpl_get _ hi, cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The prologue's loads: the lanes of the state at `r3` (`M`), complemented. -/
theorem load_ok {s : State} {M : KState} (hones : s.gpr T0 = BitVec.allOnes 64)
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (laneAddr (s.gpr .r3) i) 8)
    (hM : Lanes s.mem (s.gpr .r3) M) :
    ∃ s', runBlock isa loadLanes s = some s' ∧
      (∀ i (hi : i < 25), s'.gpr (lane i) = (cmpl M)[i]) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r4 = s.gpr .r4 := by
  obtain ⟨e', he', hp⟩ := Straight.of_check _ _ _ load_check
  let V : Nat → Lane := fun i => M[i]!
  have hV : ∀ i (hi : i < 25), V i = M[i] := fun i hi => Proof.Sha3.getElem!_eq _ hi
  have hok : Ok lCfg s :=
    { slotIn := fun k hk => by simp [lCfg] at hk
      extIn := fun k hk => by simp only [lCfg] at hk ⊢; exact hin k hk
      slots := by decide
      sep := fun k hk _ _ => by simp [lCfg] at hk }
  have hrel : Rel (AnfRel V) lCfg (fun k => some (atom k)) lEnv s :=
    { reg := fun r a h => by
        simp only [lEnv] at h
        split at h
        · rename_i hr; subst hr; cases h
          simp only [AnfRel, eval_one, hones]
        · cases h
      slot := fun _ _ _ h => by cases h
      ext := fun k a hk h => by
        simp only [Option.some.injEq] at h; subst h
        simp only [lCfg] at hk ⊢
        simp only [AnfRel, eval_atom, hV k hk]
        exact (hM k hk).symm }
  obtain ⟨s', hs', p⟩ := Straight.run (anf_sound V) hok hrel he'
  simp only [lPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have hf := p.frame
  simp only [slotRegion, lCfg, Nat.mul_zero] at hf
  refine ⟨s', hs', fun i hi => ?_, ?_, p.rd, p.wr, p.sp, p.lr,
    by have := p.ext; simpa [lCfg] using this, by have := p.base; simpa [lCfg] using this⟩
  · have h := p.rel.reg _ _ (hp i hi)
    simp only [AnfRel, eval_compl V M hV hi] at h
    exact h.symm
  · funext a
    refine hf a fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr; simp [Region.Contains] at hc

/-- The epilogue's stores: the lanes (`cmpl M` in their registers),
complemented back, to the state at `r3`, with all ones at `r4 + 24`. -/
theorem store_ok {s : State} {M : KState} {st : Addr} (h3 : s.gpr .r3 = st)
    (hones : s.mem.readW (s.gpr .r4 + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64)
    (hst : (⟨st, 200⟩ : Region) ∈ s.wr)
    (hin : ∀ k < 4, InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨st, 200⟩ ⟨s.gpr .r4, 32⟩)
    (hA : ∀ i (hi : i < 25), s.gpr (lane i) = (cmpl M)[i]) :
    ∃ s', runBlock isa storeLanes s = some s' ∧ Lanes s'.mem st M ∧
      Frame [⟨st, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.lr = s.lr ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r4 = s.gpr .r4 := by
  obtain ⟨e', he', hp⟩ := Straight.of_check _ _ _ store_check
  let V : Nat → Lane := fun i => s.gpr (lane i)
  have hV : ∀ i (hi : i < 25), V i = (cmpl M)[i] := fun i hi => hA i hi
  have hok : Ok sCfg s :=
    { slotIn := fun k hk => ⟨_, hst, by
        have := slot_contains st hk (n := 25) (by decide)
        simp only [sCfg, h3] at this ⊢; exact this⟩
      extIn := fun k hk => by simp only [sCfg] at hk ⊢; exact hin k hk
      slots := by decide
      sep := fun k hk j hj => by
        simp only [sCfg, h3] at hk hj ⊢
        exact Region.Disjoint.sep hsep (Proof.Sha3.lane_contains st hk)
          (slot_contains (s.gpr .r4) hj (by decide)) }
  have hrel : Rel (AnfRel V) sCfg sExt sEnv s :=
    { reg := fun r a h => by
        simp only [sEnv, Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        obtain ⟨rfl, hi25⟩ := laneOf_some hi
        simp only [AnfRel, eval_atom, V]
      slot := fun _ _ _ h => by cases h
      ext := fun k a _ h => by
        simp only [sExt] at h
        split at h
        · rename_i hk; subst hk; cases h
          simp only [AnfRel, eval_one, sCfg]; exact hones.symm
        · cases h }
  obtain ⟨s', hs', p⟩ := Straight.run (anf_sound V) hok hrel he'
  simp only [sPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have hb : s'.gpr .r3 = st := by have := p.base; simp only [sCfg] at this; rw [this, h3]
  refine ⟨s', hs', fun i hi => ?_, ?_, p.rd, p.wr, p.sp, p.lr,
    by have := p.base; simpa [sCfg] using this, by have := p.ext; simpa [sCfg] using this⟩
  · have h := p.rel.slot i _ (by simp only [sCfg]; exact hi) (hp i hi)
    simp only [AnfRel, eval_compl V (cmpl M) hV hi, cmpl_cmpl, sCfg, hb] at h
    exact h.symm
  · have f := p.frame
    simp only [slotRegion, sCfg, h3] at f
    exact f

end VG.Proof.Sha3.PPC64LE.Round
