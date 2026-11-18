module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Lit
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.Sha3.Compl
public import VerifiedGarbage.Impl.Sha3.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha3.ComplLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
meta import VerifiedGarbage.Proof.Sha3.Compl
meta import VerifiedGarbage.Impl.Sha3.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha3.ComplLit

/-! ### `Sha3.PPC64LE.Permute`, which only this module used -/

section

/-! ### `Sha3.PPC64LE.Round`, which only this module used -/

section

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
  cases r <;> cases h <;> exact ⟨rfl, by decide⟩

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
    simp only [V, show i ≠ 25 by omega_using [hi], ite_false]
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
        simp only [AnfRel, eval_atom, V, show i ≠ 25 by omega_using [hi25], ite_false]
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
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [hi0]⟩
    have h := p.rel.reg _ _ (hl j (by omega_using [hi]))
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

end

end

/-!
# Keccak-f[1600] on PPC64LE: the whole function

The prologue saves the nonvolatile registers in the scratch space (`Spill`),
stores all ones there, and loads the lanes into their registers, the lanes
`complLanes` complemented (`Round.load_ok`); each of the 24 rounds is
`Round.round_ok`; the epilogue stores the lanes back, complemented back
(`Round.store_ok`), and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE
open VG.Spec.Sha3 (stateAt keccakF rnd)
open VG.Proof.Sha3 (Lanes laneAddr lane_contains)
open VG.Proof.Sha3.Compl (cmpl)

abbrev KState := Spec.Sha3.State

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev scr : Addr := s₀.gpr .r4
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permutePPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stR_in : stR s₀ ∈ s₀.wr := by rw [h.wr]; simp

theorem scr_in {d : Nat} (hd : d + 8 ≤ 512) :
    InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 d) 8 := by
  rw [h.wr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩

theorem slot_in : ∀ k < 4, InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  fun _ hk => h.scr_in (by omega_using [hk])

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (laneAddr (st s₀) i) 8 := fun _ hi =>
  h.in_all (by rw [h.wr]; exact ⟨stR s₀, by simp, lane_contains _ hi⟩)

/-- The state is disjoint from every part of the scratch space. -/
theorem st_off {d n : Nat} (hn : d + n ≤ 512) :
    Region.Disjoint (stR s₀) ⟨scr s₀ + BitVec.ofNat 64 d, n⟩ :=
  h.st_scr.sub_right (Offset.sub_base _ hn)

end Pre

/-! ## The scratch space -/

theorem saved_bound : ∀ p ∈ saved, 32 ≤ p.2 ∧ p.2 + 8 ≤ 32 + 152 := by decide

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

/-- The saved registers are kept by writes to the spill slots or the state. -/
theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (h : Spill.Saved (scr s₀) s₀.gpr saved m) {R : Region}
    (hR : R = ⟨scr s₀, 32⟩ ∨ R = stR s₀) (hf : Frame [R] m m') :
    Spill.Saved (scr s₀) s₀.gpr saved m' := by
  refine h.frame_in saved_bound hf fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  rcases hR with rfl | rfl
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact (hp.st_off (by omega_using [])).symm

/-! ## The rounds -/

/-- Before round `r`: the state after `r` rounds in the lanes' registers, as
kept (`cmpl`), and the scratch space holding all ones and the saved
registers. -/
structure RInv (s₀ : State) (r : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = scr s₀
  lanes : ∀ i (hi : i < 25), s.gpr (lane i) = (cmpl ((List.range r).foldl rnd (A₀ s₀)))[i]
  ones : s.mem.readW (scr s₀ + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64
  saved : Spill.Saved (scr s₀) s₀.gpr saved s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rounds_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : RInv s₀ 0 s) :
    WP isa (.block rounds) s (RInv s₀ 24) := by
  refine wp_range_flatMap (M := isa) (RInv s₀) (fun r s' _ hI => ?_) 24 (Nat.le_refl _) s h
  refine WP.mono (Round.round_ok r hI.r4 (by rw [hI.wr]; exact hp.slot_in) hI.ones hI.lanes)
    fun s'' ⟨hl, ho, hf, hrd, hwr, _, _, h3, h4⟩ => ⟨by rw [h3, hI.r3], by rw [h4, hI.r4],
      fun i hi => by rw [hl i hi, Proof.Sha3.foldl_succ], ho, saved_frame hp hI.saved (.inl rfl) hf,
      by rw [hrd, hI.rd], by rw [hwr, hI.wr]⟩

/-! ## The prologue -/

theorem setup_eq : setup = Spill.saveCode .r4 saved ++
    ([.lis T0 0xffff, .ori T0 T0 0xffff, .store .d T0 .r4 24] : List Instr) := rfl

theorem ones_eq : (((0xffff : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 |||
    (0xffff : BitVec 16).setWidth 64) = BitVec.allOnes 64 := by decide

theorem lanes₀ (s₀ : State) : Lanes s₀.mem (st s₀) (A₀ s₀) := by
  intro i hi; simp [Spec.Sha3.stateAt, laneAddr]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (setup ++ loadLanes)) s₀ (RInv s₀ 0) := by
  rw [setup_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Spill.save_wp (by decide) saved_fits fun p hp' => hp.scr_in (by
    have := saved_bound p hp'; omega_using [this])) fun s₁ ⟨g₁, rd₁, wr₁, _, _, m₁⟩ => ?_
  have v₁ := m₁ ▸ Spill.saveMem_saved (by decide) s₀.mem (scr s₀) s₀.gpr (l := saved)
  have f₁ : Frame [⟨scr s₀ + BitVec.ofNat 64 32, 152⟩] s₀.mem s₁.mem :=
    m₁ ▸ Spill.saveMem_frame saved_bound (by omega_using []) _ _ _
  have h4 : s₁.gpr .r4 = scr s₀ := by rw [g₁]
  suffices key : ∀ s₂ : State, (∀ r, r ≠ T0 → s₂.gpr r = s₁.gpr r) → s₂.gpr T0 = BitVec.allOnes 64 →
      s₂.mem = s₁.mem.writeW (scr s₀ + BitVec.ofNat 64 24) (BitVec.allOnes 64) → s₂.rd = s₀.rd →
      s₂.wr = s₀.wr → WP isa (.block loadLanes) s₂ (RInv s₀ 0) by
    rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
    refine MdStream.PPC64LE.WP.cons exec_lis (MdStream.PPC64LE.WP.cons exec_ori
      (MdStream.PPC64LE.WP.cons (exec_store_d (by decide) (by decide) ?_) (key _ ?_ ?_ ?_ rd₁ wr₁)))
    · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ T0 by decide), h4, RegUpd.wr_write, wr₁]
      exact hp.scr_in (by omega_using [])
    · intro r hr; simp only [RegUpd.gpr_write_of_ne _ _ hr]
    · simp only [RegUpd.gpr_write_self]; exact ones_eq
    · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ T0 by decide), h4, RegUpd.gpr_write_self,
        RegUpd.mem_write]
      rw [ones_eq]
  intro s₂ g₂ o₂ mem₂ rd₂ wr₂
  have r3₂ : s₂.gpr .r3 = st s₀ := by rw [g₂ _ (by decide), g₁]
  have r4₂ : s₂.gpr .r4 = scr s₀ := by rw [g₂ _ (by decide), h4]
  -- the state and the saved registers are kept by the store of all ones
  have f₂ : Frame [⟨scr s₀ + BitVec.ofNat 64 24, 8⟩] s₁.mem s₂.mem := by
    rw [mem₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hA : Lanes s₂.mem (st s₀) (A₀ s₀) := fun i hi => by
    rw [f₂.readW (lane_contains _ hi) (by simpa using hp.st_off (d := 24) (n := 8) (by omega_using []))
      (by decide), f₁.readW (lane_contains _ hi) (by simpa using hp.st_off (d := 32) (n := 152) (by omega_using []))
      (by decide)]
    exact lanes₀ s₀ i hi
  have hsv : Spill.Saved (scr s₀) s₀.gpr saved s₂.mem :=
    v₁.frame_in saved_bound f₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [])
  have hones : s₂.mem.readW (scr s₀ + BitVec.ofNat 64 24) 64 = BitVec.allOnes 64 := by
    rw [mem₂, Mem.readW_writeW_self64]
  obtain ⟨s₃, hs₃, hl₃, m₃, rd₃, wr₃, _, _, r3₃, r4₃⟩ := Round.load_ok (M := A₀ s₀) o₂
    (fun i hi => by rw [rd₂, wr₂, r3₂]; exact hp.lane_in i hi) (by rw [r3₂]; exact hA)
  refine WP.of_runBlock ⟨s₃, hs₃, ⟨by rw [r3₃, r3₂], by rw [r4₃, r4₂],
    fun i hi => by rw [hl₃ i hi]; rfl, by rw [m₃]; exact hones, by rw [m₃]; exact hsv,
    by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩⟩

/-! ## The epilogue -/

theorem preserved_saved : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : RInv s₀ 24 s) :
    WP isa (.block (storeLanes ++ restore)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permutePPC64LE.post s₀ s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, hs₁, hl₁, hf₁, rd₁, wr₁, _, _, r3₁, r4₁⟩ := Round.store_ok (M := keccakF (A₀ s₀)) hI.r3
    (by rw [hI.r4]; exact hI.ones) (by rw [hI.wr]; exact hp.stR_in)
    (fun k hk => by rw [hI.rd, hI.wr, hI.r4]; exact hp.in_all (hp.slot_in k hk))
    (by rw [hI.r4]; simpa using hp.st_off (d := 0) (n := 32) (by omega_using [])) hI.lanes
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hsv := saved_frame hp hI.saved (.inr rfl) hf₁
  refine WP.mono (Spill.restore_wp (by decide) (b := .r4) (B := scr s₀) (by rw [r4₁, hI.r4])
    saved_fits (by decide) (fun p hp' => ?_) hsv) fun s' h => ⟨fun r hr => ?_, ?_⟩
  · rw [rd₁, wr₁, hI.rd, hI.wr]
    exact hp.in_all (hp.scr_in (by have := saved_bound p hp'; omega_using [this]))
  · exact h.gpr_of (.inl (preserved_saved r hr))
  · refine ⟨?_, by rw [h.other _ (by decide), r3₁, hI.r3], by rw [h.other _ (by decide), r4₁, hI.r4]⟩
    show stateAt s'.mem (st s₀) = keccakF (A₀ s₀)
    apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, h.mem]
    exact hl₁ i hi

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permutePPC64LE.post s₀ s' := by
  unfold permute
  rw [show setup ++ loadLanes ++ rounds ++ storeLanes ++ restore =
    (setup ++ loadLanes) ++ (rounds ++ (storeLanes ++ restore)) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (rounds_ok hp h₁) fun s₂ h₂ => epilogue_ok hp h₂

theorem permute_correct (s : State) (hs : Proof.Sha3.permutePPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permutePPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide)⟩, h₂⟩

theorem permute_noFrames : Impl.Sha3.PPC64LE.permute.noFrames = true := by lit_decide

end VG.Proof.Sha3.PPC64LE

end

end

/-! ### `Sha3.PPC64LE.Stream.CT`, which this module and modules that import it used -/

section

/-!
# The SHA-3 sponge on PPC64LE: constant time

The taint analysis of `absorb`, `pad` and `squeeze` (the permutation they
call included), from the public arguments: the pointers, `rate`, `pos` and
the lengths, and the stack pointer.

The permutation saves the nonvolatile registers in its scratch space and
restores them from there, and `absorb` and `squeeze` keep their variables
in `r26`–`r31` across its calls. So their bodies, inside the frame that
saves the link register, are analysed with public slots in the writable
regions (`slotTaint`), which keep a public value saved there public when it
is loaded back; the frame's own region is disjoint from the others by the
contract's stack. The frame (`RelCT.frame`) and the moves of the link
register around it leak nothing.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE

theorem absorb_agree {s₁ s₂ : State} (hpub : Proof.Sha3.absorbPPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pad_agree {s₁ s₂ : State} (hpub : Proof.Sha3.padPPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem squeeze_agree {s₁ s₂ : State} (hpub : Proof.Sha3.squeezePPC64LE.pub s₁ s₂) :
    PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pad_ct : ConstantTime isa Proof.Sha3.padPPC64LE.pre Proof.Sha3.padPPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.pad :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r7])
    (fun _ _ _ _ hp => pad_agree hp) (by taint_decide)

/-! ## The link register's frame -/

/-- Two runs from states related by `P`, after `mflr r0`. -/
def AfterMflr (P : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, P s₁ s₂ ∧ a = s₁.write .r0 s₁.lr ∧ b = s₂.write .r0 s₂.lr

/-- `withLr main` leaks the same trace in two runs from states related by
`P` (with the same stack pointer) if `main` does from the states its frame's
push leaves. -/
theorem withLr_rel {P : State → State → Prop} {main : Prog isa}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hm : RelCT isa (fun a b => ∃ s₁ s₂, AfterMflr P s₁ s₂ ∧ a = pushed .r0 s₁ ∧ b = pushed .r0 s₂)
      main fun _ _ => True) :
    RelCT isa P (Impl.Sha3.PPC64LE.Stream.withLr main) fun _ _ => True := by
  unfold Impl.Sha3.PPC64LE.Stream.withLr
  have h₁ : RelCT isa P (.block [.mflr .r0]) (AfterMflr P) := by
    have h := RelCT.wpDep (F := fun (s s' : State) => s' = s.write .r0 s.lr)
      (RelCT.taint (A := taint) (P := P) (c := .block [.mflr .r0]) (Taint.ofRegs []) (fun s₁ s₂ h => ⟨hsp _ _ h, by simp⟩)
        (by taint_decide))
      fun s₁ s₂ _ => ⟨WP.block_cons_iff.mpr ⟨_, exec_mflr, WP.block_nil rfl⟩,
        WP.block_cons_iff.mpr ⟨_, exec_mflr, WP.block_nil rfl⟩⟩
    exact RelCT.mono h (fun _ _ h => h) fun _ _ ⟨_, σ₁, σ₂, hp, e₁, e₂⟩ => ⟨σ₁, σ₂, hp, e₁, e₂⟩
  have h₂ := RelCT.frame (r := .r0) (r' := .r0) (body := main) (P := AfterMflr P)
    (fun _ _ ⟨s₁, s₂, hp, e₁, e₂⟩ => by subst e₁ e₂; exact hsp s₁ s₂ hp) hm
  have h₃ : RelCT isa (fun a b : State => a.sp = b.sp) (.block [.mtlr .r0]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => ⟨h, by simp⟩) (by taint_decide)
  exact RelCT.seq h₁ (RelCT.seq h₂ h₃)

/-- The frame's region is in the contract's stack, below the stack pointer. -/
theorem frame_sub (s : State) :
    Region.Sub ⟨s.sp - 48 + 32, 16⟩ ⟨s.sp - 48, 48⟩ := by
  have := Offset.sub_base (s.sp - 48) (d := 32) (n := 16) (k := 48) (by omega_using [])
  exact this

/-! ## `absorb` -/

/-- `absorbMain`'s taint: the arguments public, and the writable regions the
frame's, the state and the scratch space, at `r3` and `r8`. -/
def absorbTaint : SlotTaint.T :=
  SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7, .r8] [16, 200, 640] [(.r3, 1), (.r8, 2)]

abbrev absorbRel (s₁ s₂ : State) : Prop :=
  Proof.Sha3.absorbPPC64LE.pre s₁ ∧ Proof.Sha3.absorbPPC64LE.pre s₂ ∧ Proof.Sha3.absorbPPC64LE.pub s₁ s₂

theorem absorb_main_agree {a b : State}
    (h : ∃ s₁ s₂, AfterMflr absorbRel s₁ s₂ ∧ a = pushed .r0 s₁ ∧ b = pushed .r0 s₂) :
    SlotTaint.Agree absorbTaint a b := by
  obtain ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩ := h
  obtain ⟨-, hw₁, dSS, -, -, -, kS, -, kC, -, -⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨p3, p4, p5, p6, p7, p8, hsp⟩ := hp
  refine SlotTaint.agree_mk' (by simp only [pushed, State.write, hsp])
    (fun r hr => ?_) (by simp only [pushed, State.write, hw₁, hw₂, hsp, p3, p8]) ?_ ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [pushed, State.write, reduceCtorEq, ite_false] <;> with_reducible assumption
  · simp only [pushed, State.write, hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [pushed, State.write, hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => absurd hr List.not_mem_nil) .nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kS.sub_left (frame_sub s₁)
      · exact kC.sub_left (frame_sub s₁)
    · simp only [List.mem_singleton] at hr; subst hr; exact dSS
  · simp only [pushed, State.write, hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega_using []
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₂]

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbPPC64LE.pre Proof.Sha3.absorbPPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.absorb :=
  RelCT.constantTime (withLr_rel (P := absorbRel) (fun _ _ h => h.2.2.2.2.2.2.2.2)
    (RelCT.taint (A := slotTaint) absorbTaint (fun _ _ h => absorb_main_agree h) (by taint_decide)))

/-! ## `squeeze` -/

/-- `squeezeMain`'s taint: the arguments public, and the writable regions the
frame's, the state, the output and the scratch space, at `r3` and `r8`. -/
def squeezeTaint : SlotTaint.T :=
  SlotTaint.mk' [.r3, .r4, .r5, .r6, .r7, .r8] [16, 200, 0, 640] [(.r3, 1), (.r8, 3)]

abbrev squeezeRel (s₁ s₂ : State) : Prop :=
  Proof.Sha3.squeezePPC64LE.pre s₁ ∧ Proof.Sha3.squeezePPC64LE.pre s₂ ∧
    Proof.Sha3.squeezePPC64LE.pub s₁ s₂

theorem squeeze_main_agree {a b : State}
    (h : ∃ s₁ s₂, AfterMflr squeezeRel s₁ s₂ ∧ a = pushed .r0 s₁ ∧ b = pushed .r0 s₂) :
    SlotTaint.Agree squeezeTaint a b := by
  obtain ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩ := h
  obtain ⟨-, hw₁, dSO, dSC, dOC, -, kS, kO, kC, -, -⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨p3, p4, p5, p6, p7, p8, hsp⟩ := hp
  refine SlotTaint.agree_mk' (by simp only [pushed, State.write, hsp])
    (fun r hr => ?_) (by simp only [pushed, State.write, hw₁, hw₂, hsp, p3, p6, p7, p8]) ?_ ?_ ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [pushed, State.write, reduceCtorEq, ite_false] <;> with_reducible assumption
  · simp only [pushed, State.write, hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)))
  · simp only [pushed, State.write, hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => ?_)
      (.cons (fun r hr => absurd hr List.not_mem_nil) .nil)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact kS.sub_left (frame_sub s₁)
      · exact kO.sub_left (frame_sub s₁)
      · exact kC.sub_left (frame_sub s₁)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSO
      · exact dSC
    · simp only [List.mem_singleton] at hr; subst hr; exact dOC
  · simp only [pushed, State.write, hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> first | omega_using [] | exact Nat.le_of_lt (BitVec.isLt _)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [SlotTaint.region, pushed, State.write, hw₂]

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezePPC64LE.pre Proof.Sha3.squeezePPC64LE.pub
    Impl.Sha3.PPC64LE.Stream.squeeze :=
  RelCT.constantTime (withLr_rel (P := squeezeRel) (fun _ _ h => h.2.2.2.2.2.2.2.2)
    (RelCT.taint (A := slotTaint) squeezeTaint (fun _ _ h => squeeze_main_agree h) (by taint_decide)))

end VG.Proof.Sha3.PPC64LE.Stream

end

end

/-! ### `Sha3.PPC64LE.Stream.Wp`, which only this module used -/

section

/-!
# The SHA-3 sponge on PPC64LE: the logical instructions

Weakest-precondition rules for `xor` and `or` of registers, beside those of
`Proof/MdStream/PPC64LE/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE VG.Proof.MdStream.PPC64LE

variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end VG.Proof.Sha3.PPC64LE.Stream

end

end

/-! ### `Sha3.PPC64LE.Call`, which only this module used -/

section

@[expose] public section

/-!
# SHA-3 on PPC64LE: calling the permutation, and saving registers
-/

namespace VG.Proof.Sha3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Spec.Sha3 (stateAt keccakF)

/-- Calling `vg_keccak_f1600` on the state at `r3`, with scratch space at
`r4`: the callee-saved registers are kept, and so are `r3` and `r4`. -/
theorem call_ok' {s : State} {st scr : Addr} (h3 : s.gpr .r3 = st) (h4 : s.gpr .r4 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : PPC64LE.Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → s'.gpr .r3 = st → s'.gpr .r4 = scr → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.PPC64LE.permute) s Q := by
  have c3 : s.callEntry.gpr .r3 = st := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = scr := (State.callEntry_gpr _ (by decide)).trans h4
  refine WP.call (k := Proof.Sha3.permutePPC64LE) permute_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_ permute_noFrames
  · simp only [Proof.Sha3.permutePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4]
    exact ⟨trivial, trivial, d₁⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Sha3.permutePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost.1 hpost.2.1 hpost.2.2

/-- Calling `vg_keccak_f1600` on the state at `r3`, with scratch space at
`r4`: the callee-saved registers are kept. -/
theorem call_ok {s : State} {st scr : Addr} (h3 : s.gpr .r3 = st) (h4 : s.gpr .r4 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : PPC64LE.Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.PPC64LE.permute) s Q :=
  call_ok' h3 h4 d₁ hw fun s' hrd hwr hsp hcs hf he _ _ => hQ s' hrd hwr hsp hcs hf he

theorem preserved_r3_r4 : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 := by decide

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `r26`, with
scratch space at `r27`, which are then taken back from `r3` and `r4`. -/
theorem permuteAt_ok {s : State} {st scr : Addr} (h26 : s.gpr .r26 = st) (h27 : s.gpr .r27 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : PPC64LE.Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa permuteAt s Q := by
  unfold permuteAt mov
  refine WP.seq (MdStream.PPC64LE.wp_addi (by decide) fun s₁ u₁ =>
    MdStream.PPC64LE.wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r3 → r ≠ .r4 → s₂.gpr r = s.gpr r := fun r h3 h4 => by
    rw [u₂.other r h4, u₁.other r h3]
  refine WP.seq (call_ok' (st := st) (scr := scr)
    (by rw [u₂.other _ (by decide), u₁.gpr, h26]; exact BitVec.add_zero _)
    (by rw [u₂.gpr, u₁.other _ (by decide), h27]; exact BitVec.add_zero _)
    d₁ (by rw [u₂.wr, u₁.wr]; exact hw) fun s' rd' wr' sp' cs' f' e' r3' r4' => ?_)
  refine MdStream.PPC64LE.wp_addi (by decide) fun s₃ u₃ =>
    MdStream.PPC64LE.wp_addi (by decide) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm' : s₄.mem = s'.mem := by rw [u₄.mem, u₃.mem]
  refine hQ s₄ (by rw [u₄.rd, u₃.rd, rd', u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, wr', u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, sp', u₂.sp, u₁.sp]) (fun r hr => ?_) (by rw [hm', ← hm]; exact f')
    (by rw [hm', e', hm])
  by_cases e26 : r = .r26
  · subst e26
    rw [u₄.other _ (by decide), u₃.gpr, r3', BitVec.add_zero, h26]
  by_cases e27 : r = .r27
  · subst e27
    rw [u₄.gpr, u₃.other _ (by decide), r4', BitVec.add_zero, h27]
  rw [u₄.other r e27, u₃.other r e26, cs' r hr, g r (preserved_r3_r4 r hr).1 (preserved_r3_r4 r hr).2]

end VG.Proof.Sha3.PPC64LE

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream

/-! ## Saving the caller's registers -/

/-- The caller's callee-saved registers `g` are saved in the scratch space at `b`. -/
abbrev Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved b g saved m

/-- The memory after saving `r26`–`r31` (values `g`) at `b + 512 …`. -/
abbrev saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem := Spill.saveMem m b g saved

theorem saved_off : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Saved b g (saveMem m b g) :=
  Spill.saveMem_saved (by decide) m b g

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 512, 48⟩] m (saveMem m b g) :=
  Spill.saveMem_frame (by decide) (by decide) m b g

/-- Saving `r26`–`r31` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop} (hb : b ≠ .r0)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q :=
  Spill.save_ok (l := saved) hb (by decide) (fun p hp => hin _ (by revert p; decide) (by revert p; decide))
    (k _ rfl rfl rfl rfl rfl)

/-- `restore`, `r27` (the base) last. -/
abbrev restored : List (Reg × Nat) :=
  [(.r26, 512), (.r28, 528), (.r29, 536), (.r30, 544), (.r31, 552), (.r27, 520)]

/-- Restoring `r26`–`r31` from the save area at `scr`. -/
theorem restore_ok {s : State} {scr : Addr} (h27 : s.gpr .r27 = scr)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q :=
  WP.mono (Spill.restore_wp (l := restored) (by decide) h27 (by decide) (by decide)
    (fun p hp => hin _ (by revert p; decide) (by revert p; decide)) (hsv.sub (by decide)))
    fun s' h => have h := h.perm (l' := saved) (by decide) (by decide)
      k s' h.gpr h.other h.mem h.rd h.wr h.sp

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem Saved.permute {st scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩) (hf : Frame [⟨st, 200⟩, ⟨scr, 512⟩] m m') :
    Saved scr g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have hoff := saved_off p hp'
    have hsub : Region.Sub ⟨scr + BitVec.ofNat 64 p.2, 8⟩ ⟨scr, 640⟩ := Offset.sub_base _ (by omega_using [hoff])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega_using [hoff]) (by omega_using [hoff])

/-- Writes to a region disjoint from the scratch space keep the saved
registers. -/
theorem Saved.disjoint {R : Region} {scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : R.Disjoint ⟨scr, 640⟩) (hf : Frame [R] m m') : Saved scr g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have hoff := saved_off p hp'
    simp only [List.mem_singleton] at hr
    subst hr
    exact hd.symm.sub_left (Offset.sub_base _ (by omega_using [hoff]))

/-- Writes to the state keep the saved registers. -/
theorem Saved.state {st scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩) (hf : Frame [⟨st, 200⟩] m m') :
    Saved scr g m' :=
  h.permute hd (hf.mono (by simp))

/-- The callee-saved registers our code never touches. -/
abbrev untouched : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25]

theorem notU {r : Reg} (hr : r ∈ untouched) (x : Reg) (hx : x ∉ untouched := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

/-- The callee-saved registers are the caller's again once `restore` has run
and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  rcases preserved_split r hr with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hsv p hp
  · exact hu r h

theorem untouched_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

end VG.Proof.Sha3.PPC64LE.Stream

end

end

/-! ### `Sha3.PPC64LE.Stream.Absorb`, which only this module used -/

section

/-!
# The SHA-3 sponge on PPC64LE: `absorb`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Absorb`):
`absorbMain`, whose frame saving the link register `correct` adds
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream.Absorb

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Proof.Sha3.PPC64LE VG.Proof.Sha3.PPC64LE.Stream
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_addi wp_mov wp_subi wp_li wp_add wp_sub wp_and wp_lsr
  wp_lbz wp_stb wp_std wp_ld eval_zero eval_nonzero contains_offset toNat_ofNat_lt)
open VG.Proof.Sha3 (Rep rep_snoc xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length xorAt xorAt_single byteOf_xorAt rep_append
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev rt : Nat := (s₀.gpr .r4).toNat
abbrev pos : Nat := (s₀.gpr .r5).toNat
abbrev dp : Addr := s₀.gpr .r6
abbrev len : Nat := (s₀.gpr .r7).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 48, 48⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbPPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11⟩, ⟨h6, h7, h8, h9⟩⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  obtain h := Proof.Sha3.rate_bounds hp.rate
  omega_arith

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt

/-! ## Invariants -/

/-- The registers the body never writes. -/
abbrev keep : List Reg := [.r26, .r27, .r28, .r30, .r31] ++ untouched

theorem keepNe {r : Reg} (hr : r ∈ keep) (x : Reg) (hx : x ∉ keep := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem keep_preserved : ∀ r ∈ keep, r ∈ preserved := by decide

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  sp : s.sp = s₀.sp
  r28 : s.gpr .r28 = s₀.gpr .r4
  r30 : s.gpr .r30 = dp s₀ + BitVec.ofNat 64 c
  r31 : s.gpr .r31 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved (scr s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r29 : s.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ keep, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by decide)]; exact h.r26
  r27 := by rw [hg _ (by decide)]; exact h.r27
  sp := hsp.trans h.sp
  r28 := by rw [hg _ (by decide)]; exact h.r28
  r30 := by rw [hg _ (by decide)]; exact h.r30
  r31 := by rw [hg _ (by decide)]; exact h.r31
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩] s.mem s'.mem) : Common s₀ c s' :=
  have hg : ∀ r ∈ keep, s'.gpr r = s.gpr r := fun r hr => hcs r (keep_preserved r hr)
  { c_le := h.c_le
    rd := hrd.trans h.rd
    wr := hwr.trans h.wr
    r26 := by rw [hg _ (by decide)]; exact h.r26
    r27 := by rw [hg _ (by decide)]; exact h.r27
    sp := hsp.trans h.sp
    r28 := by rw [hg _ (by decide)]; exact h.r28
    r30 := by rw [hg _ (by decide)]; exact h.r30
    r31 := by rw [hg _ (by decide)]; exact h.r31
    untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)
    frame := h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩)
    saved := h.saved.permute hp.st_scr hf }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0) := by
  unfold setup
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  obtain hm : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain f₁ : Frame [scR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => ⟨scR s₀, by simp,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩
  obtain hf : Frame [stR s₀, scR s₀] s₀.mem s₁.mem := f₁.mono (by simp)
  obtain oth : ∀ r, r ∉ [Reg.r26, .r27, .r28, .r29, .r30, .r31] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.2.2.2.2.2, u₆.other _ hr.2.2.2.2.1, u₅.other _ hr.2.2.2.1, u₄.other _ hr.2.2.1,
      u₃.other _ hr.2.1, u₂.other _ hr.1, g₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact hf,
      by rw [hm, m₁]; exact saveMem_saved _ _ _, fun r hr => oth r (by revert r; decide)⟩,
    ?_, fun msg ⟨hs, _⟩ => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.sub_zero]
    simp [len]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi

/-! ## One iteration -/

/-- The block of the body: the byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      eval (.zero .d .r9) s' = some (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  obtain hr22 : s.gpr .r29 = BitVec.ofNat 64 j := by rw [hI.r29, hjd]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_arith) (by omega_arith)⟩
  refine wp_lbz (t := .r9) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.r30]; simp)
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  obtain ea : s₂.gpr .r10 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.r26, hr22]; simp
  refine wp_lbz (t := .r11) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_stb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_
  -- The byte stored.
  obtain hv : (s₄.gpr .r9).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  obtain hm₉ : s₉.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 →
      s₉.gpr r = s.gpr r := fun r h9 h10 h11 h23 h22 h24 => by
    rw [u₉.other r h9, u₈.other r h24, u₇.other r h22, u₆.other r h23, g₅.gpr, u₄.other r h9,
      u₃.other r h11, u₂.other r h10, u₁.other r h9]
  obtain h22 : s₉.gpr .r29 = BitVec.ofNat 64 (j + 1) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr22, ← BitVec.ofNat_add]
  obtain h21 : s₉.gpr .r28 = s₀.gpr .r4 := by
    rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, h21, ?_, ?_, ?_, ?_, fun r hr => by
      obtain hne : r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r30 ∧ r ≠ .r29 ∧ r ≠ .r31 :=
        ⟨notU hr _, notU hr _, notU hr _, notU hr _, notU hr _, notU hr _⟩
      rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
      exact hI.untouched r hr⟩, h22, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.state hp.st_scr hf
  · rw [eval_zero, u₉.gpr, ← u₉.other .r29 (by decide),
      ← u₉.other .r28 (by decide), h22, h21, sub_beq_zero (by omega_arith)]
  · refine stateAt_xorByte (by omega_arith) ?_ fun i hi hij => ?_
    · rw [hm₉, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₉, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_arith) hij))]

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega_arith), hv _ (by omega_arith), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [show p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 j) = BitVec.ofNat 64 i - BitVec.ofNat 64 j by
        bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith

/-- The block of the body: the lane of data at `c` XORed into the lane at
position `j`. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0) :
    WP isa (.block absorbWord) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      eval (.zero .d .r9) s' = some (decide ((pos s₀ + c) % rt s₀ + 8 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ⊢
  obtain hj' : j + 8 ≤ rt s₀ := by omega_arith
  obtain hr22 : s.gpr .r29 = BitVec.ofNat 64 j := by rw [hI.r29, hjd]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega_arith) (by omega_arith)⟩
  refine wp_ld (t := .r9) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.r30]; simp)
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  obtain ea : s₂.gpr .r10 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.r26, hr22]; simp
  refine wp_ld (t := .r11) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_std (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => WP.block_nil ?_
  obtain hv : s₄.gpr .r9 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem]
  obtain hm₉ : s₉.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₄.gpr .r9) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₉.mem := by
    rw [hm₉]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 →
      s₉.gpr r = s.gpr r := fun r h9 h10 h11 h23 h22 h24 => by
    rw [u₉.other r h9, u₈.other r h24, u₇.other r h22, u₆.other r h23, g₅.gpr, u₄.other r h9,
      u₃.other r h11, u₂.other r h10, u₁.other r h9]
  obtain h22 : s₉.gpr .r29 = BitVec.ofNat 64 (j + 8) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr22, ← BitVec.ofNat_add]
  obtain h21 : s₉.gpr .r28 = s₀.gpr .r4 := by
    rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, h21, ?_, ?_, ?_, ?_, fun r hr => by
      obtain hne : r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r30 ∧ r ≠ .r29 ∧ r ≠ .r31 :=
        ⟨notU hr _, notU hr _, notU hr _, notU hr _, notU hr _, notU hr _⟩
      rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
      exact hI.untouched r hr⟩, h22, ?_, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.state hp.st_scr hf
  · rw [eval_zero, u₉.gpr, ← u₉.other .r29 (by decide),
      ← u₉.other .r28 (by decide), h22, h21, sub_beq_zero (by omega_arith)]
  · rw [hm₉]
    refine stateAt_write_lane (by omega_arith) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_arith), Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_arith),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega_arith)]

/-- After a lane or a byte of data: what the permutation, if the block is
complete, turns into the invariant. -/
structure After (s₀ : State) (s : State) (c n : Nat) (s' : State) : Prop where
  common : Common s₀ (c + n) s'
  r29 : s'.gpr .r29 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n)
  z : eval (.zero .d .r9) s' = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀))
  st : stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
    (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)

/-- The permutation if the block is complete. -/
theorem after_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State} (hI : Inv s₀ c s) (h : After s₀ s c n s₁) :
    WP isa (.ite (.zero .d .r9) (.seq (.block [.li .r29 0]) permuteAt) (.block [])) s₁
      (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hC := h.common
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_arith) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, h.st, hI.repr msg hm]
  obtain hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    obtain e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega_arith]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) h.z (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_)
    obtain hC₂ := hC.of_gpr (fun r hr => u₂.other r (keepNe hr _)) u₂.mem u₂.rd u₂.wr u₂.sp
    refine permuteAt_ok hC₂.r26 hC₂.r27 (hp.st_scr.sub_right (Region.sub_prefix (by omega_arith)))
      ?_ fun s₃ rd₃ wr₃ sp₃ cs₃ f₃ e₃ => ?_
    · rw [hC₂.wr, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · refine { hC₂.after_call hp rd₃ wr₃ sp₃ cs₃ f₃ with r29 := ?_, repr := fun msg hm => ?_ }
      · rw [cs₃ _ (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC with r29 := ?_, repr := fun msg hm => ?_ }
    · rw [h.r29, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-- The whole body: a lane or a byte of data. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa (absorbBody) s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbBody
  refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => wp_subi (by decide) fun s₅ u₅ =>
    wp_lsr (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => WP.block_nil ?_)
  obtain oth : ∀ r, r ≠ .r10 → r ≠ .r11 → s₇.gpr r = s.gpr r := fun r h10 h11 => by
    rw [u₇.other r h10, u₆.other r h11, u₅.other r h11, u₄.other r h10, u₃.other r h10]
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain hI₇ : Inv s₀ c s₇ :=
    { hI.toCommon.of_gpr (fun r hr => oth r (keepNe hr _) (keepNe hr _)) m₇
        (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr])
        (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp]) with
      r29 := by rw [oth _ (by decide) (by decide)]; exact hI.r29
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  obtain hx10 : s₇.gpr .r10 = 0 → (pos s₀ + c) % rt s₀ % 8 = 0 ∧ 8 ≤ len s₀ - c := fun h0 => by
    rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₃.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hI.r29, hI.r31] at h0
    obtain h0' := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at h0'
    obtain hpos : (pos s₀ + c) % rt s₀ < 2 ^ 64 := by have := (s₀.gpr .r4).isLt; omega_arith
    simp only [show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      Nat.or_eq_zero_iff] at h0'
    obtain hl := len_lt s₀
    omega_arith
  refine WP.seq (WP.mono (Q := fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ After s₀ s₇ c n s₁) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hA⟩ => WP.mono (after_ok hp hn hfit hI₇ hA)
      fun s' h => ⟨c + n, by omega_arith, hcn, h⟩)
  refine WP.ite (s₇.gpr .r10 == 0) (eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hx10 (by simpa using hb)
    exact WP.mono (body_word hp (by omega_arith) hI₇ m8) fun s₁ ⟨hC, h22, hz, hst⟩ =>
      ⟨8, by decide, by omega_arith, by omega_arith, hC, h22, hz, hst⟩
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h22, hz, hst⟩ =>
      ⟨1, by decide, by omega_arith, by omega_arith, hC, h22, hz, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ Proof.Sha3.absorbPPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (mov .r3 .r29 :: restore)) s (Post s₀) := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  refine wp_mov fun s₁ u₁ => ?_
  refine restore_ok (scr := scr s₀) (by rw [u₁.other _ (by decide), hI.r27])
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr],
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    s₀.gpr (by rw [u₁.mem]; exact hI.saved) fun s' hsv other m _ _ sp => ⟨preserved_of hsv fun r hr => ?_,
      by rw [sp, u₁.sp, hI.sp], ⟨fun msg hm hpm => ?_, ?_⟩⟩
  · rw [other r (by revert r; decide), u₁.other r (notU hr _)]
    exact hI.untouched r hr
  · rw [Proof.Sha3.repr_iff, m, u₁.mem]
    exact hI.repr msg ⟨hm, hpm⟩
  · rw [other _ (by decide), u₁.gpr, hI.r29,
      toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

/-! ## The whole function -/

theorem absorb_eq : absorbMain = .seq (.block setup)
    (.seq (.ite (.zero .d .r31) (.block []) (.loop absorbBody (.nonzero .d .r31)))
      (.block (mov .r3 .r29 :: restore))) := rfl

/-- `absorb` without its frame. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) : WP isa absorbMain s₀ (Post s₀) := by
  obtain hl := len_lt s₀
  rw [absorb_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0))
    (by show VG.PPC64LE.eval (.zero .d .r31) s₁ = _
        rw [eval_zero, hI.r31, Nat.sub_zero, ofNat_beq_zero (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega_arith, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hp hcl hI) fun s' ⟨c', hcc, hc', hI'⟩ => ?_
    obtain hz : isa.eval (.nonzero .d .r31) s' = some (decide (len s₀ - c' ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r31) s' = _
      rw [eval_nonzero, hI'.r31, bne, ofNat_beq_zero (by omega_arith)]
      simp
    by_cases he : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
      rwa [show c' = len s₀ by omega_arith] at hI'
    · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega_arith, c', rfl, by omega_arith, hI'⟩

end VG.Proof.Sha3.PPC64LE.Stream.Absorb

end

end

/-! ### `Sha3.PPC64LE.Stream.Pad`, which only this module used -/

section

/-!
# The SHA-3 sponge on PPC64LE: `pad`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Pad`):
`padMain`, whose frame saving the link register `correct` adds
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream.Pad

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Proof.Sha3.PPC64LE VG.Proof.Sha3.PPC64LE.Stream
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_subi wp_li wp_add wp_lbz wp_stb contains_offset)
open VG.Spec.Sha3 (stateAt keccakF absorb pad rates Repr)
open VG.Proof.Sha3 (xorByte Rep stateAt_xorByte absorb_pad)

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev rt : Nat := (s₀.gpr .r4).toNat
abbrev pos : Nat := (s₀.gpr .r5).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 48, 48⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.padPPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨⟨h1, h2, h3, h7, h8⟩, ⟨h4, h5, h6⟩⟩

theorem x80 : (BitVec.ofNat 64 0x80).setWidth 8 = (0x80 : BitVec 8) := by decide

theorem keep_ne : ∀ r ∈ preserved, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r4 := by decide

/-- `pad` without its frame: the callee-saved registers are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa padMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Sha3.padPPC64LE.post s₀ s' := by
  obtain hr : 72 ≤ (s₀.gpr .r4).toNat ∧ (s₀.gpr .r4).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  have hpl : (s₀.gpr .r5).toNat < (s₀.gpr .r4).toNat := hp.pos_lt
  obtain hin : ∀ j < 200, (stR s₀).Contains (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj =>
    contains_offset (by omega_using [hj]) (by omega_using [hj])
  obtain hw : ∀ j < 200, InRegions s₀.wr (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hp.wr]; exact ⟨_, List.mem_cons_self .., hin j hj⟩
  obtain hw' : ∀ j < 200, InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hp.rd]; exact hw j hj
  unfold padMain
  refine WP.seq (wp_add fun s₁ u₁ => ?_)
  obtain e₁ : s₁.gpr .r9 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat) := by
    rw [u₁.gpr]; simp
  refine wp_lbz (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat)) (by omega_using []) e₁
    (by rw [u₁.rd, u₁.wr]; exact hw' _ (by omega_using [hr, hpl])) fun s₂ u₂ => wp_xor fun s₃ u₃ =>
    wp_stb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat)) (by omega_using [])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact e₁)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw _ (by omega_using [hr, hpl])) fun s₄ g₄ => ?_
  obtain k₄ : ∀ r, r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [g₄.gpr, u₃.other _ h', u₂.other _ h', u₁.other _ h]
  refine wp_add fun s₅ u₅ => wp_subi (by decide) fun s₆ u₆ => ?_
  obtain e₆ : s₆.gpr .r9 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1) := by
    rw [u₆.gpr, u₅.gpr, k₄ _ (by decide) (by decide), k₄ _ (by decide) (by decide)]
    simp only [st]
    rw [BitVec.add_zero]; exact Offset.add_sub_one64 _ _ (by omega_using [hr])
  refine wp_lbz (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1)) (by omega_using []) e₆
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, g₄.rd, g₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hw' _ (by omega_using [hr]))
    fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_xor fun s₉ u₉ =>
    wp_stb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1)) (by omega_using [])
      (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide)]; exact e₆)
      (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw _ (by omega_using [hr]))
    fun s₁₀ g₁₀ => wp_mov fun s₁₁ u₁₁ => WP.block_nil ?_
  -- The two bytes written.
  obtain hb₁ : s₄.mem = s₀.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat))
      (s₀.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r5).toNat)) ^^^ (s₀.gpr .r6).setWidth 8) := by
    rw [g₄.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₃.mem, u₂.mem,
      u₁.mem, Proof.Sha3.xor_byte]
  obtain hb₂ : s₁₀.mem = s₄.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1))
      (s₄.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .r4).toNat - 1)) ^^^ 0x80) := by
    rw [g₁₀.mem, u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem,
      u₅.mem, Proof.Sha3.xor_byte, x80]
  obtain hS : stateAt s₁₀.mem (st s₀) =
      xorByte (xorByte (stateAt s₀.mem (st s₀)) ((s₀.gpr .r5).toNat) ((s₀.gpr .r6).setWidth 8)) ((s₀.gpr .r4).toNat - 1) 0x80 := by
    rw [← stateAt_xorByte (m := s₀.mem) (m' := s₄.mem) (by omega_using [hr, hpl])
      (by simp only [hb₁, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₁, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega_using [hr, hpl]) hne, ite_false])]
    exact stateAt_xorByte (by omega_using [hr]) (by simp only [hb₂, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₂, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega_using [hr]) hne, ite_false])
  obtain k₁₁ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r4 → s₁₁.gpr r = s₀.gpr r :=
    fun r h9 h10 h11 h1 => by
      rw [u₁₁.other _ h1, g₁₀.gpr, u₉.other _ h10, u₈.other _ h11, u₇.other _ h10, u₆.other _ h9,
        u₅.other _ h9, k₄ _ h9 h10]
  obtain sp₁₁ : s₁₁.sp = s₀.sp := by
    rw [u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain e512 : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega_using [])
  refine call_ok (st := st s₀) (scr := scr s₀)
    (by rw [k₁₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.st_scr.sub_right e512)
    (by
      rw [u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩)
    fun s' _ _ sp' cs' _ e' => ?_
  refine ⟨fun r hr => ?_, by rw [sp', sp₁₁], fun msg hR hm => ?_⟩
  · have ne := keep_ne r hr
    rw [cs' r hr, k₁₁ r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2]
  · rw [e', u₁₁.mem, hS, absorb_pad (by omega_using [hr]) (by omega_using [hr]), ← hm,
      show Rep ((s₀.gpr .r4).toNat) msg = stateAt s₀.mem (st s₀) from hR.symm]

end VG.Proof.Sha3.PPC64LE.Stream.Pad

end

end

/-! ### `Sha3.PPC64LE.Stream.Squeeze`, which only this module used -/

section

/-!
# The SHA-3 sponge on PPC64LE: `squeeze`

The same structure as the AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Squeeze`):
`squeezeMain`, whose frame saving the link register `correct` adds
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream.Squeeze

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Proof.Sha3.PPC64LE VG.Proof.Sha3.PPC64LE.Stream
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_addi wp_mov wp_subi wp_li wp_add wp_sub wp_and wp_lsr
  wp_lbz wp_stb wp_std wp_ld eval_zero eval_nonzero contains_offset toNat_ofNat_lt)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF ofNat_beq_zero sub_beq_zero sub_ofNat writeW8_self writeW8_other div_mod_eq
  writeW64_byte)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : Addr := s₀.gpr .r3
abbrev rate : Nat := (s₀.gpr .r4).toNat
abbrev pos₀ : Nat := (s₀.gpr .r5).toNat
abbrev outp : Addr := s₀.gpr .r6
abbrev outn : Nat := (s₀.gpr .r7).toNat
abbrev scrp : Addr := s₀.gpr .r8
abbrev SR : Region := ⟨stp s₀, 200⟩
abbrev OR : Region := ⟨outp s₀, outn s₀⟩
abbrev CR : Region := ⟨scrp s₀, 640⟩
/-- The frame saving the link register, below the stack pointer. -/
abbrev KR : Region := ⟨s₀.sp - 48, 48⟩
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stp s₀)

end

structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [SR s₀, OR s₀, CR s₀]
  st_o : (SR s₀).Disjoint (OR s₀)
  st_c : (SR s₀).Disjoint (CR s₀)
  o_c : (OR s₀).Disjoint (CR s₀)
  rate_mem : rate s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rate s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (KR s₀).Disjoint (SR s₀)
  o : (KR s₀).Disjoint (OR s₀)
  c : (KR s₀).Disjoint (CR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezePPC64LE.pre s₀) : SPre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11⟩, ⟨h6, h7, h8, h9⟩⟩

theorem SPre.rate_pos {s₀ : State} (hp : SPre s₀) : 0 < rate s₀ ∧ rate s₀ ≤ 200 := by
  have := Proof.Sha3.rate_bounds hp.rate_mem
  omega_arith

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt

/-- The registers the body never writes but by the call. -/
abbrev keep : List Reg := [.r26, .r27, .r28, .r29, .r30, .r31] ++ untouched

theorem keepNe {r : Reg} (hr : r ∈ keep) (x : Reg) (hx : x ∉ keep := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rate s₀ * k + pos
  pos_le : pos ≤ rate s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = stp s₀
  r27 : s.gpr .r27 = scrp s₀
  r28 : s.gpr .r28 = s₀.gpr .r4
  r29 : s.gpr .r29 = BitVec.ofNat 64 pos
  r30 : s.gpr .r30 = outp s₀ + BitVec.ofNat 64 i
  r31 : s.gpr .r31 = BitVec.ofNat 64 (outn s₀ - i)
  sp : s.sp = s₀.sp
  frame : Frame [SR s₀, OR s₀, CR s₀] s₀.mem s.mem
  saved : Saved (scrp s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  state : stateAt s.mem (stp s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (outp s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rate s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rate s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ keep, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by decide)]; exact h.r26
  r27 := by rw [hg _ (by decide)]; exact h.r27
  r28 := by rw [hg _ (by decide)]; exact h.r28
  r29 := by rw [hg _ (by decide)]; exact h.r29
  r30 := by rw [hg _ (by decide)]; exact h.r30
  r31 := by rw [hg _ (by decide)]; exact h.r31
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  untouched := fun r hr => (hg r (List.mem_append_right _ hr)).trans (h.untouched r hr)
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

theorem prologue_ok {s₀ : State} (hp : SPre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0 0 (pos₀ s₀)) := by
  unfold setup
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨CR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  obtain hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [CR s₀] s₀.mem s.mem := by
    rw [m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => ⟨CR s₀, by simp,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩
  obtain oth : ∀ r, r ∉ [Reg.r26, .r27, .r28, .r29, .r30, .r31] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2.2.2, u₅.other _ hr.2.2.2.2.1, u₄.other _ hr.2.2.2.1, u₃.other _ hr.2.2.1,
      u₂.other _ hr.2.1, u₁.other _ hr.1, g₁]
  refine ⟨Nat.zero_le _, by simp, hp.pos_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hm]; exact hf.mono (by simp), by rw [hm, m₁]; exact saveMem_saved _ _ _,
    fun r hr => oth r (by revert r; decide), ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wr₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₁]; simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₁]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₁]; simp
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, sp₁]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun j hj => hf.bytes (R := SR s₀) (by simpa using hp.st_c) (by simp) hj

/-! ## One iteration -/

theorem permute_ok {s₀ : State} (hp : SPre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rate s₀) s) :
    WP isa (.seq (.block [.li .r29 0]) permuteAt) s (Inv s₀ i (k + 1) 0) := by
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain e200 : Region.Sub ⟨stp s₀, 200⟩ (SR s₀) := fun _ h => h
  obtain e512 : Region.Sub ⟨scrp s₀, 512⟩ (CR s₀) := Region.sub_prefix (by omega_arith)
  refine permuteAt_ok (st := stp s₀) (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.r26])
    (by rw [u₁.other _ (by decide), hI.r27]) (hp.st_c.sub_right e512) ?_
    fun s' rd' wr' sp' cs' hf hst => ?_
  · rw [u₁.wr, hI.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨SR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨CR s₀, by simp, 0, by simp, by simp⟩
  have cs : ∀ r ∈ preserved, s'.gpr r = s₁.gpr r := cs'
  obtain hd : ∀ r ∈ [(⟨stp s₀, 200⟩ : Region), ⟨scrp s₀, 512⟩], (OR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_c.sub_right e512
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans (u₁.wr.trans hI.wr), ?_, ?_, ?_, ?_, ?_, ?_, by rw [sp', u₁.sp, hI.sp], ?_, ?_, (fun r hr => by
      rw [cs r (untouched_preserved r hr), u₁.other r (notU hr _)]
      exact hI.untouched r hr), ?_,
    fun j hj => ?_⟩
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r26]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r27]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r28]
  · rw [cs _ (by decide), u₁.gpr]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r30]
  · rw [cs _ (by decide), u₁.other _ (by decide), hI.r31]
  · have hfs : Frame [SR s₀, OR s₀, CR s₀] s₁.mem s'.mem := by
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨SR s₀, by simp, e200⟩
      · exact ⟨CR s₀, by simp, e512⟩
    rw [u₁.mem] at hfs
    exact hI.frame.trans hfs
  · exact Saved.permute (by rw [u₁.mem]; exact hI.saved) hp.st_c hf
  · rw [hst, u₁.mem, hI.state, iterF_succ]
  · refine Eq.trans (hf.bytes (R := OR s₀) hd (Nat.le_of_lt (outn_lt s₀)) (by have := hI.i_le; omega_arith : j < outn s₀)) ?_
    rw [u₁.mem]; exact hI.out j hj

theorem store_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rate s₀) (hi : i < outn s₀) :
    WP isa (.block squeezeByte) s (Inv s₀ (i + 1) k (pos + 1)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_lbz (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.r26, hI.r29]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₂ u₂ => ?_
  refine wp_stb (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.r30]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r10 → r ≠ .r9 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  obtain hb : s.mem (stp s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, byteOf_stateAt _ _ (by omega_arith)]
  obtain hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by omega_arith),
      BitVec.setWidth_eq, hb]
  obtain hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  refine ⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      rw [g r (notU hr _) (notU hr _) (notU hr _) (notU hr _) (notU hr _)]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · exact hI.saved.disjoint hp.o_c hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) e)]
      exact hI.out j (by omega_arith)

/-- Every rate is a whole number of lanes. -/
theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem store8_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos + 8 ≤ rate s₀) (hi : i + 8 ≤ outn s₀) :
    WP isa (.block squeezeWord) s (Inv s₀ (i + 8) k (pos + 8)) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  obtain hn := outn_lt s₀
  refine wp_add fun s₁ u₁ => ?_
  refine wp_ld (a := stp s₀ + BitVec.ofNat 64 pos) (by decide) (by rw [u₁.gpr, hI.r26, hI.r29]; simp)
    ⟨SR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₂ u₂ => ?_
  refine wp_std (a := outp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.r30]; simp)
    (by rw [u₂.wr, u₁.wr, hI.wr, hp.wr]; exact ⟨OR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r10 → r ≠ .r9 → r ≠ .r30 → r ≠ .r29 → r ≠ .r31 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  obtain hm : s₆.mem = s.mem.writeW (outp s₀ + BitVec.ofNat 64 i) (s.mem.readW (stp s₀ + BitVec.ofNat 64 pos) 64) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₂.mem, u₁.mem]
  obtain hfw : Frame [OR s₀] s.mem s₆.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega_arith) (by omega_arith))
  refine ⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.frame.trans (hfw.mono (by simp)), ?_, (fun r hr => by
      rw [g r (notU hr _) (notU hr _) (notU hr _) (notU hr _) (notU hr _)]
      exact hI.untouched r hr), ?_, fun j hj => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27]
  · rw [g .r28 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r28]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, ← BitVec.ofNat_add]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r30, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r31, sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, hI.sp]
  · exact hI.saved.disjoint hp.o_c hfw
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfw.bytes (R := SR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hm]
    by_cases e : i ≤ j
    · rw [show outp s₀ + BitVec.ofNat 64 j = outp s₀ + BitVec.ofNat 64 i + BitVec.ofNat 64 (j - i) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' e],
        writeW64_byte _ _ _ (by omega_arith), Mem.readW, BitVec.setWidth_eq,
        Mem.extractLsb'_read s.mem (stp s₀ + BitVec.ofNat 64 pos) (n := 64 / 8) (show j - i < 64 / 8 by omega_arith),
        BitVec.add_assoc, ← BitVec.ofNat_add,
        ← byteOf_stateAt s.mem (stp s₀) (show pos + (j - i) < 200 by omega_arith), hI.state]
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr0 (show pos + (j - i) < rate s₀ by omega_arith)
      rw [show pos₀ s₀ + j = rate s₀ * k + (pos + (j - i)) by have := hI.hi; omega_arith, d, m]
    · rw [Mem.writeW, Mem.write_apply (by
        rw [show outp s₀ + BitVec.ofNat 64 j - (outp s₀ + BitVec.ofNat 64 i) =
          BitVec.ofNat 64 (2 ^ 64 - (i - j)) by bv_omega, BitVec.toNat_ofNat]
        omega_arith)]
      exact hI.out j (by omega_arith)

theorem body_ok {s₀ : State} (hp : SPre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa (squeezeBody) s fun s' => ∃ i' k' pos', i < i' ∧ i' ≤ outn s₀ ∧ Inv s₀ i' k' pos' s' := by
  have ⟨hr0, _⟩ := hp.rate_pos
  obtain h8 := rate_mod8 hp.rate_mem
  unfold squeezeBody
  refine WP.seq (wp_sub fun s₁ u₁ => WP.block_nil ?_)
  obtain hI₁ := hI.congr (fun r hr => u₁.other r (keepNe hr _)) u₁.mem u₁.rd u₁.wr u₁.sp
  obtain hz : eval (.zero .d .r9) s₁ = some (decide (pos = rate s₀)) := by
    rw [eval_zero, u₁.gpr, hI.r29, hI.r28,
      sub_beq_zero (by have := hI.pos_le; have := (s₀.gpr .r4).isLt; omega_arith)]
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rate s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => ?_)
  · refine WP.ite (decide (pos = rate s₀)) hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      subst hb
      exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr0⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact WP.block_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega_arith⟩
  -- a lane or a byte
  refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => wp_subi (by decide) fun s₅ u₅ =>
    wp_lsr (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => WP.block_nil ?_)
  obtain hI₇ := hI₂.congr (fun r hr => by
    rw [u₇.other r (keepNe hr _), u₆.other r (keepNe hr _), u₅.other r (keepNe hr _),
      u₄.other r (keepNe hr _), u₃.other r (keepNe hr _)])
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]) (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]) (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp])
  obtain hx10 : s₇.gpr .r10 = 0 → pos' % 8 = 0 ∧ 8 ≤ outn s₀ - i := fun h0 => by
    rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₃.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hI₂.r29, hI₂.r31] at h0
    obtain h0' := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at h0'
    obtain hpos : pos' < 2 ^ 64 := by have := hI₂.pos_le; have := (s₀.gpr .r4).isLt; omega_arith
    simp only [show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
      Nat.or_eq_zero_iff] at h0'
    obtain hn := outn_lt s₀
    omega_arith
  refine WP.ite (s₇.gpr .r10 == 0) (eval_zero _ _) (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, l8⟩ := hx10 (by simpa using hb)
    exact WP.mono (store8_ok hp hI₇ (by have := hI₇.pos_le; omega_arith) (by omega_arith))
      fun s' h => ⟨i + 8, k', pos' + 8, by omega_arith, by omega_arith, h⟩
  · exact WP.mono (store_ok hp hI₇ hlt hi) fun s' h => ⟨i + 1, k', pos' + 1, by omega_arith, by omega_arith, h⟩

/-! ## The epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ Proof.Sha3.squeezePPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : SPre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block (mov .r3 .r29 :: restore)) s (Post s₀) := by
  have ⟨hr0, hr200⟩ := hp.rate_pos
  have hpl := hI.pos_le
  refine wp_mov fun s₁ u₁ => ?_
  obtain hx0 : s₁.gpr .r3 = BitVec.ofNat 64 pos := by rw [u₁.gpr, hI.r29]
  refine restore_ok (scr := scrp s₀) (by rw [u₁.other _ (by decide), hI.r27])
    (fun d hd₁ hd₂ => ⟨CR s₀, by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr],
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    s₀.gpr (by rw [u₁.mem]; exact hI.saved) fun s' hsv other m _ _ sp => ⟨preserved_of hsv fun r hr => ?_,
      by rw [sp, u₁.sp, hI.sp], ⟨?_, ?_, fun d => ?_⟩⟩
  · rw [other r (by revert r; decide), u₁.other r (notU hr _)]
    exact hI.untouched r hr
  · have ax : s'.gpr .r3 = s₁.gpr .r3 := other _ (by decide)
    show bytesAt s'.mem (outp s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [m, u₁.mem]
    refine List.ext_getElem (by rw [length_squeezeFrom hr0 hr200]; simp [bytesAt]) fun j h₁ _ => ?_
    obtain hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr0 hr200 _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · rw [other _ (by decide), hx0, toNat_ofNat_lt (by omega_arith)]; exact hI.pos_le
  · show Spec.Sha3.squeezeFrom (rate s₀) (stateAt s'.mem (stp s₀)) (s'.gpr .r3).toNat d =
      Spec.Sha3.squeezeFrom (rate s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [m, u₁.mem, hI.state, other _ (by decide), hx0, toNat_ofNat_lt (by have := hI.pos_le; omega_arith),
      squeezeFrom_iterF hr0 hr200, ← hI.hi]

/-! ## The whole function -/

theorem squeeze_eq : squeezeMain = .seq (.block setup)
    (.seq (.ite (.zero .d .r31) (.block []) (.loop squeezeBody (.nonzero .d .r31)))
      (.block (mov .r3 .r29 :: restore))) := rfl

/-- `squeeze` without its frame. -/
theorem correctMain {s₀ : State} (hp : SPre s₀) : WP isa squeezeMain s₀ (Post s₀) := by
  obtain hn := outn_lt s₀
  rw [squeeze_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0))
    (by show VG.PPC64LE.eval (.zero .d .r31) s₁ = _
        rw [eval_zero, hI.r31, Nat.sub_zero, ofNat_beq_zero (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s)
      ?_ (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega_arith, by omega_arith, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨i', k', pos', hii, hi', hI'⟩ => ?_
    obtain hz : isa.eval (.nonzero .d .r31) s' = some (decide (outn s₀ - i' ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r31) s' = _
      rw [eval_nonzero, hI'.r31, bne, ofNat_beq_zero (by omega_arith)]
      simp
    by_cases hl : outn s₀ - i' = 0
    · exact .inl ⟨by rw [hz]; simp [hl], k', pos', by rwa [show i' = outn s₀ by omega_arith] at hI'⟩
    · exact .inr ⟨by rw [hz]; simp [hl], _, by omega_arith, i', k', pos', rfl, by omega_arith, hI'⟩

end VG.Proof.Sha3.PPC64LE.Stream.Squeeze

end

end


/-!
# The SHA-3 sponge on PPC64LE: `Verified`

`absorb`, `pad` and `squeeze` (`Stream/`), each run in a frame that saves the
link register (`WP.frameReg`): correctness, with constant time from `CT`, and
a state satisfying each precondition. They take their working space as an
argument; `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` run
them in a frame that allocates it (`Verified.stackScratch`): 640 bytes,
after the frame's 32-byte header.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.MdStream.PPC64LE (frame_sub write_frame_bytes WP.cons)

/-- The state a function's main part starts in: the link register moved to
`r0`, then pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem inner_gpr (s₀ : State) {r : Reg} (h : r ≠ .r0) : (inner s₀).gpr r = s₀.gpr r := by
  simp [framed, State.write, h]

/-- The bytes of a region disjoint from the frame are those before it. -/
theorem inner_bytes {s₀ : State} {R : Region} (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ R)
    (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    (inner s₀).mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) :=
  write_frame_bytes (v := s₀.lr) hd hR hi

theorem inner_state {s₀ : State} {p : Addr} (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, 200⟩) :
    stateAt (inner s₀).mem p = stateAt s₀.mem p :=
  Proof.Sha3.stateAt_congr fun _ hi => inner_bytes (R := ⟨p, 200⟩) hd (show 200 < 2 ^ 64 by decide) hi

theorem inner_bytesAt {s₀ : State} {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, n⟩)
    (hn : n < 2 ^ 64) : bytesAt (inner s₀).mem p n = bytesAt s₀.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => inner_bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The state at `p`, apart from the frame, is what it was once the frame's
bytes are lost. -/
theorem lost_state {s₀ : State} {m m' : Mem} {p : Addr} (f : Frame [⟨s₀.sp - 48, 48⟩] m m')
    (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, 200⟩) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hi => f.bytes (R := ⟨p, 200⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.symm) (show 200 ≤ 2 ^ 64 by decide) hi

/-- So are the `n` bytes at `p`. -/
theorem lost_bytesAt {s₀ : State} {m m' : Mem} {p : Addr} {n : Nat} (f : Frame [⟨s₀.sp - 48, 48⟩] m m')
    (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, n⟩) (hn : n < 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => f.bytes (R := ⟨p, n⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd.symm) (show n ≤ 2 ^ 64 by omega_using [hn]) (List.mem_range.mp hi)

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem pushFrames_of_noFrames {c : Prog isa} (h : c.noFrames = true) : pushFrames c = true := by
  induction c <;> simp_all [Code.noFrames, pushFrames]

/-- The epilogue of the frame: the link register is restored from `r0`, and
the callee-saved registers and the stack pointer are the caller's. -/
theorem withLr_ok {main : Prog isa} {s₀ : State} {Q : State → State → Prop}
    (hsp : 48 ≤ s₀.sp.toNat)
    (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 48, 48⟩ R)
    (hmain : WP isa main (inner s₀) fun s' =>
      (∀ r ∈ preserved, s'.gpr r = (inner s₀).gpr r) ∧ s'.sp = (inner s₀).sp ∧ Q (inner s₀) s')
    (hQ : ∀ s' s'', Frame [⟨s₀.sp - 48, 48⟩] s'.mem s''.mem → s''.gpr .r3 = s'.gpr .r3 →
      Q (inner s₀) s' → Q s₀ s'')
    (hn : main.noFrames = true) :
    WP isa (Impl.Sha3.PPC64LE.Stream.withLr main) s₀ fun s' => abiPreserved s₀ s' ∧ Q s₀ s' := by
  unfold Impl.Sha3.PPC64LE.Stream.withLr
  refine WP.seq (MdStream.PPC64LE.WP.cons PPC64LE.exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by exact hsp) (fun R hR => (hd R hR).sub_left (frame_sub _))
    (WP.mono hmain fun s' ⟨hk, _, hq⟩ m u f => ?_)
    (by rw [fdepth_of_noFrames hn]; decide) (pushFrames_of_noFrames hn)
  refine MdStream.PPC64LE.WP.cons PPC64LE.exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, hQ s' _ f rfl hq⟩)
  · have h0 : r ≠ .r0 := by revert r hr; decide
    simp only [State.write, h0, ite_false]
    rw [hk r hr]
    simp only [framed, State.write, h0, ite_false]
  · simp [State.write]

/-! ## `absorb` -/

theorem absorbMain_noFrames : Impl.Sha3.PPC64LE.Stream.absorbMain.noFrames = true := by lit_decide

theorem absorb_correct (s : State) (hs : Proof.Sha3.absorbPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.Stream.absorb s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.absorbPPC64LE.post s s' := by
  obtain ⟨hp, hk⟩ := Absorb.pre_of hs
  obtain hpi : Absorb.Pre (inner s) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr, hp.rate, hp.pos_lt⟩
  refine withLr_ok (Q := fun s₀ s' => Proof.Sha3.absorbPPC64LE.post s₀ s') hk.sp48
    (fun R hR => ?_) (WP.mono (Absorb.correctMain hpi) fun s' ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)
    (fun s' s'' hm h3 ⟨h₁, h₂⟩ => ⟨fun msg hR hpm => ?_, by rw [h3]; simpa (disch := decide) only [inner_gpr] using h₂⟩) absorbMain_noFrames
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [hk.st, hk.scr]
  · simp (disch := decide) only [inner_gpr] at h₁
    obtain e := h₁ msg (by rw [Proof.Sha3.repr_iff, inner_state hk.st]; exact hR) hpm
    rw [Proof.Sha3.repr_iff, lost_state hm hk.st]
    rw [Proof.Sha3.repr_iff, inner_bytesAt hk.d (s.gpr .r7).isLt] at e
    exact e

/-- A state satisfying `absorb`'s precondition, with no data. -/
def absorbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 72 | .r6 => 0x2000 | .r8 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

/-! ## `pad` -/

theorem padMain_noFrames : Impl.Sha3.PPC64LE.Stream.padMain.noFrames = true := by lit_decide

theorem pad_correct (s : State) (hs : Proof.Sha3.padPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.Stream.pad s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.padPPC64LE.post s s' := by
  obtain ⟨hp, hk⟩ := Pad.pre_of hs
  obtain hpi : Pad.Pre (inner s) := ⟨hp.rd, hp.wr, hp.st_scr, hp.rate, hp.pos_lt⟩
  refine withLr_ok (Q := fun s₀ s' => Proof.Sha3.padPPC64LE.post s₀ s') hk.sp48
    (fun R hR => ?_) (WP.mono (Pad.correctMain hpi) fun s' ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)
    (fun s' s'' hm _ h₁ msg hR hpm => ?_) padMain_noFrames
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [hk.st, hk.scr]
  · simp (disch := decide) only [Proof.Sha3.padPPC64LE, inner_gpr] at h₁
    rw [lost_state hm hk.st]
    exact h₁ msg (by rw [Proof.Sha3.repr_iff, inner_state hk.st]; exact hR) hpm

/-- A state satisfying `pad`'s precondition. -/
def padSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 136 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

/-! ## `squeeze` -/

theorem squeezeMain_noFrames : Impl.Sha3.PPC64LE.Stream.squeezeMain.noFrames = true := by lit_decide

theorem squeeze_correct (s : State) (hs : Proof.Sha3.squeezePPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.Stream.squeeze s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.squeezePPC64LE.post s s' := by
  obtain ⟨hp, hk⟩ := Squeeze.pre_of hs
  obtain hpi : Squeeze.SPre (inner s) :=
    ⟨hp.rd, hp.wr, hp.st_o, hp.st_c, hp.o_c, hp.rate_mem, hp.pos_le⟩
  refine withLr_ok (Q := fun s₀ s' => Proof.Sha3.squeezePPC64LE.post s₀ s') hk.sp48
    (fun R hR => ?_) (WP.mono (Squeeze.correctMain hpi) fun s' ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)
    (fun s' s'' hm h3 h => ?_) squeezeMain_noFrames
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    exacts [hk.st, hk.o, hk.c]
  · simp (disch := decide) only [Proof.Sha3.squeezePPC64LE, inner_gpr] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    rw [inner_state hk.st] at h₁ h₃
    refine ⟨by rw [lost_bytesAt hm hk.o (s.gpr .r7).isLt]; exact h₁, by rw [h3]; exact h₂, fun d => ?_⟩
    rw [lost_state hm hk.st, h3]
    exact h₃ d

/-- A state satisfying `squeeze`'s precondition, with no output. -/
def squeezeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 72 | .r6 => 0x2000 | .r8 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x3000, 640⟩]

end VG.Proof.Sha3.PPC64LE.Stream
