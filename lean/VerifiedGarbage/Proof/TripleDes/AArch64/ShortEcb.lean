module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Short
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.AArch64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Short
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit

/-!
# Triple DES-ECB on AArch64: a few blocks through the table block

`ecb_wp`: `Short.ecb d` is ECB, by the loop invariant `Inv` over the table
block (`enc_ok`, `dec_ok`, `Proof/CmacTripleDes/AArch64/Block.lean`).
`ecbOf_verified`: `Short.ecbOf d`, which runs it for fewer than eleven blocks
and the bitsliced batch otherwise, meets the batch's contract, whichever
`few` runs (`few_wp`), and is constant time by the taint analysis of the
whole function.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.Short
materialize_code ecbEncrypt
materialize_code ecbDecrypt
end VG.Impl.TripleDes.AArch64.Short

namespace VG.Proof.TripleDes.AArch64.Short

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.CmacTripleDes.AArch64 (mov prep enc dec savedReg)
open VG.Impl.TripleDes.AArch64.Short
open VG.Proof.CmacTripleDes VG.Proof.CmacTripleDes.AArch64
open VG.Spec.TripleDes (Direction blockAt)
open VG.Proof.TripleDes.Bitslice (blockOut wAt)

abbrev W (s : State) : Addr := s.gpr .x0
abbrev D (s : State) : Addr := s.gpr .x1
abbrev N (s : State) : Nat := (s.gpr .x2).toNat
abbrev S (s : State) : Addr := s.gpr .x3
abbrev keyR (s : State) : Region := ⟨W s, 384⟩
abbrev dataR (s : State) : Region := ⟨D s, 8 * N s⟩
abbrev scrR (s : State) : Region := ⟨S s, 1024⟩
abbrev changes (s : State) : List Region := [dataR s, ⟨S s, 456⟩]
abbrev K (s : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s.mem (W s)

/-- The bitsliced functions' precondition. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [keyR s]
  wr : s.wr = [dataR s, scrR s]
  key_data : (keyR s).Disjoint (dataR s)
  key_scr : (keyR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  data_fit : (D s).toNat + 8 * N s ≤ 2 ^ 64

structure Inv (d : Direction) (s₀ : State) (k : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = W s₀
  x15 : s.gpr .x15 = S s₀
  x1 : s.gpr .x1 = D s₀ + BitVec.ofNat 64 (8 * k)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (changes s₀) s₀.mem s.mem
  consts : Consts s
  masks : Masks s
  keys : ∀ i < 48, s.mem.readW (S s₀ + BitVec.ofNat 64 (8 * i)) 64 = spread ((K s₀).getD i 0)
  slots : VG.AArch64.Spill.Saved (S s₀) s₀.gpr saveSlots s.mem
  data : ∀ j < N s₀, blockAt s.mem (wAt (D s₀) j) =
    if j < k then blockOut (K s₀) d (blockAt s₀.mem (wAt (D s₀) j)) else blockAt s₀.mem (wAt (D s₀) j)

section
variable {s₀ : State}

theorem scr_sub {d n : Nat} (h : d + n ≤ 1024) :
    Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

theorem data_sub {j : Nat} (hj : j < N s₀) :
    Region.Sub ⟨wAt (D s₀) j, 8⟩ (dataR s₀) := Offset.sub_base _ (by omega_using [hj])

theorem sched_frame (hp : Pre s₀) {m : Mem} (hf : Frame (changes s₀) s₀.mem m) :
    Spec.TripleDes.scheduleAt m (W s₀) = K s₀ :=
  scheduleAt_frame hf fun r hr => by
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.key_data
    · exact hp.key_scr.sub_right (Region.sub_prefix (by decide))

theorem block_pre (hp : Pre s₀) {s : State} (h14 : s.gpr .x14 = W s₀) (h15 : s.gpr .x15 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨keyR s₀, by rw [hrd, hwr, hp.rd]; simp, by rw [h14], by show 384 ≤ 384; decide,
    by show 384 < 2 ^ 64; decide⟩
  scr := ⟨scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 456 ≤ 1024; decide,
    by show 1024 < 2 ^ 64; decide⟩
  disj := by rw [h14, h15]; exact hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-- The block at `x1` into `x5`, as the integer the table block takes. -/
theorem load_ok (s : State) {q : Addr} (hq : s.gpr .x1 = q) (rq : InRegions (s.rd ++ s.wr) q 8) :
    ∃ s', runBlock isa load s = some s' ∧
      s'.gpr .x5 = Spec.TripleDes.decodeBlock (blockAt s.mem q) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  have rq' : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, hq]; exact rq
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 0) 64)
  let s₂ := s₁.write .x .x5 (rev64 (s₁.read .x .x5))
  refine ⟨s₂, by
    rw [load, runBlock_cons, exec_ldr_x (by decide) rq', runStep_some, runBlock_cons, exec_rev,
      runStep_some, runBlock_nil], ?_, fun r h => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [s₂, s₁, State.read, gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, hq]
    exact (decodeBlock_readW s.mem q).symm
  · simp only [s₂, s₁, gpr_write_of_ne _ _ _ h]

/-- `x5` to the block at `x1`, and on to the next. -/
theorem store_ok (s : State) {q : Addr} (hq : s.gpr .x1 = q) (wq : InRegions s.wr q 8) :
    ∃ s', runBlock isa store s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + 8 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ∉ [Reg.x1, .x2, .x5] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW q (rev64 (s.gpr .x5)) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  have wq' : InRegions s₁.wr (s₁.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide), hq]; exact wq
  refine ⟨_, by
    rw [store, runBlock_cons, exec_rev, runStep_some, runBlock_cons,
      exec_str_x (by decide) wq', runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [s₁, gpr_write, State.read]
  · simp [s₁, gpr_write, State.read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₁, gpr_write, hr.1, hr.2.1, hr.2.2]
  · simp only [s₁, mem_write, State.read, gpr_write, BitVec.setWidth_eq, hq, BitVec.add_zero,
      reduceCtorEq, ↓reduceIte]

/-- The table block of the direction `d`. -/
theorem crypt_wp (d : Direction) {s₀ : State} (hp : BlockPre s₀) {s : State} (h : TInv s₀ s) :
    WP isa (crypt d) s fun s' =>
      Same s₀ s' ∧ s'.gpr .x14 = s₀.gpr .x14 ∧
      (∀ b, s₀.gpr .x5 = Spec.TripleDes.decodeBlock b →
        Spec.TripleDes.encodeBlock (s'.gpr .x5) = blockOut (sch s₀) d b) ∧
      Consts s' ∧ Masks s' ∧ Keys s₀ s'.mem 48 := by
  cases d
  · exact WP.mono (enc_ok hp h) fun s' ⟨a, b, c, e⟩ => ⟨a, b, fun _ hb => by rw [c, hb]; rfl, e⟩
  · exact WP.mono (dec_ok hp h) fun s' ⟨a, b, c, e⟩ => ⟨a, b, fun _ hb => by rw [c, hb]; rfl, e⟩

theorem load_v : load.all (fun i => vdstOf i == none) = true := by decide

/-- One block, after the setup the blocks share. -/
theorem body_ok (d : Direction) {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv d s₀ k s) :
    WP isa (.seq (.block load) (.seq (crypt d) (.block store))) s (Inv d s₀ (k + 1)) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
  have hdw := hp.data_fit
  have rdwr : s.rd ++ s.wr = [keyR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inData : (dataR s₀).Contains (wAt (D s₀) k) 8 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hdw])
  obtain ⟨s₁, run₁, ax₁, keep₁, sp₁, mem₁, rd₁, wr₁, vec₁⟩ := load_ok s h.x1
    (by rw [rdwr]; exact in_rw (r := dataR s₀) (by simp) inData)
  have x14₁ : s₁.gpr .x14 = W s₀ := by rw [keep₁ _ (by decide), h.x14]
  have x15₁ : s₁.gpr .x15 = S s₀ := by rw [keep₁ _ (by decide), h.x15]
  have bp : BlockPre s₁ := block_pre hp x14₁ x15₁ (rd₁.trans h.rd) (wr₁.trans h.wr)
  have sch₁ : sch s₁ = K s₀ := by rw [sch, x14₁, mem₁]; exact sched_frame hp h.frame
  have ready : TInv s₁ s₁ := ⟨Same.refl _, rfl, rfl, h.consts.congr (fun w _ _ _ _ => by rw [vec₁]),
    h.masks.congr (fun p hp' => keep₁ _ (maskRegs_ne p hp').1),
    fun i hi => by rw [x15₁, sch₁, mem₁]; exact h.keys i hi⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (crypt_wp d bp ready) fun s₂ ⟨same₂, x14₂, ax₂, const₂, mask₂, keys₂⟩ => ?_)
  have fr₂ : Frame [⟨S s₀, 384⟩] s.mem s₂.mem := by rw [← mem₁, ← x15₁]; exact same₂.frame
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  have x1₂ : s₂.gpr .x1 = wAt (D s₀) k := by
    rw [same₂.keep .x1 (by simp [outer]), keep₁ _ (by decide), h.x1]
  obtain ⟨s₃, run₃, x1₃, x2₃, keep₃, mem₃, sp₃, rd₃, wr₃, vec₃⟩ := store_ok s₂ x1₂
    (by rw [wr₂]; exact in_rw (r := dataR s₀) (by simp) inData)
  have vals₂ : ∀ j < N s₀, blockAt s₂.mem (wAt (D s₀) j) =
      if j < k then blockOut (K s₀) d (blockAt s₀.mem (wAt (D s₀) j))
      else blockAt s₀.mem (wAt (D s₀) j) := by
    intro j hj
    rw [VG.Proof.TripleDes.Bitslice.blockAt_frame fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hp.data_scr.sub_left (data_sub hj)).sub_right (Region.sub_prefix (by decide)))]
    exact h.data j hj
  have value : Spec.TripleDes.encodeBlock (s₂.gpr .x5) =
      blockOut (K s₀) d (blockAt s₀.mem (wAt (D s₀) k)) := by
    have e := ax₂ (blockAt s.mem (wAt (D s₀) k)) ax₁
    rw [sch₁, h.data k hk, ite_eq_right (Nat.lt_irrefl _)] at e
    exact e
  have fStore : Frame [⟨wAt (D s₀) k, 8⟩] s₂.mem s₃.mem := by
    rw [mem₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have stD : ∀ {o n : Nat}, o + n ≤ 1024 → ∀ r ∈ [(⟨wAt (D s₀) k, 8⟩ : Region)],
      (⟨S s₀ + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
    intro o n hon r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((hp.data_scr.sub_left (data_sub hk)).sub_right (scr_sub hon)).symm
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [keep₃ _ (by decide), x14₂, x14₁]
  · rw [keep₃ _ (by decide), same₂.x15, x15₁]
  · rw [x1₃, x1₂]
    exact x2_succ _ _
  · rw [x2₃, same₂.keep .x2 (by simp [outer]), keep₁ _ (by decide), h.x2,
      ofNat_sub_one (by omega_using [hk]) (by omega_using [hN])]
    congr 1
  · rw [sp₃, same₂.sp, sp₁, h.sp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · exact (h.frame.trans (fr₂.sub (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨S s₀, 456⟩, by simp [changes], Region.sub_prefix (by decide)⟩))).trans
        (fStore.sub (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact ⟨dataR s₀, by simp [changes], data_sub hk⟩))
  · exact const₂.congr (fun w _ _ _ _ => by rw [vec₃])
  · exact mask₂.congr (fun p hp' => keep₃ _ (by
      obtain ⟨n5, -, -, -, -, -, -, -, -, n1, n2, -, -⟩ := maskRegs_ne p hp'
      simp [n1, n2, n5]))
  · intro i hi
    rw [fStore.readW (Region.contains_self _ _) (stD (by omega_using [hi])) (by decide)]
    have e := keys₂ i hi
    rw [x15₁, sch₁] at e
    exact e
  · exact (h.slots.frame_in (lo := 384) (n := 72) saveSlots_facts.1 fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint_base _ (by decide) (by decide))).frame fStore
        (fun q hq => stD (by have := saveSlots_facts.1 q hq; omega_using [this]))
  · intro j hj
    by_cases he : j = k
    · subst j
      rw [mem₃, blockAt_writeW, value, ite_eq_left (by omega_using [])]
    · rw [VG.Proof.TripleDes.Bitslice.blockAt_frame fStore (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint (D s₀) (by omega_using [he]) (by omega_using [hdw, hj])
          (by omega_using [hk, hdw])), vals₂ j hj]
      by_cases hlt : j < k
      · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_using [he, hlt])]

/-- The loop over the blocks. -/
theorem loop_ok (d : Direction) {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv d s₀ k s) :
    WP isa (.loop (.seq (.block load) (.seq (crypt d) (.block store))) (.nonzero .x .x2)) s
      (Inv d s₀ (N s₀)) := by
  refine WP.loop (M := isa) (c := .nonzero .x .x2) (Q := Inv d s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ Inv d s₀ j t) ?_ (N s₀ - k) s
      ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok d hp hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
  have ev := eval_nonzero (r := .x2) (x := N s₀ - (k + 1)) (by omega_using [hN]) h'.x2
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    exact ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl,
      by omega_using [hz], h'⟩

/-- What the ECB functions leave. -/
def Result (d : Direction) (s₀ s : State) : Prop :=
  Spec.TripleDes.blocksAt s.mem (D s₀) (N s₀) =
    Spec.TripleDes.ecb (K s₀) d (Spec.TripleDes.blocksAt s₀.mem (D s₀) (N s₀))

/-- ECB over the table block, keeping the registers the block saves. -/
theorem ecb_wp (d : Direction) {s₀ : State} (hp : Pre s₀) :
    WP isa (ecb d) s₀ fun s => Result d s₀ s ∧ ∀ i < 9, s.gpr (savedReg i) = s₀.gpr (savedReg i) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
  let s₁ := (s₀.write .x .x14 (s₀.gpr .x0)).write .x .x15 ((s₀.write .x .x14 (s₀.gpr .x0)).gpr .x3)
  have g₁ : ∀ r, r ≠ .x14 → r ≠ .x15 → s₁.gpr r = s₀.gpr r := fun r h14 h15 => by
    simp only [s₁, gpr_write_of_ne _ _ _ h15, gpr_write_of_ne _ _ _ h14]
  have x14₁ : s₁.gpr .x14 = W s₀ := by simp [s₁, gpr_write]
  have x15₁ : s₁.gpr .x15 = S s₀ := by simp [s₁, gpr_write]
  change WP isa (.seq _ _) _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_nil], ?_⟩)
  have ev := eval_zero (r := .x2) (x := N s₀) hN (by
    rw [g₁ _ (by decide) (by decide)]; simp [N])
  have savedNe : ∀ i < 9, savedReg i ≠ .x14 ∧ savedReg i ≠ .x15 := by decide
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ⟨?_, fun i hi => ?_⟩)
      (fun h => by cases h)
    · simp [Result, hn, Spec.TripleDes.blocksAt, Spec.TripleDes.ecb]
    · exact g₁ _ (savedNe i hi).1 (savedNe i hi).2
  refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
  have bp : BlockPre s₁ := block_pre hp x14₁ x15₁ rfl rfl
  apply WP.seq
  refine WP.mono (prep_ok bp) fun s₂ h₂ => ?_
  have outer₂ : ∀ r ∈ outer, s₂.gpr r = s₀.gpr r := by
    intro r hr
    rw [h₂.same.keep r hr]
    simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  have hS : sch s₁ = K s₀ := by rw [sch, x14₁]; rfl
  have inv₂ : Inv d s₀ 0 s₂ := by
    refine ⟨by rw [h₂.x14, x14₁], by rw [h₂.same.x15, x15₁],
      by rw [outer₂ .x1 (by simp [outer])]; exact (BitVec.add_zero _).symm,
      by rw [outer₂ .x2 (by simp [outer])]; simp [N],
      h₂.same.sp, h₂.same.rd, h₂.same.wr, ?_, h₂.consts, h₂.masks, ?_, ?_, ?_⟩
    · exact h₂.same.frame.sub (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨⟨S s₀, 456⟩, by simp [changes], by rw [x15₁]; exact fun _ h => h⟩)
    · intro i hi
      have e := h₂.keys i hi
      rw [x15₁, hS] at e
      exact e
    · intro p hp'
      rw [← x15₁, h₂.slots p hp']
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp'
      exact g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2
    · intro j hj
      rw [ite_eq_right (Nat.not_lt_zero _)]
      exact VG.Proof.TripleDes.Bitslice.blockAt_frame h₂.same.frame (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [x15₁]
        exact (hp.data_scr.sub_left (data_sub hj)).sub_right (Region.sub_prefix (by decide)))
  apply WP.seq
  refine WP.mono (loop_ok d hp (by omega_using [hn]) inv₂) fun s₃ h₃ => ?_
  refine WP.mono (restore_ok' bp (by rw [h₃.x15, x15₁]) h₃.rd h₃.wr (by
    rw [x15₁]
    intro p hp'
    rw [h₃.slots p hp']
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp'
    exact (g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2).symm))
    fun s₄ h₄ => ⟨?_, fun i hi => ?_⟩
  · rw [Result, h₄.mem]
    refine VG.Proof.TripleDes.Bitslice.ecb_blocks _ _ _ _ _ _ fun b hb => ?_
    rw [h₃.data b hb, ite_eq_left hb]
  · rw [h₄.gpr_of (.inl (List.mem_map.mpr ⟨_, mem_saveSlots hi, rfl⟩))]
    exact g₁ _ (savedNe i hi).1 (savedNe i hi).2

/-! ## Fewer than eleven blocks, or the batch -/

/-- `few` runs one of its two programs, from a state that differs in `x13`. -/
theorem few_wp {n : Reg} {short long : Prog isa} {s₀ : State} {Q : State → Prop}
    (h : ∀ s₁, (∀ r, r ≠ .x13 → s₁.gpr r = s₀.gpr r) → s₁.mem = s₀.mem → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → WP isa short s₁ Q ∧ WP isa long s₁ Q) : WP isa (few n short long) s₀ Q := by
  obtain ⟨sₐ, eₐ, _, gₐ, mₐ, rdₐ, wrₐ⟩ := Modes.AArch64.addImm_ok s₀ .x13 n (v := 5) (by decide)
  obtain ⟨s₁, e', _, g', m', rd', wr'⟩ := Modes.AArch64.lsr_ok sₐ .x13 .x13 (sh := 4) (by decide)
  have e₁ : runBlock isa [.addImm .x .x13 n 5, .lsr .x .x13 .x13 4] s₀ = some s₁ := by
    rw [show ([.addImm .x .x13 n 5, .lsr .x .x13 .x13 4] : List Instr) =
      [.addImm .x .x13 n 5] ++ [.lsr .x .x13 .x13 4] from rfl, Modes.AArch64.runBlock_app, eₐ,
      Option.bind_some, e']
  obtain ⟨hs, hl⟩ := h s₁ (fun r hr => (g' r hr).trans (gₐ r hr)) (m'.trans mₐ) (rd'.trans rdₐ)
    (wr'.trans wrₐ)
  unfold few
  exact WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.ite _ rfl (fun _ => hs) (fun _ => hl)⟩)

open VG.Proof.TripleDes.AArch64.Ecb (contract)
open VG.Impl.TripleDes.AArch64 (BitsliceNeon.ecb)

theorem savedRegs_ne13 : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs, r ≠ .x13 := by decide

/-- `WP.gprs` for registers the calls of `c` keep (none of `linkRegs`). -/
theorem gprs_of_notLink {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : c.allInstrs (fun i => rs.all fun r => !clobbers i r) = true) (hl : ∀ r ∈ rs, r ∉ linkRegs) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  rw [Code.allInstrs_eq] at hc
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inr (hl r hr))⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- Either path keeps the return address: the table block's, which calls
nothing and does not write it, and the bitsliced ECB's. -/
theorem few_ecb_keeps_x30 (d : Direction)
    (hs : (ecb d).allInstrs (fun i => !clobbers i .x30) = true) (hn : (ecb d).noCalls = true)
    {s s' : State} {t : List Leak} (he : Exec isa (few .x2 (ecb d) (BitsliceNeon.ecb d)) s t s') :
    s'.gpr .x30 = s.gpr .x30 := by
  unfold few at he
  cases he with
  | seq hA hR =>
    obtain k : ∀ i ∈ instrs (.block [.addImm .x .x13 .x2 5, .lsr .x .x13 .x13 4] : Prog isa),
        clobbers i .x30 = false := by decide
    rw [← Exec.gpr k hA (.inl rfl)]
    cases hR with
    | iteT _ h =>
      refine Exec.gpr (fun i hi => ?_) h (.inl hn)
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hs) i hi
      revert this; cases clobbers i .x30 <;> simp
    | iteF _ h => exact VG.Proof.TripleDes.AArch64.BitslicedNeon.ecb_keeps_x30 d h

/-- Either path is ECB and keeps the registers the table block saves. -/
theorem few_ecb_wp (d : Direction) {s₀ : State} (hp : (contract d).pre s₀)
    (hk : (BitsliceNeon.ecb d).allInstrs (fun i =>
      VG.Proof.CmacTripleDes.AArch64.savedRegs.all fun r => !clobbers i r) = true) :
    WP isa (few .x2 (ecb d) (BitsliceNeon.ecb d)) s₀ fun s' =>
      (contract d).post s₀ s' ∧ ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs, s'.gpr r = s₀.gpr r := by
  refine few_wp fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  have hp₁ : (contract d).pre s₁ := by
    simpa only [contract, m₁, rd₁, wr₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide),
      g₁ .x3 (by decide)] using hp
  have back {s' : State} (h : (contract d).post s₁ s') : (contract d).post s₀ s' := by
    simpa only [contract, m₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide)] using h
  constructor
  · obtain ⟨hrd, hwr, kd, ks, ds, fit⟩ := hp₁
    refine WP.mono (ecb_wp d ⟨hrd, hwr, kd, ks, ds, fit⟩) fun s' ⟨res, sv⟩ => ⟨back res, fun r hr => ?_⟩
    obtain ⟨i, hi, rfl⟩ := mem_savedRegs hr
    exact (sv i hi).trans (g₁ _ (savedRegs_ne13 _ hr))
  · refine WP.mono (gprs_of_notLink (VG.Proof.TripleDes.AArch64.BitslicedNeon.ecb_contract d s₁ hp₁) hk
      (by decide))
      fun s' ⟨res, sv⟩ => ⟨back res, fun r hr => (sv r hr).trans (g₁ _ (savedRegs_ne13 _ hr))⟩

theorem few_ecb_correct (d : Direction) {c : Prog isa} (hc : c = few .x2 (ecb d) (BitsliceNeon.ecb d))
    (hk : (BitsliceNeon.ecb d).allInstrs (fun i =>
      VG.Proof.CmacTripleDes.AArch64.savedRegs.all fun r => !clobbers i r) = true)
    (hs : (ecb d).allInstrs (fun i => !clobbers i .x30) = true) (hn : (ecb d).noCalls = true)
    (ho : c.allInstrs (fun i => (preserved.filter
      (fun r => r ∉ VG.Proof.CmacTripleDes.AArch64.savedRegs ∧ r ≠ .x30)).all (fun r => !clobbers i r)) = true)
    (hv : c.allInstrs keepsV = true)
    (s : State) (hp : (contract d).pre s) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
  subst hc
  obtain ⟨t, s', he, ⟨post, sv⟩, other⟩ := gprs_of_notLink (few_ecb_wp d hp hk) ho (by decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩, post⟩
  by_cases h30 : r = .x30
  · subst h30; exact few_ecb_keeps_x30 d hs hn he
  by_cases hsv : r ∈ VG.Proof.CmacTripleDes.AArch64.savedRegs
  · exact sv r hsv
  · exact other r (List.mem_filter.mpr ⟨hr, by simpa using And.intro hsv h30⟩)

/-- What `few_ecb_correct` asks of the code `c` of direction `d`. -/
def EcbChecks (d : Direction) (c : Prog isa) : Prop :=
  ((BitsliceNeon.ecb d).allInstrs (fun i =>
      VG.Proof.CmacTripleDes.AArch64.savedRegs.all fun r => !clobbers i r) = true ∧
    (ecb d).allInstrs (fun i => !clobbers i .x30) = true ∧ (ecb d).noCalls = true) ∧
  c.allInstrs (fun i => (preserved.filter
    (fun r => r ∉ VG.Proof.CmacTripleDes.AArch64.savedRegs ∧ r ≠ .x30)).all (fun r => !clobbers i r)) = true ∧
  c.allInstrs keepsV = true

/-- The checks of both directions' code, in one kernel evaluation (`taint_decide_all`): what an
instruction writes is evaluated once, for the checks of the registers the table block saves and
of the others, and for both directions, whose code is mostly the same instructions. -/
theorem ecb_checks : EcbChecks .encrypt ecbEncrypt ∧ EcbChecks .decrypt ecbDecrypt := by
  unfold EcbChecks
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  taint_decide_all

theorem ecbEncrypt_correct (s : State) (hp : (contract .encrypt).pre s) :
    ∃ t s', Exec isa ecbEncrypt s t s' ∧ abiPreserved s s' ∧ (contract .encrypt).post s s' :=
  few_ecb_correct .encrypt rfl ecb_checks.1.1.1 ecb_checks.1.1.2.1 ecb_checks.1.1.2.2 ecb_checks.1.2.1
    ecb_checks.1.2.2 s hp

theorem ecbDecrypt_correct (s : State) (hp : (contract .decrypt).pre s) :
    ∃ t s', Exec isa ecbDecrypt s t s' ∧ abiPreserved s s' ∧ (contract .decrypt).post s s' :=
  few_ecb_correct .decrypt rfl ecb_checks.2.1.1 ecb_checks.2.1.2.1 ecb_checks.2.1.2.2 ecb_checks.2.2.1
    ecb_checks.2.2.2 s hp

theorem ecbEncrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) ecbEncrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem ecbDecrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) ecbDecrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

open VG.Proof.TripleDes.AArch64.BitslicedNeon (satState publicRegs_four) in
theorem ecbEncrypt_verified :
    Verified target ecbEncrypt (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct ecbEncrypt_correct (ecbEncrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_four]
    [satState] using satState

open VG.Proof.TripleDes.AArch64.BitslicedNeon (satState publicRegs_four) in
theorem ecbDecrypt_verified :
    Verified target ecbDecrypt (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct ecbDecrypt_correct (ecbDecrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_four]
    [satState] using satState

end VG.Proof.TripleDes.AArch64.Short
