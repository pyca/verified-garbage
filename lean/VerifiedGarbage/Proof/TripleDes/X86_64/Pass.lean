module

public import VerifiedGarbage.Proof.TripleDes.X86_64.PassStart
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
import VerifiedGarbage.Proof.TripleDes.X86_64.Box
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

def passesAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 456

theorem passes_round_disjoint (s : State) :
    (⟨passesAddr s, 8⟩ : Region).Disjoint (roundRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem passes_step_disjoint (s : State) :
    (⟨passesAddr s, 8⟩ : Region).Disjoint ⟨stepAddr s, 8⟩ :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem step_sub_work (s : State) : Region.Sub ⟨stepAddr s, 8⟩ (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem passes_sub_work (s : State) : Region.Sub ⟨passesAddr s, 8⟩ (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem passCountAdvance_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (passesAddr s) 8)
    (hwrite : InRegions s.wr (passesAddr s) 8) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      s'.mem = s.mem.writeW (passesAddr s) (s.mem.readW (passesAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (passesAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold passesAddr at hread hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 456) = BitVec.ofNat 64 456 := rfl
  refine ⟨_, by
    simp only [passCountAdvance, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, hoff, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [zf_setReg, zf_arithFlags]
    rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr .rdi = s.mem.readW (savedKeyAddr s) 64 + BitVec.ofNat 64 (passOffset c d)
  mem : t.mem = (s.mem.writeW (countAddr s) (BitVec.ofNat 64 16)).writeW (stepAddr s) (stepVal d)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .rax → r ≠ .rdi → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

/-- The comparison of `rax` with an immediate. -/
def cmpState (s : State) (v : BitVec 32) : State :=
  arithFlags s (s.gpr .rax - v.signExtend 64) (decide ((s.gpr .rax).toNat < (v.signExtend 64).toNat))
    (subOverflow (s.gpr .rax) (v.signExtend 64) (s.gpr .rax - v.signExtend 64))

theorem cmp_run (s : State) (v : BitVec 32) :
    runBlock isa [.alu .cmp .rax (.imm v)] s = some (cmpState s v) := by
  rw [runBlock_cons]
  rfl

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 p)
    (hpRead : InRegions (s.rd ++ s.wr) (passesAddr s) 8)
    (hread : InRegions (s.rd ++ s.wr) (savedKeyAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) (hstep : InRegions s.wr (stepAddr s) 8) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  -- a branch, from a state that differs from `s` in `rax` and the flags only
  have branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hrd hwr hg
    subst hq
    have hdx : t.gpr .rdx = s.gpr .rdx := hg .rdx (by decide)
    have hsaved : savedKeyAddr t = savedKeyAddr s := by simp only [savedKeyAddr, hdx]
    have hcount : countAddr t = countAddr s := by simp only [countAddr, hdx]
    have hstepA : stepAddr t = stepAddr s := by simp only [stepAddr, hdx]
    obtain ⟨u, run, ptr, mem, rd, wr, regs⟩ := passStart_ok (passOf d q).1 (passOf_lt d q)
      (passOf d q).2 t (by rw [hrd, hwr, hsaved]; exact hread) (by rw [hwr, hcount]; exact hwrite)
      (by rw [hwr, hstepA]; exact hstep)
    refine WP.of_runBlock ⟨u, run, ?_, ?_, rd.trans hrd, wr.trans hwr, ?_⟩
    · rw [ptr, hm, hsaved]
    · rw [mem, hm, hcount, hstepA]
    · intro r hrax hrdi
      exact (regs r hrax hrdi).trans (hg r hrax)
  let v := s.mem.readW (passesAddr s) 64
  let s₁ := s.setReg .rax v
  have e₁ : exec (.mov .rax (.mem (memOp .rdx 456))) s = some s₁ := by
    unfold passesAddr at hpRead
    have hoff : BitVec.ofInt 64 (Int.ofNat 456) = BitVec.ofNat 64 456 := rfl
    simp only [exec, readSrc, State.ea, memOp, hoff, State.load64, hpRead]
    rfl
  let t₁ := cmpState s₁ 3
  have hrax₁ : t₁.gpr .rax = BitVec.ofNat 64 p := by
    simp only [t₁, cmpState, gpr_arithFlags, s₁, gpr_setReg_self, v, hpasses]
  have hg₁ : ∀ r, r ≠ .rax → t₁.gpr r = s.gpr r := by
    intro r hr
    simp only [t₁, cmpState, gpr_arithFlags, s₁, gpr_setReg_of_ne (s := s) v hr]
  have hm₁ : t₁.mem = s.mem := by simp only [t₁, cmpState, mem_arithFlags, s₁, mem_setReg]
  have hrd₁ : t₁.rd = s.rd := by simp only [t₁, cmpState, rd_arithFlags, s₁, rd_setReg]
  have hwr₁ : t₁.wr = s.wr := by simp only [t₁, cmpState, wr_arithFlags, s₁, wr_setReg]
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by rw [runBlock_cons, e₁, runStep_some, cmp_run], ?_⟩
  have zf₁ : isa.eval .e t₁ = some (p == 3) := by
    change t₁.zf = _
    simp only [t₁, cmpState, zf_arithFlags, s₁, gpr_setReg_self, v, hpasses]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm hm₁ hrd₁ hwr₁ hg₁
  · intro h3
    have hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := cmpState t₁ 2
    refine WP.of_runBlock ⟨t₂, cmp_run t₁ 2, ?_⟩
    have zf₂ : isa.eval .e t₂ = some (p == 2) := by
      change t₂.zf = _
      simp only [t₂, cmpState, zf_arithFlags, hrax₁]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    have hg₂ : ∀ r, r ≠ .rax → t₂.gpr r = s.gpr r := by
      intro r hr
      simp only [t₂, cmpState, gpr_arithFlags]
      exact hg₁ r hr
    have hm₂ : t₂.mem = s.mem := by simp only [t₂, cmpState, mem_arithFlags, hm₁]
    have hrd₂ : t₂.rd = s.rd := by simp only [t₂, cmpState, rd_arithFlags, hrd₁]
    have hwr₂ : t₂.wr = s.wr := by simp only [t₂, cmpState, wr_arithFlags, hwr₁]
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm hm₂ hrd₂ hwr₂ hg₂
    · intro h2
      have hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega) hm₂ hrd₂ hwr₂ hg₂

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem
  passes : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 (n - 1)
  zf : isa.eval .ne s = some (decide (n ≠ 1))

/-- A complete DES pass: the choice of its keys by the passes left, its
sixteen rounds, the final half swap and the passes left counted down. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hpasses : origin.mem.readW (passesAddr origin) 64 = BitVec.ofNat 64 p)
    (hpRead : InRegions (origin.rd ++ origin.wr) (passesAddr origin) 8)
    (hpWrite : InRegions origin.wr (passesAddr origin) 8)
    (hptr : origin.mem.readW (savedKeyAddr origin) 64 +
      BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) = keyAddr base (passOf d p).2 0)
    (hsavedRead : InRegions (origin.rd ++ origin.wr) (savedKeyAddr origin) 8)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hstepWrite : InRegions origin.wr (stepAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base (passOf d p).2 j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base (passOf d p).2 j, 8⟩ : Region).Disjoint (workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base (passOf d p).2 j) 64).setWidth 48 =
      roundKey keys (passOf d p).2 j) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses hpRead hsavedRead hcountWrite hstepWrite)
    fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hread hsep hkeys ⊢
  have hbase : s.gpr .rdx = origin.gpr .rdx := hs.regs .rdx (by decide) (by decide)
  have hcountAddr : countAddr s = countAddr origin := by simp only [countAddr, hbase]
  have hstepAddr : stepAddr s = stepAddr origin := by simp only [stepAddr, hbase]
  have hpassesAddr : passesAddr s = passesAddr origin := by simp only [passesAddr, hbase]
  have hroundR : roundRegion s = roundRegion origin := by simp only [roundRegion, hbase]
  have hsepR : ∀ j < 16, (⟨keyAddr base dir j, 8⟩ : Region).Disjoint (roundRegion origin) :=
    fun j hj => (hsep j hj).sub_right (round_sub_work origin)
  have hsepStep : ∀ j < 16, (⟨keyAddr base dir j, 8⟩ : Region).Disjoint ⟨stepAddr origin, 8⟩ :=
    fun j hj => (hsep j hj).sub_right (step_sub_work origin)
  -- what the start writes
  have hframe : Frame [roundRegion origin, ⟨stepAddr origin, 8⟩] origin.mem s.mem := by
    rw [hs.mem]
    refine Frame.trans ((countWrite_frame _ _ _).sub ?_) ((countWrite_frame _ _ _).sub ?_)
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_cons_self .., count_sub_work origin⟩
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, by simp, fun _ h => h⟩
  have hframeDisj : ∀ (r : Region), r.Disjoint (roundRegion origin) →
      r.Disjoint ⟨stepAddr origin, 8⟩ → ∀ r' ∈ [roundRegion origin, ⟨stepAddr origin, 8⟩],
      r.Disjoint r' := by
    intro r h1 h2 r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h1
    · exact h2
  have hkeysS : ∀ j < 16, (s.mem.readW (keyAddr base dir j) 64).setWidth 48 =
      roundKey keys dir j := by
    intro j hj
    have hmem := hframe.readW (a := keyAddr base dir j) (w := 64)
      (r := ⟨keyAddr base dir j, 8⟩) (Region.contains_self _ _)
      (hframeDisj _ (hsepR j hj) (hsepStep j hj)) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys j hj)
  have hcountS : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 16 := by
    rw [hs.mem, hcountAddr]
    have hsepCS : (⟨countAddr origin, 8⟩ : Region).Disjoint ⟨stepAddr origin, 8⟩ :=
      Offset.disjoint (origin.gpr .rdx) (by decide) (by decide) (by decide)
    rw [((countWrite_frame (origin.mem.writeW (countAddr origin) (BitVec.ofNat 64 16))
      (stepAddr origin) (stepVal dir)).readW (r := ⟨countAddr origin, 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact hsepCS) (by decide))]
    exact Mem.readW_writeW_self64 _ _ _
  have hstepS : s.mem.readW (stepAddr s) 64 = stepVal dir := by
    rw [hs.mem, hstepAddr]
    exact Mem.readW_writeW_self64 _ _ _
  have hpassesS : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 p := by
    rw [hpassesAddr, hframe.readW (r := ⟨passesAddr origin, 8⟩) (Region.contains_self _ _)
      (hframeDisj _ (passes_round_disjoint origin) (passes_step_disjoint origin)) (by decide)]
    exact hpasses
  have hloop := roundsLoop_ok keys dir base s v
    (hok.congr hbase hbase hs.rd hs.wr)
    ((hs.regs .r12 (by decide) (by decide)).trans hl)
    ((hs.regs .r13 (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hcountS
    (by rw [hs.rd, hs.wr, hcountAddr]; exact hcountRead)
    (by rw [hs.wr, hcountAddr]; exact hcountWrite) hstepS
    (by rw [hs.rd, hs.wr, hstepAddr]
        exact ⟨_, hstepWrite.choose_spec.1 |> List.mem_append_right _,
          hstepWrite.choose_spec.2⟩)
    (by rw [hs.rd, hs.wr]; exact hread)
    (by rw [hroundR]; exact hsepR) hkeysS
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  have hbase₂ : s₂.gpr .rdx = origin.gpr .rdx := (hs₂.regs .rdx (by decide)).trans hbase
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  have hbase₃ : s₃.gpr .rdx = origin.gpr .rdx := (regs₃ .rdx (by decide)).trans hbase₂
  have hpassesAddr₃ : passesAddr s₃ = passesAddr origin := by simp only [passesAddr, hbase₃]
  obtain ⟨s₄, run₄, mem₄, zf₄, rd₄, wr₄, regs₄⟩ := passCountAdvance_ok s₃
    (by rw [rd₃, wr₃, hs₂.rd, hs₂.wr, hs.rd, hs.wr, hpassesAddr₃]; exact hpRead)
    (by rw [wr₃, hs₂.wr, hs.wr, hpassesAddr₃]; exact hpWrite)
  have hp₃ : s₃.mem.readW (passesAddr s₃) 64 = BitVec.ofNat 64 p := by
    rw [mem₃, hpassesAddr₃, ← hpassesAddr, hs₂.frame.readW (r := ⟨passesAddr s, 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact passes_round_disjoint s) (by decide)]
    exact hpassesS
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), ?_, ?_, ?_, ?_⟩
  · exact (regs₄ .r12 (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ .r13 (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hrax : q ≠ .rax := by revert hq; cases q <;> decide
    have hrdi : q ≠ .rdi := by revert hq; cases q <;> decide
    exact (regs₄ q hrax).trans ((regs₃ q hq').trans ((hs₂.regs q hq).trans (hs.regs q hrax hrdi)))
  · have hf₁ : Frame [workRegion origin] origin.mem s.mem := hframe.sub (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, round_sub_work origin⟩
      · exact ⟨_, List.mem_singleton_self _, step_sub_work origin⟩)
    have hf₂ : Frame [workRegion origin] s.mem s₂.mem := hs₂.frame.sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, by rw [hroundR]; exact round_sub_work origin⟩)
    have hf₄ : Frame [workRegion origin] s₃.mem s₄.mem := by
      rw [mem₄]
      exact (countWrite_frame _ _ _).sub (by
        intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact ⟨_, List.mem_singleton_self _, by rw [hpassesAddr₃]; exact passes_sub_work origin⟩)
    rw [mem₃] at hf₄
    exact hf₁.trans (hf₂.trans hf₄)
  · have hpassesAddr₄ : passesAddr s₄ = passesAddr s₃ := by
      simp only [passesAddr, regs₄ .rdx (by decide)]
    rw [hpassesAddr₄, mem₄, Mem.readW_writeW_self64, hp₃, hsub]
  · change VG.X86_64.eval .ne s₄ = some (decide (p ≠ 1))
    simp only [VG.X86_64.eval, zf₄, hp₃, hzero, Option.map_some]
    simp

end VG.Proof.TripleDes.X86_64
