import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout`. -/
section

/-! Shared frame and call invariants for complete Arm Ed25519. -/
namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm

def Within (r R : Region) : Prop :=
  ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : VG.Proof.Ed25519.Arm.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

abbrev FR (E : BitVec 32) : Region := ⟨State.addr E, 248⟩
abbrev ARGS (E : BitVec 32) : Region := ⟨State.addr E + 248, 24⟩

/-- The baseline memory is the state after the incoming arguments have been
saved. The body cannot write those saved arguments. -/
structure Ctx (E : BitVec 32) (g : Reg → BitVec 32)
    (m₀ : Mem) (R W : List Region) (t : State) : Prop where
  rd : t.rd = R
  wr : t.wr = VG.Proof.Ed25519.Arm.Whole.FR E :: W
  sp : t.sp = E
  cs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = g r
  frame : Frame (W ++ [VG.Proof.Ed25519.Arm.Whole.FR E]) m₀ t.mem

namespace Ctx
variable {E : BitVec 32} {g : Reg → BitVec 32}
  {m₀ : Mem} {rd wr : List Region} {t u : State}

theorem of_frame (h : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (VG.Proof.Ed25519.Arm.Whole.FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn),
    h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨VG.Proof.Ed25519.Arm.Whole.FR E, List.mem_append_right _ (List.mem_singleton_self _), hf⟩
  · exact ⟨R, List.mem_append_left _ hR, hs⟩

theorem regs (h : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = t.gpr r)
    (hm : u.mem = t.mem) : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), hm ▸ h.frame⟩

theorem readable_frame (h : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (VG.Proof.Ed25519.Arm.Whole.FR E).Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [h.rd, h.wr]
  exact ⟨VG.Proof.Ed25519.Arm.Whole.FR E, List.mem_append_right _ List.mem_cons_self, hc⟩

theorem writable_frame (h : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (VG.Proof.Ed25519.Arm.Whole.FR E).Contains a n) : InRegions t.wr a n := by
  rw [h.wr]
  exact ⟨VG.Proof.Ed25519.Arm.Whole.FR E, List.mem_cons_self, hc⟩
end Ctx

theorem call_ok {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {t : State} (h : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.Arm.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.Arm.Whole.Within r (VG.Proof.Ed25519.Arm.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.Arm.Whole.Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr u → Frame wr' t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨VG.Proof.Ed25519.Arm.Whole.FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  obtain ⟨trace,u,he,habi,hpost⟩ := hv _ hpre
  obtain ⟨hrd,hwr,_,hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd,State.withRegions_wr,State.withRegions_mem,State.callEntry_mem] at hrd hwr hf
  have he' := Exec.widen he (rd := t.rd) (wr := t.wr) (by simpa using hcr) (by simpa using hcw)
  simp only [State.withRegions_withRegions] at he'
  rw [show t.callEntry.withRegions t.rd t.wr=t.callEntry from rfl] at he'
  have hlr := habi.1 .lr (by decide)
  have hret : isa.ret t.callEntry (u.withRegions t.rd t.wr)=some (u.withRegions t.rd t.wr) := by
    simp only [State.withRegions_gpr] at hlr
    simp only [isa,ret,State.withRegions_gpr,hlr,ite_true]
  refine ⟨_,_,Exec.call (call_callEntry t) he' hret,?_⟩
  have hc : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr (u.withRegions t.rd t.wr) := by
    refine h.of_frame (u := u.withRegions t.rd t.wr) rfl rfl habi.2 ?_ hf ?_
    · intro r hr hrl
      simp only [State.withRegions_gpr]
      rw [habi.1 r hr,State.withRegions_gpr,State.callEntry_gpr _ (preserved_not_link r hr hrl)]
    · intro r hr
      rcases hw r hr with hf | ⟨R,hR,hs⟩
      · exact .inl hf.sub
      · exact .inr ⟨R,hR,hs.sub⟩
  apply hQ _ hc hf
  have eq : (u.withRegions t.rd t.wr).withRegions rd' wr'=u := by
    rw [State.withRegions_withRegions,←hrd,←hwr]
    rfl
  rw [eq]
  exact hpost

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm

structure CallReady (k : Contract isa) (E : BitVec 32) (rd wr : List Region) (t : State) where
  reads : List Region
  writes : List Region
  pre : k.pre (t.callEntry.withRegions reads writes)
  covers : Covers (reads ++ writes) (rd ++ VG.Proof.Ed25519.Arm.Whole.FR E :: wr)
  writable : ∀ r ∈ writes, VG.Proof.Ed25519.Arm.Whole.Within r (VG.Proof.Ed25519.Arm.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.Arm.Whole.Within r R

theorem CallReady.covers_state {k : Contract isa} {E : BitVec 32} {g : Reg → BitVec 32}
    {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.Arm.Whole.Ctx E g m rd wr t)
    (h : VG.Proof.Ed25519.Arm.Whole.CallReady k E rd wr t) :
    Covers (h.reads ++ h.writes) (t.rd ++ t.wr) ∧ Covers h.writes t.wr := by
  refine ⟨by rw [hc.rd, hc.wr]; exact h.covers, Covers.of_sub fun r hr => ?_⟩
  rw [hc.wr]
  rcases h.writable r hr with h | ⟨R, hr, h⟩
  · exact ⟨VG.Proof.Ed25519.Arm.Whole.FR E, List.mem_cons_self, h⟩
  · exact ⟨R, List.mem_cons_of_mem _ hr, h⟩

theorem CallReady.wp {k : Contract isa} {E : BitVec 32} {g : Reg → BitVec 32}
    {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.Arm.Whole.Ctx E g m rd wr t)
    (h : VG.Proof.Ed25519.Arm.Whole.CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) :
    WP isa (.call name c) t (VG.Proof.Ed25519.Arm.Whole.Ctx E g m rd wr) :=
  VG.Proof.Ed25519.Arm.Whole.call_ok hc hv hn h.pre h.covers h.writable fun _ hc _ _ => hc

/-- Independent permission narrowing in each run leaves call traces unchanged. -/
theorem callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∃ ar aw br bw,
      k.pre (a.callEntry.withRegions ar aw) ∧ k.pre (b.callEntry.withRegions br bw) ∧
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw) ∧
      Covers (ar ++ aw) (a.rd ++ a.wr) ∧ Covers aw a.wr ∧
      Covers (br ++ bw) (b.rd ++ b.wr) ∧ Covers bw b.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ar, aw, br, bw, pa, pb, pub, ca, wa, cb, wb⟩ := hP a b hp
  cases ea with
  | call ha xa ra =>
    cases eb with
    | call hb xb rb =>
      rw [call_callEntry, Option.some.injEq] at ha hb
      subst ha hb
      obtain ⟨_, na⟩ := trace_narrow hv pa (by simpa using ca) (by simpa using wa) xa
      obtain ⟨_, nb⟩ := trace_narrow hv pb (by simpa using cb) (by simpa using wb) xb
      have ht := hct _ _ _ _ _ _ pa pb pub na nb
      exact ⟨by simp only [ht], trivial⟩

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.Entry`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure EntryStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r

theorem EntryStep.refl (s : State) : VG.Proof.Ed25519.Arm.Whole.EntryStep s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
theorem EntryStep.trans {s t u : State} (h : VG.Proof.Ed25519.Arm.Whole.EntryStep s t) (h' : VG.Proof.Ed25519.Arm.Whole.EntryStep t u) : VG.Proof.Ed25519.Arm.Whole.EntryStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r hn hl => (h'.regs r hn hl).trans (h.regs r hn hl)⟩

theorem argReg_ne12 (j : Nat) : argReg j ≠ .r12 := by unfold argReg; split <;> decide
theorem argReg_neLR (j : Nat) : argReg j ≠ .lr := by unfold argReg; split <;> decide

def inputWord (s : State) (j : Nat) : BitVec 32 :=
  if j < 4 then s.gpr (argReg j)
  else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 32

theorem saveWord_ok {s : State} {j : Nat} (hj : j < 6)
    (hw : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 (248 + 4 * j))) 4)
    (hr : 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4) :
    WP isa (.block (saveWord j)) s fun t => VG.Proof.Ed25519.Arm.Whole.EntryStep s t ∧
      t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 (248 + 4 * j))) (VG.Proof.Ed25519.Arm.Whole.inputWord s j) := by
  have hs : 4 * j < 4096 := by omega
  have ha : BitVec.ofNat 32 248 + BitVec.ofNat 32 (4 * j) = BitVec.ofNat 32 (248 + 4 * j) :=
    (BitVec.ofNat_add 248 (4 * j)).symm
  by_cases h4 : j < 4
  · apply WP.of_runBlock
    simp only [saveWord, ite_true, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.store32, Nat.reduceLT, hs, ite_true, RegUpd.gpr_setReg, RegUpd.wr_setReg,
      RegUpd.mem_setReg, RegUpd.sp_setReg, VG.Proof.Ed25519.Arm.Whole.argReg_ne12, ite_false, BitVec.add_assoc, ha,
      hw, Option.some.injEq, exists_eq_left', VG.Proof.Ed25519.Arm.Whole.inputWord, h4, ite_true]
    refine ⟨⟨rfl, rfl, rfl, ?_⟩, True.intro⟩
    intro r hn _
    simp only [RegUpd.gpr_setReg, hn, ite_false]
  · have hl : 280 + 4 * (j - 4) < 4096 := by omega
    have hr' := hr (by omega)
    apply WP.of_runBlock
    simp only [saveWord, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
      Nat.reduceLT, reduceCtorEq, hs, hl, ite_true, hr', Option.map_some, RegUpd.gpr_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.sp_setReg, BitVec.add_assoc, ha,
      hw, Option.some.injEq, exists_eq_left', VG.Proof.Ed25519.Arm.Whole.inputWord, h4, ite_false]
    refine ⟨⟨rfl, rfl, rfl, ?_⟩, True.intro⟩
    intro r hn hlr
    simp only [RegUpd.gpr_setReg, hn, hlr, ite_false]

structure Saved (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.Arm.Whole.EntryStep s t
  frame : Frame [⟨State.addr s.sp + 248, 24⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr s.sp + BitVec.ofNat 64 (248 + 4 * j)) 32 = VG.Proof.Ed25519.Arm.Whole.inputWord s j

theorem Saved.input_word {s t : State} {n j : Nat} (h : VG.Proof.Ed25519.Arm.Whole.Saved s n t)
    (_hj : j < 6) (hf : s.sp.toNat + 280 + 4 * (j - 4) < 2 ^ 32) : VG.Proof.Ed25519.Arm.Whole.inputWord t j = VG.Proof.Ed25519.Arm.Whole.inputWord s j := by
  unfold VG.Proof.Ed25519.Arm.Whole.inputWord
  split
  · exact h.step.regs _ (VG.Proof.Ed25519.Arm.Whole.argReg_ne12 _) (VG.Proof.Ed25519.Arm.Whole.argReg_neLR _)
  · rw [h.step.sp]
    refine h.frame.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4))), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr, addr_add (by omega)]
    exact Offset.disjoint _ (d := 280 + 4 * (j - 4)) (e := 248)
      (by omega) (by omega) (by omega)

theorem saveArgs_ok {s : State} : ∀ n ≤ 6,
    s.sp.toNat + 280 + 4 * (n - 4) ≤ 2 ^ 32 →
    (⟨State.addr s.sp + 248, 24⟩ : Region) ∈ s.wr →
    (∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4) →
    WP isa (.block (saveArgs n)) s (VG.Proof.Ed25519.Arm.Whole.Saved s n)
  | 0, _, _, _, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn, hf, hw, hr => by
    rw [saveArgs, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.Whole.saveArgs_ok n (by omega) (by omega) hw (fun j hj => hr j (by omega))) fun u hu => ?_
    have he : State.addr (u.sp + BitVec.ofNat 32 (248 + 4 * n)) =
        State.addr s.sp + BitVec.ofNat 64 (248 + 4 * n) := by
      rw [hu.step.sp, addr_add (by omega)]
    have uw : InRegions u.wr (State.addr (u.sp + BitVec.ofNat 32 (248 + 4 * n))) 4 := by
      rw [he, hu.step.wr]
      exact ⟨_, hw, Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
    have ur : 4 ≤ n → InRegions (u.rd ++ u.wr)
        (State.addr (u.sp + BitVec.ofNat 32 (280 + 4 * (n - 4)))) 4 := by
      intro h4
      rw [hu.step.sp, hu.step.rd, hu.step.wr]
      exact hr n (by omega) h4
    refine WP.mono (VG.Proof.Ed25519.Arm.Whole.saveWord_ok (by omega) uw ur) fun t ⟨ht, mt⟩ => ?_
    have hi : VG.Proof.Ed25519.Arm.Whole.inputWord u n = VG.Proof.Ed25519.Arm.Whole.inputWord s n := by
      by_cases h4 : n < 4
      · simp only [VG.Proof.Ed25519.Arm.Whole.inputWord, h4, ite_true]
        exact hu.step.regs _ (VG.Proof.Ed25519.Arm.Whole.argReg_ne12 _) (VG.Proof.Ed25519.Arm.Whole.argReg_neLR _)
      · exact hu.input_word (by omega) (by omega)
    rw [he, hi] at mt
    refine ⟨hu.step.trans ht, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def value (E : BitVec 32) (m : Mem) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => E + BitVec.ofNat 32 d
  | .caller j d => m.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 + BitVec.ofNat 32 d

def valid : Value → Prop
  | .const n => n < 65536
  | .frame d => d < 256
  | .caller j d => j < 6 ∧ d < 256

structure SetupStep (rs : List Reg) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r

theorem SetupStep.refl (s : State) : VG.Proof.Ed25519.Arm.Whole.SetupStep [] s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem SetupStep.trans {rs rs' : List Reg} {s t u : State}
    (h : VG.Proof.Ed25519.Arm.Whole.SetupStep rs s t) (h' : VG.Proof.Ed25519.Arm.Whole.SetupStep rs' t u) : VG.Proof.Ed25519.Arm.Whole.SetupStep (rs ++ rs') s u := by
  refine ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    h'.mem.trans h.mem, ?_⟩
  intro r hr
  exact (h'.regs r (fun hmem => hr (List.mem_append_right _ hmem))).trans
    (h.regs r (fun hmem => hr (List.mem_append_left _ hmem)))

theorem setArg_ok {s : State} {E : BitVec 32} {r : Reg} {v : Value}
    (he : s.sp = E) (hE : E.toNat + 272 ≤ 2^32) (hv : VG.Proof.Ed25519.Arm.Whole.valid v)
    (hr : ∀ j d, v = .caller j d → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (setArg r v)) s fun t => VG.Proof.Ed25519.Arm.Whole.SetupStep [r] s t ∧ t.gpr r = VG.Proof.Ed25519.Arm.Whole.value E s.mem v := by
  cases v with
  | const n =>
    change n < 65536 at hv
    have hn : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    apply WP.of_runBlock
    simp only [setArg, VG.Proof.Ed25519.Arm.Whole.value, runBlock_cons, runStep_some, runBlock_nil, exec,
      hn, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩, RegUpd.gpr_setReg_self ..⟩
    intro q hq
    exact RegUpd.gpr_setReg_of_ne s _ (by simpa using hq)
  | frame d =>
    change d < 256 at hv
    apply WP.of_runBlock
    simp only [setArg, VG.Proof.Ed25519.Arm.Whole.value, runBlock_cons, runStep_some, runBlock_nil, exec,
      hv, ite_true, he, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩, RegUpd.gpr_setReg_self ..⟩
    intro q hq
    exact RegUpd.gpr_setReg_of_ne s _ (by simpa using hq)
  | caller j d =>
    obtain ⟨hj,hd⟩ := hv
    have ha : 248 + 4*j < 4096 := by omega
    have he' : State.addr (E + BitVec.ofNat 32 (248 + 4*j)) =
        State.addr E + BitVec.ofNat 64 (248 + 4*j) := addr_add (by omega)
    have enc : encodable (BitVec.ofNat 32 d) = true := by
      apply List.any_eq_true.mpr
      refine ⟨0, by decide, ?_⟩
      simp only [Nat.mul_zero, BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.zero_mod, Nat.sub_zero,
        BitVec.shiftLeft_zero, BitVec.ushiftRight_eq_zero (Nat.le_refl 32), BitVec.or_zero,
        BitVec.toNat_ofNat, decide_eq_true_eq]
      omega
    have hr' := hr j d rfl
    apply WP.of_runBlock
    simp only [setArg,VG.Proof.Ed25519.Arm.Whole.value,runBlock_cons,runStep_some,runBlock_nil,exec,
      ha,ite_true,he,he',State.load32,hr',Option.map_some,Op2.eval,enc,
      RegUpd.gpr_setReg_self,Option.some.injEq,exists_eq_left']
    refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩, True.intro⟩
    intro q hq
    have hqr : q ≠ r := by simpa using hq
    rw [RegUpd.gpr_setReg_of_ne _ _ hqr,RegUpd.gpr_setReg_of_ne _ _ hqr]

/-- Setup does not touch memory and writes each destination exactly once. -/
theorem setupRegs_ok {s : State} {E : BitVec 32} {args : List (Reg × Value)}
    (he : s.sp = E) (hE : E.toNat + 272 ≤ 2^32) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.Arm.Whole.valid p.2)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (args.flatMap fun (r,v) => setArg r v)) s fun t => VG.Proof.Ed25519.Arm.Whole.SetupStep (args.map Prod.fst) s t ∧
      ∀ p ∈ args, t.gpr p.1 = VG.Proof.Ed25519.Arm.Whole.value E s.mem p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r,v) List.mem_cons_self
    refine WP.mono (VG.Proof.Ed25519.Arm.Whole.setArg_ok he hE hv0 ?_) fun u ⟨hu, hval⟩ => ?_
    · intro j d h
      subst v
      exact hr j hv0.1
    refine WP.mono (ih (hu.sp.trans he) hn.2
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) ?_) fun t ⟨ht, hvals⟩ => ?_
    · intro j hj
      rw [hu.rd, hu.wr]
      exact hr j hj
    refine ⟨hu.trans ht, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (ht.regs r hn.1).trans hval
    · rw [hvals p hp, hu.mem]


/-- Values only read the saved arguments, beyond the outgoing stack slots. -/
theorem value_frame {E : BitVec 32} {m m' : Mem}
    (hf : Frame [⟨State.addr E,24⟩] m m') {v : Value} (hv : VG.Proof.Ed25519.Arm.Whole.valid v) :
    VG.Proof.Ed25519.Arm.Whole.value E m' v = VG.Proof.Ed25519.Arm.Whole.value E m v := by
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    obtain ⟨hj,hd⟩ := hv
    unfold VG.Proof.Ed25519.Arm.Whole.value
    apply congrArg (· + BitVec.ofNat 32 d)
    refine hf.readW (r := ⟨State.addr E + BitVec.ofNat 64 (248+4*j),4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (d := 248+4*j) (by omega) (by omega)

structure StackStep (E : BitVec 32) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r
  frame : Frame [⟨State.addr E,24⟩] s.mem t.mem

theorem StackStep.refl (E : BitVec 32) (s : State) : VG.Proof.Ed25519.Arm.Whole.StackStep E s s :=
  ⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _⟩

theorem StackStep.trans {E : BitVec 32} {s t u : State}
    (h : VG.Proof.Ed25519.Arm.Whole.StackStep E s t) (h' : VG.Proof.Ed25519.Arm.Whole.StackStep E t u) : VG.Proof.Ed25519.Arm.Whole.StackStep E s u :=
  ⟨h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp,
    fun r h0 h12 => (h'.regs r h0 h12).trans (h.regs r h0 h12),h.frame.trans h'.frame⟩

theorem putArg_ok {s : State} {E : BitVec 32} {j : Nat} {v : Value}
    (he : s.sp = E) (hE : E.toNat+272 ≤ 2^32) (hj : j < 6) (hv : VG.Proof.Ed25519.Arm.Whole.valid v)
    (hr : ∀ i < 6, InRegions (s.rd++s.wr) (State.addr E+BitVec.ofNat 64 (248+4*i)) 4)
    (hw : InRegions s.wr (State.addr E+BitVec.ofNat 64 (4*j)) 4) :
    WP isa (.block (putArg j v)) s fun t => VG.Proof.Ed25519.Arm.Whole.StackStep E s t ∧
      t.mem = s.mem.writeW (State.addr E+BitVec.ofNat 64 (4*j)) (VG.Proof.Ed25519.Arm.Whole.value E s.mem v) := by
  rw [putArg,WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.Whole.setArg_ok he hE hv ?_) fun u ⟨hu,hval⟩ => ?_
  · intro i d h
    subst v
    exact hr i hv.1
  have hoff : 4*j < 256 := by omega
  have ha : State.addr (E+BitVec.ofNat 32 (4*j)) = State.addr E+BitVec.ofNat 64 (4*j) :=
    addr_add (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,hoff,ite_true,
    State.store32,Nat.reduceLT,RegUpd.gpr_setReg,RegUpd.wr_setReg,reduceCtorEq,
    ite_false,BitVec.add_zero,hu.sp,he,ha,hu.wr,hw,RegUpd.mem_setReg,hu.mem,
    hval,Option.some.injEq,exists_eq_left']
  refine ⟨⟨hu.rd,rfl,hu.sp,?_,?_⟩,True.intro⟩
  · intro r h0 h12
    rw [RegUpd.gpr_setReg_of_ne _ _ h12]
    exact hu.regs r (by simpa using h0)
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))

structure StackReady (E : BitVec 32) (s : State) (start : Nat) (vs : List Value) (t : State) : Prop where
  step : VG.Proof.Ed25519.Arm.Whole.StackStep E s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 (4*start),4*vs.length⟩] s.mem t.mem
  words : ∀ j (hj : j < vs.length), t.mem.readW (State.addr E+BitVec.ofNat 64 (4*(start+j))) 32 = VG.Proof.Ed25519.Arm.Whole.value E s.mem (vs[j]'hj)


theorem setupStack_ok {E : BitVec 32} (hE : E.toNat+272 ≤ 2^32)
    {s : State} {start : Nat} {vs : List Value}
    (he : s.sp = E) (hs : start+vs.length ≤ 6)
    (hv : ∀ v ∈ vs, VG.Proof.Ed25519.Arm.Whole.valid v)
    (hr : ∀ j < 6, InRegions (s.rd++s.wr) (State.addr E+BitVec.ofNat 64 (248+4*j)) 4)
    (hw : ∀ j < 6, InRegions s.wr (State.addr E+BitVec.ofNat 64 (4*j)) 4) :
    WP isa (.block (setupStack start vs)) s (VG.Proof.Ed25519.Arm.Whole.StackReady E s start vs) := by
  induction vs generalizing s start with
  | nil => exact WP.block_nil ⟨.refl _ _,Frame.refl _ _,fun j hj => by simp at hj⟩
  | cons v vs ih =>
    rw [setupStack,WP.block_append_iff]
    have hj : start < 6 := by simp only [List.length_cons] at hs; omega
    refine WP.mono (VG.Proof.Ed25519.Arm.Whole.putArg_ok he hE hj (hv v List.mem_cons_self) hr (hw start hj)) fun u ⟨hu,hmem⟩ => ?_
    refine WP.mono (ih (hu.sp.trans he) (by simp only [List.length_cons] at hs; omega)
      (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))
      (by intro j hj; rw [hu.rd,hu.wr]; exact hr j hj)
      (by intro j hj; rw [hu.wr]; exact hw j hj)) fun t ht => ?_
    refine ⟨hu.trans ht.step,?_,?_⟩
    · have first : Frame [⟨State.addr E+BitVec.ofNat 64 (4*start),4*(v::vs).length⟩] s.mem u.mem := by
        rw [hmem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero,Nat.zero_add,List.length_cons]; omega)
      refine first.trans (Frame.sub ht.frame ?_)
      intro r hr
      rw [List.mem_singleton.mp hr]
      refine ⟨_,List.mem_singleton_self _,?_⟩
      exact Offset.sub _ (by omega) (by simp only [List.length_cons]; omega)
    · intro j hj'
      cases j with
      | zero =>
        simp only [Nat.add_zero,List.getElem_cons_zero]
        rw [ht.frame.readW (r := ⟨State.addr E+BitVec.ofNat 64 (4*start),4⟩)
          (Region.contains_self _ _) (by
            intro r hr
            rw [List.mem_singleton.mp hr]
            exact Offset.disjoint _ (by omega) (by omega) (by simp only [List.length_cons] at hs; omega)) (by decide)]
        rw [hmem,Mem.readW_writeW_self32]
      | succ j =>
        have hj : j < vs.length := by simpa using hj'
        have hw' := ht.words j hj
        rw [VG.Proof.Ed25519.Arm.Whole.value_frame hu.frame (hv vs[j] (List.mem_cons_of_mem _ (List.getElem_mem hj)))] at hw'
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using hw'

theorem Ctx.setup {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr s)
    (hE : E.toNat+272 ≤ 2^32)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed25519.Arm.Whole.valid p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, VG.Proof.Ed25519.Arm.Whole.valid v)
    (hr : VG.Proof.Ed25519.Arm.Whole.ARGS E ∈ rd) (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args stack)) s fun t => VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨State.addr E,24⟩] s.mem t.mem ∧
      (∀ p ∈ args, t.gpr p.1 = VG.Proof.Ed25519.Arm.Whole.value E s.mem p.2) ∧
      (∀ j (hj : j < stack.length), stackArg t j = VG.Proof.Ed25519.Arm.Whole.value E s.mem (stack[j]'hj)) := by
  have read : ∀ j < 6, InRegions (s.rd++s.wr) (State.addr E+BitVec.ofNat 64 (248+4*j)) 4 := by
    intro j hj
    rw [hc.rd,hc.wr]
    refine ⟨VG.Proof.Ed25519.Arm.Whole.ARGS E,List.mem_append_left _ hr,?_⟩
    exact Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)
  have write : ∀ j < 6, InRegions s.wr (State.addr E+BitVec.ofNat 64 (4*j)) 4 := by
    intro j hj
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  rw [Impl.Ed25519.Arm.Whole.setup,WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.Arm.Whole.setupStack_ok hE hc.sp (by simpa using hs) hvs read write) fun u hu => ?_
  refine WP.mono (VG.Proof.Ed25519.Arm.Whole.setupRegs_ok (hu.step.sp.trans hc.sp) hE hn hv
    (by intro j hj; rw [hu.step.rd,hu.step.wr]; exact read j hj)) fun t ⟨ht,hvals⟩ => ?_
  have hcu : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr u := by
    refine hc.of_frame hu.step.rd hu.step.wr hu.step.sp ?_ hu.step.frame ?_
    · intro r hr _
      exact hu.step.regs r (by intro h; subst r; exact (by decide : Reg.r0 ∉ preserved) hr) (by intro h; subst r; exact (by decide : Reg.r12 ∉ preserved) hr)
    · intro R hR
      rw [List.mem_singleton.mp hR]
      exact .inl (Region.sub_prefix (by decide))
  have hct : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t := by
    refine hcu.regs ht.rd ht.wr ht.sp ?_ ht.mem
    intro r hpres _
    apply ht.regs
    intro hm
    obtain ⟨p,hp,heq⟩ := List.mem_map.mp hm
    exact hregs p hp (heq ▸ hpres)
  refine ⟨hct,ht.mem ▸ hu.step.frame,?_,?_⟩
  · intro p hp
    rw [hvals p hp,VG.Proof.Ed25519.Arm.Whole.value_frame hu.step.frame (hv p hp)]
  · intro j hj
    have hsp : t.sp = E := ht.sp.trans (hu.step.sp.trans hc.sp)
    have ha : State.addr (E+BitVec.ofNat 32 (4*j)) = State.addr E+BitVec.ofNat 64 (4*j) :=
      addr_add (by omega)
    simp only [stackArg,stackArgAddr,hsp,ha,ht.mem]
    simpa only [Nat.zero_add] using hu.words j hj

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure WipeStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r

theorem WipeStep.trans {s t u : State} (h : VG.Proof.Ed25519.Arm.Whole.WipeStep s t) (h' : VG.Proof.Ed25519.Arm.Whole.WipeStep t u) : VG.Proof.Ed25519.Arm.Whole.WipeStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem zeroWord_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hr : (⟨State.addr E, 248⟩ : Region) ∈ s.wr)
    {k : Nat} (hk : k < 62) :
    WP isa (.block (zeroWord k)) s fun t => VG.Proof.Ed25519.Arm.Whole.WipeStep s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32) := by
  have ae : State.addr (E + BitVec.ofNat 32 (4 * k)) = State.addr E + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  have dest : InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, hr, Offset.contains_base _ (by omega) (by omega)⟩
  have ha {t : State} : exec (.addSp .r12 0) t = some (t.setReg .r12 t.sp) := by
    simp only [exec, show 0 < 256 from by decide, ite_true, BitVec.add_zero]
  have hz {t : State} : exec (.movw .r0 0) t = some (t.setReg .r0 0) := rfl
  apply WP.of_runBlock
  simp only [zeroWord, runBlock_cons, runStep_some, ha, hz]
  rw [exec_str (by omega) (by
    simpa only [RegUpd.wr_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true,
      he, ae] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h12
    simp only [RegUpd.gpr_setReg, h0, h12, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, he, ae]

structure WipeInv (E : BitVec 32) (s : State) (start n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.Arm.Whole.WipeStep s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * n⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr E + BitVec.ofNat 64 (4 * (start + j))) 32 = 0

theorem zeroWords_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) (start : Nat) :
    ∀ n, start + n ≤ 62 → WP isa (.block (VG.Impl.Ed25519.Arm.Whole.zeroWords start n)) s (VG.Proof.Ed25519.Arm.Whole.WipeInv E s start n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [VG.Impl.Ed25519.Arm.Whole.zeroWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.Whole.zeroWords_ok he hf hw start n (by omega)) fun u hu => ?_
    refine WP.mono (VG.Proof.Ed25519.Arm.Whole.zeroWord_ok (hu.step.sp.trans he) hf (hu.step.wr ▸ hw) (by omega : start + n < 62))
      fun t ⟨kt, mt⟩ => ?_
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      have old : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * (n + 1)⟩] s.mem u.mem :=
        Frame.sub hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
      exact old.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := State.addr E + BitVec.ofNat 64 (4 * (start + j)))
          (b := State.addr E + BitVec.ofNat 64 (4 * (start + n))) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem Ctx.zeroWords {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr s)
    (hf : E.toNat + 248 ≤ 2 ^ 32) {start count : Nat} (hn : start + count ≤ 62) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.zeroWords start count)) s fun t => VG.Proof.Ed25519.Arm.Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (State.addr E + BitVec.ofNat 64 (4 * (start + j))) 32 = 0 := by
  refine WP.mono (VG.Proof.Ed25519.Arm.Whole.zeroWords_ok hc.sp hf (by rw [hc.wr]; exact List.mem_cons_self) start count hn)
    fun t ht => ⟨?_, ht.frame, ht.words⟩
  refine hc.of_frame ht.step.rd ht.step.wr ht.step.sp ?_ ht.frame ?_
  · intro r hr _
    apply ht.step.regs
    · rintro rfl; simp [preserved] at hr
    · rintro rfl; simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap`. -/
section

/-! Merged from `Proof.Ed25519.Arm.Whole.WrapSaved`. -/
section
/-! Merged from `Proof.Ed25519.Arm.Whole.WrapGeometry`. -/
section
namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev base (s : State) : BitVec 32 := s.sp - 280
abbrev entered (s : State) : State := allocated 248 (allocated 24 (pushed [.r12] (pushed [.lr] s)))
abbrev bodyRd (s : State) : List Region := s.rd ++ [VG.Proof.Ed25519.Arm.Whole.ARGS (VG.Proof.Ed25519.Arm.Whole.base s)]
abbrev bodyWr (s : State) : List Region := VG.Proof.Ed25519.Arm.Whole.FR (VG.Proof.Ed25519.Arm.Whole.base s) :: s.wr
abbrev stack (s : State) : Region := ⟨State.addr (VG.Proof.Ed25519.Arm.Whole.base s), 280⟩

theorem entered_sp (s : State) : (VG.Proof.Ed25519.Arm.Whole.entered s).sp = VG.Proof.Ed25519.Arm.Whole.base s := by
  change s.sp - 4#32 - 4#32 - 24#32 - 248#32 = s.sp - 280
  simp only [BitVec.sub_sub]
  rfl

theorem base_args (s : State) : VG.Proof.Ed25519.Arm.Whole.base s + 248#32 = s.sp - 4#32 - 4#32 - 24#32 := by
  simp only [VG.Proof.Ed25519.Arm.Whole.base, BitVec.sub_sub]
  change s.sp - 280#32 + 248#32 = s.sp - 32#32
  rw [show (280#32) = 32#32 + 248#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_pad (s : State) : VG.Proof.Ed25519.Arm.Whole.base s + 272#32 = s.sp - 4#32 - 4#32 := by
  simp only [VG.Proof.Ed25519.Arm.Whole.base, BitVec.sub_sub]
  change s.sp - 280#32 + 272#32 = s.sp - 8#32
  rw [show (280#32) = 8#32 + 272#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_lr (s : State) : VG.Proof.Ed25519.Arm.Whole.base s + 276#32 = s.sp - 4#32 := by
  change s.sp - 280#32 + 276#32 = s.sp - 4#32
  rw [show (280#32) = 4#32 + 276#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_top {s : State} (h : 280 ≤ s.sp.toNat) : (VG.Proof.Ed25519.Arm.Whole.base s).toNat + 280 = s.sp.toNat := by
  change (s.sp - 280#32).toNat + 280 = s.sp.toNat
  rw [BitVec.toNat_sub_of_le (by change 280 ≤ s.sp.toNat; exact h)]
  change s.sp.toNat - 280 + 280 = s.sp.toNat
  omega

theorem base_addr {s : State} (h : 280 ≤ s.sp.toNat) :
    State.addr (VG.Proof.Ed25519.Arm.Whole.base s) = State.addr s.sp - 280 := by
  have e : VG.Proof.Ed25519.Arm.Whole.base s + 280#32 = s.sp := BitVec.sub_add_cancel _ _
  have ha := addr_add (a := VG.Proof.Ed25519.Arm.Whole.base s) (k := 280) (by rw [VG.Proof.Ed25519.Arm.Whole.base_top h]; exact s.sp.isLt)
  rw [e] at ha
  rw [ha]
  exact (BitVec.add_sub_cancel _ _).symm

theorem entered_wr {s : State} (h : 280 ≤ s.sp.toNat) :
    (VG.Proof.Ed25519.Arm.Whole.entered s).wr = VG.Proof.Ed25519.Arm.Whole.FR (VG.Proof.Ed25519.Arm.Whole.base s) :: VG.Proof.Ed25519.Arm.Whole.ARGS (VG.Proof.Ed25519.Arm.Whole.base s) ::
      ⟨State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 272, 4⟩ :: ⟨State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 276, 4⟩ :: s.wr := by
  have hb := VG.Proof.Ed25519.Arm.Whole.base_top h
  have hs := s.sp.isLt
  change ⟨State.addr (VG.Proof.Ed25519.Arm.Whole.entered s).sp, 248⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32 - 24#32), 24⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32), 4⟩ :: ⟨State.addr (s.sp - 4#32), 4⟩ :: s.wr = _
  rw [VG.Proof.Ed25519.Arm.Whole.entered_sp, ← VG.Proof.Ed25519.Arm.Whole.base_args, ← VG.Proof.Ed25519.Arm.Whole.base_pad, ← VG.Proof.Ed25519.Arm.Whole.base_lr,
    addr_add (by omega), addr_add (by omega), addr_add (by omega)]
  rfl

theorem entered_mem {s : State} (h : 280 ≤ s.sp.toNat) :
    (VG.Proof.Ed25519.Arm.Whole.entered s).mem = (s.mem.writeW (State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 276) (s.gpr .lr)).writeW
      (State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 272) (s.gpr .r12) := by
  have hb := VG.Proof.Ed25519.Arm.Whole.base_top h
  have hs := s.sp.isLt
  change (s.mem.writeW (State.addr (s.sp - 4#32)) (s.gpr .lr)).writeW
    (State.addr (s.sp - 4#32 - 4#32)) (s.gpr .r12) = _
  rw [← VG.Proof.Ed25519.Arm.Whole.base_pad, ← VG.Proof.Ed25519.Arm.Whole.base_lr, addr_add (by omega), addr_add (by omega)]
  rfl

end VG.Proof.Ed25519.Arm.Whole
end

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem entered_frame {s : State} (h : 280 ≤ s.sp.toNat) :
    Frame [VG.Proof.Ed25519.Arm.Whole.stack s] s.mem (VG.Proof.Ed25519.Arm.Whole.entered s).mem := by
  rw [VG.Proof.Ed25519.Arm.Whole.entered_mem h]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide : 276 + 4 ≤ 280) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide : 272 + 4 ≤ 280) (by decide))

theorem saved_ctx {s p : State} {n : Nat} (hs : VG.Proof.Ed25519.Arm.Whole.Saved (VG.Proof.Ed25519.Arm.Whole.entered s) n p) :
    VG.Proof.Ed25519.Arm.Whole.Ctx (VG.Proof.Ed25519.Arm.Whole.base s) s.gpr p.mem (VG.Proof.Ed25519.Arm.Whole.bodyRd s) s.wr (p.withRegions (VG.Proof.Ed25519.Arm.Whole.bodyRd s) (VG.Proof.Ed25519.Arm.Whole.bodyWr s)) := by
  refine ⟨rfl, rfl, hs.step.sp.trans (VG.Proof.Ed25519.Arm.Whole.entered_sp s), ?_, Frame.refl _ _⟩
  intro r hr hlr
  exact hs.step.regs r (by intro h; subst r; simp [preserved] at hr) hlr

theorem saved_frame {s p : State} {n : Nat} (h : 280 ≤ s.sp.toNat) (hs : VG.Proof.Ed25519.Arm.Whole.Saved (VG.Proof.Ed25519.Arm.Whole.entered s) n p) :
    Frame [VG.Proof.Ed25519.Arm.Whole.stack s] s.mem p.mem := by
  refine (VG.Proof.Ed25519.Arm.Whole.entered_frame h).trans (Frame.sub hs.frame fun r hr => ?_)
  rw [List.mem_singleton.mp hr, VG.Proof.Ed25519.Arm.Whole.entered_sp]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : 248 + 24 ≤ 280)⟩

def originalWord (s : State) (j : Nat) : BitVec 32 :=
  if j < 4 then s.gpr (argReg j)
  else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 32

theorem input_entered {s : State} {j : Nat} (hs : 280 ≤ s.sp.toNat)
    (_hj : j < 6) (ht : s.sp.toNat + 4 * (j - 4) < 2 ^ 32) :
    VG.Proof.Ed25519.Arm.Whole.inputWord (VG.Proof.Ed25519.Arm.Whole.entered s) j = VG.Proof.Ed25519.Arm.Whole.originalWord s j := by
  unfold VG.Proof.Ed25519.Arm.Whole.inputWord VG.Proof.Ed25519.Arm.Whole.originalWord
  split
  · rfl
  · have e : (VG.Proof.Ed25519.Arm.Whole.entered s).sp + BitVec.ofNat 32 (280 + 4 * (j - 4)) =
        s.sp + BitVec.ofNat 32 (4 * (j - 4)) := by
      rw [VG.Proof.Ed25519.Arm.Whole.entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc]
      change s.sp - 280#32 + 280#32 + _ = _
      rw [BitVec.sub_add_cancel]
    rw [e]
    have hb := VG.Proof.Ed25519.Arm.Whole.base_top hs
    have ae : State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4))) =
        State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + BitVec.ofNat 64 (280 + 4 * (j - 4)) := by
      rw [← e, VG.Proof.Ed25519.Arm.Whole.entered_sp, addr_add (by omega)]
    refine (VG.Proof.Ed25519.Arm.Whole.entered_frame hs).readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4))), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr, ae]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem saved_words {s p : State} {n j : Nat} (hs : 280 ≤ s.sp.toNat)
    (hn : n ≤ 6) (ht : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hp : VG.Proof.Ed25519.Arm.Whole.Saved (VG.Proof.Ed25519.Arm.Whole.entered s) n p) (hj : j < n) :
    p.mem.readW (State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + BitVec.ofNat 64 (248 + 4 * j)) 32 = VG.Proof.Ed25519.Arm.Whole.originalWord s j := by
  have h := hp.words j hj
  rw [VG.Proof.Ed25519.Arm.Whole.entered_sp] at h
  refine h.trans (VG.Proof.Ed25519.Arm.Whole.input_entered hs (by omega) ?_)
  by_cases h4 : j < 4
  · have hi := s.sp.isLt
    omega
  · omega

/-- Widen permissions around a body while retaining its precise write frame. -/
theorem narrow {c : Prog isa} {s : State} {rd wr : List Region} {P Q : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (hQ : ∀ u, u.rd = rd → u.wr = wr → u.sp = s.sp → Frame wr s.mem u.mem → P u →
      Q (u.withRegions s.rd s.wr)) (hn : c.noFrames = true) : WP isa c s Q := by
  obtain ⟨t, u, he, hp⟩ := h
  obtain ⟨hr, hw', hs, hf⟩ := Exec.regions he hn
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) hc hw
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  exact ⟨t, _, he', hQ u hr hw' hs hf hp⟩

theorem enter_save {s : State} {n : Nat} (hcount : n ≤ 6) (hsp : 280 ≤ s.sp.toNat)
    (htop : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hr : ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4) :
    WP isa (.block (saveArgs n)) (VG.Proof.Ed25519.Arm.Whole.entered s) (VG.Proof.Ed25519.Arm.Whole.Saved (VG.Proof.Ed25519.Arm.Whole.entered s) n) := by
  have he : (VG.Proof.Ed25519.Arm.Whole.entered s).sp.toNat + 280 + 4 * (n - 4) ≤ 2 ^ 32 := by
    rw [VG.Proof.Ed25519.Arm.Whole.entered_sp, VG.Proof.Ed25519.Arm.Whole.base_top hsp]
    exact htop
  have ha : (⟨State.addr (VG.Proof.Ed25519.Arm.Whole.entered s).sp + 248, 24⟩ : Region) ∈ (VG.Proof.Ed25519.Arm.Whole.entered s).wr := by
    rw [VG.Proof.Ed25519.Arm.Whole.entered_sp, VG.Proof.Ed25519.Arm.Whole.entered_wr hsp]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hsread : ∀ j < n, 4 ≤ j → InRegions ((VG.Proof.Ed25519.Arm.Whole.entered s).rd ++ (VG.Proof.Ed25519.Arm.Whole.entered s).wr)
      (State.addr ((VG.Proof.Ed25519.Arm.Whole.entered s).sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4 := by
    intro j hj h4
    rw [VG.Proof.Ed25519.Arm.Whole.entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc]
    change InRegions _ (State.addr (s.sp - 280#32 + 280#32 + _)) _
    rw [BitVec.sub_add_cancel]
    obtain ⟨r, hR, hC⟩ := hr j hj h4
    refine ⟨r, ?_, hC⟩
    change r ∈ s.rd ++ (VG.Proof.Ed25519.Arm.Whole.entered s).wr
    rw [VG.Proof.Ed25519.Arm.Whole.entered_wr hsp]
    exact List.mem_append.mpr (List.mem_append.mp hR |>.imp id fun h =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
  exact VG.Proof.Ed25519.Arm.Whole.saveArgs_ok n hcount he ha hsread

end VG.Proof.Ed25519.Arm.Whole
end

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def finish (u : State) : State := popped .lr 4 (popped .r12 4 (freed 24 (freed 248 u)))

theorem finish_mem (u : State) : (VG.Proof.Ed25519.Arm.Whole.finish u).mem = u.mem := rfl
theorem finish_sp (u : State) : (VG.Proof.Ed25519.Arm.Whole.finish u).sp = u.sp + 280#32 := by
  change u.sp + 248#32 + 24#32 + 4#32 + 4#32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem finish_gpr (u : State) {r : Reg} (h12 : r ≠ .r12) (hl : r ≠ .lr) :
    (VG.Proof.Ed25519.Arm.Whole.finish u).gpr r = u.gpr r := by
  rw [VG.Proof.Ed25519.Arm.Whole.finish, popped_gpr hl, popped_gpr h12]
  rfl

theorem finish_lr (u : State) :
    (VG.Proof.Ed25519.Arm.Whole.finish u).gpr .lr = u.mem.readW (State.addr (u.sp + 276#32)) 32 := by
  change u.mem.readW (State.addr (u.sp + 248#32 + 24#32 + 4#32)) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem saved_lr {s p : State} {n : Nat} (hsp : 280 ≤ s.sp.toNat) (hp : VG.Proof.Ed25519.Arm.Whole.Saved (VG.Proof.Ed25519.Arm.Whole.entered s) n p) :
    p.mem.readW (State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 276) 32 = s.gpr .lr := by
  rw [hp.frame.readW (r := ⟨State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 276, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rw [VG.Proof.Ed25519.Arm.Whole.entered_mem hsp, Mem.readW_writeW_sep ?_ (by decide)]
    · exact Mem.readW_writeW_self32 _ _ _
    · exact Offset.sep _ (by decide) (by decide) (by decide)
  · rintro r hr
    rw [List.mem_singleton.mp hr, VG.Proof.Ed25519.Arm.Whole.entered_sp]
    exact Offset.disjoint _ (d := 276) (e := 248) (by decide) (by decide) (by decide)

theorem wrap_ok {body : Prog isa} (hn : body.noFrames = true) {s : State} {n : Nat}
    (hcount : n ≤ 6) (hsp : 280 ≤ s.sp.toNat)
    (htop : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hr : ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4)
    (hw : ∀ r ∈ s.wr, (VG.Proof.Ed25519.Arm.Whole.stack s).Disjoint r)
    {P : Mem → Mem → BitVec 32 → Prop}
    (hb : ∀ p, VG.Proof.Ed25519.Arm.Whole.Saved (VG.Proof.Ed25519.Arm.Whole.entered s) n p →
      WP isa body (p.withRegions (VG.Proof.Ed25519.Arm.Whole.bodyRd s) (VG.Proof.Ed25519.Arm.Whole.bodyWr s)) fun u =>
        VG.Proof.Ed25519.Arm.Whole.Ctx (VG.Proof.Ed25519.Arm.Whole.base s) s.gpr p.mem (VG.Proof.Ed25519.Arm.Whole.bodyRd s) s.wr u ∧ P p.mem u.mem (u.gpr .r0)) :
    WP isa (wrap n body) s fun t => abiPreserved s t ∧
      ∃ m, Frame [VG.Proof.Ed25519.Arm.Whole.stack s] s.mem m ∧ P m t.mem (t.gpr .r0) := by
  refine WP.frame (by decide) (by change 4 ≤ s.sp.toNat; omega) (by decide) ?_
  refine WP.frame (by decide) ?_ (by decide) ?_
  · change 4 ≤ (s.sp - 4#32).toNat
    rw [BitVec.toNat_sub_of_le (by change 4 ≤ s.sp.toNat; omega)]
    change 4 ≤ s.sp.toNat - 4
    omega
  · refine WP.alloc (by decide) ?_ ?_
    · change 24 ≤ (s.sp - 4#32 - 4#32).toNat
      rw [BitVec.sub_sub]
      change 24 ≤ (s.sp - 8#32).toNat
      rw [BitVec.toNat_sub_of_le (by change 8 ≤ s.sp.toNat; omega)]
      change 24 ≤ s.sp.toNat - 8
      omega
    · refine WP.alloc (by decide) ?_ ?_
      · change 248 ≤ (s.sp - 4#32 - 4#32 - 24#32).toNat
        simp only [BitVec.sub_sub]
        change 248 ≤ (s.sp - 32#32).toNat
        rw [BitVec.toNat_sub_of_le (by change 32 ≤ s.sp.toNat; omega)]
        change 248 ≤ s.sp.toNat - 32
        omega
      · refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.Whole.enter_save hcount hsp htop hr) fun p hp => ?_)
        refine VG.Proof.Ed25519.Arm.Whole.narrow (hb p hp) ?_ ?_ ?_ hn
        · refine Covers.of_sub fun r hR => ?_
          rw [hp.step.rd, hp.step.wr, VG.Proof.Ed25519.Arm.Whole.entered_wr hsp]
          simp only [VG.Proof.Ed25519.Arm.Whole.bodyRd, VG.Proof.Ed25519.Arm.Whole.bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with (hR | rfl) | (rfl | hR)
          · exact ⟨r, List.mem_append_left _ hR, 0, by simp⟩
          · exact ⟨VG.Proof.Ed25519.Arm.Whole.ARGS (VG.Proof.Ed25519.Arm.Whole.base s), List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp⟩
          · exact ⟨VG.Proof.Ed25519.Arm.Whole.FR (VG.Proof.Ed25519.Arm.Whole.base s), List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
          · exact ⟨r, List.mem_append_right _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR)))), 0, by simp⟩
        · refine Covers.of_sub fun r hR => ?_
          rw [hp.step.wr, VG.Proof.Ed25519.Arm.Whole.entered_wr hsp]
          simp only [VG.Proof.Ed25519.Arm.Whole.bodyWr, List.mem_cons] at hR
          rcases hR with rfl | hR
          · exact ⟨VG.Proof.Ed25519.Arm.Whole.FR (VG.Proof.Ed25519.Arm.Whole.base s), List.mem_cons_self, 0, by simp⟩
          · exact ⟨r, by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR))), 0, by simp⟩
        · intro u _ _ _ _ hbody
          obtain ⟨hc, ho⟩ := hbody
          have lr : u.mem.readW (State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 276) 32 = s.gpr .lr := by
            rw [hc.frame.readW (r := ⟨State.addr (VG.Proof.Ed25519.Arm.Whole.base s) + 276, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
            · exact VG.Proof.Ed25519.Arm.Whole.saved_lr hsp hp
            · intro r hR
              simp only [List.mem_append, List.mem_singleton] at hR
              rcases hR with hR | rfl
              · exact (hw r hR).sub_left (Offset.sub_base _ (by decide : 276 + 4 ≤ 280))
              · exact Offset.disjoint_base _ (by decide) (by decide)
          change abiPreserved s (VG.Proof.Ed25519.Arm.Whole.finish (u.withRegions p.rd p.wr)) ∧ _
          refine ⟨⟨?_, ?_⟩, p.mem, VG.Proof.Ed25519.Arm.Whole.saved_frame hsp hp, ?_⟩
          · intro r hR
            by_cases hl : r = .lr
            · subst r
              rw [VG.Proof.Ed25519.Arm.Whole.finish_lr, State.withRegions_sp, hc.sp,
                addr_add (by have hb := VG.Proof.Ed25519.Arm.Whole.base_top hsp; have hi := s.sp.isLt; omega)]
              exact lr
            · rw [VG.Proof.Ed25519.Arm.Whole.finish_gpr _ (by intro h; subst r; simp [preserved] at hR) hl]
              exact hc.cs r hR hl
          · rw [VG.Proof.Ed25519.Arm.Whole.finish_sp, State.withRegions_sp, hc.sp]
            exact BitVec.sub_add_cancel _ _
          · change P p.mem (VG.Proof.Ed25519.Arm.Whole.finish (u.withRegions p.rd p.wr)).mem
              ((VG.Proof.Ed25519.Arm.Whole.finish (u.withRegions p.rd p.wr)).gpr .r0)
            rw [VG.Proof.Ed25519.Arm.Whole.finish_mem, VG.Proof.Ed25519.Arm.Whole.finish_gpr _ (by decide) (by decide)]
            exact ho

end VG.Proof.Ed25519.Arm.Whole

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem block_cons_ct {i : Instr} {is : List Instr} {P R Q : State → State → Prop}
    (hi : ∀ a b a' b', P a b → exec i a = some a' → exec i b = some b' →
      addrs i a = addrs i b ∧ R a' b')
    (ht : RelCT isa R (.block is) Q) : RelCT isa P (.block (i :: is)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      cases ha : exec i a with
      | none => simp only [execBlock, ha, reduceCtorEq] at ea
      | some u =>
        cases hb : exec i b with
        | none => simp only [execBlock, hb, reduceCtorEq] at eb
        | some v =>
          simp only [execBlock, ha, hb, Option.map_eq_some_iff,
            Prod.exists, Prod.mk.injEq] at ea eb
          obtain ⟨u', tr, eu, rfl, rfl⟩ := ea
          obtain ⟨v', ts, ev, rfl, rfl⟩ := eb
          obtain ⟨he, hr⟩ := hi a b u v hp ha hb
          obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ hr (.block eu) (.block ev)
          exact ⟨by change (addrs i a).map Leak.addr ++ tr = _; rw [he], hq⟩

theorem block_nil_ct {P : State → State → Prop} : RelCT isa P (.block []) P := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at ea eb
      obtain ⟨rfl, rfl⟩ := ea
      obtain ⟨rfl, rfl⟩ := eb
      exact ⟨rfl, hp⟩

theorem block_append_ct {xs ys : List Instr} {P R Q : State → State → Prop}
    (hx : RelCT isa P (.block xs) R) (hy : RelCT isa R (.block ys) Q) :
    RelCT isa P (.block (xs ++ ys)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      rw [VG.execBlock_append] at ea eb
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.exists, Prod.mk.injEq] at ea eb
      obtain ⟨u, tx, ex, v, ty, ey, rfl, rfl⟩ := ea
      obtain ⟨u', tx', ex', v', ty', ey', rfl, rfl⟩ := eb
      obtain ⟨rfl, hr⟩ := hx _ _ _ _ _ _ hp (.block ex) (.block ex')
      obtain ⟨rfl, hq⟩ := hy _ _ _ _ _ _ hr (.block ey) (.block ey')
      exact ⟨rfl, hq⟩

private theorem store_ct (r : Reg) (off : Nat) :
    RelCT isa (fun a b => a.sp = b.sp)
      (.block [.addSp .r12 248, .str r .r12 off]) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    simp only [exec, show 248 < 256 from by decide, ite_true, Option.some.injEq] at ha hb
    subst a' b'
    exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 248) hp⟩
  · apply block_cons_ct (ht := block_nil_ct)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs, hp.2], (exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem saveWord_ct (j : Nat) : RelCT isa (fun a b => a.sp = b.sp)
    (.block (saveWord j)) (fun a b => a.sp = b.sp) := by
  by_cases h : j < 4
  · simp only [saveWord, h, ite_true, List.nil_append]
    exact store_ct _ _
  · simp only [saveWord, h, ite_false, List.cons_append, List.nil_append]
    apply block_cons_ct (ht := store_ct _ _)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs, hp], (exec_sp ha).trans (hp.trans (exec_sp hb).symm)⟩

theorem saveArgs_ct (n : Nat) : RelCT isa (fun a b => a.sp = b.sp)
    (.block (saveArgs n)) (fun a b => a.sp = b.sp) := by
  induction n with
  | zero => exact block_nil_ct
  | succ n ih =>
    simp only [saveArgs, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact block_append_ct ih (saveWord_ct n)

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem step_sp_ct {i : Instr} {is : List Instr}
    (ha : ∀ a b : State, a.sp = b.sp → addrs i a = addrs i b)
    (ht : RelCT isa (fun a b => a.sp = b.sp) (.block is) (fun a b => a.sp = b.sp)) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (i::is)) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (ht := ht)
  intro a b a' b' hp ea eb
  exact ⟨ha a b hp,(exec_sp ea).trans (hp.trans (exec_sp eb).symm)⟩

theorem setArg_ct (r : Reg) (v : Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (setArg r v)) (fun a b => a.sp = b.sp) := by
  cases v with
  | const n => exact step_sp_ct (fun _ _ _ => rfl) block_nil_ct
  | frame d => exact step_sp_ct (fun _ _ _ => rfl) block_nil_ct
  | caller j d =>
    exact step_sp_ct (fun _ _ h => by simp only [addrs,h])
      (step_sp_ct (fun _ _ _ => rfl) block_nil_ct)

theorem addSp_store_ct (j : Nat) :
    RelCT isa (fun a b => a.sp = b.sp)
      (.block [.addSp .r12 (4*j),.str .r0 .r12 0]) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    by_cases h : 4*j < 256
    · simp only [exec,h,ite_true,Option.some.injEq] at ha hb
      subst a' b'
      exact ⟨rfl,hp,congrArg (· + BitVec.ofNat 32 (4*j)) hp⟩
    · simp only [exec,h,ite_false,reduceCtorEq] at ha
  · apply block_cons_ct (ht := block_nil_ct)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs,hp.2],(exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem putArg_ct (j : Nat) (v : Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (putArg j v)) (fun a b => a.sp = b.sp) :=
  block_append_ct (setArg_ct _ _) (addSp_store_ct _)

theorem setupStack_ct (start : Nat) (vs : List Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (setupStack start vs)) (fun a b => a.sp = b.sp) := by
  induction vs generalizing start with
  | nil => exact block_nil_ct
  | cons v vs ih => exact block_append_ct (putArg_ct _ _) (ih _)

theorem setupRegs_ct (args : List (Reg × Value)) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (args.flatMap fun (r,v) => setArg r v))
      (fun a b => a.sp = b.sp) := by
  induction args with
  | nil => exact block_nil_ct
  | cons p ps ih => exact block_append_ct (setArg_ct _ _) ih

theorem setup_ct (args : List (Reg × Value)) (stack : List Value) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (setup args stack)) (fun a b => a.sp = b.sp) :=
  block_append_ct (setupStack_ct _ _) (setupRegs_ct _)

theorem flatMap_sp_ct {α : Type} (xs : List α) (f : α → List Instr)
    (hf : ∀ x ∈ xs, RelCT isa (fun a b => a.sp = b.sp) (.block (f x)) (fun a b => a.sp = b.sp)) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (xs.flatMap f)) (fun a b => a.sp = b.sp) := by
  induction xs with
  | nil => exact block_nil_ct
  | cons x xs ih =>
    exact block_append_ct (hf x List.mem_cons_self) (ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)))

theorem quiet_block_ct (is : List Instr)
    (h : ∀ i ∈ is, ∀ s, addrs i s = []) :
    RelCT isa (fun a b => a.sp = b.sp) (.block is) (fun a b => a.sp = b.sp) := by
  induction is with
  | nil => exact block_nil_ct
  | cons i is ih =>
    exact step_sp_ct (fun a b _ => (h i List.mem_cons_self a).trans (h i List.mem_cons_self b).symm)
      (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

theorem frame_store_ct (d off : Nat) (r : Reg) :
    RelCT isa (fun a b => a.sp = b.sp)
      (.block [.addSp .r12 d,.str r .r12 off]) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    by_cases h : d < 256
    · simp only [exec,h,ite_true,Option.some.injEq] at ha hb
      subst a' b'
      exact ⟨rfl,hp,congrArg (· + BitVec.ofNat 32 d) hp⟩
    · simp only [exec,h,ite_false,reduceCtorEq] at ha
  · apply block_cons_ct (ht := block_nil_ct)
    intro a b a' b' hp ha hb
    exact ⟨by simp only [addrs,hp.2],(exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem zeroWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (zeroWord k)) (fun a b => a.sp = b.sp) := by
  apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
  · intro a b a' b' hp ha hb
    simp only [exec,show 0 < 256 from by decide,ite_true,Option.some.injEq] at ha hb
    subst a' b'
    exact ⟨rfl,hp,congrArg (· + BitVec.ofNat 32 0) hp⟩
  · apply block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
    · intro a b a' b' hp ha hb
      simp only [exec,Option.some.injEq] at ha hb
      subst a' b'
      exact ⟨rfl,hp.1,by simpa only [RegUpd.gpr_setReg,reduceCtorEq,ite_false] using hp.2⟩
    · apply block_cons_ct (ht := block_nil_ct)
      intro a b a' b' hp ha hb
      exact ⟨by simp only [addrs,hp.2],(exec_sp ha).trans (hp.1.trans (exec_sp hb).symm)⟩

theorem zeroWords_ct (start count : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (zeroWords start count)) (fun a b => a.sp = b.sp) :=
  flatMap_sp_ct _ _ (fun _ _ => zeroWord_ct _)

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1,hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.HashPre`. -/
section

/-! Merged from `Proof.Ed25519.Arm.Whole.Hash`. -/
section
namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Sha512.Arm.Stream

private theorem rounds_noFrames (n : Nat) : (Impl.Sha512.Arm.rounds n).noFrames = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Impl.Sha512.Arm.rounds, Code.noFrames, ih, Bool.and_self]

theorem update_noFrames : update.noFrames = true := by
  simp only [update, Impl.MdStream.Arm.update, Impl.MdStream.Arm.updateBody, Impl.MdStream.Arm.fill,
    Impl.MdStream.Arm.compressN, Impl.MdStream.Arm.compressWith,
    Impl.Sha512.Arm.compress, Impl.Sha512.Arm.body, Code.noFrames, Bool.and_self]
  rw [rounds_noFrames]; rfl

theorem finalize_noFrames : finalize.noFrames = true := by
  simp only [finalize, Impl.MdStream.Arm.finalize, Impl.MdStream.Arm.finalizeBody,
    Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith,
    Impl.Sha512.Arm.compress, Impl.Sha512.Arm.body, Code.noFrames, Bool.and_self]
  rw [rounds_noFrames]; rfl

variable {E : BitVec 32} {g : Reg → BitVec 32}
  {m₀ : Mem} {rd wr : List Region} {t : State}

theorem init_call (hc : Ctx E g m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : (Proof.Sha512.initArm Spec.Sha512.H0_512).pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr : BitVec 32} (ha : t.gpr .r0 = scr) :
    WP isa (.call Spec.Sha512.init512Api.name (init Spec.Sha512.H0_512)) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr scr) [] := by
  refine call_ok hc (Proof.Sha512.Arm.Stream.init_verified _).1 rfl hp hcov hw
    fun u hu hf hpost => ⟨hu,hf,?_⟩
  change Spec.Sha512.Repr _ u.mem (State.addr (t.callEntry.gpr .r0)) [] at hpost
  rw [State.callEntry_gpr _ (by decide),ha] at hpost
  exact hpost

theorem update_call (hc : Ctx E g m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.updateArm.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr p len : BitVec 32} {prev : List Byte}
    (h0 : t.gpr .r0 = scr) (hdata : stackArg t 0 = p) (hlen : stackArg t 1 = len)
    (hcount : Proof.Sha512.countArm t = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr scr) prev) :
    WP isa (.call Spec.Sha512.updateScratchApi.name update) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr scr)
        (prev ++ Spec.Ed25519.bytesAt t.mem (State.addr p) len.toNat) := by
  refine call_ok hc Proof.Sha512.Arm.Stream.Update.update_verified.1 update_noFrames hp hcov hw
    fun u hu hf hpost => ⟨hu,hf,?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .r0 = scr := by
    rw [State.withRegions_gpr,State.callEntry_gpr _ (by decide),h0]
  have hcount' : Proof.Sha512.countArm (t.callEntry.withRegions rd' wr') = BitVec.ofNat 64 prev.length := by
    simpa only [Proof.Sha512.countArm,State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] using hcount
  have hh := hpost Spec.Sha512.H0_512 prev (by rw [h0']; exact hr) hcount'
  change Spec.Sha512.Repr _ u.mem (State.addr (t.callEntry.gpr .r0))
    (prev ++ Spec.Ed25519.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat) at hh
  rw [State.callEntry_gpr _ (by decide),h0,hdata,hlen] at hh
  exact hh

theorem finalize_call (hc : Ctx E g m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr out : BitVec 32} {msg : List Byte}
    (h0 : t.gpr .r0 = scr) (hout : stackArg t 0 = out)
    (hcount : Proof.Sha512.countArm t = BitVec.ofNat 64 msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr scr) msg) (hlen : msg.length < 2^64) :
    WP isa (.call Spec.Sha512.finalizeScratchApi.name finalize) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Ed25519.bytesAt u.mem (State.addr out) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  refine call_ok hc Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1 finalize_noFrames hp hcov hw
    fun u hu hf hpost => ⟨hu,hf,?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .r0 = scr := by
    rw [State.withRegions_gpr,State.callEntry_gpr _ (by decide),h0]
  have hcount' : Proof.Sha512.countArm (t.callEntry.withRegions rd' wr') = BitVec.ofNat 64 msg.length := by
    simpa only [Proof.Sha512.countArm,State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] using hcount
  have hh := hpost Spec.Sha512.H0_512 msg (by rw [h0']; exact hr) hlen hcount'
  change Spec.Ed25519.bytesAt u.mem (State.addr (stackArg t 0)) 64 = _ at hh
  rw [hout] at hh
  exact hh

end VG.Proof.Ed25519.Arm.Whole
end

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm

abbrev SHA (scr : BitVec 32) : Region := ⟨State.addr scr,192⟩
abbrev WORK (scr : BitVec 32) : Region := ⟨State.addr scr+192,272⟩
abbrev CALLARGS (E : BitVec 32) (n : Nat) : Region := ⟨State.addr E,n⟩
def initWr (scr : BitVec 32) : List Region := [SHA scr]
def updateRd (E p len : BitVec 32) : List Region := [⟨State.addr p,len.toNat⟩,CALLARGS E 12]
def hashWr (scr : BitVec 32) : List Region := [SHA scr,WORK scr]
def finalizeRd (E : BitVec 32) : List Region := [CALLARGS E 8]
def finalizeWr (scr out : BitVec 32) : List Region := [SHA scr,⟨State.addr out,64⟩,WORK scr]

theorem sha_sub (scr : BitVec 32) : Region.Sub (SHA scr) ⟨State.addr scr,8192⟩ := Region.sub_prefix (by decide)
theorem work_sub (scr : BitVec 32) : Region.Sub (WORK scr) ⟨State.addr scr,8192⟩ := Offset.sub_base _ (by decide)
theorem sha_work (scr : BitVec 32) : (SHA scr).Disjoint (WORK scr) := Offset.base_disjoint _ (by decide) (by decide)

theorem init_pre {t : State} {scr : BitVec 32} (ha : t.gpr .r0 = scr)
    (hn : scr.toNat+8192 ≤ 2^32) :
    (Proof.Sha512.initArm Spec.Sha512.H0_512).pre (t.callEntry.withRegions [] (initWr scr)) := by
  simp only [Proof.Sha512.initArm,State.withRegions_rd,State.withRegions_wr,
    State.withRegions_gpr,State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),ha]
  exact ⟨True.intro,rfl,by omega⟩

theorem update_pre {t : State} {E scr p len : BitVec 32}
    (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (hdp : stackArg t 0 = p) (hl : stackArg t 1 = len) (hw : stackArg t 2 = scr+192)
    (hd : Region.Disjoint ⟨State.addr p,len.toNat⟩ ⟨State.addr scr,8192⟩)
    (hs : (CALLARGS E 12).Disjoint ⟨State.addr scr,8192⟩)
    (nc : scr.toNat+8192 ≤ 2^32) (np : p.toNat+len.toNat ≤ 2^32) (ne : E.toNat+12 ≤ 2^32) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) := by
  have ac : State.addr (scr+192) = State.addr scr+192 := addr_add (k := 192) (by omega)
  have wc : (scr+192).toNat+272 ≤ 2^32 := by
    rw [BitVec.toNat_add_of_lt (by change scr.toNat+192<2^32; omega)]
    change scr.toNat+192+272≤2^32
    omega
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) 0 = State.addr t.sp := by simp [stackArgAddr,State.withRegions_sp,State.callEntry_sp]
  simp only [Proof.Sha512.updateArm,sa,spa,State.withRegions_rd,State.withRegions_wr,
    State.withRegions_gpr,State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),h0,
    State.withRegions_sp,State.callEntry_sp]
  rw [hdp,hl,hw,he,ac]
  exact ⟨rfl,rfl,sha_work scr,hd.sub_right (sha_sub scr),hd.sub_right (work_sub scr),
    hs.sub_right (sha_sub scr),hs.sub_right (work_sub scr),by omega,np,wc,ne⟩

theorem finalize_pre {t : State} {E scr out : BitVec 32}
    (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (ho : stackArg t 0 = out) (hw : stackArg t 1 = scr+192)
    (hd : Region.Disjoint ⟨State.addr out,64⟩ ⟨State.addr scr,8192⟩)
    (hs : (CALLARGS E 8).Disjoint ⟨State.addr scr,8192⟩)
    (hso : (CALLARGS E 8).Disjoint ⟨State.addr out,64⟩)
    (nc : scr.toNat+8192 ≤ 2^32) (no : out.toNat+64 ≤ 2^32) (ne : E.toNat+8 ≤ 2^32) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) := by
  have ac : State.addr (scr+192) = State.addr scr+192 := addr_add (k := 192) (by omega)
  have wc : (scr+192).toNat+272 ≤ 2^32 := by
    rw [BitVec.toNat_add_of_lt (by change scr.toNat+192<2^32; omega)]
    change scr.toNat+192+272≤2^32
    omega
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) 0 = State.addr t.sp := by simp [stackArgAddr,State.withRegions_sp,State.callEntry_sp]
  simp only [Proof.Sha512.finalizeArm,sa,spa,State.withRegions_rd,State.withRegions_wr,
    State.withRegions_gpr,State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),h0,
    State.withRegions_sp,State.callEntry_sp]
  rw [ho,hw,he,ac]
  exact ⟨rfl,rfl,(hd.sub_right (sha_sub scr)).symm,sha_work scr,hd.sub_right (work_sub scr),
    hs.sub_right (sha_sub scr),hso,hs.sub_right (work_sub scr),by omega,no,wc,ne⟩

/-- Hash calls only write prefixes of the outer scratch allocation. -/
theorem hash_writes {E scr : BitVec 32} {wr : List Region} (hs : (⟨State.addr scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ hashWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  simp only [hashWr,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_,hs,0,(BitVec.add_zero _).symm,by change 0+192≤8192; decide⟩
  · exact .inr ⟨_,hs,192,rfl,by change 192+272≤8192; decide⟩

theorem init_writes {E scr : BitVec 32} {wr : List Region} (hs : (⟨State.addr scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ initWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨_,hs,0,(BitVec.add_zero _).symm,by change 0+192≤8192; decide⟩

theorem covers_writes {E : BitVec 32} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, Within r (FR E) ∨ ∃ R ∈ wr, Within r R) : Covers ws (rd++FR E::wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R,hR,hs⟩
  · exact ⟨FR E,List.mem_append_right _ List.mem_cons_self,hf⟩
  · exact ⟨R,List.mem_append_right _ (List.mem_cons_of_mem _ hR),hs⟩

end VG.Proof.Ed25519.Arm.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT`. -/
section

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

/-- Relational rule for a register-saving frame. -/
theorem frame_ct {r r' : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed [r] s ∧ b = pushed [r] t) body R) :
    RelCT isa P (.frame (.push [r]) body (.pop r' 4)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have push_eq : ∀ {a b : State}, isa.push (.push [r]) a = some b → b = pushed [r] a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := push_eq ps
      have eb := push_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      have sp₁ := (Exec.rdwr bs).2.2
      have sp₂ := (Exec.rdwr bt).2.2
      have he := hsp s t hp
      refine ⟨?_, trivial⟩
      simp only [addrs, sp₁, sp₂, pushed, he]

/-- Allocating and freeing a buffer emits no data-address leakage. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- The trace from wider permissions is determined by any terminating
execution with the narrowed body permissions. -/
theorem body_trace {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (hb : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    {trace : List Leak} {t : State} (he : Exec isa c s trace t) :
    ∃ u, Exec isa c (s.withRegions rd wr) trace u := by
  obtain ⟨tr, u, hu, _⟩ := hb
  have hw' := Exec.widen hu (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, _⟩ := Exec.det he hw'
  exact ⟨_, hu⟩

theorem saved_covers {s p : State} {n : Nat} (hsp : 280 ≤ s.sp.toNat) (hp : Saved (entered s) n p) :
    Covers (bodyRd s ++ bodyWr s) (p.rd ++ p.wr) ∧ Covers (bodyWr s) p.wr := by
  constructor
  · refine Covers.of_sub fun r hR => ?_
    rw [hp.step.rd, hp.step.wr, entered_wr hsp]
    simp only [bodyRd, bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with (hR | rfl) | (rfl | hR)
    · exact ⟨r, List.mem_append_left _ hR, 0, by simp⟩
    · exact ⟨ARGS (base s), List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp⟩
    · exact ⟨FR (base s), List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
    · exact ⟨r, List.mem_append_right _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR)))), 0, by simp⟩
  · refine Covers.of_sub fun r hR => ?_
    rw [hp.step.wr, entered_wr hsp]
    simp only [bodyWr, List.mem_cons] at hR
    rcases hR with rfl | hR
    · exact ⟨FR (base s), List.mem_cons_self, 0, by simp⟩
    · exact ⟨r, by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR))), 0, by simp⟩

/-- The saved-argument prologue and all four frames preserve body constant time. -/
theorem wrap_ct {body : Prog isa} {n : Nat} {Pre : State → Prop} {Pub : State → State → Prop}
    (hn : n ≤ 6) (hsp : ∀ s t, Pub s t → s.sp = t.sp)
    (hstack : ∀ s, Pre s → 280 ≤ s.sp.toNat)
    (htop : ∀ s, Pre s → s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hread : ∀ s, Pre s → ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4)
    (hb : ∀ s, Pre s → ∀ p, Saved (entered s) n p →
      WP isa body (p.withRegions (bodyRd s) (bodyWr s)) (fun _ => True))
    (hct : ∀ s t, Pre s → Pre t → Pub s t → RelCT isa
      (fun a b => ∃ p q, Saved (entered s) n p ∧ Saved (entered t) n q ∧
        a = p.withRegions (bodyRd s) (bodyWr s) ∧ b = q.withRegions (bodyRd t) (bodyWr t))
      body (fun _ _ => True)) : ConstantTime isa Pre Pub (wrap n body) := by
  apply RelCT.constantTime
  refine frame_ct (fun s t h => hsp s t h.2.2) (frame_ct ?_ (alloc_ct (alloc_ct (R := fun _ _ => True) ?_)))
  · rintro a b ⟨s, t, ⟨_, _, hp⟩, rfl, rfl⟩
    exact congrArg (fun x => x - BitVec.ofNat 32 4) (hsp s t hp)
  · rintro a b ta tb a' b'
      ⟨p, q, ⟨p', q', ⟨p'', q'', ⟨s, t, ⟨ps, pt, pub⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩ ea eb
    cases ea with
    | seq esa eba =>
      cases eb with
      | seq esb ebb =>
        obtain ⟨_, pa, exa, hpa⟩ := enter_save hn (hstack s ps) (htop s ps) (hread s ps)
        obtain ⟨_, pb, exb, hpb⟩ := enter_save hn (hstack t pt) (htop t pt) (hread t pt)
        obtain ⟨_, rfl⟩ := Exec.det esa exa
        obtain ⟨_, rfl⟩ := Exec.det esb exb
        have trsave := (saveArgs_ct n _ _ _ _ _ _ (by
          change (entered s).sp = (entered t).sp
          rw [entered_sp, entered_sp]
          exact congrArg (fun x : BitVec 32 => x - 280) (hsp s t pub)) esa esb).1
        obtain ⟨ua, eua⟩ := body_trace (hb s ps _ hpa)
          (saved_covers (hstack s ps) hpa).1 (saved_covers (hstack s ps) hpa).2 eba
        obtain ⟨ub, eub⟩ := body_trace (hb t pt _ hpb)
          (saved_covers (hstack t pt) hpb).1 (saved_covers (hstack t pt) hpb).2 ebb
        have trbody := (hct s t ps pt pub _ _ _ _ _ _ ⟨_, _, hpa, hpb, rfl, rfl⟩ eua eub).1
        exact ⟨by rw [trsave, trbody], trivial⟩

end VG.Proof.Ed25519.Arm.Whole

end
