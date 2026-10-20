module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsFinish
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsStep
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsLoop
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Exact-domain recognition compares public bytes on a public table schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

theorem compare_ct : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9 ∧
    s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r10 = t.gpr .r10) VG.Impl.Ffdh.Arm.VettedGroups.compare (fun _ _ => True) := by
  have args : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r10 = t.gpr .r10) (.block compareArgs)
      (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .lr = t.gpr .lr) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing : RelCT isa (fun _ _ => True) (.block compareArgs) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _; exact Taint.agree_ofRegs (by simp)
    obtain ⟨_, u', eu, ⟨u0,u1,ul,_,_⟩,_⟩ := compareArgs_ok s
    obtain ⟨_, v', ev, ⟨v0,v1,vl,_,_⟩,_⟩ := compareArgs_ok t
    obtain ⟨-,rfl⟩ := Exec.det e1 eu
    obtain ⟨-,rfl⟩ := Exec.det e2 ev
    exact ⟨(timing _ _ _ _ _ _ trivial e1 e2).1,
      u0.trans (h.1.trans v0.symm), u1.trans (h.2.1.trans v1.symm), ul.trans (h.2.2.trans vl.symm)⟩
  exact args.seq (fun s t tr1 tr2 u v h e1 e2 => ⟨compareBytes_ct _ _ _ _ _ _ trivial trivial h e1 e2, trivial⟩)

theorem finish_ct : RelCT isa (fun s t => (s.gpr .r2 = 0 ↔ t.gpr .r2 = 0)) finish (fun _ _ => True) := by
  have test : RelCT isa (fun s t => (s.gpr .r2 = 0 ↔ t.gpr .r2 = 0))
      (.block [.cmp .r2 (.imm 0)]) (fun s t => s.z = t.z) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨_,u',eu,⟨zu,_⟩,_⟩ := zero_test s .r2
    obtain ⟨_,v',ev,⟨zv,_⟩,_⟩ := zero_test t .r2
    obtain ⟨-,rfl⟩ := Exec.det e1 eu
    obtain ⟨-,rfl⟩ := Exec.det e2 ev
    have timing : RelCT isa (fun _ _ => True) (.block [.cmp .r2 (.imm 0)]) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _; exact Taint.agree_ofRegs (by simp)
    refine ⟨(timing _ _ _ _ _ _ trivial e1 e2).1, ?_⟩
    change u.z = v.z
    rw [zu,zv]
    exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using h)
  have branch : RelCT isa (fun s t => s.z = t.z) (.ite .eq (.block matched) (.block next)) (fun _ _ => True) := by
    apply RelCT.ite (fun _ _ h => by simp only [eval,h])
    · exact (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  have last : RelCT isa (fun _ _ => True) (.block [.cmp .r7 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact test.seq (branch.seq last)

abbrev ScanReady (table src : BitVec 32) (k : Nat) (dom : List Byte) (gs : List Group) (s : State) : Prop :=
  Source src k dom s ∧ TableAt table gs s ∧ Cursor table src k dom gs s

theorem step_ct {table src : BitVec 32} {k : Nat} {dom : List Byte} {g : Group} {gs : List Group}
    (kfit : k < 2 ^ 32) :
    RelCT isa (fun s t => ScanReady table src k dom (g::gs) s ∧ ScanReady table src k dom (g::gs) t)
      step (fun _ _ => True) := by
  let H := fun s : State => Source src k dom s ∧ RecordAt table g s ∧
    s.gpr .r4 = table + 8 ∧ s.gpr .r9 = src ∧ s.gpr .r10 = BitVec.ofNat 32 dom.length ∧
    s.z = decide (g.len = k) ∧ s.gpr .r2 = 1
  have headerPost (s : State) (h : ScanReady table src k dom (g::gs) s) : WP isa (.block header) s H := by
    refine WP.mono (header_ok s h.2.1.1 h.2.2.ptr h.2.2.width kfit) ?_
    rintro u ⟨⟨ptr,_,_,one,zero,mem⟩,rest⟩
    exact ⟨h.1.after mem rest, h.2.1.1.after mem rest, ptr,
      (rest.gpr .r9 (by simp)).trans h.2.2.source, (rest.gpr .r10 (by simp)).trans h.2.2.length,zero,one⟩
  have headerCT : RelCT isa (fun s t => ScanReady table src k dom (g::gs) s ∧ ScanReady table src k dom (g::gs) t)
      (.block header) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.2.2.ptr.trans h.2.2.2.ptr.symm)
  have branchPost (s : State) (h : H s) : WP isa (.ite .eq VG.Impl.Ffdh.Arm.VettedGroups.compare (.block [])) s
      (fun u => u.gpr .r2 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) := by
    refine WP.ite (decide (g.len = k)) (by simp only [eval,h.2.2.2.2.2.1]) ?_ ?_
    · intro yes
      have same := of_decide_eq_true yes
      exact WP.mono (compare_ok s h.1 h.2.1 same h.2.2.2.1 h.2.2.1 h.2.2.2.2.1)
        (fun _ out => by simpa only [same,true_and] using out.1)
    · intro no
      refine WP.block_nil ?_
      rw [h.2.2.2.2.2.2]
      simp only [show (1:BitVec 32) ≠ 0 by decide,false_iff]
      exact fun hit => of_decide_eq_false no hit.1
  have branchCT : RelCT isa (fun s t => H s ∧ H t) (.ite .eq VG.Impl.Ffdh.Arm.VettedGroups.compare (.block [])) (fun _ _ => True) := by
    apply RelCT.ite (fun _ _ h => by simp only [eval,h.1.2.2.2.2.2.1,h.2.2.2.2.2.2.1])
    · exact compare_ct.mono (fun _ _ h => ⟨h.1.1.2.2.2.1.trans h.1.2.2.2.2.1.symm,
        h.1.1.2.2.1.trans h.1.2.2.2.1.symm, h.1.1.2.2.2.2.1.trans h.1.2.2.2.2.2.1.symm⟩) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ _ => trivial)
  unfold step
  exact ((headerCT.wp (fun s t h => ⟨headerPost s h.1,headerPost t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1,h.2.2⟩)).seq
    (((branchCT.wp (fun s t h => ⟨branchPost s h.1,branchPost t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2.1.trans h.2.2.symm)).seq finish_ct)



theorem loop_ct {table src : BitVec 32} {k : Nat} {dom : List Byte} {gs : List Group}
    (positive : gs ≠ []) (kfit : k < 2 ^ 32) (fits : gs.length < 2 ^ 32) :
    RelCT isa (fun s t => ScanReady table src k dom gs s ∧ ScanReady table src k dom gs t)
      loop (fun _ _ => True) := by
  let I := fun n (s t : State) => ∃ (table : BitVec 32) (g : Group) (gs : List Group),
    (g :: gs).length = n ∧ n < 2 ^ 32 ∧
      ScanReady table src k dom (g :: gs) s ∧ ScanReady table src k dom (g :: gs) t
  have body (n : Nat) : RelCT isa (I n) step fun s t =>
      eval .ne s = eval .ne t ∧ (eval .ne s = some false → True) ∧
      (eval .ne s = some true → ∃ m < n, I m s t) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨table, g, gs, size, fit, hs, ht⟩ := h
    have nextFit : gs.length < 2 ^ 32 := by simp only [List.length_cons] at size; omega
    have timing := step_ct kfit s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    obtain ⟨_, u', eu, memU, resultU, restU⟩ := step_ok s hs.1 hs.2.1.1 hs.2.2 kfit nextFit
    obtain ⟨_, v', ev, memV, resultV, restV⟩ := step_ok t ht.1 ht.2.1.1 ht.2.2 kfit nextFit
    obtain ⟨_, rfl⟩ := Exec.det e1 eu
    obtain ⟨_, rfl⟩ := Exec.det e2 ev
    by_cases hit : g.len = k ∧ dom = g.domain.take dom.length
    · rw [ite_eq_left hit] at resultU resultV
      have exitU : eval .ne u = some false := by simp only [eval, resultU.2.2, Bool.not_true]
      have exitV : eval .ne v = some false := by simp only [eval, resultV.2.2, Bool.not_true]
      exact ⟨timing.1, exitU.trans exitV.symm, fun _ => trivial,
        fun impossible => by rw [exitU] at impossible; cases impossible⟩
    · rw [ite_eq_right hit] at resultU resultV
      by_cases last : gs = []
      · subst gs
        have exitU : eval .ne u = some false := by simp only [eval, resultU.2.2.2, List.length_nil, decide_true, Bool.not_true]
        have exitV : eval .ne v = some false := by simp only [eval, resultV.2.2.2, List.length_nil, decide_true, Bool.not_true]
        exact ⟨timing.1, exitU.trans exitV.symm, fun _ => trivial,
          fun impossible => by rw [exitU] at impossible; cases impossible⟩
      · have nonzero : gs.length ≠ 0 := by intro eq; exact last (List.eq_nil_of_length_eq_zero eq)
        have continueU : eval .ne u = some true := by simp only [eval, resultU.2.2.2, nonzero, decide_false, Bool.not_false]
        have continueV : eval .ne v = some true := by simp only [eval, resultV.2.2.2, nonzero, decide_false, Bool.not_false]
        have readyU : ScanReady (table + BitVec.ofNat 32 (8 + 3 * g.len)) src k dom gs u :=
          ⟨hs.1.after memU restU, hs.2.1.2.after memU restU,
            ⟨resultU.2.1, resultU.2.2.1,
              (restU.gpr .r6 (by simp [clobbers])).trans hs.2.2.width,
              (restU.gpr .r9 (by simp [clobbers])).trans hs.2.2.source,
              (restU.gpr .r10 (by simp [clobbers])).trans hs.2.2.length⟩⟩
        have readyV : ScanReady (table + BitVec.ofNat 32 (8 + 3 * g.len)) src k dom gs v :=
          ⟨ht.1.after memV restV, ht.2.1.2.after memV restV,
            ⟨resultV.2.1, resultV.2.2.1,
              (restV.gpr .r6 (by simp [clobbers])).trans ht.2.2.width,
              (restV.gpr .r9 (by simp [clobbers])).trans ht.2.2.source,
              (restV.gpr .r10 (by simp [clobbers])).trans ht.2.2.length⟩⟩
        refine ⟨timing.1, continueU.trans continueV.symm, fun _ => trivial, fun _ => ?_⟩
        cases gs with
        | nil => exact False.elim (last rfl)
        | cons g' gs' => exact ⟨(g'::gs').length, by simp only [List.length_cons] at size ⊢; omega,
            _, g', gs', rfl, nextFit, readyU, readyV⟩
  have start : ∀ s t, ScanReady table src k dom gs s ∧ ScanReady table src k dom gs t → I gs.length s t := by
    intro s t h
    cases gs with
    | nil => exact False.elim (positive rfl)
    | cons g gs => exact ⟨table, g, gs, rfl, fits, h⟩
  exact (RelCT.loop I body gs.length).mono start (fun _ _ h => h)



theorem entry_ct : RelCT isa (fun s t => s.sp = t.sp) (.block entry) (fun _ _ => True) := by
  have pureHead : RelCT isa (fun _ _ => True) (.block [.mov .r8 (.reg .r0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  have head := relCT_keep_sp (pureHead.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun _ _ h => h)
  have tail : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.adrSym .r4 tableSym, .mov .r7 (.imm 10)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (head.seq (RelCT.block_append
    ((stackLoads_ct [(.r9,24),(.r10,28),(.r6,32)]).seq tail)))

theorem code_ct {p : Inputs} {slots : List Nat}
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ environment.holds p s) ∧
      (Context p slots t ∧ environment.holds p t) ∧ s.sp = t.sp ∧ environment.publicRel s t)
      code (fun _ _ => True) := by
  let P := fun s t : State => (Context p slots s ∧ environment.holds p s) ∧
    (Context p slots t ∧ environment.holds p t) ∧ s.sp = t.sp ∧ environment.publicRel s t
  let Q := fun s t : State => ∃ table, ScanReady table p.domain p.k p.dom groups s ∧
    ScanReady table p.domain p.k p.dom groups t
  have stage : RelCT isa P (.block entry) Q := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := entry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, ⟨cu,_,mu⟩,ru⟩ := entry_ok s h.1.1 h24 h28 h32
    obtain ⟨_, v', ev, ⟨cv,_,mv⟩,rv⟩ := entry_ok t h.2.1.1 h24 h28 h32
    obtain ⟨_,rfl⟩ := Exec.det e1 eu
    obtain ⟨_,rfl⟩ := Exec.det e2 ev
    have source (a b : State) (context : Context p slots a)
        (mem : b.mem = a.mem) (rest : VG.Proof.X25519.Arm.Rest [.r4,.r6,.r7,.r8,.r9,.r10] a b) :
        Source p.domain p.k p.dom b :=
      ⟨by rw [p.domainLength]; split <;> have := p.minLength <;> omega,
        context.domain.fits, by rw [rest.rd,rest.wr]; exact context.domain.readable,
        by rw [mem]; exact context.domain.bytes, by rw [p.domainLength]; split <;> simp⟩
    have tabU := h.1.2.1.after mu ru
    have tabV := h.2.1.2.1.after mv rv
    have symbol : s.syms tableSym = t.syms tableSym := h.2.2.2
    rw [← symbol] at tabV cv
    exact ⟨timing.1, s.syms tableSym,
      ⟨source s u h.1.1 mu ru, tabU, cu⟩, ⟨source t v h.2.1.1 mv rv, tabV, cv⟩⟩
  have scanning : RelCT isa Q loop (fun _ _ => True) := by
    apply RelCT.exists_
    intro table
    exact loop_ct (by decide) (by have := p.maxLength; omega) (by decide)
  have restore : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r8)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact stage.seq (scanning.seq restore)

end VG.Proof.Ffdh.Arm.VettedGroups
