module

public import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Frag
public import VerifiedGarbage.Proof.MlKem.Arm.HashCT
public import VerifiedGarbage.Proof.MlKem.Arm.CallF
public import VerifiedGarbage.Proof.MlKem.Arm.Prims
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.Arm.Calls

/-! ### `MlDsa.Arm.KeyGen.Base`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: the primitives, and calling them

Key generation and verification are proven for any implementations of the
primitives they call that are verified against their contracts with at most
`S` bytes of stack, and whose frames use at most `S` bytes (`Callee`).

A call is the moves of its arguments (`glue`, which computes `glueSt`), then
the call (`callV`), or, with a fifth argument on the stack, the call in a
frame that pushes it (`callVS`): from the callee's precondition on entry, it
changes only the callee's writable buffers and the stack below the stack
pointer (`Kept`, as ML-KEM's), and the callee's postcondition holds. Two runs
of a call leak the same if the callee's preconditions hold and its public
data agree (`callV_tr`, `callVS_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen

/-! ## The primitives -/

/-- Code `c` verified against the contract `k stk` of some stack `stk ≤ S`,
whose frames use at most `S` bytes of stack. -/
structure Callee (c : Prog isa) (k : Nat → Contract isa) (S : Nat) : Prop where
  verified : ∃ stk, stk ≤ S ∧ Verified Arm.target c (k stk)
  stack : stackUse c ≤ S

/-! ## Moves -/

theorem ldc_eq (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_zero]
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega_using [])]
  omega_using []

theorem setReg_setReg (s : State) (d : Reg) (x y : BitVec 32) : (s.setReg d x).setReg d y = s.setReg d y := by
  simp only [State.setReg]
  congr 1
  funext r
  split <;> rfl

theorem ldc_ok (d : Reg) (v : Nat) (s : State) :
    WP isa (.block (ldc d v)) s (· = s.setReg d (BitVec.ofNat 32 v)) := by
  apply WP.of_runBlock
  simp only [ldc, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Option.some.injEq, exists_eq_left',
    gpr_setReg_self, setReg_setReg, ldc_eq]

/-- The value of an argument. -/
def argVal (s : State) : Arg → BitVec 32
  | .ptr p => s.gpr p.1 + BitVec.ofNat 32 p.2
  | .imm v => BitVec.ofNat 32 v

/-- An argument whose pointer, if any, is in a callee-saved register. -/
def argOk : Arg → Bool
  | .ptr p => p.1 == .r4 || p.1 == .r5 || p.1 == .r6 || p.1 == .r7
  | .imm _ => true

theorem arg_ok (d : Reg) (a : Arg) (h : ∀ p : Ptr, a = .ptr p → p.1 ≠ d) (s : State) :
    WP isa (.block (a.instrs d)) s (· = s.setReg d (argVal s a)) := by
  cases a with
  | ptr p =>
    have hb := h p rfl
    apply WP.of_runBlock
    simp only [Arg.instrs, argVal, ldc, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, isa, exec, Op2.eval, Option.map_some, Option.some.injEq, exists_eq_left', gpr_setReg_self,
      setReg_setReg, ldc_eq, gpr_setReg_of_ne _ _ hb]
  | imm v => exact ldc_ok d v s

/-- The state after the moves of the arguments `as`. -/
def glueSt (s : State) : List (Reg × Arg) → State
  | [] => s
  | (d, a) :: as => glueSt (s.setReg d (argVal s a)) as

/-- The moves of arguments into `r0`–`r3` and `r12`, of pointers in `r4`–`r7`. -/
def glueOk (as : List (Reg × Arg)) : Bool :=
  as.all fun x => (x.1 == .r0 || x.1 == .r1 || x.1 == .r2 || x.1 == .r3 || x.1 == .r12) && argOk x.2

theorem glue_ok : ∀ {as : List (Reg × Arg)}, glueOk as = true → ∀ s, WP isa (.block (glue as)) s (· = glueSt s as)
  | [], _, s => WP.block_nil rfl
  | (d, a) :: as, h, s => by
    simp only [glueOk, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨⟨hd, ha⟩, hs⟩ := h
    rw [glue, WP.block_append_iff]
    refine WP.mono (arg_ok d a (fun p e => ?_) s) fun s1 e1 => ?_
    · subst e
      simp only [argOk, Bool.or_eq_true, beq_iff_eq] at ha hd
      intro e; subst e
      rcases ha with ((h | h) | h) | h <;> rw [h] at hd <;> simp at hd
    · subst e1
      exact glue_ok (as := as) hs _

theorem glueSt_mem (s : State) : ∀ as, (glueSt s as).mem = s.mem
  | [] => rfl
  | _ :: as => glueSt_mem _ as
theorem glueSt_rd (s : State) : ∀ as, (glueSt s as).rd = s.rd
  | [] => rfl
  | _ :: as => glueSt_rd _ as
theorem glueSt_wr (s : State) : ∀ as, (glueSt s as).wr = s.wr
  | [] => rfl
  | _ :: as => glueSt_wr _ as
theorem glueSt_sp (s : State) : ∀ as, (glueSt s as).sp = s.sp
  | [] => rfl
  | _ :: as => glueSt_sp _ as

/-- The registers the moves do not write. -/
theorem glueSt_gpr {r : Reg} (hr : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12) :
    ∀ (s : State) {as : List (Reg × Arg)}, glueOk as = true → (glueSt s as).gpr r = s.gpr r
  | s, [], _ => rfl
  | s, (d, a) :: as, h => by
    simp only [glueOk, List.all_cons, Bool.and_eq_true] at h
    rw [glueSt, glueSt_gpr hr _ (as := as) h.2, gpr_setReg_of_ne]
    intro e; subst e
    obtain ⟨⟨hd, -⟩, -⟩ := h
    simp only [Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with (((h | h) | h) | h) | h <;> simp_all

theorem glueSt_pres (s : State) {as : List (Reg × Arg)} (h : glueOk as = true) :
    ∀ r ∈ preserved, (glueSt s as).gpr r = s.gpr r := fun r hr =>
  glueSt_gpr (by revert r; decide) s h

theorem glue_append : ∀ as bs : List (Reg × Arg), glue (as ++ bs) = glue as ++ glue bs
  | [], _ => rfl
  | (d, a) :: as, bs => by rw [List.cons_append, glue, glue, glue_append as bs, List.append_assoc]

theorem glue_noMem : ∀ as : List (Reg × Arg), (glue as).all noMem = true
  | [] => rfl
  | (d, a) :: as => by
    rw [glue, List.all_append, glue_noMem as, Bool.and_true]
    cases a <;> rfl

/-- The registers the moves of `as` do not write. -/
theorem glueSt_gpr' {r : Reg} : ∀ (s : State) {as : List (Reg × Arg)}, r ∉ as.map Prod.fst →
    (glueSt s as).gpr r = s.gpr r
  | s, [], _ => rfl
  | s, (d, a) :: as, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [glueSt, glueSt_gpr' _ h.2, gpr_setReg_of_ne _ _ h.1]

/-- An argument's register holds its value after the moves. -/
theorem glueSt_arg (s : State) {d : Reg} {a : Arg} :
    ∀ {as : List (Reg × Arg)}, glueOk as = true → (as.map Prod.fst).Nodup → (d, a) ∈ as →
      (glueSt s as).gpr d = argVal s a
  | [], _, _, hm => absurd hm List.not_mem_nil
  | (d', a') :: as, hg, hn, hm => by
    simp only [glueOk, List.all_cons, Bool.and_eq_true] at hg
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [glueSt]
    rcases List.mem_cons.mp hm with e | hm
    · rw [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rw [glueSt_gpr' _ hn.1, gpr_setReg_self]
    · rw [glueSt_arg _ hg.2 hn.2 hm]
      have ha : argOk a = true := by
        have := List.all_eq_true.mp hg.2 _ hm
        simp only [Bool.and_eq_true] at this; exact this.2
      obtain ⟨⟨hd', -⟩, -⟩ := hg
      cases a with
      | imm v => rfl
      | ptr q =>
        simp only [argVal]
        rw [gpr_setReg_of_ne]
        intro e
        simp only [argOk, Bool.or_eq_true, beq_iff_eq, e] at ha hd'
        rcases hd' with (((h | h) | h) | h) | h <;> subst h <;> simp at ha

/-! ## Calls -/

/-- A call, after the moves of its arguments. -/
theorem callV {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {as : List (Reg × Arg)} (hg : glueOk as = true) {s : State} {rd wr : List Region}
    (hpre : k.pre (view (glueSt s as) rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) (hsu : stackUse c ≤ s.sp.toNat)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (wr ++ [below s (stackUse c)]) s s' →
      k.post (view (glueSt s as) rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (callAt name c as) s Q := by
  refine WP.seq (WP.mono (glue_ok hg s) fun s1 e => ?_)
  subst e
  refine WP.callF hv hpre (by rw [glueSt_rd, glueSt_wr]; exact hc) (by rw [glueSt_wr]; exact hw)
    (by rw [glueSt_sp]; exact hsu) fun s' hrd hwr hsp hf hcs hp => hQ s' ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ hp
  · rw [hcs r hr hl, glueSt_pres s hg r hr]
  · rw [hsp, glueSt_sp]
  · rw [hrd, glueSt_rd]
  · rw [hwr, glueSt_wr]
  · rw [glueSt_mem, glueSt_sp] at hf; exact hf

/-- The word pushed by a frame of `r12`. -/
theorem pushed12_word (s : State) :
    (pushed [.r12] s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 4)) 32 = s.gpr .r12 :=
  Mem.readW_writeW_self32 _ _ _

/-- A frame of `r12` changes memory only in the word below the stack pointer. -/
theorem pushed12_frame (s : State) (h : 4 ≤ s.sp.toNat) : Frame [below s 4] s.mem (pushed [.r12] s).mem := by
  have := storeWords_frame s.mem (s.sp - BitVec.ofNat 32 4) [s.gpr .r12] (by
    simp only [List.length_cons, List.length_nil]; have := s.sp.isLt; bv_omega)
  refine this.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  rw [List.mem_singleton] at hr; subst hr
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  simp only [Region.Contains, List.length_cons, List.length_nil] at hx ⊢
  bv_omega

/-- A call in a frame that pushes its stack argument, after the moves of its
arguments: the callee runs from the state after the push, `pushed [.r12] (glueSt s as')`,
and may write its stack argument. -/
theorem callVS {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {as : List (Reg × Arg)} {st : Arg} (hg : glueOk (as ++ [(.r12, st)]) = true) {s : State}
    {rd wr : List Region}
    (hpre : k.pre (view (pushed [.r12] (glueSt s (as ++ [(.r12, st)])))
      (rd ++ [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩]) wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) (hsu : 4 + stackUse c ≤ s.sp.toNat)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (wr ++ [below s (4 + stackUse c)]) s s' →
      (∃ s₃ : State, s₃.mem = s'.mem ∧ (∀ r, r ≠ .r12 → s₃.gpr r = s'.gpr r) ∧
        k.post (view (pushed [.r12] (glueSt s (as ++ [(.r12, st)])))
          (rd ++ [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩]) wr)
          (s₃.withRegions (rd ++ [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩]) wr)) → Q s') :
    WP isa (callAtS name c as st) s Q := by
  have eg : glue as ++ st.instrs .r12 = glue (as ++ [(.r12, st)]) := by
    rw [glue_append, glue, glue, List.append_nil]
  unfold callAtS
  rw [eg]
  refine WP.seq (WP.mono (glue_ok hg s) fun s1 e => ?_)
  subst e
  have hsp1 := glueSt_sp s (as ++ [(.r12, st)])
  have hs4 : 4 ≤ s.sp.toNat := by omega_using [hsu]
  refine WP.frame (rs := [.r12]) (r := .r12) rfl (by simp only [List.length_cons, List.length_nil, hsp1]; omega_using [hsu])
    (by decide) ?_
  have hsp2 : (pushed [.r12] (glueSt s (as ++ [(.r12, st)]))).sp = s.sp - BitVec.ofNat 32 4 := by
    rw [pushed_sp, hsp1]; rfl
  have hsp2' : ((pushed [.r12] (glueSt s (as ++ [(.r12, st)]))).sp).toNat = s.sp.toNat - 4 := by
    rw [hsp2]; bv_omega
  have hwr2 : (pushed [.r12] (glueSt s (as ++ [(.r12, st)]))).wr =
      ⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩ :: s.wr := by
    rw [pushed_wr, hsp1, glueSt_wr]; rfl
  have hrd2 : (pushed [.r12] (glueSt s (as ++ [(.r12, st)]))).rd = s.rd := by
    rw [pushed_rd, glueSt_rd]
  refine WP.callF hv hpre ?_ ?_ (by rw [hsp2']; omega_using [hsu]) fun s3 hrd hwr hsp hf hcs hp => hQ _ ⟨fun r hr hl => ?_,
    ?_, ?_, ?_, ?_⟩ ⟨s3, rfl, fun r hr => (popped_gpr hr _ _).symm, hp⟩
  · rw [hrd2, hwr2]
    intro a n ⟨r, hr, hc'⟩
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | rfl) | hr
    · obtain ⟨r', hr', hc''⟩ := hc a n ⟨r, List.mem_append_left _ hr, hc'⟩
      refine ⟨r', ?_, hc''⟩
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), hc'⟩
    · obtain ⟨r', hr', hc''⟩ := hc a n ⟨r, List.mem_append_right _ hr, hc'⟩
      refine ⟨r', ?_, hc''⟩
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · rw [hwr2]
    intro a n ⟨r, hr, hc'⟩
    obtain ⟨r', hr', hc''⟩ := hw a n ⟨r, hr, hc'⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc''⟩
  · rw [popped_gpr (by revert r; decide) _ _, hcs r hr hl, pushed_gpr, glueSt_pres s hg r hr]
  · rw [popped_sp, hsp, hsp2]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd, hrd2]
  · rw [popped_wr, hwr, hwr2]; rfl
  · rw [popped_mem]
    have f₀ : Frame [belowA s.sp 4] s.mem (pushed [.r12] (glueSt s (as ++ [(.r12, st)]))).mem := by
      have := pushed12_frame (glueSt s (as ++ [(.r12, st)])) (by rw [hsp1]; exact hs4)
      rwa [glueSt_mem, below, hsp1] at this
    rw [hsp2] at hf
    refine (f₀.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega_using [])⟩
    · rw [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_push hsu⟩

/-! ## Two runs of a call -/

/-- The preconditions and public data of a callee in two runs, from the states
`a` and `b` it starts from, with the regions `rd` and `wr`. -/
def CallRel (k : Contract isa) (rd wr : List Region) (x y a b : State) : Prop :=
  k.pre (a.callEntry.withRegions rd wr) ∧ k.pre (b.callEntry.withRegions rd wr) ∧
    k.pub (a.callEntry.withRegions rd wr) (b.callEntry.withRegions rd wr) ∧
    Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧ Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr

/-- Two runs of a call leak the same, if the callee's preconditions hold and
its public data agree. -/
theorem callV_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × Arg)} (hg : glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr x y (glueSt x as) (glueSt y as)) :
    RelCT isa P (callAt name c as) fun _ _ => True := by
  unfold callAt
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = glueSt x as) (relct_noMem (glue_noMem as))
    fun x y _ => ⟨glue_ok hg x, glue_ok hg y⟩) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, ∃ x y : State, CallRel k rw.1 rw.2 x y a b ∧
      x.rd = a.rd ∧ x.wr = a.wr ∧ y.rd = b.rd ∧ y.wr = b.wr)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.call hv hct rw.1 rw.2 fun a b ⟨x, y, h, e1, e2, e3, e4⟩ => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      exact ⟨h1, h2, h3, by rwa [← e1, ← e2], by rwa [← e2], by rwa [← e3, ← e4], by rwa [← e4]⟩) ?_
    fun _ _ h => h
  rintro a b ⟨-, x, y, hp, rfl, rfl⟩
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), x, y, h, (glueSt_rd x as).symm, (glueSt_wr x as).symm, (glueSt_rd y as).symm,
    (glueSt_wr y as).symm⟩

/-- Two runs of a call in a frame that pushes its stack argument. -/
theorem callVS_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × Arg)} {st : Arg}
    (hg : glueOk (as ++ [(.r12, st)]) = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp) (h4 : ∀ x y, P x y → 4 ≤ x.sp.toNat ∧ 4 ≤ y.sp.toNat)
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr (pushed [.r12] (glueSt x (as ++ [(.r12, st)])))
      (pushed [.r12] (glueSt y (as ++ [(.r12, st)]))) (pushed [.r12] (glueSt x (as ++ [(.r12, st)])))
      (pushed [.r12] (glueSt y (as ++ [(.r12, st)])))) :
    RelCT isa P (callAtS name c as st) fun _ _ => True := by
  have eg : glue as ++ st.instrs .r12 = glue (as ++ [(.r12, st)]) := by
    rw [glue_append, glue, glue, List.append_nil]
  unfold callAtS
  rw [eg]
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = glueSt x (as ++ [(.r12, st)]))
    (relct_noMem (glue_noMem _)) fun x y _ => ⟨glue_ok hg x, glue_ok hg y⟩) ?_
  refine RelCT.frame (fun a b h => by
    obtain ⟨-, x, y, hp, e1, e2⟩ := h
    rw [e1, e2, glueSt_sp, glueSt_sp]; exact hsp x y hp) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, CallRel k rw.1 rw.2 a b a b)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.call hv hct rw.1 rw.2 fun a b h => h) ?_
    fun _ _ h => h
  rintro a b ⟨a0, b0, ⟨-, x, y, hp, rfl, rfl⟩, pa, pb⟩
  have hx := h4 x y hp
  rw [push_pushed rfl (by rw [glueSt_sp]; exact hx.1), Option.some.injEq] at pa
  rw [push_pushed rfl (by rw [glueSt_sp]; exact hx.2), Option.some.injEq] at pb
  subst pa pb
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), h⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

end


/-!
# ML-DSA on 32-bit ARM: the buffers of the top-level functions

The top-level functions work on five buffers (a `Lay`, as ML-KEM's): `scratch`
(buffer 0), the `STK` bytes of stack below the stack pointer (buffer 1), and
their arguments (buffers 2, 3 and 4, whose pointers they keep in `r4`, `r5`
and `r6`; `r7` holds `scratch`): `ix` maps each register to the buffer it
points into. A state where they run their parts is a `Site`.

A pointer `q` (a register and an offset) is the address `lpa L q`, and the
region of `l` bytes there the triple `tri q l`, so that what a part writes
and what the proofs keep track of are lists of triples (`Kept`, `sepB`, as
in ML-KEM). The sponge (`hash`) is ML-KEM's (`hash_ok`, `hash_ct`), which
use the 8 bytes below the stack pointer as buffer 1: `hashLay` is the layout
with buffer 1 so narrowed (`hashS`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.Sha3 (bytesAt)

/-- The buffer each register points into. -/
def ix : Reg → Nat
  | .r7 => 0
  | .r4 => 2
  | .r5 => 3
  | .r6 => 4
  | _ => 5

/-- The `l` bytes at the pointer `q`. -/
abbrev tri (q : Ptr) (l : Nat) : Nat × Nat × Nat := (ix q.1, q.2, l)

/-- The address of the pointer `q`. -/
abbrev lpa (L : Lay) (q : Ptr) : Addr := L.A (ix q.1) q.2

/-- The buffers fit in the address space, and a buffer of `Wb` (written, or
the stack) is apart from every other: buffers only read may overlap each
other. -/
structure OkW (L : Lay) (Wb : List Nat) : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j → (i ∈ Wb ∨ j ∈ Wb) →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

/-- Two regions apart, one of them in a buffer of `Wb`, or both in the same. -/
theorem disjW' {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb ∨ i = j) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 32 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    exact region_disj_off hs' hla hlb (addr_fit _ (by omega_arith))
  · have hw' : i ∈ Wb ∨ j ∈ Wb := by rcases hw with h | h | h; exacts [.inl h, .inr h, absurd h e]
    exact ((hL.disj _ ha _ hb e hw').sub_left (Lay.R_sub hla)).sub_right (Lay.R_sub hlb)

/-- Two regions apart, one of them in a buffer of `Wb`. -/
theorem disjW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb) :
    (L.R i o l).Disjoint (L.R j o' l') :=
  disjW' hL h (hw.elim .inl fun h => .inr (.inl h))

/-- A state where the parts of a top-level function run, with `STK` bytes of
stack, and the buffers `Wb` written (and the stack). -/
structure Site (L : Lay) (Wb : List Nat) (STK : Nat) (s : State) : Prop where
  ok : OkW L Wb
  len : L.sizes.length = 5
  w0 : 0 ∈ Wb
  w1 : 1 ∈ Wb
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = STK
  p1 : L.ptr 1 = s.sp - BitVec.ofNat 32 STK
  s8 : 8 ≤ STK
  spk : STK ≤ s.sp.toNat
  r7 : s.gpr .r7 = L.ptr 0
  r4 : s.gpr .r4 = L.ptr 2
  r5 : s.gpr .r5 = L.ptr 3
  r6 : s.gpr .r6 = L.ptr 4
  cw : ∀ i ∈ Wb, i ≠ 1 → L.buf i ∈ s.wr
  cr : ∀ i < 5, i ≠ 1 → L.buf i ∈ s.rd ++ s.wr

theorem Site.kept {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s) {rs : List Region}
    (hk : Kept rs s s') : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hk.sp]; exact h.p1, h.s8, by rw [hk.sp]; exact h.spk,
    by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.cs .r4 (by decide) (by decide), h.r4],
    by rw [hk.cs .r5 (by decide) (by decide), h.r5], by rw [hk.cs .r6 (by decide) (by decide), h.r6],
    by rw [hk.wr]; exact h.cw, by rw [hk.wr, hk.rd]; exact h.cr⟩

/-- A register of the layout holds the pointer to its buffer. -/
theorem Site.base {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {r : Reg}
    (hr : argOk (.ptr (r, 0)) = true) : s.gpr r = L.ptr (ix r) := by
  simp only [argOk, Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with ((rfl | rfl) | rfl) | rfl
  exacts [h.r4, h.r5, h.r6, h.r7]

/-- A buffer, but the stack, with `l` bytes at offset `o`. -/
def inB (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  w.1 != 1 && w.1 < sz.length && w.2.1 + w.2.2 ≤ sz.getD w.1 0

theorem inB_bounds {sz : List Nat} {w : Nat × Nat × Nat} (h : inB sz w = true) :
    w.1 ≠ 1 ∧ w.1 < sz.length ∧ w.2.1 + w.2.2 ≤ sz.getD w.1 0 := by
  simp only [inB, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem inB_sep {sz : List Nat} {w : Nat × Nat × Nat} (h : inB sz w = true) {o l : Nat}
    (hs : o + l ≤ sz.getD 1 0) (h1 : 1 < sz.length) : sepB sz w (1, o, l) = true := by
  obtain ⟨h1', h2, h3⟩ := inB_bounds h
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨h2, h1⟩, h3⟩, hs⟩, .inl (.inl h1')⟩

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s)
include h

/-- The value of a pointer argument. -/
theorem Site.val {q : Ptr} (hq : argOk (.ptr q) = true) :
    argVal s (.ptr q) = L.ptr (ix q.1) + BitVec.ofNat 32 q.2 := by
  simp only [argVal, h.base (r := q.1) (by simpa [argOk] using hq)]

/-- The address of a pointer argument into a buffer. -/
theorem Site.addr {q : Ptr} {l : Nat} (hb : inB L.sizes (tri q l) = true) (hl : 0 < l) :
    State.addr (L.ptr (ix q.1) + BitVec.ofNat 32 q.2) = lpa L q ∧
      (L.ptr (ix q.1) + BitVec.ofNat 32 q.2).toNat + l ≤ 2 ^ 32 := by
  obtain ⟨-, h2, h3⟩ := inB_bounds hb
  dsimp only [tri] at h2 h3
  have hf := h.ok.fit _ h2
  simp only [Lay.size] at hf
  refine ⟨addr_add (by omega_arith), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q.2) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The stack below the stack pointer, as buffer 1. -/
theorem Site.belowSub {n : Nat} (hn : n ≤ STK) : Region.Sub (VG.Proof.MlKem.Arm.below s n) (L.R 1 0 STK) := by
  intro x hx
  have e1 := h.p1
  have := h.spk
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 STK)
  simp only [Region.Contains, e1] at hx ⊢
  bv_omega

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem Site.stkD {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) {n : Nat} (hn : n ≤ STK) :
    (L.R w.1 w.2.1 w.2.2).Disjoint (VG.Proof.MlKem.Arm.below s n) := by
  have hsep := inB_sep hb (o := 0) (l := STK) (by rw [← h.sz1]; simp [Lay.size]) (by rw [h.len]; decide)
  exact (disjW h.ok hsep (.inr h.w1)).sub_right (h.belowSub hn)

omit h in
/-- Covers of a buffer the state may write. -/
theorem Site.covW {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) (hw : L.buf w.1 ∈ s.wr) :
    Covers [L.R w.1 w.2.1 w.2.2] s.wr :=
  Lay.covers hw (inB_bounds hb).2.2

omit h in
/-- Covers of a buffer the state may read. -/
theorem Site.covR {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) (hw : L.buf w.1 ∈ s.rd ++ s.wr) :
    Covers [L.R w.1 w.2.1 w.2.2] (s.rd ++ s.wr) :=
  Lay.covers hw (inB_bounds hb).2.2

end

/-! ## Changes of the stack -/

/-- What a call changes below the stack pointer is in buffer 1. -/
theorem Site.kept_stk {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s) {W : List (Nat × Nat × Nat)}
    {rs : List Region} (hrs : ∀ r ∈ rs, ∃ w ∈ W, Region.Sub r (L.R w.1 w.2.1 w.2.2)) {n : Nat} (hn : n ≤ STK)
    (hk : Kept (rs ++ [VG.Proof.MlKem.Arm.below s n]) s s') : Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  ⟨hk.cs, hk.sp, hk.rd, hk.wr, hk.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, hs⟩ := hrs r hr
      exact ⟨_, List.mem_map.mpr ⟨w, List.mem_append_left _ hw, rfl⟩, hs⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨(1, 0, STK), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩,
        h.belowSub hn⟩⟩

/-! ## The sponge -/

/-- The layout with buffer 1 the 8 bytes below the stack pointer, as ML-KEM's
sponge routine (`hash_ok`) takes it, and of the arguments only those `K`
says (the others empty, so that the buffers are pairwise disjoint). -/
def hashLay (L : Lay) (s : State) (K : Nat → Bool) : Lay :=
  ⟨fun i => if i = 1 then s.sp - BitVec.ofNat 32 8 else L.ptr i,
    [L.size 0, 8, if K 2 then L.size 2 else 0, if K 3 then L.size 3 else 0, if K 4 then L.size 4 else 0]⟩

theorem hashLay_ptr (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) :
    (hashLay L s K).ptr i = L.ptr i := by
  simp only [hashLay, hi, ite_false]

theorem hashLay_R (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (o l : Nat) :
    (hashLay L s K).R i o l = L.R i o l := by
  simp only [Lay.R, hashLay_ptr L s K hi]

theorem hashLay_size_le (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (hi5 : i < 5) :
    (hashLay L s K).size i ≤ L.size i := by
  rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact Nat.le_refl _
  all_goals (show (if _ then _ else 0) ≤ _; split <;> omega_arith)

theorem hashLay_size (L : Lay) (s : State) {K : Nat → Bool} {i : Nat} (hi : i ≠ 1) (hK : i = 0 ∨ K i = true)
    (hi5 : i < 5) : (hashLay L s K).size i = L.size i := by
  rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    rcases hK with h | h
    · omega_arith
    · show (if _ then _ else 0) = _; rw [ite_eq_left h]

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {K : Nat → Bool}
  (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
include h hK

theorem hashLay_ok : (hashLay L s K).Ok := by
  have hL := h.ok
  have e8 : (⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ : Region) = VG.Proof.MlKem.Arm.below s 8 := by
    rw [addr_sub (Nat.le_trans h.s8 h.spk)]
  have hsub : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ (L.buf 1) := by
    rw [e8, Lay.buf, show (⟨State.addr (L.ptr 1), L.size 1⟩ : Region) = L.R 1 0 STK by
      rw [h.sz1]; simp only [Lay.R, add_ofNat_zero]]
    exact h.belowSub h.s8
  have hl5 := h.len
  have bi : ∀ k, k < 5 → k ≠ 1 → Region.Sub ⟨State.addr ((hashLay L s K).ptr k), (hashLay L s K).size k⟩
      (L.buf k) := fun k hk hk1 => by
    rw [hashLay_ptr L s K hk1]
    intro x hx
    have := hashLay_size_le L s K hk1 hk
    simp only [Region.Contains] at hx ⊢
    omega_arith
  have b1 : (⟨State.addr ((hashLay L s K).ptr 1), (hashLay L s K).size 1⟩ : Region) =
      ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · simp only [hashLay, List.length_cons, List.length_nil] at hi
    by_cases e : i = 1
    · subst e
      show (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
      have := h.s8; have := h.spk; have := s.sp.isLt; bv_omega
    · have := hashLay_size_le L s K e (by omega_arith)
      simp only [hashLay_ptr L s K e]
      exact Nat.le_trans (Nat.add_le_add_left this _) (hL.fit i (by omega_arith))
  · simp only [hashLay, List.length_cons, List.length_nil] at hi hj
    -- an empty buffer is apart from every other
    by_cases z : (hashLay L s K).size i = 0 ∨ (hashLay L s K).size j = 0
    · intro x hx hy
      rcases z with z | z
      · simp only [Region.Contains, z] at hx; omega_arith
      · simp only [Region.Contains, z] at hy; omega_arith
    have hKi : i ≤ 1 ∨ K i = true := by
      rcases (by omega_arith : i ≤ 1 ∨ 2 ≤ i) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega_arith : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl <;>
          exact z (.inl (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hKj : j ≤ 1 ∨ K j = true := by
      rcases (by omega_arith : j ≤ 1 ∨ 2 ≤ j) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega_arith : j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl <;>
          exact z (.inr (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hw : i ∈ Wb ∨ j ∈ Wb := by
      rcases (by omega_arith : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h'
      · exact .inl h.w0
      · exact .inl h.w1
      rcases (by omega_arith : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h''
      · exact .inr h.w0
      · exact .inr h.w1
      exact hK i hi j hj hij h' h'' (hKi.resolve_left (by omega_arith)) (hKj.resolve_left (by omega_arith))
    by_cases ei : i = 1
    · subst ei
      rw [b1]
      exact (hL.disj 1 (by omega_arith) j (by omega_arith) hij hw).sub_left hsub |>.sub_right (bi j hj (Ne.symm hij))
    · by_cases ej : j = 1
      · subst ej
        rw [b1]
        exact ((hL.disj i (by omega_arith) 1 (by omega_arith) hij hw).sub_right hsub).sub_left (bi i hi ei)
      · exact ((hL.disj i (by omega_arith) j (by omega_arith) hij hw).sub_left (bi i hi ei)).sub_right (bi j hj ej)

theorem Site.ctx : Ctx (hashLay L s K) s :=
  ⟨hashLay_ok h hK, by rw [hashLay_size L s (by decide) (.inl rfl) (by decide)]; exact h.sz0, rfl, by simp [hashLay],
    by rw [h.r7]; rfl, Nat.le_trans h.s8 h.spk, by simp [hashLay],
    by rw [show (⟨State.addr ((hashLay L s K).ptr 0), (hashLay L s K).size 0⟩ : Region) = L.buf 0 from rfl]
       exact h.cw 0 h.w0 (by decide)⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
