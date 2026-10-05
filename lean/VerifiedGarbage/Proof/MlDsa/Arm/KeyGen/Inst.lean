import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Frag
import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.KeyGen
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.Arm.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Base`. -/
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
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

theorem setReg_setReg (s : State) (d : Reg) (x y : BitVec 32) : (s.setReg d x).setReg d y = s.setReg d y := by
  simp only [State.setReg]
  congr 1
  funext r
  split <;> rfl

theorem ldc_ok (d : Reg) (v : Nat) (s : State) :
    WP isa (.block (ldc d v)) s (· = s.setReg d (BitVec.ofNat 32 v)) := by
  apply WP.of_runBlock
  simp only [ldc, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Option.some.injEq, exists_eq_left',
    gpr_setReg_self, VG.Proof.MlDsa.Arm.KeyGen.setReg_setReg, VG.Proof.MlDsa.Arm.KeyGen.ldc_eq]

/-- The value of an argument. -/
def argVal (s : State) : Arg → BitVec 32
  | .ptr p => s.gpr p.1 + BitVec.ofNat 32 p.2
  | .imm v => BitVec.ofNat 32 v

/-- An argument whose pointer, if any, is in a callee-saved register. -/
def argOk : Arg → Bool
  | .ptr p => p.1 == .r4 || p.1 == .r5 || p.1 == .r6 || p.1 == .r7
  | .imm _ => true

theorem arg_ok (d : Reg) (a : Arg) (h : ∀ p : Ptr, a = .ptr p → p.1 ≠ d) (s : State) :
    WP isa (.block (a.instrs d)) s (· = s.setReg d (VG.Proof.MlDsa.Arm.KeyGen.argVal s a)) := by
  cases a with
  | ptr p =>
    have hb := h p rfl
    apply WP.of_runBlock
    simp only [Arg.instrs, VG.Proof.MlDsa.Arm.KeyGen.argVal, ldc, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, isa, exec, Op2.eval, Option.map_some, Option.some.injEq, exists_eq_left', gpr_setReg_self,
      VG.Proof.MlDsa.Arm.KeyGen.setReg_setReg, VG.Proof.MlDsa.Arm.KeyGen.ldc_eq, gpr_setReg_of_ne _ _ hb]
  | imm v => exact VG.Proof.MlDsa.Arm.KeyGen.ldc_ok d v s

/-- The state after the moves of the arguments `as`. -/
def glueSt (s : State) : List (Reg × Arg) → State
  | [] => s
  | (d, a) :: as => VG.Proof.MlDsa.Arm.KeyGen.glueSt (s.setReg d (VG.Proof.MlDsa.Arm.KeyGen.argVal s a)) as

/-- The moves of arguments into `r0`–`r3` and `r12`, of pointers in `r4`–`r7`. -/
def glueOk (as : List (Reg × Arg)) : Bool :=
  as.all fun x => (x.1 == .r0 || x.1 == .r1 || x.1 == .r2 || x.1 == .r3 || x.1 == .r12) && VG.Proof.MlDsa.Arm.KeyGen.argOk x.2

theorem glue_ok : ∀ {as : List (Reg × Arg)}, VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true → ∀ s, WP isa (.block (glue as)) s (· = VG.Proof.MlDsa.Arm.KeyGen.glueSt s as)
  | [], _, s => WP.block_nil rfl
  | (d, a) :: as, h, s => by
    simp only [VG.Proof.MlDsa.Arm.KeyGen.glueOk, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨⟨hd, ha⟩, hs⟩ := h
    rw [glue, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.arg_ok d a (fun p e => ?_) s) fun s1 e1 => ?_
    · subst e
      simp only [VG.Proof.MlDsa.Arm.KeyGen.argOk, Bool.or_eq_true, beq_iff_eq] at ha hd
      intro e; subst e
      rcases ha with ((h | h) | h) | h <;> rw [h] at hd <;> simp at hd
    · subst e1
      exact VG.Proof.MlDsa.Arm.KeyGen.glue_ok (as := as) hs _

theorem glueSt_mem (s : State) : ∀ as, (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).mem = s.mem
  | [] => rfl
  | _ :: as => VG.Proof.MlDsa.Arm.KeyGen.glueSt_mem _ as
theorem glueSt_rd (s : State) : ∀ as, (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).rd = s.rd
  | [] => rfl
  | _ :: as => VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd _ as
theorem glueSt_wr (s : State) : ∀ as, (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).wr = s.wr
  | [] => rfl
  | _ :: as => VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr _ as
theorem glueSt_sp (s : State) : ∀ as, (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).sp = s.sp
  | [] => rfl
  | _ :: as => VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp _ as

/-- The registers the moves do not write. -/
theorem glueSt_gpr {r : Reg} (hr : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12) :
    ∀ (s : State) {as : List (Reg × Arg)}, VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true → (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).gpr r = s.gpr r
  | s, [], _ => rfl
  | s, (d, a) :: as, h => by
    simp only [VG.Proof.MlDsa.Arm.KeyGen.glueOk, List.all_cons, Bool.and_eq_true] at h
    rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt, VG.Proof.MlDsa.Arm.KeyGen.glueSt_gpr hr _ (as := as) h.2, gpr_setReg_of_ne]
    intro e; subst e
    obtain ⟨⟨hd, -⟩, -⟩ := h
    simp only [Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with (((h | h) | h) | h) | h <;> simp_all

theorem glueSt_pres (s : State) {as : List (Reg × Arg)} (h : VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true) :
    ∀ r ∈ preserved, (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).gpr r = s.gpr r := fun r hr =>
  VG.Proof.MlDsa.Arm.KeyGen.glueSt_gpr (by revert r; decide) s h

theorem glue_append : ∀ as bs : List (Reg × Arg), glue (as ++ bs) = glue as ++ glue bs
  | [], _ => rfl
  | (d, a) :: as, bs => by rw [List.cons_append, glue, glue, VG.Proof.MlDsa.Arm.KeyGen.glue_append as bs, List.append_assoc]

theorem glue_noMem : ∀ as : List (Reg × Arg), (glue as).all noMem = true
  | [] => rfl
  | (d, a) :: as => by
    rw [glue, List.all_append, VG.Proof.MlDsa.Arm.KeyGen.glue_noMem as, Bool.and_true]
    cases a <;> rfl

/-- The registers the moves of `as` do not write. -/
theorem glueSt_gpr' {r : Reg} : ∀ (s : State) {as : List (Reg × Arg)}, r ∉ as.map Prod.fst →
    (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).gpr r = s.gpr r
  | s, [], _ => rfl
  | s, (d, a) :: as, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt, VG.Proof.MlDsa.Arm.KeyGen.glueSt_gpr' _ h.2, gpr_setReg_of_ne _ _ h.1]

/-- An argument's register holds its value after the moves. -/
theorem glueSt_arg (s : State) {d : Reg} {a : Arg} :
    ∀ {as : List (Reg × Arg)}, VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true → (as.map Prod.fst).Nodup → (d, a) ∈ as →
      (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).gpr d = VG.Proof.MlDsa.Arm.KeyGen.argVal s a
  | [], _, _, hm => absurd hm List.not_mem_nil
  | (d', a') :: as, hg, hn, hm => by
    simp only [VG.Proof.MlDsa.Arm.KeyGen.glueOk, List.all_cons, Bool.and_eq_true] at hg
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt]
    rcases List.mem_cons.mp hm with e | hm
    · rw [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_gpr' _ hn.1, gpr_setReg_self]
    · rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg _ hg.2 hn.2 hm]
      have ha : VG.Proof.MlDsa.Arm.KeyGen.argOk a = true := by
        have := List.all_eq_true.mp hg.2 _ hm
        simp only [Bool.and_eq_true] at this; exact this.2
      obtain ⟨⟨hd', -⟩, -⟩ := hg
      cases a with
      | imm v => rfl
      | ptr q =>
        simp only [VG.Proof.MlDsa.Arm.KeyGen.argVal]
        rw [gpr_setReg_of_ne]
        intro e
        simp only [VG.Proof.MlDsa.Arm.KeyGen.argOk, Bool.or_eq_true, beq_iff_eq, e] at ha hd'
        rcases hd' with (((h | h) | h) | h) | h <;> subst h <;> simp at ha

/-! ## Calls -/

/-- A call, after the moves of its arguments. -/
theorem callV {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {as : List (Reg × Arg)} (hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true) {s : State} {rd wr : List Region}
    (hpre : k.pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as) rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) (hsu : stackUse c ≤ s.sp.toNat)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (wr ++ [below s (stackUse c)]) s s' →
      k.post (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as) rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (callAt name c as) s Q := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.glue_ok hg s) fun s1 e => ?_)
  subst e
  refine WP.callF hv hpre (by rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd, VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr]; exact hc) (by rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr]; exact hw)
    (by rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp]; exact hsu) fun s' hrd hwr hsp hf hcs hp => hQ s' ⟨fun r hr hl => ?_, ?_, ?_, ?_, ?_⟩ hp
  · rw [hcs r hr hl, VG.Proof.MlDsa.Arm.KeyGen.glueSt_pres s hg r hr]
  · rw [hsp, VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp]
  · rw [hrd, VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd]
  · rw [hwr, VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr]
  · rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_mem, VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp] at hf; exact hf

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
    {as : List (Reg × Arg)} {st : Arg} (hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk (as ++ [(.r12, st)]) = true) {s : State}
    {rd wr : List Region}
    (hpre : k.pre (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)])))
      (rd ++ [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩]) wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) (hsu : 4 + stackUse c ≤ s.sp.toNat)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (wr ++ [below s (4 + stackUse c)]) s s' →
      (∃ s₃ : State, s₃.mem = s'.mem ∧ (∀ r, r ≠ .r12 → s₃.gpr r = s'.gpr r) ∧
        k.post (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)])))
          (rd ++ [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩]) wr)
          (s₃.withRegions (rd ++ [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩]) wr)) → Q s') :
    WP isa (callAtS name c as st) s Q := by
  have eg : glue as ++ st.instrs .r12 = glue (as ++ [(.r12, st)]) := by
    rw [VG.Proof.MlDsa.Arm.KeyGen.glue_append, glue, glue, List.append_nil]
  unfold callAtS
  rw [eg]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.glue_ok hg s) fun s1 e => ?_)
  subst e
  have hsp1 := VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp s (as ++ [(.r12, st)])
  have hs4 : 4 ≤ s.sp.toNat := by omega
  refine WP.frame (rs := [.r12]) (r := .r12) rfl (by simp only [List.length_cons, List.length_nil, hsp1]; omega)
    (by decide) ?_
  have hsp2 : (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)]))).sp = s.sp - BitVec.ofNat 32 4 := by
    rw [pushed_sp, hsp1]; rfl
  have hsp2' : ((pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)]))).sp).toNat = s.sp.toNat - 4 := by
    rw [hsp2]; bv_omega
  have hwr2 : (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)]))).wr =
      ⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩ :: s.wr := by
    rw [pushed_wr, hsp1, VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr]; rfl
  have hrd2 : (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)]))).rd = s.rd := by
    rw [pushed_rd, VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd]
  refine WP.callF hv hpre ?_ ?_ (by rw [hsp2']; omega) fun s3 hrd hwr hsp hf hcs hp => hQ _ ⟨fun r hr hl => ?_,
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
  · rw [popped_gpr (by revert r; decide) _ _, hcs r hr hl, pushed_gpr, VG.Proof.MlDsa.Arm.KeyGen.glueSt_pres s hg r hr]
  · rw [popped_sp, hsp, hsp2]; exact BitVec.sub_add_cancel _ _
  · rw [popped_rd, hrd, hrd2]
  · rw [popped_wr, hwr, hwr2]; rfl
  · rw [popped_mem]
    have f₀ : Frame [belowA s.sp 4] s.mem (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)]))).mem := by
      have := VG.Proof.MlDsa.Arm.KeyGen.pushed12_frame (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (as ++ [(.r12, st)])) (by rw [hsp1]; exact hs4)
      rwa [VG.Proof.MlDsa.Arm.KeyGen.glueSt_mem, below, hsp1] at this
    rw [hsp2] at hf
    refine (f₀.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
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
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × Arg)} (hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, VG.Proof.MlDsa.Arm.KeyGen.CallRel k rd wr x y (VG.Proof.MlDsa.Arm.KeyGen.glueSt x as) (VG.Proof.MlDsa.Arm.KeyGen.glueSt y as)) :
    RelCT isa P (callAt name c as) fun _ _ => True := by
  unfold callAt
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = VG.Proof.MlDsa.Arm.KeyGen.glueSt x as) (relct_noMem (VG.Proof.MlDsa.Arm.KeyGen.glue_noMem as))
    fun x y _ => ⟨VG.Proof.MlDsa.Arm.KeyGen.glue_ok hg x, VG.Proof.MlDsa.Arm.KeyGen.glue_ok hg y⟩) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, ∃ x y : State, VG.Proof.MlDsa.Arm.KeyGen.CallRel k rw.1 rw.2 x y a b ∧
      x.rd = a.rd ∧ x.wr = a.wr ∧ y.rd = b.rd ∧ y.wr = b.wr)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.call hv hct rw.1 rw.2 fun a b ⟨x, y, h, e1, e2, e3, e4⟩ => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      exact ⟨h1, h2, h3, by rwa [← e1, ← e2], by rwa [← e2], by rwa [← e3, ← e4], by rwa [← e4]⟩) ?_
    fun _ _ h => h
  rintro a b ⟨-, x, y, hp, rfl, rfl⟩
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), x, y, h, (VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd x as).symm, (VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr x as).symm, (VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd y as).symm,
    (VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr y as).symm⟩

/-- Two runs of a call in a frame that pushes its stack argument. -/
theorem callVS_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × Arg)} {st : Arg}
    (hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk (as ++ [(.r12, st)]) = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp) (h4 : ∀ x y, P x y → 4 ≤ x.sp.toNat ∧ 4 ≤ y.sp.toNat)
    (hP : ∀ x y, P x y → ∃ rd wr, VG.Proof.MlDsa.Arm.KeyGen.CallRel k rd wr (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt x (as ++ [(.r12, st)])))
      (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt y (as ++ [(.r12, st)]))) (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt x (as ++ [(.r12, st)])))
      (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt y (as ++ [(.r12, st)])))) :
    RelCT isa P (callAtS name c as st) fun _ _ => True := by
  have eg : glue as ++ st.instrs .r12 = glue (as ++ [(.r12, st)]) := by
    rw [VG.Proof.MlDsa.Arm.KeyGen.glue_append, glue, glue, List.append_nil]
  unfold callAtS
  rw [eg]
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = VG.Proof.MlDsa.Arm.KeyGen.glueSt x (as ++ [(.r12, st)]))
    (relct_noMem (VG.Proof.MlDsa.Arm.KeyGen.glue_noMem _)) fun x y _ => ⟨VG.Proof.MlDsa.Arm.KeyGen.glue_ok hg x, VG.Proof.MlDsa.Arm.KeyGen.glue_ok hg y⟩) ?_
  refine RelCT.frame (fun a b h => by
    obtain ⟨-, x, y, hp, e1, e2⟩ := h
    rw [e1, e2, VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp, VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp]; exact hsp x y hp) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, VG.Proof.MlDsa.Arm.KeyGen.CallRel k rw.1 rw.2 a b a b)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.call hv hct rw.1 rw.2 fun a b h => h) ?_
    fun _ _ h => h
  rintro a b ⟨a0, b0, ⟨-, x, y, hp, rfl, rfl⟩, pa, pb⟩
  have hx := h4 x y hp
  rw [push_pushed rfl (by rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp]; exact hx.1), Option.some.injEq] at pa
  rw [push_pushed rfl (by rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp]; exact hx.2), Option.some.injEq] at pb
  subst pa pb
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), h⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Site`. -/
section

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
abbrev tri (q : Ptr) (l : Nat) : Nat × Nat × Nat := (VG.Proof.MlDsa.Arm.KeyGen.ix q.1, q.2, l)

/-- The address of the pointer `q`. -/
abbrev lpa (L : Lay) (q : Ptr) : Addr := L.A (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2

/-- The buffers fit in the address space, and a buffer of `Wb` (written, or
the stack) is apart from every other: buffers only read may overlap each
other. -/
structure OkW (L : Lay) (Wb : List Nat) : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 32
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j → (i ∈ Wb ∨ j ∈ Wb) →
    (⟨State.addr (L.ptr i), L.size i⟩ : Region).Disjoint ⟨State.addr (L.ptr j), L.size j⟩

theorem OkW.ok {L : Lay} {Wb : List Nat} (h : VG.Proof.MlDsa.Arm.KeyGen.OkW L Wb) (hall : ∀ i < L.sizes.length, i ∈ Wb) : L.Ok :=
  ⟨h.fit, fun i hi j hj hij => h.disj i hi j hj hij (.inl (hall i hi))⟩

/-- Two regions apart, one of them in a buffer of `Wb`, or both in the same. -/
theorem disjW' {L : Lay} {Wb : List Nat} (hL : VG.Proof.MlDsa.Arm.KeyGen.OkW L Wb) {i o l j o' l' : Nat}
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
    exact region_disj_off hs' hla hlb (addr_fit _ (by omega))
  · have hw' : i ∈ Wb ∨ j ∈ Wb := by rcases hw with h | h | h; exacts [.inl h, .inr h, absurd h e]
    exact ((hL.disj _ ha _ hb e hw').sub_left (Lay.R_sub hla)).sub_right (Lay.R_sub hlb)

/-- Two regions apart, one of them in a buffer of `Wb`. -/
theorem disjW {L : Lay} {Wb : List Nat} (hL : VG.Proof.MlDsa.Arm.KeyGen.OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb) :
    (L.R i o l).Disjoint (L.R j o' l') :=
  VG.Proof.MlDsa.Arm.KeyGen.disjW' hL h (hw.elim .inl fun h => .inr (.inl h))

/-- A state where the parts of a top-level function run, with `STK` bytes of
stack, and the buffers `Wb` written (and the stack). -/
structure Site (L : Lay) (Wb : List Nat) (STK : Nat) (s : State) : Prop where
  ok : VG.Proof.MlDsa.Arm.KeyGen.OkW L Wb
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

theorem Site.kept {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {rs : List Region}
    (hk : Kept rs s s') : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hk.sp]; exact h.p1, h.s8, by rw [hk.sp]; exact h.spk,
    by rw [hk.cs .r7 (by decide) (by decide), h.r7], by rw [hk.cs .r4 (by decide) (by decide), h.r4],
    by rw [hk.cs .r5 (by decide) (by decide), h.r5], by rw [hk.cs .r6 (by decide) (by decide), h.r6],
    by rw [hk.wr]; exact h.cw, by rw [hk.wr, hk.rd]; exact h.cr⟩

/-- A register of the layout holds the pointer to its buffer. -/
theorem Site.base {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {r : Reg}
    (hr : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr (r, 0)) = true) : s.gpr r = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix r) := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.argOk, Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with ((rfl | rfl) | rfl) | rfl
  exacts [h.r4, h.r5, h.r6, h.r7]

/-- A buffer, but the stack, with `l` bytes at offset `o`. -/
def inB (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  w.1 != 1 && w.1 < sz.length && w.2.1 + w.2.2 ≤ sz.getD w.1 0

theorem inB_bounds {sz : List Nat} {w : Nat × Nat × Nat} (h : VG.Proof.MlDsa.Arm.KeyGen.inB sz w = true) :
    w.1 ≠ 1 ∧ w.1 < sz.length ∧ w.2.1 + w.2.2 ≤ sz.getD w.1 0 := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.inB, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem inB_sep {sz : List Nat} {w : Nat × Nat × Nat} (h : VG.Proof.MlDsa.Arm.KeyGen.inB sz w = true) {o l : Nat}
    (hs : o + l ≤ sz.getD 1 0) (h1 : 1 < sz.length) : sepB sz w (1, o, l) = true := by
  obtain ⟨h1', h2, h3⟩ := VG.Proof.MlDsa.Arm.KeyGen.inB_bounds h
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨h2, h1⟩, h3⟩, hs⟩, .inl (.inl h1')⟩

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s)
include h

/-- The value of a pointer argument. -/
theorem Site.val {q : Ptr} (hq : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr q) = true) :
    VG.Proof.MlDsa.Arm.KeyGen.argVal s (.ptr q) = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2 := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.argVal, h.base (r := q.1) (by simpa [VG.Proof.MlDsa.Arm.KeyGen.argOk] using hq)]

/-- The address of a pointer argument into a buffer. -/
theorem Site.addr {q : Ptr} {l : Nat} (hb : VG.Proof.MlDsa.Arm.KeyGen.inB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri q l) = true) (hl : 0 < l) :
    State.addr (L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2) = VG.Proof.MlDsa.Arm.KeyGen.lpa L q ∧
      (L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2).toNat + l ≤ 2 ^ 32 := by
  obtain ⟨-, h2, h3⟩ := VG.Proof.MlDsa.Arm.KeyGen.inB_bounds hb
  dsimp only [VG.Proof.MlDsa.Arm.KeyGen.tri] at h2 h3
  have hf := h.ok.fit _ h2
  simp only [Lay.size] at hf
  refine ⟨addr_add (by omega), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q.2) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

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
theorem Site.stkD {w : Nat × Nat × Nat} (hb : VG.Proof.MlDsa.Arm.KeyGen.inB L.sizes w = true) {n : Nat} (hn : n ≤ STK) :
    (L.R w.1 w.2.1 w.2.2).Disjoint (VG.Proof.MlKem.Arm.below s n) := by
  have hsep := VG.Proof.MlDsa.Arm.KeyGen.inB_sep hb (o := 0) (l := STK) (by rw [← h.sz1]; simp [Lay.size]) (by rw [h.len]; decide)
  exact (VG.Proof.MlDsa.Arm.KeyGen.disjW h.ok hsep (.inr h.w1)).sub_right (h.belowSub hn)

omit h in
/-- Covers of a buffer the state may write. -/
theorem Site.covW {w : Nat × Nat × Nat} (hb : VG.Proof.MlDsa.Arm.KeyGen.inB L.sizes w = true) (hw : L.buf w.1 ∈ s.wr) :
    Covers [L.R w.1 w.2.1 w.2.2] s.wr :=
  Lay.covers hw (VG.Proof.MlDsa.Arm.KeyGen.inB_bounds hb).2.2

omit h in
/-- Covers of a buffer the state may read. -/
theorem Site.covR {w : Nat × Nat × Nat} (hb : VG.Proof.MlDsa.Arm.KeyGen.inB L.sizes w = true) (hw : L.buf w.1 ∈ s.rd ++ s.wr) :
    Covers [L.R w.1 w.2.1 w.2.2] (s.rd ++ s.wr) :=
  Lay.covers hw (VG.Proof.MlDsa.Arm.KeyGen.inB_bounds hb).2.2

end

/-! ## Changes of the stack -/

/-- What a call changes below the stack pointer is in buffer 1. -/
theorem Site.kept_stk {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {W : List (Nat × Nat × Nat)}
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
    (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).ptr i = L.ptr i := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.hashLay, hi, ite_false]

theorem hashLay_R (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (o l : Nat) :
    (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).R i o l = L.R i o l := by
  simp only [Lay.R, VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr L s K hi]

theorem hashLay_size_le (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (hi5 : i < 5) :
    (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size i ≤ L.size i := by
  rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact Nat.le_refl _
  all_goals (show (if _ then _ else 0) ≤ _; split <;> omega)

theorem hashLay_size (L : Lay) (s : State) {K : Nat → Bool} {i : Nat} (hi : i ≠ 1) (hK : i = 0 ∨ K i = true)
    (hi5 : i < 5) : (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size i = L.size i := by
  rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    rcases hK with h | h
    · omega
    · show (if _ then _ else 0) = _; rw [ite_eq_left h]

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {K : Nat → Bool}
  (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
include h hK

theorem hashLay_ok : (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).Ok := by
  have hL := h.ok
  have e8 : (⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ : Region) = VG.Proof.MlKem.Arm.below s 8 := by
    rw [VG.Proof.MlKem.Arm.addr_sub (Nat.le_trans h.s8 h.spk)]
  have hsub : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ (L.buf 1) := by
    rw [e8, Lay.buf, show (⟨State.addr (L.ptr 1), L.size 1⟩ : Region) = L.R 1 0 STK by
      rw [h.sz1]; simp only [Lay.R, add_ofNat_zero]]
    exact h.belowSub h.s8
  have hl5 := h.len
  have bi : ∀ k, k < 5 → k ≠ 1 → Region.Sub ⟨State.addr ((VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).ptr k), (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size k⟩
      (L.buf k) := fun k hk hk1 => by
    rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr L s K hk1]
    intro x hx
    have := VG.Proof.MlDsa.Arm.KeyGen.hashLay_size_le L s K hk1 hk
    simp only [Region.Contains] at hx ⊢
    omega
  have b1 : (⟨State.addr ((VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).ptr 1), (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size 1⟩ : Region) =
      ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · simp only [VG.Proof.MlDsa.Arm.KeyGen.hashLay, List.length_cons, List.length_nil] at hi
    by_cases e : i = 1
    · subst e
      show (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
      have := h.s8; have := h.spk; have := s.sp.isLt; bv_omega
    · have := VG.Proof.MlDsa.Arm.KeyGen.hashLay_size_le L s K e (by omega)
      simp only [VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr L s K e]
      exact Nat.le_trans (Nat.add_le_add_left this _) (hL.fit i (by omega))
  · simp only [VG.Proof.MlDsa.Arm.KeyGen.hashLay, List.length_cons, List.length_nil] at hi hj
    -- an empty buffer is apart from every other
    by_cases z : (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size i = 0 ∨ (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size j = 0
    · intro x hx hy
      rcases z with z | z
      · simp only [Region.Contains, z] at hx; omega
      · simp only [Region.Contains, z] at hy; omega
    have hKi : i ≤ 1 ∨ K i = true := by
      rcases (by omega : i ≤ 1 ∨ 2 ≤ i) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl <;>
          exact z (.inl (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hKj : j ≤ 1 ∨ K j = true := by
      rcases (by omega : j ≤ 1 ∨ 2 ≤ j) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega : j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl <;>
          exact z (.inr (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hw : i ∈ Wb ∨ j ∈ Wb := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h'
      · exact .inl h.w0
      · exact .inl h.w1
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h''
      · exact .inr h.w0
      · exact .inr h.w1
      exact hK i hi j hj hij h' h'' (hKi.resolve_left (by omega)) (hKj.resolve_left (by omega))
    by_cases ei : i = 1
    · subst ei
      rw [b1]
      exact (hL.disj 1 (by omega) j (by omega) hij hw).sub_left hsub |>.sub_right (bi j hj (Ne.symm hij))
    · by_cases ej : j = 1
      · subst ej
        rw [b1]
        exact ((hL.disj i (by omega) 1 (by omega) hij hw).sub_right hsub).sub_left (bi i hi ei)
      · exact ((hL.disj i (by omega) j (by omega) hij hw).sub_left (bi i hi ei)).sub_right (bi j hj ej)

theorem Site.ctx : Ctx (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K) s :=
  ⟨VG.Proof.MlDsa.Arm.KeyGen.hashLay_ok h hK, by rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_size L s (by decide) (.inl rfl) (by decide)]; exact h.sz0, rfl, by simp [VG.Proof.MlDsa.Arm.KeyGen.hashLay],
    by rw [h.r7]; rfl, Nat.le_trans h.s8 h.spk, by simp [VG.Proof.MlDsa.Arm.KeyGen.hashLay],
    by rw [show (⟨State.addr ((VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).ptr 0), (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).size 0⟩ : Region) = L.buf 0 from rfl]
       exact h.cw 0 h.w0 (by decide)⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Contracts`. -/
section

/-!
# ML-DSA on 32-bit ARM: the contracts of the primitives, evaluated

For each primitive the top-level functions call, its contract's precondition
(`ntt_pre`, …), from plain facts about the state `x` the callee starts from:
the arguments in their registers (and the fifth in the stack slot, `stackArg x
0`), the regions it is given, their disjointness and the stack below `x.sp`;
what its postcondition says (`…_post`); and its public data, from the
equalities of two such states (`…_pub`). Each is proven once, by evaluating
the contract (`sig_pre`, `sig_post`, `sig_pub`) on a state that is a variable.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Closes the evaluated precondition of a contract from the hypotheses. -/
macro "cpre" : tactic => `(tactic| (
  try simp only [State.addr] at *
  and_intros <;> first
    | with_reducible assumption
    | (have := State.sp _ |>.isLt; omega)
    | omega
    | assumption))

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {stk : Nat} {x y : State}

theorem ip_pre {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {f w : BitVec 32} (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = w)
    (hrd : x.rd = []) (hwr : x.wr = [regA f 1024, regA w 1024]) (hsp : stk ≤ x.sp.toNat)
    (hd : (regA f 1024).Disjoint (regA w 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kw : (below x stk).Disjoint (regA w 1024)) (ff : f.toNat + 1024 ≤ 2 ^ 32) (fw : w.toNat + 1024 ≤ 2 ^ 32)
    (hr : Reduced x.mem (State.addr f)) : (inPlaceContract Arm.abi t stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem ip_post {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} (h : (inPlaceContract Arm.abi t stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0)) (t (polyAt x.mem (State.addr (x.gpr .r0)))) := by
  sig_post [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  exact h

theorem ip_pub {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (inPlaceContract Arm.abi t stk).pub x y := by
  sig_pub [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {stk : Nat} {x y : State} {h f g : BitVec 32}

theorem mul_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = f) (g2 : x.gpr .r2 = g)
    (hrd : x.rd = [regA f 1024, regA g 1024]) (hwr : x.wr = [regA h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA f 1024)) (d2 : (regA h 1024).Disjoint (regA g 1024))
    (kh : (below x stk).Disjoint (regA h 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kg : (below x stk).Disjoint (regA g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 32) (ff : f.toNat + 1024 ≤ 2 ^ 32)
    (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f)) (rg : Reduced x.mem (State.addr g)) :
    (mulContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem mul_post (hp : (mulContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (multiplyNTT (polyAt x.mem (State.addr (x.gpr .r1))) (polyAt x.mem (State.addr (x.gpr .r2)))) := by
  sig_post [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem mulAdd_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = f) (g2 : x.gpr .r2 = g)
    (hrd : x.rd = [regA f 1024, regA g 1024]) (hwr : x.wr = [regA h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA f 1024)) (d2 : (regA h 1024).Disjoint (regA g 1024))
    (kh : (below x stk).Disjoint (regA h 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kg : (below x stk).Disjoint (regA g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 32) (ff : f.toNat + 1024 ≤ 2 ^ 32)
    (fg : g.toNat + 1024 ≤ 2 ^ 32) (rh : Reduced x.mem (State.addr h)) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (mulAddContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem mulAdd_post (hp : (mulAddContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0)) (VG.Spec.MlDsa.add (polyAt x.mem (State.addr (x.gpr .r0)))
      (multiplyNTT (polyAt x.mem (State.addr (x.gpr .r1))) (polyAt x.mem (State.addr (x.gpr .r2))))) := by
  sig_post [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem mul_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (mulContract Arm.abi stk).pub x y := by
  sig_pub [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

theorem mulAdd_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (mulAddContract Arm.abi stk).pub x y := by
  sig_pub [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

end

/-! ## `vg_mldsa_add`, `vg_mldsa_sub` -/

section
variable {stk : Nat} {x y : State} {f g : BitVec 32}

theorem add_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = g) (hrd : x.rd = [regA g 1024])
    (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (regA f 1024).Disjoint (regA g 1024))
    (kf : (below x stk).Disjoint (regA f 1024)) (kg : (below x stk).Disjoint (regA g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 32) (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (addContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem add_post (hp : (addContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (VG.Spec.MlDsa.add (polyAt x.mem (State.addr (x.gpr .r0))) (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem add_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (addContract Arm.abi stk).pub x y := by
  sig_pub [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

theorem sub_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = g) (hrd : x.rd = [regA g 1024])
    (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (regA f 1024).Disjoint (regA g 1024))
    (kf : (below x stk).Disjoint (regA f 1024)) (kg : (below x stk).Disjoint (regA g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 32) (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (subContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem sub_post (hp : (subContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (VG.Spec.MlDsa.sub (polyAt x.mem (State.addr (x.gpr .r0))) (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem sub_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (subContract Arm.abi stk).pub x y := by
  sig_pub [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w e : BitVec 32}

theorem rejNtt_pre (g0 : x.gpr .r0 = sd) (g1 : x.gpr .r1 = a) (g2 : x.gpr .r2 = w)
    (hrd : x.rd = [regA sd 34]) (hwr : x.wr = [regA a 1024, regA w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA sd 34).Disjoint (regA a 1024)) (d2 : (regA sd 34).Disjoint (regA w 2048))
    (d3 : (regA a 1024).Disjoint (regA w 2048))
    (k1 : (below x stk).Disjoint (regA sd 34)) (k2 : (below x stk).Disjoint (regA a 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (f1 : sd.toNat + 34 ≤ 2 ^ 32) (f2 : a.toNat + 1024 ≤ 2 ^ 32)
    (f3 : w.toNat + 2048 ≤ 2 ^ 32) : (rejNTTContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem rejNtt_post (hp : (rejNTTContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r1))) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt x.mem (State.addr (x.gpr .r0)) 34)) (y.gpr .r0)
        (polyAt y.mem (State.addr (x.gpr .r1)))) := by
  sig_post [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem rejNtt_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) 34 = bytesAt y.mem (State.addr (y.gpr .r0)) 34) :
    (rejNTTContract Arm.abi stk).pub x y := by
  sig_pub [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2⟩

theorem rejBounded_pre (g0 : x.gpr .r0 = sd) (g1 : x.gpr .r1 = e) (g2 : x.gpr .r2 = a) (g3 : x.gpr .r3 = w)
    (hrd : x.rd = [regA sd 66]) (hwr : x.wr = [regA a 1024, regA w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA sd 66).Disjoint (regA a 1024)) (d2 : (regA sd 66).Disjoint (regA w 2048))
    (d3 : (regA a 1024).Disjoint (regA w 2048))
    (k1 : (below x stk).Disjoint (regA sd 66)) (k2 : (below x stk).Disjoint (regA a 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 32) (f2 : a.toNat + 1024 ≤ 2 ^ 32)
    (f3 : w.toNat + 2048 ≤ 2 ^ 32) (he : e.toNat = 2 ∨ e.toNat = 4) : (rejBoundedContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3]
    cpre

theorem rejBounded_post (hp : (rejBoundedContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r2))) ∧
      Outcome (fun b => (rejBoundedPoly (x.gpr .r1).toNat b.rejBounded (bytesAt x.mem (State.addr (x.gpr .r0)) 66)).map
        toRq) (y.gpr .r0) (polyAt y.mem (State.addr (x.gpr .r2)))) := by
  sig_post [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem rejBounded_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3)
    (hl : rejBoundedLeak (x.gpr .r1).toNat (bytesAt x.mem (State.addr (x.gpr .r0)) 66) =
      rejBoundedLeak (y.gpr .r1).toNat (bytesAt y.mem (State.addr (y.gpr .r0)) 66)) :
    (rejBoundedContract Arm.abi stk).pub x y := by
  sig_pub [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, hl, h0, h1, h2, h3⟩

end

/-! ## `vg_mldsa_power2round` -/

section
variable {stk : Nat} {x y : State} {t t1 t0 : BitVec 32}

theorem p2r_pre (g0 : x.gpr .r0 = t) (g1 : x.gpr .r1 = t1) (g2 : x.gpr .r2 = t0)
    (hrd : x.rd = [regA t 1024]) (hwr : x.wr = [regA t1 1024, regA t0 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA t 1024).Disjoint (regA t1 1024)) (d2 : (regA t 1024).Disjoint (regA t0 1024))
    (d3 : (regA t1 1024).Disjoint (regA t0 1024))
    (k1 : (below x stk).Disjoint (regA t 1024)) (k2 : (below x stk).Disjoint (regA t1 1024))
    (k3 : (below x stk).Disjoint (regA t0 1024)) (f1 : t.toNat + 1024 ≤ 2 ^ 32) (f2 : t1.toNat + 1024 ≤ 2 ^ 32)
    (f3 : t0.toNat + 1024 ≤ 2 ^ 32) (hr : Reduced x.mem (State.addr t)) : (power2RoundContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem p2r_post (hp : (power2RoundContract Arm.abi stk).post x y) :
    NatPolyIs y.mem (State.addr (x.gpr .r1))
        ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => (VG.Spec.MlDsa.power2Round c).1.toNat) ∧
      PolyIs y.mem (State.addr (x.gpr .r2)) ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) := by
  sig_post [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem p2r_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (power2RoundContract Arm.abi stk).pub x y := by
  sig_pub [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

end

/-! ## `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

section
variable {stk : Nat} {x y : State} {f a b o l : BitVec 32}

theorem sbp_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = b) (g2 : x.gpr .r2 = o) (g3 : x.gpr .r3 = l)
    (hrd : x.rd = [regA f 1024]) (hwr : x.wr = [regA o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA f 1024).Disjoint (regA o l.toNat))
    (k1 : (below x stk).Disjoint (regA f 1024)) (k2 : (below x stk).Disjoint (regA o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 32) (f2 : o.toNat + l.toNat ≤ 2 ^ 32) (hb : b.toNat ∈ simpleBitPackBounds)
    (hl : l.toNat = 32 * bitlen b.toNat) (hc : ∀ i < n, (coeffAt x.mem (State.addr f) i).toNat ≤ b.toNat) :
    (simpleBitPackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3]
    cpre

theorem sbp_post (hp : (simpleBitPackContract Arm.abi stk).post x y) :
    bytesAt y.mem (State.addr (x.gpr .r2)) (x.gpr .r3).toNat =
      VG.Spec.MlDsa.simpleBitPack (natPolyAt x.mem (State.addr (x.gpr .r0))) (x.gpr .r1).toNat := by
  sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem sbp_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) : (simpleBitPackContract Arm.abi stk).pub x y := by
  sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3⟩

theorem bp_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = a) (g2 : x.gpr .r2 = b) (g3 : x.gpr .r3 = o)
    (ga : stackArg x 0 = l)
    (hrd : x.rd = [regA f 1024, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA f 1024).Disjoint (regA o l.toNat)) (d2 : (regA o l.toNat).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA f 1024)) (k2 : (below x stk).Disjoint (regA o l.toNat))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : f.toNat + 1024 ≤ 2 ^ 32) (f2 : o.toNat + l.toNat ≤ 2 ^ 32) (hab : (a.toNat, b.toNat) ∈ bitPackParams)
    (hl : l.toNat = 32 * bitlen (a.toNat + b.toNat)) (hr : Reduced x.mem (State.addr f))
    (hc : ∀ i < n, -(a.toNat : Int) ≤ modPm (coeffAt x.mem (State.addr f) i).toNat VG.Spec.MlDsa.q ∧
      modPm (coeffAt x.mem (State.addr f) i).toNat VG.Spec.MlDsa.q ≤ b.toNat) :
    (bitPackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem bp_post (hp : (bitPackContract Arm.abi stk).post x y) :
    bytesAt y.mem (State.addr (x.gpr .r3)) (stackArg x 0).toNat =
      VG.Spec.MlDsa.bitPack ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => modPm c.val VG.Spec.MlDsa.q) (x.gpr .r1).toNat
        (x.gpr .r2).toNat := by
  sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem bp_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0) :
    (bitPackContract Arm.abi stk).pub x y := by
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {stk : Nat} {x y : State} {ct len tau c w : BitVec 32}

theorem ball_pre (g0 : x.gpr .r0 = ct) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = tau) (g3 : x.gpr .r3 = c)
    (ga : stackArg x 0 = w)
    (hrd : x.rd = [regA ct len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA c 1024, regA w 2048])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA ct len.toNat).Disjoint (regA c 1024)) (d2 : (regA ct len.toNat).Disjoint (regA w 2048))
    (d3 : (regA c 1024).Disjoint (regA w 2048)) (d4 : (regA c 1024).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (d5 : (regA w 2048).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA ct len.toNat)) (k2 : (below x stk).Disjoint (regA c 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (k4 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : ct.toNat + len.toNat ≤ 2 ^ 32) (f2 : c.toNat + 1024 ≤ 2 ^ 32) (f3 : w.toNat + 2048 ≤ 2 ^ 32)
    (hp : (len.toNat, tau.toNat) ∈ ballParams) : (sampleInBallContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem ball_post (hp : (sampleInBallContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r3))) ∧
      Outcome (fun b => (sampleInBall (x.gpr .r2).toNat b.ball
        (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat)).map toRq) (y.gpr .r0)
        (polyAt y.mem (State.addr (x.gpr .r3)))) := by
  sig_post [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem ball_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat =
      bytesAt y.mem (State.addr (y.gpr .r0)) (y.gpr .r1).toNat) :
    (sampleInBallContract Arm.abi stk).pub x y := by
  sig_pub [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {stk : Nat} {x y : State} {h r g2 o : BitVec 32}

theorem useHint_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = r) (gg : x.gpr .r2 = g2) (g3 : x.gpr .r3 = o)
    (hrd : x.rd = [regA h 1024, regA r 1024]) (hwr : x.wr = [regA o 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA o 1024)) (d2 : (regA r 1024).Disjoint (regA o 1024))
    (k1 : (below x stk).Disjoint (regA h 1024)) (k2 : (below x stk).Disjoint (regA r 1024))
    (k3 : (below x stk).Disjoint (regA o 1024)) (f1 : h.toNat + 1024 ≤ 2 ^ 32) (f2 : r.toNat + 1024 ≤ 2 ^ 32)
    (f3 : o.toNat + 1024 ≤ 2 ^ 32) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem (State.addr r)) :
    (useHintContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, gg, g3]
    cpre

theorem useHint_post (hp : (useHintContract Arm.abi stk).post x y) :
    NatPolyIs y.mem (State.addr (x.gpr .r3)) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint (x.gpr .r2).toNat hj rj).toNat)
      ((hintAt x.mem (State.addr (x.gpr .r0)) 1).headD (Vector.replicate n false))
      (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem useHint_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) : (useHintContract Arm.abi stk).pub x y := by
  sig_pub [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3⟩

end

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

section
variable {stk : Nat} {x y : State} {v len a b f : BitVec 32}

theorem bu_pre (g0 : x.gpr .r0 = v) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = a) (g3 : x.gpr .r3 = b)
    (ga : stackArg x 0 = f)
    (hrd : x.rd = [regA v len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA f 1024])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA v len.toNat).Disjoint (regA f 1024)) (d2 : (regA f 1024).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA v len.toNat)) (k2 : (below x stk).Disjoint (regA f 1024))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : v.toNat + len.toNat ≤ 2 ^ 32) (f2 : f.toNat + 1024 ≤ 2 ^ 32)
    (hab : (a.toNat, b.toNat) ∈ bitPackParams) (hl : len.toNat = 32 * bitlen (a.toNat + b.toNat)) :
    (bitUnpackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem bu_post (hp : (bitUnpackContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (stackArg x 0))
      (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat) (x.gpr .r2).toNat
        (x.gpr .r3).toNat)) := by
  sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem bu_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0) :
    (bitUnpackContract Arm.abi stk).pub x y := by
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3, ha⟩

theorem t1_pre (g0 : x.gpr .r0 = v) (g1 : x.gpr .r1 = f)
    (hrd : x.rd = [regA v 320]) (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA v 320).Disjoint (regA f 1024))
    (k1 : (below x stk).Disjoint (regA v 320)) (k2 : (below x stk).Disjoint (regA f 1024))
    (f1 : v.toNat + 320 ≤ 2 ^ 32) (f2 : f.toNat + 1024 ≤ 2 ^ 32) :
    (unpackT1Contract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem t1_post (hp : (unpackT1Contract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r1))
      ((simpleBitUnpack (bytesAt x.mem (State.addr (x.gpr .r0)) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  sig_post [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem t1_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (unpackT1Contract Arm.abi stk).pub x y := by
  sig_pub [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {stk : Nat} {x y : State} {yy len om h hl : BitVec 32}

theorem hbu_pre (g0 : x.gpr .r0 = yy) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = om) (g3 : x.gpr .r3 = h)
    (ga : stackArg x 0 = hl)
    (hrd : x.rd = [regA yy len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA h (hl.toNat * 4)])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA yy len.toNat).Disjoint (regA h (hl.toNat * 4)))
    (d2 : (regA h (hl.toNat * 4)).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA yy len.toNat)) (k2 : (below x stk).Disjoint (regA h (hl.toNat * 4)))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : yy.toNat + len.toNat ≤ 2 ^ 32) (f2 : h.toNat + hl.toNat * 4 ≤ 2 ^ 32)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat)) :
    (hintBitUnpackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem hbu_post (hp : (hintBitUnpackContract Arm.abi stk).post x y) :
    match hintBitUnpack (x.gpr .r2).toNat ((x.gpr .r1).toNat - (x.gpr .r2).toNat)
      (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat) with
    | some hint => y.gpr .r0 = 1 ∧ HintIs y.mem (State.addr (x.gpr .r3)) ((x.gpr .r1).toNat - (x.gpr .r2).toNat) hint
    | none => y.gpr .r0 = 0 := by
  sig_post [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem hbu_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat =
      bytesAt y.mem (State.addr (y.gpr .r0)) (y.gpr .r1).toNat) :
    (hintBitUnpackContract Arm.abi stk).pub x y := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {stk : Nat} {x y : State} {f : BitVec 32}

theorem normLt_pre (g0 : x.gpr .r0 = f) (hrd : x.rd = [regA f 1024]) (hwr : x.wr = [])
    (hsp : stk ≤ x.sp.toNat) (k1 : (below x stk).Disjoint (regA f 1024)) (f1 : f.toNat + 1024 ≤ 2 ^ 32)
    (hr : Reduced x.mem (State.addr f)) : (normLtContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0]
    cpre

theorem normLt_post (hp : (normLtContract Arm.abi stk).post x y) :
    y.gpr .r0 = if normRq [polyAt x.mem (State.addr (x.gpr .r0))] < (x.gpr .r1).toNat then 1 else 0 := by
  sig_post [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem normLt_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (normLtContract Arm.abi stk).pub x y := by
  sig_pub [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call`. -/
section

/-!
# ML-DSA on 32-bit ARM: calling the primitives on the buffers of a `Site`

A call of each primitive, with its arguments pointers into the buffers of a
`Site` (`PtrIn`): the callee's precondition from the layout (`ip_preS`, …),
what the call changes and what its postcondition says (`ip_ok`, …), and that
two runs of it with the same pointers leak the same (`ip_tr`, …).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A pointer, in a register of the layout, to `l` bytes of a buffer (but the stack). -/
def PtrIn (L : Lay) (q : Ptr) (l : Nat) : Prop := VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr q) = true ∧ VG.Proof.MlDsa.Arm.KeyGen.inB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri q l) = true

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s)
include hs

theorem Site.regE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) (hl : 0 < l) :
    regA (L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2) l = L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l := by
  simp only [regA, (hs.addr pq.2 hl).1]

theorem Site.fitE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) (hl : 0 < l) :
    (L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2).toNat + l ≤ 2 ^ 32 := (hs.addr pq.2 hl).2

theorem Site.addrE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) (hl : 0 < l) :
    State.addr (L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2) = VG.Proof.MlDsa.Arm.KeyGen.lpa L q := (hs.addr pq.2 hl).1

/-- A pointer argument's register after the moves. -/
theorem Site.gE {as : List (Reg × Arg)} (hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {q : Ptr}
    (hm : (d, .ptr q) ∈ as) (hq : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr q) = true) :
    (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as).gpr d = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) + BitVec.ofNat 32 q.2 := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s hg hn hm, hs.val hq]

/-- A buffer the state may write. -/
theorem Site.cwE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) (wq : VG.Proof.MlDsa.Arm.KeyGen.ix q.1 ∈ Wb) : Covers [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l] s.wr :=
  Site.covW (w := (VG.Proof.MlDsa.Arm.KeyGen.ix q.1, q.2, l)) pq.2 (hs.cw _ wq (VG.Proof.MlDsa.Arm.KeyGen.inB_bounds pq.2).1)

/-- A buffer the state may read. -/
theorem Site.crE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) : Covers [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l] (s.rd ++ s.wr) :=
  Site.covR (w := (VG.Proof.MlDsa.Arm.KeyGen.ix q.1, q.2, l)) pq.2 (hs.cr _ (by have := (VG.Proof.MlDsa.Arm.KeyGen.inB_bounds pq.2).2.1; rw [hs.len] at this; exact this) (VG.Proof.MlDsa.Arm.KeyGen.inB_bounds pq.2).1)

/-- Two regions apart, one of them written. -/
theorem Site.dE {q q' : Ptr} {l l' : Nat} (hd : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri q l) (VG.Proof.MlDsa.Arm.KeyGen.tri q' l') = true)
    (hw : VG.Proof.MlDsa.Arm.KeyGen.ix q.1 ∈ Wb ∨ VG.Proof.MlDsa.Arm.KeyGen.ix q'.1 ∈ Wb) : (L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l).Disjoint (L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q'.1) q'.2 l') := VG.Proof.MlDsa.Arm.KeyGen.disjW hs.ok hd hw

/-- The stack below the stack pointer is apart from a buffer. -/
theorem Site.kE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) {n : Nat} (hn : n ≤ STK) {x : State} (hx : x.sp = s.sp) :
    (below x n).Disjoint (L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l) := by
  have := (hs.stkD pq.2 hn).symm
  simp only [below, hx] at this ⊢
  exact this

end

theorem view_glue_sp (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as) rd wr).sp = s.sp := VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp s as

theorem view_glue_mem (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as) rd wr).mem = s.mem := VG.Proof.MlDsa.Arm.KeyGen.glueSt_mem s as

/-- The registers of the layout, the stack pointer, and the pointers of both
runs are the same. -/
theorem Site.gpr_eq {L : Lay} {Wb : List Nat} {STK : Nat} {x y : State} (hx : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x) (hy : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y)
    {as : List (Reg × Arg)} (hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {a : Arg} (hm : (d, a) ∈ as) :
    (VG.Proof.MlDsa.Arm.KeyGen.glueSt x as).gpr d = (VG.Proof.MlDsa.Arm.KeyGen.glueSt y as).gpr d := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg x hg hn hm, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg y hg hn hm]
  cases a with
  | imm v => rfl
  | ptr q =>
    have ha : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr q) = true := by
      have := List.all_eq_true.mp hg _ hm; simp only [Bool.and_eq_true] at this; exact this.2
    rw [hx.val ha, hy.val ha]

/-- Kept, with the regions written those of the triples `W`. -/
theorem Site.keptW {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s)
    (W : List (Nat × Nat × Nat)) {n : Nat} (hn : n ≤ STK) (hk : Kept (L.RL W ++ [below s n]) s s') :
    Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  hs.kept_stk (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact ⟨w, hw, fun _ h => h⟩) hn hk

theorem imm_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Calls in a frame that pushes the stack argument -/

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (s1 : State)
  (e1 : s1.sp = s.sp) (rd wr : List Region)
include hs e1

omit hs in
theorem push_sp : (view (pushed [.r12] s1) rd wr).sp = s.sp - BitVec.ofNat 32 4 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e1]; rfl

omit hs in
theorem push_spN (h4 : 4 ≤ s.sp.toNat) : (view (pushed [.r12] s1) rd wr).sp.toNat = s.sp.toNat - 4 := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.push_sp s1 e1]; bv_omega

omit hs in
theorem push_argAddr : stackArgAddr (view (pushed [.r12] s1) rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 4) := by
  show State.addr ((view (pushed [.r12] s1) rd wr).sp + BitVec.ofNat 32 (4 * 0)) = _
  rw [VG.Proof.MlDsa.Arm.KeyGen.push_sp s1 e1]; congr 1; bv_omega

omit hs e1 in
theorem push_arg : stackArg (view (pushed [.r12] s1) rd wr) 0 = s1.gpr .r12 := by
  have e : stackArgAddr (view (pushed [.r12] s1) rd wr) 0 = State.addr (s1.sp - BitVec.ofNat 32 4) := by
    show State.addr ((pushed [.r12] s1).sp + BitVec.ofNat 32 (4 * 0)) = _
    rw [pushed_sp]; congr 1; simp only [List.length_cons, List.length_nil]; bv_omega
  show (pushed [.r12] s1).mem.readW (stackArgAddr (view (pushed [.r12] s1) rd wr) 0) 32 = _
  rw [e]; exact VG.Proof.MlDsa.Arm.KeyGen.pushed12_word s1

/-- The stack a callee in the frame may use is apart from a buffer. -/
theorem push_kE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) {n : Nat} (hn : 4 + n ≤ STK) :
    (below (view (pushed [.r12] s1) rd wr) n).Disjoint (L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l) := by
  have h4 : 4 + n ≤ s.sp.toNat := Nat.le_trans hn hs.spk
  refine ((hs.stkD pq.2 hn).symm).sub_left ?_
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  simp only [Region.Contains, VG.Proof.MlDsa.Arm.KeyGen.push_sp s1 e1] at hx ⊢
  bv_omega

/-- The stack slot of the argument is apart from a buffer. -/
theorem push_aE {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) :
    (L.R (VG.Proof.MlDsa.Arm.KeyGen.ix q.1) q.2 l).Disjoint ⟨stackArgAddr (view (pushed [.r12] s1) rd wr) 0, 4⟩ := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.push_argAddr s1 e1 rd wr]
  refine (hs.stkD pq.2 (n := 4) (by have := hs.s8; omega)).sub_right ?_
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  have := hs.s8; have := hs.spk
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- The stack a callee in the frame may use is apart from the stack slot of its argument. -/
theorem push_kA {n : Nat} (hn : 4 + n ≤ STK) :
    (below (view (pushed [.r12] s1) rd wr) n).Disjoint ⟨stackArgAddr (view (pushed [.r12] s1) rd wr) 0, 4⟩ := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.push_argAddr s1 e1 rd wr]
  intro x hx hy
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  have := hs.s8; have := hs.spk
  simp only [Region.Contains, VG.Proof.MlDsa.Arm.KeyGen.push_sp s1 e1] at hx hy
  bv_omega

/-- The memory of the frame: the pushed word below the stack pointer. -/
theorem push_frame (hm : s1.mem = s.mem) : Frame [below s 4] s.mem (view (pushed [.r12] s1) rd wr).mem := by
  have h4 : 4 ≤ s1.sp.toNat := by rw [e1]; have := hs.s8; have := hs.spk; omega
  have := VG.Proof.MlDsa.Arm.KeyGen.pushed12_frame s1 h4
  simp only [below, e1, hm] at this
  exact this

/-- A buffer's bytes in the frame. -/
theorem push_bytes (hm : s1.mem = s.mem) {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) (hl : l ≤ 2 ^ 64) :
    ∀ k < l, (view (pushed [.r12] s1) rd wr).mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q + BitVec.ofNat 64 k) = s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q + BitVec.ofNat 64 k) :=
  Proof.MlKem.bytes_frame (VG.Proof.MlDsa.Arm.KeyGen.push_frame hs s1 e1 rd wr hm) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hs.stkD pq.2 (by have := hs.s8; omega)) hl

omit hs e1 in
theorem push_fit (h4 : 4 ≤ s.sp.toNat) (e1 : s1.sp = s.sp) :
    (view (pushed [.r12] s1) rd wr).sp.toNat + 4 ≤ 2 ^ 32 := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.push_spN s1 e1 rd wr h4]; have := s.sp.isLt; omega

end

theorem sp4 {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) : 4 ≤ s.sp.toNat := by
  have := hs.s8; have := hs.spk; omega

/-- A polynomial of a buffer in the frame. -/
theorem push_reduced {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q 1024) :
    Reduced (view (pushed [.r12] s1) rd wr).mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) ↔ Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) :=
  ⟨Proof.MlDsa.Verify.reduced_congr fun k hk => (VG.Proof.MlDsa.Arm.KeyGen.push_bytes hs s1 e1 rd wr hm pq (by decide) k hk).symm,
    Proof.MlDsa.Verify.reduced_congr (VG.Proof.MlDsa.Arm.KeyGen.push_bytes hs s1 e1 rd wr hm pq (by decide))⟩

theorem push_polyAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q 1024) :
    polyAt (view (pushed [.r12] s1) rd wr).mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) = polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) :=
  Proof.MlDsa.Verify.polyAt_congr (VG.Proof.MlDsa.Arm.KeyGen.push_bytes hs s1 e1 rd wr hm pq (by decide))

theorem push_coeffAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q 1024) {i : Nat} (hi : i < n) :
    coeffAt (view (pushed [.r12] s1) rd wr).mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) i = coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) i :=
  Proof.MlDsa.Verify.coeffAt_congr (VG.Proof.MlDsa.Arm.KeyGen.push_bytes hs s1 e1 rd wr hm pq (by decide)) hi

theorem push_bytesAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} {l : Nat} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q l) (hl : l < 2 ^ 64) :
    bytesAt (view (pushed [.r12] s1) rd wr).mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) l = bytesAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) l := by
  have hb := VG.Proof.MlDsa.Arm.KeyGen.push_bytes hs s1 e1 rd wr hm pq (Nat.le_of_lt hl)
  exact Proof.MlKem.bytesAt_eq! (by simp [bytesAt]) fun k hk => by
    rw [Proof.MlKem.bytesAt_getElem! _ _ hk, hb k hk]

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {f w : Ptr}

abbrev ipArgs (f w : Ptr) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .ptr w)]
abbrev ipWr (L : Lay) (f w : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) f.2 1024, L.R (VG.Proof.MlDsa.Arm.KeyGen.ix w.1) w.2 1024]

theorem ip_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024)
    (pw : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L w 1024) (wf : VG.Proof.MlDsa.Arm.KeyGen.ix f.1 ∈ Wb) (hd : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri w 1024) = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) :
    (inPlaceContract Arm.abi t stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w)) [] (VG.Proof.MlDsa.Arm.KeyGen.ipWr L f w)) := by
  have hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w) = true := by simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, pf.1, pw.1]
  have hn : ((VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w) [] (VG.Proof.MlDsa.Arm.KeyGen.ipWr L f w)
  refine VG.Proof.MlDsa.Arm.KeyGen.ip_pre (by rw [view_r0, hs.gE hg hn (by simp) pf.1]) (by rw [view_r1, hs.gE hg hn (by simp) pw.1]) rfl
    (by rw [State.withRegions_wr, hs.regE pf (by decide), hs.regE pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ (hs.fitE pf (by decide)) (hs.fitE pw (by decide)) ?_
  · rw [hs.regE pf (by decide), hs.regE pw (by decide)]; exact hs.dE hd (.inl wf)
  · rw [hs.regE pf (by decide)]; exact hs.kE pf hstk hsp
  · rw [hs.regE pw (by decide)]; exact hs.kE pw hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE pf (by decide)]; exact hr

theorem ip_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => inPlaceContract Arm.abi t stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024) (pw : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L w 1024)
    (wf : VG.Proof.MlDsa.Arm.KeyGen.ix f.1 ∈ Wb) (ww : VG.Proof.MlDsa.Arm.KeyGen.ix w.1 ∈ Wb) (hd : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri w 1024) = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri f 1024, VG.Proof.MlDsa.Arm.KeyGen.tri w 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) (t (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f))) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w) = true := by simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, pf.1, pw.1]
  have hn : ((VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have cw : Covers (VG.Proof.MlDsa.Arm.KeyGen.ipWr L f w) s.wr := covers_cons' (hs.cwE pf wf) (covers_cons' (hs.cwE pw ww) covers_nil')
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 hg (VG.Proof.MlDsa.Arm.KeyGen.ip_preS hs (Nat.le_trans hstk hS) pf pw wf hd hr) (Covers.right cw) cw
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.kept_stk (W := [VG.Proof.MlDsa.Arm.KeyGen.tri f 1024, VG.Proof.MlDsa.Arm.KeyGen.tri w 1024]) (fun r hr => ?_) (Nat.le_trans hc.stack hS) hk) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · have := VG.Proof.MlDsa.Arm.KeyGen.ip_post hp
    rwa [State.withRegions_mem, view_r0, hs.gE hg hn (by simp) pf.1, hs.addrE pf (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this

theorem ip_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => inPlaceContract Arm.abi t stk) S) (hS : S ≤ STK)
    {name : String} (pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024) (pw : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L w 1024) (wf : VG.Proof.MlDsa.Arm.KeyGen.ix f.1 ∈ Wb) (ww : VG.Proof.MlDsa.Arm.KeyGen.ix w.1 ∈ Wb)
    (hd : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri w 1024) = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have hg : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w) = true := by simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, pf.1, pw.1]
  have hn : ((VG.Proof.MlDsa.Arm.KeyGen.ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 hg fun x y h => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y h
  have cx : Covers (VG.Proof.MlDsa.Arm.KeyGen.ipWr L f w) x.wr := covers_cons' (hx.cwE pf wf) (covers_cons' (hx.cwE pw ww) covers_nil')
  have cy : Covers (VG.Proof.MlDsa.Arm.KeyGen.ipWr L f w) y.wr := covers_cons' (hy.cwE pf wf) (covers_cons' (hy.cwE pw ww) covers_nil')
  refine ⟨[], VG.Proof.MlDsa.Arm.KeyGen.ipWr L f w, VG.Proof.MlDsa.Arm.KeyGen.ip_preS hx (Nat.le_trans hstk hS) pf pw wf hd rx,
    VG.Proof.MlDsa.Arm.KeyGen.ip_preS hy (Nat.le_trans hstk hS) pf pw wf hd ry, VG.Proof.MlDsa.Arm.KeyGen.ip_pub ?_ ?_ ?_, Covers.right cx, cx, Covers.right cy, cy⟩
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp]
  · rw [view_r0, view_r0, hx.gE hg hn (by simp) pf.1, hy.gE hg hn (by simp) pf.1]
  · rw [view_r1, view_r1, hx.gE hg hn (by simp) pw.1, hy.gE hg hn (by simp) pw.1]

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallArith`. -/
section

/-!
# ML-DSA on 32-bit ARM: calling the multiplications, additions and subtractions

As `ip_ok` and `ip_tr` (`Call.lean`), for `vg_mldsa_multiply_ntt`,
`vg_mldsa_multiply_add_ntt`, `vg_mldsa_add` and `vg_mldsa_sub`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h f g : Ptr}

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.r0, .ptr h), (.r1, .ptr f), (.r2, .ptr g)]
abbrev mulRd (L : Lay) (f g : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) f.2 1024, L.R (VG.Proof.MlDsa.Arm.KeyGen.ix g.1) g.2 1024]
abbrev mulWr (L : Lay) (h : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix h.1) h.2 1024]

/-- The facts the multiplications need of their pointers. -/
structure MulOk (L : Lay) (Wb : List Nat) (h f g : Ptr) : Prop where
  ph : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L h 1024
  pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024
  pg : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L g 1024
  wh : VG.Proof.MlDsa.Arm.KeyGen.ix h.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri h 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) = true
  d2 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri h 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri g 1024) = true

theorem MulOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.ph.1, m.pf.1, m.pg.1]

theorem mulArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem mulG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix h.1) + BitVec.ofNat 32 h.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) rd wr).gpr .r1 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) rd wr).gpr .r2 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix g.1) + BitVec.ofNat 32 g.2 :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.mulArgs_nodup (by simp) m.ph.1],
    by rw [view_r1, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.mulArgs_nodup (by simp) m.pf.1],
    by rw [view_r2, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.mulArgs_nodup (by simp) m.pg.1]⟩

theorem mul_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    (mulContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g) (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hs m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  refine VG.Proof.MlDsa.Arm.KeyGen.mul_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.pf (by decide), hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.ph (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [hs.regE m.ph (by decide), hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inl m.wh)
  · rw [hs.regE m.ph (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d2 (.inl m.wh)
  · rw [hs.regE m.ph (by decide)]; exact hs.kE m.ph hstk hsp
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem mulAdd_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g)
    (rh : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h)) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    (mulAddContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g) (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hs m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  refine VG.Proof.MlDsa.Arm.KeyGen.mulAdd_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.pf (by decide), hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.ph (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_ ?_
  · rw [hs.regE m.ph (by decide), hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inl m.wh)
  · rw [hs.regE m.ph (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d2 (.inl m.wh)
  · rw [hs.regE m.ph (by decide)]; exact hs.kE m.ph hstk hsp
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.ph (by decide)]; exact rh
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem mul_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g ++ VG.Proof.MlDsa.Arm.KeyGen.mulWr L h) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pf) (covers_cons' (hs.crE m.pg) covers_nil'))
    (Covers.right (covers_cons' (hs.cwE m.ph m.wh) covers_nil')), covers_cons' (hs.cwE m.ph m.wh) covers_nil'⟩

theorem mul_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => mulContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri h 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g))) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mul_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.mul_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hs m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  have := VG.Proof.MlDsa.Arm.KeyGen.mul_post hp
  rwa [State.withRegions_mem, g0, g1, g2, hs.addrE m.ph (by decide), hs.addrE m.pf (by decide),
    hs.addrE m.pg (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this

theorem mulAdd_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => mulAddContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g)
    (rh : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h)) (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri h 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h))
        (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)))) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mul_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.mulAdd_preS hs (Nat.le_trans hstk hS) m rh rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hs m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  have := VG.Proof.MlDsa.Arm.KeyGen.mulAdd_post hp
  rwa [State.withRegions_mem, g0, g1, g2, hs.addrE m.ph (by decide), hs.addrE m.pf (by decide),
    hs.addrE m.pg (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this

theorem mul_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => mulContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rfx, rgx, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hx m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  obtain ⟨gy0, gy1, gy2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hy m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g, VG.Proof.MlDsa.Arm.KeyGen.mulWr L h, VG.Proof.MlDsa.Arm.KeyGen.mul_preS hx (Nat.le_trans hstk hS) m rfx rgx,
    VG.Proof.MlDsa.Arm.KeyGen.mul_preS hy (Nat.le_trans hstk hS) m rfy rgy, VG.Proof.MlDsa.Arm.KeyGen.mul_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]), (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hx m).2,
    (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hy m).2⟩

theorem mulAdd_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => mulAddContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.MulOk L Wb h f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h) ∧
      Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L h) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.mulArgs h f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rhx, rfx, rgx, rhy, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hx m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  obtain ⟨gy0, gy1, gy2⟩ := VG.Proof.MlDsa.Arm.KeyGen.mulG hy m (VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g) (VG.Proof.MlDsa.Arm.KeyGen.mulWr L h)
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.mulRd L f g, VG.Proof.MlDsa.Arm.KeyGen.mulWr L h, VG.Proof.MlDsa.Arm.KeyGen.mulAdd_preS hx (Nat.le_trans hstk hS) m rhx rfx rgx,
    VG.Proof.MlDsa.Arm.KeyGen.mulAdd_preS hy (Nat.le_trans hstk hS) m rhy rfy rgy, VG.Proof.MlDsa.Arm.KeyGen.mulAdd_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]), (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hx m).2,
    (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.mul_cov hy m).2⟩

end

/-! ## `vg_mldsa_add`, `vg_mldsa_sub` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f g : Ptr}

abbrev accArgs (f g : Ptr) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .ptr g)]
abbrev accRd (L : Lay) (g : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix g.1) g.2 1024]
abbrev accWr (L : Lay) (f : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) f.2 1024]

/-- The facts the additions need of their pointers. -/
structure AccOk (L : Lay) (Wb : List Nat) (f g : Ptr) : Prop where
  pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024
  pg : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L g 1024
  wf : VG.Proof.MlDsa.Arm.KeyGen.ix f.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri g 1024) = true

theorem AccOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.pf.1, m.pg.1]

theorem accArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.accArgs f g).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem accG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) rd wr).gpr .r1 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix g.1) + BitVec.ofNat 32 g.2 :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.accArgs_nodup (by simp) m.pf.1],
    by rw [view_r1, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.accArgs_nodup (by simp) m.pg.1]⟩

theorem acc_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.accRd L g ++ VG.Proof.MlDsa.Arm.KeyGen.accWr L f) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.accWr L f) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pg) covers_nil') (Covers.right (covers_cons' (hs.cwE m.pf m.wf) covers_nil')),
    covers_cons' (hs.cwE m.pf m.wf) covers_nil'⟩

theorem add_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    (addContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g) (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  obtain ⟨g0, g1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hs m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  refine VG.Proof.MlDsa.Arm.KeyGen.add_pre g0 g1 (by rw [State.withRegions_rd, hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pf (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [hs.regE m.pf (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d1 (.inl m.wf)
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem sub_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    (subContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g) (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  obtain ⟨g0, g1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hs m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  refine VG.Proof.MlDsa.Arm.KeyGen.sub_pre g0 g1 (by rw [State.withRegions_rd, hs.regE m.pg (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pf (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [hs.regE m.pf (by decide), hs.regE m.pg (by decide)]; exact hs.dE m.d1 (.inl m.wf)
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [hs.regE m.pg (by decide)]; exact hs.kE m.pg hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pf (by decide)]; exact rf
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pg (by decide)]; exact rg

theorem add_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => addContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g))) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.acc_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.add_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hs m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  have := VG.Proof.MlDsa.Arm.KeyGen.add_post hp
  rwa [State.withRegions_mem, g0, g1, hs.addrE m.pf (by decide), hs.addrE m.pg (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this

theorem sub_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => subContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g)
    (rf : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (rg : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) (VG.Spec.MlDsa.sub (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) (polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g))) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.acc_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.sub_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hs m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  have := VG.Proof.MlDsa.Arm.KeyGen.sub_post hp
  rwa [State.withRegions_mem, g0, g1, hs.addrE m.pf (by decide), hs.addrE m.pg (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this

theorem add_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => addContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rfx, rgx, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hx m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  obtain ⟨gy0, gy1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hy m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.accRd L g, VG.Proof.MlDsa.Arm.KeyGen.accWr L f, VG.Proof.MlDsa.Arm.KeyGen.add_preS hx (Nat.le_trans hstk hS) m rfx rgx,
    VG.Proof.MlDsa.Arm.KeyGen.add_preS hy (Nat.le_trans hstk hS) m rfy rgy, VG.Proof.MlDsa.Arm.KeyGen.add_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]), (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hy m).2⟩

theorem sub_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => subContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.AccOk L Wb f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧ Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L g)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.accArgs f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rfx, rgx, rfy, rgy⟩ := hP x y hxy
  obtain ⟨gx0, gx1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hx m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  obtain ⟨gy0, gy1⟩ := VG.Proof.MlDsa.Arm.KeyGen.accG hy m (VG.Proof.MlDsa.Arm.KeyGen.accRd L g) (VG.Proof.MlDsa.Arm.KeyGen.accWr L f)
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.accRd L g, VG.Proof.MlDsa.Arm.KeyGen.accWr L f, VG.Proof.MlDsa.Arm.KeyGen.sub_preS hx (Nat.le_trans hstk hS) m rfx rgx,
    VG.Proof.MlDsa.Arm.KeyGen.sub_preS hy (Nat.le_trans hstk hS) m rfy rgy, VG.Proof.MlDsa.Arm.KeyGen.sub_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]), (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.acc_cov hy m).2⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallPack`. -/
section

/-!
# ML-DSA on 32-bit ARM: calling `Power2Round` and the encodings of key generation

As `ip_ok` and `ip_tr` (`Call.lean`), for `vg_mldsa_power2round`,
`vg_mldsa_simple_bit_pack` and `vg_mldsa_bit_pack`, whose fifth argument, the
length, is on the stack.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_power2round` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t t1 t0 : Ptr}

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.r0, .ptr t), (.r1, .ptr t1), (.r2, .ptr t0)]
abbrev p2rRd (L : Lay) (t : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix t.1) t.2 1024]
abbrev p2rWr (L : Lay) (t1 t0 : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix t1.1) t1.2 1024, L.R (VG.Proof.MlDsa.Arm.KeyGen.ix t0.1) t0.2 1024]

/-- The facts `vg_mldsa_power2round` needs of its pointers. -/
structure P2rOk (L : Lay) (Wb : List Nat) (t t1 t0 : Ptr) : Prop where
  pt : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L t 1024
  p1 : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L t1 1024
  p0 : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L t0 1024
  w1 : VG.Proof.MlDsa.Arm.KeyGen.ix t1.1 ∈ Wb
  w0 : VG.Proof.MlDsa.Arm.KeyGen.ix t0.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri t 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri t1 1024) = true
  d2 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri t 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri t0 1024) = true
  d3 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri t1 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri t0 1024) = true

theorem P2rOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.P2rOk L Wb t t1 t0) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.pt.1, m.p1.1, m.p0.1]

theorem p2rArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem p2rG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.P2rOk L Wb t t1 t0) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0)) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix t.1) + BitVec.ofNat 32 t.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0)) rd wr).gpr .r1 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix t1.1) + BitVec.ofNat 32 t1.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0)) rd wr).gpr .r2 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix t0.1) + BitVec.ofNat 32 t0.2 :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.p2rArgs_nodup (by simp) m.pt.1],
    by rw [view_r1, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.p2rArgs_nodup (by simp) m.p1.1],
    by rw [view_r2, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.p2rArgs_nodup (by simp) m.p0.1]⟩

theorem p2r_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.P2rOk L Wb t t1 t0) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t ++ VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pt) covers_nil')
    (Covers.right (covers_cons' (hs.cwE m.p1 m.w1) (covers_cons' (hs.cwE m.p0 m.w0) covers_nil'))),
    covers_cons' (hs.cwE m.p1 m.w1) (covers_cons' (hs.cwE m.p0 m.w0) covers_nil')⟩

theorem p2r_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.P2rOk L Wb t t1 t0)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t)) :
    (power2RoundContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0)) (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t) (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0) (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t) (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0)
  obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.p2rG hs m (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t) (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0)
  refine VG.Proof.MlDsa.Arm.KeyGen.p2r_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.pt (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.p1 (by decide), hs.regE m.p0 (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ ?_ ?_ ?_
    (hs.fitE m.pt (by decide)) (hs.fitE m.p1 (by decide)) (hs.fitE m.p0 (by decide)) ?_
  · rw [hs.regE m.pt (by decide), hs.regE m.p1 (by decide)]; exact hs.dE m.d1 (.inr m.w1)
  · rw [hs.regE m.pt (by decide), hs.regE m.p0 (by decide)]; exact hs.dE m.d2 (.inr m.w0)
  · rw [hs.regE m.p1 (by decide), hs.regE m.p0 (by decide)]; exact hs.dE m.d3 (.inl m.w1)
  · rw [hs.regE m.pt (by decide)]; exact hs.kE m.pt hstk hsp
  · rw [hs.regE m.p1 (by decide)]; exact hs.kE m.p1 hstk hsp
  · rw [hs.regE m.p0 (by decide)]; exact hs.kE m.p0 hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pt (by decide)]; exact hr

theorem p2r_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => power2RoundContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.P2rOk L Wb t t1 t0) (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t))
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri t1 1024, VG.Proof.MlDsa.Arm.KeyGen.tri t0 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t1) ((polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t)).map fun c => (VG.Spec.MlDsa.power2Round c).1.toNat) →
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t0) ((polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t)).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.p2r_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.p2r_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri t1 1024, VG.Proof.MlDsa.Arm.KeyGen.tri t0 1024] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.p2rG hs m (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t) (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0)
    have := VG.Proof.MlDsa.Arm.KeyGen.p2r_post hp
    rw [State.withRegions_mem, g0, g1, g2, hs.addrE m.pt (by decide), hs.addrE m.p1 (by decide),
      hs.addrE m.p0 (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this
  exacts [this.1, this.2]

theorem p2r_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => power2RoundContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.P2rOk L Wb t t1 t0) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t) ∧
      Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L t)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.p2rArgs t t1 t0)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := VG.Proof.MlDsa.Arm.KeyGen.p2rG hx m (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t) (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0)
  obtain ⟨gy0, gy1, gy2⟩ := VG.Proof.MlDsa.Arm.KeyGen.p2rG hy m (VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t) (VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0)
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.p2rRd L t, VG.Proof.MlDsa.Arm.KeyGen.p2rWr L t1 t0, VG.Proof.MlDsa.Arm.KeyGen.p2r_preS hx (Nat.le_trans hstk hS) m rx, VG.Proof.MlDsa.Arm.KeyGen.p2r_preS hy (Nat.le_trans hstk hS) m ry,
    VG.Proof.MlDsa.Arm.KeyGen.p2r_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]),
    (VG.Proof.MlDsa.Arm.KeyGen.p2r_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.p2r_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.p2r_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.p2r_cov hy m).2⟩

end

/-! ## `vg_mldsa_simple_bit_pack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f o : Ptr} {b l : Nat}

abbrev sbpArgs (f : Ptr) (b : Nat) (o : Ptr) (l : Nat) : List (Reg × Arg) :=
  [(.r0, .ptr f), (.r1, .imm b), (.r2, .ptr o), (.r3, .imm l)]
abbrev sbpRd (L : Lay) (f : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) f.2 1024]
abbrev sbpWr (L : Lay) (o : Ptr) (l : Nat) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix o.1) o.2 l]

/-- The facts `vg_mldsa_simple_bit_pack` needs of its arguments. -/
structure SbpOk (L : Lay) (Wb : List Nat) (f : Ptr) (b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024
  po : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L o l
  wo : VG.Proof.MlDsa.Arm.KeyGen.ix o.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri o l) = true
  hb : b ∈ simpleBitPackBounds
  hl : l = 32 * bitlen b

theorem SbpOk.lt (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l) : b < 2 ^ 32 ∧ 0 < l ∧ l < 2 ^ 32 := by
  have hb := m.hb
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [m.hl]
  rcases hb with rfl | rfl | rfl <;> decide

theorem SbpOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.pf.1, m.po.1, show ∀ v, VG.Proof.MlDsa.Arm.KeyGen.argOk (.imm v) = true from fun _ => rfl]

theorem sbpArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem sbpG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) rd wr).gpr .r1 = BitVec.ofNat 32 b ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) rd wr).gpr .r2 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix o.1) + BitVec.ofNat 32 o.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) rd wr).gpr .r3 = BitVec.ofNat 32 l :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.sbpArgs_nodup (by simp) m.pf.1],
    by rw [view_r1, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.sbpArgs_nodup (a := .imm b) (by simp)]; rfl,
    by rw [view_r2, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.sbpArgs_nodup (by simp) m.po.1],
    by rw [view_r3, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.sbpArgs_nodup (a := .imm l) (by simp)]; rfl⟩

theorem sbp_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pf) covers_nil') (Covers.right (covers_cons' (hs.cwE m.po m.wo) covers_nil')),
    covers_cons' (hs.cwE m.po m.wo) covers_nil'⟩

theorem sbp_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l)
    (hc : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat ≤ b) :
    (simpleBitPackContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l) (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  obtain ⟨g0, g1, g2, g3⟩ := VG.Proof.MlDsa.Arm.KeyGen.sbpG hs m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  obtain ⟨lb, l0, ll⟩ := m.lt
  refine VG.Proof.MlDsa.Arm.KeyGen.sbp_pre g0 g1 g2 g3 (by rw [State.withRegions_rd, hs.regE m.pf (by decide)])
    (by rw [State.withRegions_wr, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.po l0]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll]; exact hs.fitE m.po l0)
    (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb]; exact m.hb) (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb]; exact m.hl) ?_
  · rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.pf (by decide), hs.regE m.po l0]; exact hs.dE m.d1 (.inr m.wo)
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.po l0]; exact hs.kE m.po hstk hsp
  · rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hs.addrE m.pf (by decide), VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb]; exact hc

theorem sbp_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => simpleBitPackContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l)
    (hcf : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat ≤ b) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri o l, (1, 0, STK)]) s s' →
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L o) l = VG.Spec.MlDsa.simpleBitPack (natPolyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)) b → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.sbp_cov hs m
  obtain ⟨lb, l0, ll⟩ := m.lt
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.sbp_preS hs (Nat.le_trans hstk hS) m hcf) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri o l] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, g2, g3⟩ := VG.Proof.MlDsa.Arm.KeyGen.sbpG hs m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  have := VG.Proof.MlDsa.Arm.KeyGen.sbp_post hp
  rwa [State.withRegions_mem, g0, g1, g2, g3, hs.addrE m.pf (by decide), hs.addrE m.po l0, VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem,
    VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll] at this

theorem sbp_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => simpleBitPackContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.SbpOk L Wb f b o l) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧
      (∀ i < n, (coeffAt x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat ≤ b) ∧ (∀ i < n, (coeffAt y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat ≤ b)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.sbpArgs f b o l)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3⟩ := VG.Proof.MlDsa.Arm.KeyGen.sbpG hx m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  obtain ⟨gy0, gy1, gy2, gy3⟩ := VG.Proof.MlDsa.Arm.KeyGen.sbpG hy m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f, VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l, VG.Proof.MlDsa.Arm.KeyGen.sbp_preS hx (Nat.le_trans hstk hS) m rx, VG.Proof.MlDsa.Arm.KeyGen.sbp_preS hy (Nat.le_trans hstk hS) m ry,
    VG.Proof.MlDsa.Arm.KeyGen.sbp_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2])
      (by rw [gx3, gy3]), (VG.Proof.MlDsa.Arm.KeyGen.sbp_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.sbp_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.sbp_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.sbp_cov hy m).2⟩

end

/-! ## `vg_mldsa_bit_pack` -/

/-- The stack slot of a fifth argument, below the stack pointer. -/
abbrev argR (s : State) : Region := ⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩

/-- What a callee in a frame may access: its buffers, and its stack argument. -/
theorem push_cov {s : State} (as : List (Reg × Arg)) {rd wr : List Region}
    (c1 : Covers (rd ++ wr) (s.rd ++ s.wr)) (c2 : Covers wr s.wr) :
    Covers ((rd ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) ++ wr) ((pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as)).rd ++ (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as)).wr) ∧
      Covers wr (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as)).wr := by
  have hw : (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s as)).wr = VG.Proof.MlDsa.Arm.KeyGen.argR s :: s.wr := by
    rw [pushed_wr, VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp, VG.Proof.MlDsa.Arm.KeyGen.glueSt_wr]; rfl
  rw [pushed_rd, VG.Proof.MlDsa.Arm.KeyGen.glueSt_rd, hw]
  refine ⟨fun x n ⟨r, hr, hc⟩ => ?_, fun x n ⟨r, hr, hc⟩ => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | rfl) | hr
    · obtain ⟨r', hr', hc'⟩ := c1 x n ⟨r, List.mem_append_left _ hr, hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), hc⟩
    · obtain ⟨r', hr', hc'⟩ := c1 x n ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · obtain ⟨r', hr', hc'⟩ := c2 x n ⟨r, hr, hc⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f o : Ptr} {a b l : Nat}

abbrev bpArgs (f : Ptr) (a b : Nat) (o : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr f), (.r1, .imm a), (.r2, .imm b), (.r3, .ptr o)]
abbrev bpAll (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : List (Reg × Arg) := VG.Proof.MlDsa.Arm.KeyGen.bpArgs f a b o ++ [(.r12, .imm l)]

/-- The facts `vg_mldsa_bit_pack` needs of its arguments. -/
structure BpOk (L : Lay) (Wb : List Nat) (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L f 1024
  po : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L o l
  wo : VG.Proof.MlDsa.Arm.KeyGen.ix o.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri f 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri o l) = true
  hab : (a, b) ∈ bitPackParams
  hl : l = 32 * bitlen (a + b)

theorem BpOk.lt (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l) : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 0 < l ∧ l < 2 ^ 32 := by
  have hab := m.hab
  simp only [bitPackParams, d, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rw [m.hl]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem BpOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.pf.1, m.po.1, show ∀ v, VG.Proof.MlDsa.Arm.KeyGen.argOk (.imm v) = true from fun _ => rfl]

theorem bpAll_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem bpG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l) (rd wr : List Region) :
    (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l))) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix f.1) + BitVec.ofNat 32 f.2 ∧
    (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l))) rd wr).gpr .r1 = BitVec.ofNat 32 a ∧
    (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l))) rd wr).gpr .r2 = BitVec.ofNat 32 b ∧
    (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l))) rd wr).gpr .r3 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix o.1) + BitVec.ofNat 32 o.2 ∧
    stackArg (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l))) rd wr) 0 = BitVec.ofNat 32 l :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.bpAll_nodup (by simp) m.pf.1],
    by rw [view_r1, pushed_gpr, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.bpAll_nodup (a := .imm a) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.bpAll_nodup (a := .imm b) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.bpAll_nodup (by simp) m.po.1],
    by rw [VG.Proof.MlDsa.Arm.KeyGen.push_arg, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.bpAll_nodup (a := .imm l) (by simp)]; rfl⟩

theorem bp_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pf) covers_nil') (Covers.right (covers_cons' (hs.cwE m.po m.wo) covers_nil')),
    covers_cons' (hs.cwE m.po m.wo) covers_nil'⟩

theorem bp_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f))
    (hc : ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ∧ modPm (coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ≤ b) :
    (bitPackContract Arm.abi stk).pre
      (view (pushed [.r12] (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l))) (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)) := by
  have e1 := VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l)
  have hm := VG.Proof.MlDsa.Arm.KeyGen.glueSt_mem s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l)
  obtain ⟨g0, g1, g2, g3, ga⟩ := VG.Proof.MlDsa.Arm.KeyGen.bpG hs m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  have h4 := VG.Proof.MlDsa.Arm.KeyGen.sp4 hs
  refine VG.Proof.MlDsa.Arm.KeyGen.bp_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, hs.regE m.pf (by decide), VG.Proof.MlDsa.Arm.KeyGen.push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.po l0])
    (by rw [VG.Proof.MlDsa.Arm.KeyGen.push_spN _ e1 _ _ h4]; have := hs.spk; omega) (VG.Proof.MlDsa.Arm.KeyGen.push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.pf (by decide)) (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll]; exact hs.fitE m.po l0)
    (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat la, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb]; exact m.hab) (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat la, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll]; exact m.hl)
    (by rw [hs.addrE m.pf (by decide), VG.Proof.MlDsa.Arm.KeyGen.push_reduced hs e1 hm _ _ m.pf]; exact hr) ?_
  · rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.pf (by decide), hs.regE m.po l0]; exact hs.dE m.d1 (.inr m.wo)
  · rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.po l0]; exact VG.Proof.MlDsa.Arm.KeyGen.push_aE hs _ e1 _ _ m.po
  · rw [hs.regE m.pf (by decide)]; exact VG.Proof.MlDsa.Arm.KeyGen.push_kE hs _ e1 _ _ m.pf hstk
  · rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll, hs.regE m.po l0]; exact VG.Proof.MlDsa.Arm.KeyGen.push_kE hs _ e1 _ _ m.po hstk
  · exact VG.Proof.MlDsa.Arm.KeyGen.push_kA hs _ e1 _ _ hstk
  · intro i hi
    rw [hs.addrE m.pf (by decide), VG.Proof.MlDsa.Arm.KeyGen.push_coeffAt hs e1 hm _ _ m.pf hi, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat la, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb]
    exact hc i hi

theorem bp_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => bitPackContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l)
    (hr : Reduced s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f))
    (hcf : ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ∧
      modPm (coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ≤ b) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri o l, (1, 0, STK)]) s s' →
      bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L o) l = VG.Spec.MlDsa.bitPack ((polyAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f)).map fun c => modPm c.val VG.Spec.MlDsa.q) a b → Q s') :
    WP isa (callAtS name c (VG.Proof.MlDsa.Arm.KeyGen.bpArgs f a b o) (.imm l)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.bp_cov hs m
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  have e1 := VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l)
  have hm := VG.Proof.MlDsa.Arm.KeyGen.glueSt_mem s (VG.Proof.MlDsa.Arm.KeyGen.bpAll f a b o l)
  refine VG.Proof.MlDsa.Arm.KeyGen.callVS hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.bp_preS hs (by omega) m hr hcf) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri o l] (by have := hc.stack; omega) hk) ?_
  obtain ⟨s₃, hm₃, -, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, ga⟩ := VG.Proof.MlDsa.Arm.KeyGen.bpG hs m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  have := VG.Proof.MlDsa.Arm.KeyGen.bp_post hp
  rwa [State.withRegions_mem, hm₃, g0, g1, g2, g3, ga, hs.addrE m.pf (by decide), hs.addrE m.po l0,
    VG.Proof.MlDsa.Arm.KeyGen.push_polyAt hs e1 hm _ _ m.pf, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat la, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat lb, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat ll] at this

theorem bp_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => bitPackContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.BpOk L Wb f a b o l) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      Reduced y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) ∧
      (∀ i < n, -(a : Int) ≤ modPm (coeffAt x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ∧
        modPm (coeffAt x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ≤ b) ∧
      (∀ i < n, -(a : Int) ≤ modPm (coeffAt y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ∧
        modPm (coeffAt y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L f) i).toNat VG.Spec.MlDsa.q ≤ b)) :
    RelCT isa P (callAtS name c (VG.Proof.MlDsa.Arm.KeyGen.bpArgs f a b o) (.imm l)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2.1)
    (fun x y h => ⟨VG.Proof.MlDsa.Arm.KeyGen.sp4 (hP x y h).1, VG.Proof.MlDsa.Arm.KeyGen.sp4 (hP x y h).2.1⟩) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry, cx, cy⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := VG.Proof.MlDsa.Arm.KeyGen.bpG hx m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := VG.Proof.MlDsa.Arm.KeyGen.bpG hy m (VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l)
  have ex : VG.Proof.MlDsa.Arm.KeyGen.argR y = VG.Proof.MlDsa.Arm.KeyGen.argR x := by simp only [VG.Proof.MlDsa.Arm.KeyGen.argR, hsp]
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.sbpRd L f ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x], VG.Proof.MlDsa.Arm.KeyGen.sbpWr L o l, VG.Proof.MlDsa.Arm.KeyGen.bp_preS hx (by omega) m rx cx, ?_,
    VG.Proof.MlDsa.Arm.KeyGen.bp_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, VG.Proof.MlDsa.Arm.KeyGen.glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]),
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact VG.Proof.MlDsa.Arm.KeyGen.bp_preS hy (by omega) m ry cy
  · exact (VG.Proof.MlDsa.Arm.KeyGen.push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hx m).2).1
  · exact (VG.Proof.MlDsa.Arm.KeyGen.push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hx m).2).2
  · rw [← ex]; exact (VG.Proof.MlDsa.Arm.KeyGen.push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hy m).2).1
  · exact (VG.Proof.MlDsa.Arm.KeyGen.push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.bp_cov hy m).2).2

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.CallSample`. -/
section

/-!
# ML-DSA on 32-bit ARM: calling the samplers

As `ip_ok` and `ip_tr` (`Call.lean`), for `vg_mldsa_rej_ntt_poly` and
`vg_mldsa_rej_bounded_poly`, whose public data include what they leak of their
seeds.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_rej_ntt_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr}

abbrev rnArgs (sd a w : Ptr) : List (Reg × Arg) := [(.r0, .ptr sd), (.r1, .ptr a), (.r2, .ptr w)]
abbrev rnRd (L : Lay) (sd : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix sd.1) sd.2 34]
abbrev rnWr (L : Lay) (a w : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix a.1) a.2 1024, L.R (VG.Proof.MlDsa.Arm.KeyGen.ix w.1) w.2 2048]

/-- The facts `vg_mldsa_rej_ntt_poly` needs of its pointers. -/
structure RnOk (L : Lay) (Wb : List Nat) (sd a w : Ptr) : Prop where
  ps : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L sd 34
  pa : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L a 1024
  pw : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L w 2048
  wa : VG.Proof.MlDsa.Arm.KeyGen.ix a.1 ∈ Wb
  ww : VG.Proof.MlDsa.Arm.KeyGen.ix w.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri sd 34) (VG.Proof.MlDsa.Arm.KeyGen.tri a 1024) = true
  d2 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri sd 34) (VG.Proof.MlDsa.Arm.KeyGen.tri w 2048) = true
  d3 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri a 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri w 2048) = true

theorem RnOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.RnOk L Wb sd a w) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.ps.1, m.pa.1, m.pw.1]

theorem rnArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem rnG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.RnOk L Wb sd a w) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w)) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix sd.1) + BitVec.ofNat 32 sd.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w)) rd wr).gpr .r1 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix a.1) + BitVec.ofNat 32 a.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w)) rd wr).gpr .r2 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix w.1) + BitVec.ofNat 32 w.2 :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.rnArgs_nodup (by simp) m.ps.1],
    by rw [view_r1, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.rnArgs_nodup (by simp) m.pa.1],
    by rw [view_r2, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.rnArgs_nodup (by simp) m.pw.1]⟩

theorem rn_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.RnOk L Wb sd a w) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd ++ VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.ps) covers_nil')
    (Covers.right (covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil'))),
    covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil')⟩

theorem rn_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.RnOk L Wb sd a w) :
    (rejNTTContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w)) (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w) (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  obtain ⟨g0, g1, g2⟩ := VG.Proof.MlDsa.Arm.KeyGen.rnG hs m (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  refine VG.Proof.MlDsa.Arm.KeyGen.rejNtt_pre g0 g1 g2 (by rw [State.withRegions_rd, hs.regE m.ps (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pa (by decide), hs.regE m.pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ ?_ ?_ ?_
    (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
  · rw [hs.regE m.ps (by decide), hs.regE m.pa (by decide)]; exact hs.dE m.d1 (.inr m.wa)
  · rw [hs.regE m.ps (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [hs.regE m.pa (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d3 (.inl m.wa)
  · rw [hs.regE m.ps (by decide)]; exact hs.kE m.ps hstk hsp
  · rw [hs.regE m.pa (by decide)]; exact hs.kE m.pa hstk hsp
  · rw [hs.regE m.pw (by decide)]; exact hs.kE m.pw hstk hsp

theorem rn_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => rejNTTContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri a 1024, VG.Proof.MlDsa.Arm.KeyGen.tri w 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L sd) 34)) (s'.gpr .r0) (polyAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a)) →
      Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.rn_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.rn_preS hs (Nat.le_trans hstk hS) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri a 1024, VG.Proof.MlDsa.Arm.KeyGen.tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g0, g1, -⟩ := VG.Proof.MlDsa.Arm.KeyGen.rnG hs m (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
    have := VG.Proof.MlDsa.Arm.KeyGen.rejNtt_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g0, g1, hs.addrE m.ps (by decide),
      hs.addrE m.pa (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem] at this
  exacts [this.1, this.2]

theorem rn_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => rejNTTContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.RnOk L Wb sd a w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L sd) 34 = bytesAt y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L sd) 34) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.rnArgs sd a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2⟩ := VG.Proof.MlDsa.Arm.KeyGen.rnG hx m (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  obtain ⟨gy0, gy1, gy2⟩ := VG.Proof.MlDsa.Arm.KeyGen.rnG hy m (VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.rnRd L sd, VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w, VG.Proof.MlDsa.Arm.KeyGen.rn_preS hx (Nat.le_trans hstk hS) m, VG.Proof.MlDsa.Arm.KeyGen.rn_preS hy (Nat.le_trans hstk hS) m,
    VG.Proof.MlDsa.Arm.KeyGen.rejNtt_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) ?_,
    (VG.Proof.MlDsa.Arm.KeyGen.rn_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.rn_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.rn_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.rn_cov hy m).2⟩
  rw [gx0, gy0, VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hx.addrE m.ps (by decide)]
  exact hl

end

/-! ## `vg_mldsa_rej_bounded_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr} {η : Nat}

abbrev rbArgs (sd : Ptr) (η : Nat) (a w : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr sd), (.r1, .imm η), (.r2, .ptr a), (.r3, .ptr w)]
abbrev rbRd (L : Lay) (sd : Ptr) : List Region := [L.R (VG.Proof.MlDsa.Arm.KeyGen.ix sd.1) sd.2 66]

/-- The facts `vg_mldsa_rej_bounded_poly` needs of its pointers. -/
structure RbOk (L : Lay) (Wb : List Nat) (sd a w : Ptr) : Prop where
  ps : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L sd 66
  pa : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L a 1024
  pw : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L w 2048
  wa : VG.Proof.MlDsa.Arm.KeyGen.ix a.1 ∈ Wb
  ww : VG.Proof.MlDsa.Arm.KeyGen.ix w.1 ∈ Wb
  d1 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri sd 66) (VG.Proof.MlDsa.Arm.KeyGen.tri a 1024) = true
  d2 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri sd 66) (VG.Proof.MlDsa.Arm.KeyGen.tri w 2048) = true
  d3 : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri a 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri w 2048) = true

theorem RbOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.RbOk L Wb sd a w) : VG.Proof.MlDsa.Arm.KeyGen.glueOk (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w) = true := by
  simp [VG.Proof.MlDsa.Arm.KeyGen.glueOk, m.ps.1, m.pa.1, m.pw.1, show VG.Proof.MlDsa.Arm.KeyGen.argOk (.imm η) = true from rfl]

theorem rbArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem rbG {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.RbOk L Wb sd a w) (rd wr : List Region) :
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) rd wr).gpr .r0 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix sd.1) + BitVec.ofNat 32 sd.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) rd wr).gpr .r1 = BitVec.ofNat 32 η ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) rd wr).gpr .r2 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix a.1) + BitVec.ofNat 32 a.2 ∧
    (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) rd wr).gpr .r3 = L.ptr (VG.Proof.MlDsa.Arm.KeyGen.ix w.1) + BitVec.ofNat 32 w.2 :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.rbArgs_nodup (by simp) m.ps.1],
    by rw [view_r1, VG.Proof.MlDsa.Arm.KeyGen.glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.rbArgs_nodup (a := .imm η) (by simp)]; rfl,
    by rw [view_r2, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.rbArgs_nodup (by simp) m.pa.1],
    by rw [view_r3, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.rbArgs_nodup (by simp) m.pw.1]⟩

theorem rb_cov {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.RbOk L Wb sd a w) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd ++ VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.ps) covers_nil')
    (Covers.right (covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil'))),
    covers_cons' (hs.cwE m.pa m.wa) (covers_cons' (hs.cwE m.pw m.ww) covers_nil')⟩

theorem rb_preS {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.RbOk L Wb sd a w)
    (hη : η = 2 ∨ η = 4) :
    (rejBoundedContract Arm.abi stk).pre (view (VG.Proof.MlDsa.Arm.KeyGen.glueSt s (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)) := by
  have hsp := VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w) (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  obtain ⟨g0, g1, g2, g3⟩ := VG.Proof.MlDsa.Arm.KeyGen.rbG (η := η) hs m (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  refine VG.Proof.MlDsa.Arm.KeyGen.rejBounded_pre g0 g1 g2 g3 (by rw [State.withRegions_rd, hs.regE m.ps (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.pa (by decide), hs.regE m.pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ ?_ ?_ ?_
    (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
    (by rw [VG.Proof.MlDsa.Arm.KeyGen.imm_toNat (by omega)]; exact hη)
  · rw [hs.regE m.ps (by decide), hs.regE m.pa (by decide)]; exact hs.dE m.d1 (.inr m.wa)
  · rw [hs.regE m.ps (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [hs.regE m.pa (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d3 (.inl m.wa)
  · rw [hs.regE m.ps (by decide)]; exact hs.kE m.ps hstk hsp
  · rw [hs.regE m.pa (by decide)]; exact hs.kE m.pa hstk hsp
  · rw [hs.regE m.pw (by decide)]; exact hs.kE m.pw hstk hsp

theorem rb_ok {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => rejBoundedContract Arm.abi stk) S) {s : State}
    (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri a 1024, VG.Proof.MlDsa.Arm.KeyGen.tri w 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a)) →
      Outcome (fun b => (rejBoundedPoly η b.rejBounded (bytesAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L sd) 66)).map toRq) (s'.gpr .r0)
        (polyAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a)) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.rb_cov hs m
  refine VG.Proof.MlDsa.Arm.KeyGen.callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.rb_preS hs (Nat.le_trans hstk hS) m hη) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [VG.Proof.MlDsa.Arm.KeyGen.tri a 1024, VG.Proof.MlDsa.Arm.KeyGen.tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g0, g1, g2, -⟩ := VG.Proof.MlDsa.Arm.KeyGen.rbG (η := η) hs m (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
    have := VG.Proof.MlDsa.Arm.KeyGen.rejBounded_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g0, g1, g2, hs.addrE m.ps (by decide),
      hs.addrE m.pa (by decide), VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, VG.Proof.MlDsa.Arm.KeyGen.imm_toNat (by omega)] at this
  exacts [this.1, this.2]

theorem rb_tr {c : Prog isa} (hc : VG.Proof.MlDsa.Arm.KeyGen.Callee c (fun stk => rejBoundedContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp ∧
      rejBoundedLeak η (bytesAt x.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L sd) 66) = rejBoundedLeak η (bytesAt y.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L sd) 66)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.rbArgs sd η a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine VG.Proof.MlDsa.Arm.KeyGen.callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3⟩ := VG.Proof.MlDsa.Arm.KeyGen.rbG (η := η) hx m (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  obtain ⟨gy0, gy1, gy2, gy3⟩ := VG.Proof.MlDsa.Arm.KeyGen.rbG (η := η) hy m (VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd) (VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w)
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.rbRd L sd, VG.Proof.MlDsa.Arm.KeyGen.rnWr L a w, VG.Proof.MlDsa.Arm.KeyGen.rb_preS hx (Nat.le_trans hstk hS) m hη, VG.Proof.MlDsa.Arm.KeyGen.rb_preS hy (Nat.le_trans hstk hS) m hη,
    VG.Proof.MlDsa.Arm.KeyGen.rejBounded_pub (by rw [VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, VG.Proof.MlDsa.Arm.KeyGen.view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1])
      (by rw [gx2, gy2]) (by rw [gx3, gy3]) ?_, (VG.Proof.MlDsa.Arm.KeyGen.rb_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.rb_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.rb_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.rb_cov hy m).2⟩
  rw [gx0, gy0, gx1, gy1, VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, VG.Proof.MlDsa.Arm.KeyGen.view_glue_mem, hx.addrE m.ps (by decide), VG.Proof.MlDsa.Arm.KeyGen.imm_toNat (by omega)]
  exact hl

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Lay`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: its parameters, precondition and buffers

The facts about the parameter sets the proof uses (`PFacts`); the precondition
of the shared contract, evaluated (`Pre`, `pre_of`); and the buffers of the
function (`lay`): `scratch`, the stack, `seed`, `pk` and `sk`, pairwise
disjoint, of which all but `seed` are written. `lsep` proves the facts about
the offsets of pointers into them (`sepB`, `inB`) by `omega`, for any
parameter set.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k
  encPk : encodable (BitVec.ofNat 32 p.pkLen) = true

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.Arm.KeyGen.PFacts p := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

theorem PFacts.scr {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) : 1024 * (p.k * p.ℓ + p.ℓ + p.k + 3) + 36864 ≤ VG.Proof.MlDsa.Arm.KeyGen.scrLen p ∧
    VG.Proof.MlDsa.Arm.KeyGen.scrLen p < 2 ^ 32 := by
  have := hF.k; have := hF.l; have := hF.kl
  simp only [VG.Proof.MlDsa.Arm.KeyGen.scrLen, scratchWords]; omega

theorem PFacts.lens {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) : p.pkLen < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ oT0 p + 416 * p.k ≤ p.skLen := by
  have := hF.k; have := hF.l
  refine ⟨by rw [hF.pk]; omega, ?_, by rw [hF.sk]⟩
  rw [hF.sk]; rcases hF.eta with ⟨_, he⟩ | ⟨_, he⟩ <;> simp only [oT0, he] <;> omega

/-! ## The precondition -/

section
variable (σ : State)

abbrev pSeed : BitVec 32 := σ.gpr .r0
abbrev pPk : BitVec 32 := σ.gpr .r1
abbrev pSk : BitVec 32 := σ.gpr .r2
abbrev pScr : BitVec 32 := σ.gpr .r3

end

/-- The precondition of `keyGenContract` with `STK` bytes of stack. -/
structure Pre (p : Params) (STK : Nat) (σ : State) : Prop where
  stk : STK ≤ σ.sp.toNat
  rd : σ.rd = [regA (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ) 32]
  wr : σ.wr = [regA (VG.Proof.MlDsa.Arm.KeyGen.pPk σ) p.pkLen, regA (VG.Proof.MlDsa.Arm.KeyGen.pSk σ) p.skLen, regA (VG.Proof.MlDsa.Arm.KeyGen.pScr σ) (VG.Proof.MlDsa.Arm.KeyGen.scrLen p)]
  d_xp : (regA (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ) 32).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pPk σ) p.pkLen)
  d_xs : (regA (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ) 32).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pSk σ) p.skLen)
  d_xc : (regA (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ) 32).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pScr σ) (VG.Proof.MlDsa.Arm.KeyGen.scrLen p))
  d_ps : (regA (VG.Proof.MlDsa.Arm.KeyGen.pPk σ) p.pkLen).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pSk σ) p.skLen)
  d_pc : (regA (VG.Proof.MlDsa.Arm.KeyGen.pPk σ) p.pkLen).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pScr σ) (VG.Proof.MlDsa.Arm.KeyGen.scrLen p))
  d_sc : (regA (VG.Proof.MlDsa.Arm.KeyGen.pSk σ) p.skLen).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pScr σ) (VG.Proof.MlDsa.Arm.KeyGen.scrLen p))
  b_x : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ) 32)
  b_p : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pPk σ) p.pkLen)
  b_s : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pSk σ) p.skLen)
  b_c : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.KeyGen.pScr σ) (VG.Proof.MlDsa.Arm.KeyGen.scrLen p))
  f_x : (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ).toNat + 32 ≤ 2 ^ 32
  f_p : (VG.Proof.MlDsa.Arm.KeyGen.pPk σ).toNat + p.pkLen ≤ 2 ^ 32
  f_s : (VG.Proof.MlDsa.Arm.KeyGen.pSk σ).toNat + p.skLen ≤ 2 ^ 32
  f_c : (VG.Proof.MlDsa.Arm.KeyGen.pScr σ).toNat + VG.Proof.MlDsa.Arm.KeyGen.scrLen p ≤ 2 ^ 32

theorem pre_of {p : Params} {n : Nat} {σ : State} (h : (Spec.MlDsa.keyGenContract p Arm.abi (n + 1)).pre σ) :
    VG.Proof.MlDsa.Arm.KeyGen.Pre p (n + 1) σ := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-! ## The buffers -/

/-- `scratch` (0), the stack (1), `seed` (2), `pk` (3) and `sk` (4). -/
def lay (p : Params) (STK : Nat) (σ : State) : Lay :=
  ⟨fun i => [VG.Proof.MlDsa.Arm.KeyGen.pScr σ, σ.sp - BitVec.ofNat 32 STK, VG.Proof.MlDsa.Arm.KeyGen.pSeed σ, VG.Proof.MlDsa.Arm.KeyGen.pPk σ, VG.Proof.MlDsa.Arm.KeyGen.pSk σ].getD i 0,
    [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen]⟩

theorem lay_sizes (p : Params) (STK : Nat) (σ : State) :
    (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).sizes = [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] := rfl

theorem lay_size0 (p : Params) (STK : Nat) (σ : State) : (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).size 0 = VG.Proof.MlDsa.Arm.KeyGen.scrLen p := rfl

/-- The buffers written: all but `seed`. -/
abbrev kWb : List Nat := [0, 1, 3, 4]

theorem lay_ok {p : Params} {STK : Nat} {σ : State} (hp : VG.Proof.MlDsa.Arm.KeyGen.Pre p STK σ) : VG.Proof.MlDsa.Arm.KeyGen.OkW (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb := by
  have es : (⟨State.addr (σ.sp - BitVec.ofNat 32 STK), STK⟩ : Region) = below σ STK := by
    rw [VG.Proof.MlKem.Arm.addr_sub hp.stk]
  refine ⟨fun i hi => ?_, fun i hi j hj hij _ => ?_⟩
  · simp only [VG.Proof.MlDsa.Arm.KeyGen.lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 32 STK).toNat + STK ≤ 2 ^ 32
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_x
    · exact hp.f_p
    · exact hp.f_s
  · simp only [VG.Proof.MlDsa.Arm.KeyGen.lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.MlDsa.Arm.KeyGen.lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_c.symm
    · exact hp.d_xc.symm
    · exact hp.d_pc.symm
    · exact hp.d_sc.symm
    · rw [es]; exact hp.b_c
    · rw [es]; exact hp.b_x
    · rw [es]; exact hp.b_p
    · rw [es]; exact hp.b_s
    · exact hp.d_xc
    · rw [es]; exact hp.b_x.symm
    · exact hp.d_xp
    · exact hp.d_xs
    · exact hp.d_pc
    · rw [es]; exact hp.b_p.symm
    · exact hp.d_xp.symm
    · exact hp.d_ps
    · exact hp.d_sc
    · rw [es]; exact hp.b_s.symm
    · exact hp.d_xs.symm
    · exact hp.d_ps.symm

/-- Decides a fact about offsets in the buffers, for any parameter set with
the facts `hF`. -/
syntax "lsep " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lsep $hF) => `(tactic| lsep $hF [])
  | `(tactic| lsep $hF [$ls,*]) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).lens
      have := ($hF).eta; have := ($hF).pk; have := ($hF).sk
      try dsimp only [$ls,*]
      try dsimp only [sepB, sepAll, inB, tri, ix, aP, sP, tP, t1P, t0P, sc, oP, oSS, oKL, oHX, oSA, oSB, oT0]
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [sepB, sepAll, inB, lay_sizes, List.getD_cons_zero,
        List.getD_cons_succ, List.length_cons, List.length_nil, List.all_cons, List.all_nil, tri, ix,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_true, Bool.true_and,
        true_and, and_true, true_or, or_true, Nat.zero_add, oP, oSS, oKL, oHX, oSA, oSB, oT0, aP, sP, tP, t1P, t0P,
        sc, false_or, or_false, decide_eq_true_iff, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece`. -/
section

/-!
# ML-DSA on 32-bit ARM: pieces of code, correct and constant time together

As on x86-64: a piece of code takes each run of a function, from an entry
state `σ` that satisfies its precondition `Pre`, from the invariant `I` to `J`
(`ok`), and leaks the same in two runs related by `I` whose entry states agree
on the public data `Pub` (`tr`, `Rel2`). Pieces compose (`Piece.seq`,
`Piece.seqR`), which proves correctness and constant time together.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen (seqR)

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {I I' : State → State → Prop} {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 Pre Pub I) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 Pre Pub I) c (VG.Proof.MlDsa.Arm.KeyGen.Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {c : Prog isa} {Q : State → State → Prop} (h : RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 Pre Pub fun σ s => s = σ) c Q) :
    ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (Pre : State → Prop) (Pub : State → State → Prop) (I J : State → State → Prop) (c : Prog isa) :
    Prop where
  ok : ∀ σ s, Pre σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 Pre Pub I) c fun _ _ => True

variable {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub I J c₁) (h₂ : VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub J K c₂) :
    VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (VG.Proof.MlDsa.Arm.KeyGen.relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub I J c)
    (hI : ∀ σ s, Pre σ → I' σ s → I σ s) (hJ : ∀ σ s, Pre σ → J σ s → J' σ s) : VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub (I k) (I (k + 1)) (f k)) →
      VG.Proof.MlDsa.Arm.KeyGen.Piece Pre Pub (I a) (I (a + n)) (VG.Impl.MlDsa.Arm.KeyGen.seqR f a n)
  | 0, a, _ => ⟨fun _ _ _ hs => WP.block_nil hs, fun _ _ _ _ _ _ _ e₁ e₂ => by
      rw [VG.Impl.MlDsa.Arm.KeyGen.seqR, Exec.block_iff] at e₁ e₂
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
      obtain ⟨-, rfl⟩ := e₁
      obtain ⟨-, rfl⟩ := e₂
      exact ⟨rfl, trivial⟩⟩
  | n + 1, a, h => by
    have h1 := Piece.seqR (I := I) n (a + 1) fun k h₁ h₂ => h k (by omega) (by omega)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact (h a (Nat.le_refl _) (by omega)).seq (c₂ := VG.Impl.MlDsa.Arm.KeyGen.seqR f (a + 1) n) h1

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inv`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: what holds throughout, and the prologue

What holds of the state throughout (`KC`: the layout, the permissions and
stack pointer of the entry state, our caller's registers saved in `scratch`,
and the seed `ξ`), which a part keeps if it writes apart from the saved
registers and the seed (`kcChk`); the pieces of key generation (`KPiece`); and
the prologue, which saves our caller's registers and keeps the pointers
(`pro_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (VG.Proof.MlDsa.Arm.KeyGen.pSeed σ)) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ)).2.2

/-- The public data of `keyGenContract`. -/
def kgPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ VG.Proof.MlDsa.Arm.KeyGen.pSeed σ₁ = VG.Proof.MlDsa.Arm.KeyGen.pSeed σ₂ ∧ VG.Proof.MlDsa.Arm.KeyGen.pPk σ₁ = VG.Proof.MlDsa.Arm.KeyGen.pPk σ₂ ∧ VG.Proof.MlDsa.Arm.KeyGen.pSk σ₁ = VG.Proof.MlDsa.Arm.KeyGen.pSk σ₂ ∧ VG.Proof.MlDsa.Arm.KeyGen.pScr σ₁ = VG.Proof.MlDsa.Arm.KeyGen.pScr σ₂ ∧
    keyGenLeak p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ₁) = keyGenLeak p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ₂)

/-- The pieces of key generation. -/
abbrev KPiece (p : Params) (STK : Nat) := VG.Proof.MlDsa.Arm.KeyGen.Piece (VG.Proof.MlDsa.Arm.KeyGen.Pre p STK) (VG.Proof.MlDsa.Arm.KeyGen.kgPub p)

/-- Two runs of a key generation with public data that agree have the same layout. -/
theorem lay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : VG.Proof.MlDsa.Arm.KeyGen.kgPub p σ₁ σ₂) : VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ₁ = VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [VG.Proof.MlDsa.Arm.KeyGen.lay, VG.Proof.MlDsa.Arm.KeyGen.pSeed, VG.Proof.MlDsa.Arm.KeyGen.pPk, VG.Proof.MlDsa.Arm.KeyGen.pSk, VG.Proof.MlDsa.Arm.KeyGen.pScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : VG.Proof.MlKem.Arm.Saved s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 840) σ.gpr
  lr : s.mem.readW ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 872) 32 = σ.gpr .lr
  xi : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 2 0) 32 = VG.Proof.MlDsa.Arm.KeyGen.xiOf σ

theorem xi_eq (p : Params) (STK : Nat) (σ : State) : bytesAt σ.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 2 0) 32 = VG.Proof.MlDsa.Arm.KeyGen.xiOf σ := by
  simp only [Lay.A, add_ofNat_zero]; rfl

/-- A part that writes the regions `W` keeps `KC`. -/
def kcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, 840, 36) W &&
    sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (2, 0, 32) W

theorem KC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.KeyGen.kcChk p STK W = true) : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s' := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.kcChk, Bool.and_eq_true] at hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL W, ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 0 840 36).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact VG.Proof.MlDsa.Arm.KeyGen.disjW hL (List.all_eq_true.mp hc.1 w hw) (.inl (by decide))
  have hd2 : ∀ r ∈ (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL W, ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 2 0 32).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      have hs := List.all_eq_true.mp hc.2 w hw
      refine VG.Proof.MlDsa.Arm.KeyGen.disjW' hL hs (.inr ?_)
      have hb : w.1 < 5 := by
        simp only [sepB, Bool.and_eq_true, decide_eq_true_eq, List.length_cons, List.length_nil] at hs
        exact hs.1.1.1.2
      rcases (by omega : w.1 = 0 ∨ w.1 = 1 ∨ w.1 = 2 ∨ w.1 = 3 ∨ w.1 = 4) with e | e | e | e | e <;> rw [e]
      · exact .inl (by decide)
      · exact .inl (by decide)
      · exact .inr rfl
      · exact .inl (by decide)
      · exact .inl (by decide)
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW (r := (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.lr
  · rw [Proof.MlKem.bytesAt_frame hk.frame hd2 (by decide)]; exact h.xi

end VG.Proof.MlDsa.Arm.KeyGen

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)

/-! ## The prologue -/

theorem pro_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (hSTK : 8 ≤ STK) {σ : State} (hp : VG.Proof.MlDsa.Arm.KeyGen.Pre p STK σ) :
    WP isa (.block VG.Impl.MlDsa.Arm.KeyGen.pro) σ fun s => VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s ∧ s.gpr .r11 = 1 := by
  have hL := VG.Proof.MlDsa.Arm.KeyGen.lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).buf 0 = regA (VG.Proof.MlDsa.Arm.KeyGen.pScr σ) (VG.Proof.MlDsa.Arm.KeyGen.scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have eA : ∀ o, (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 o = State.addr (σ.gpr .r3) + BitVec.ofNat 64 o := fun o => rfl
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 o) n := fun {o n} h =>
    Lay.covers (o := o) (l := n) w0 (by rw [VG.Proof.MlDsa.Arm.KeyGen.lay_size0]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [VG.Impl.MlDsa.Arm.KeyGen.pro, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega) fc) fun i hi => by
    rw [add_ofNat_add, ← eA]; exact wS (o := 840 + 4 * i) (n := 4) (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = VG.Proof.MlDsa.Arm.KeyGen.pScr σ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 872 := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have o1 : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have e1 : encodable (1 : BitVec 32) = true := by decide
  run_block [i872, o1, e1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 872) v).readW
      ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by rw [eA] at h1 h2; bv_omega) (by decide)
  have fr : Frame [(VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 0 840 36] σ.mem (s₁.mem.writeW ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 872) (s₁.gpr .lr)) := by
    refine (h₁.frame.sub fun r hr => ⟨(VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 0 840 36, List.mem_singleton_self _, ?_⟩).writeW
      (r := (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).R 0 840 36) (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      intro x hx; simp only [Region.Contains, eA] at hx ⊢; bv_omega
    · simp only [Region.Contains, eA]; bv_omega
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by rw [VG.Proof.MlDsa.Arm.KeyGen.lay_size0]; omega, rfl,
    show σ.sp - BitVec.ofNat 32 STK = s₁.sp - BitVec.ofNat 32 STK by rw [h₁.sp], hSTK,
    by rw [h₁.sp]; exact hp.stk, ?_, ?_, ?_, ?_, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, h₁.rd, h₁.wr, h₁.sp,
    fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show _ ∈ s₁.wr
    rw [h₁.wr, hp.wr]
    simp only [VG.Proof.MlDsa.Arm.KeyGen.kWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp [Lay.buf, VG.Proof.MlDsa.Arm.KeyGen.lay]
    · exact absurd rfl hi1
    · simp [Lay.buf, VG.Proof.MlDsa.Arm.KeyGen.lay]
    · simp [Lay.buf, VG.Proof.MlDsa.Arm.KeyGen.lay]
  · show _ ∈ s₁.rd ++ s₁.wr
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, VG.Proof.MlDsa.Arm.KeyGen.lay]
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    exact h₁.saved i hi
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, show (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 872 = (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, ← VG.Proof.MlDsa.Arm.KeyGen.xi_eq p STK σ]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact VG.Proof.MlDsa.Arm.KeyGen.disjW' (i := 2) (o := 0) (l := 32) (j := 0) (o' := 840) (l' := 36) hL (by lsep hF)
        (.inr (.inl (by decide)))) (by decide)
  · trivial

theorem pro_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (hSTK : 8 ≤ STK) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => s = σ) (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s ∧ s.gpr .r11 = 1) (.block VG.Impl.MlDsa.Arm.KeyGen.pro) :=
  ⟨fun σ s hp hs => by subst hs; exact VG.Proof.MlDsa.Arm.KeyGen.pro_ok hF hSTK hp,
    Sample.taint_block [.r0, .r1, .r2, .r3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by taint_decide)⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps`. -/
section

/-!
# ML-DSA on 32-bit ARM: bytes, copies and the sponge in the buffers of a `Site`

A byte stored (`setB_ok`), bytes copied (`copyS`, from ML-KEM's `copy_loop`),
and the sponge (`hashS`, from ML-KEM's `hash_ok`), with what they change as
triples of the layout.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece hash copy copyBody)
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad rates)
open VG.Proof.MlKem.Arm (PieceOk Outs)

/-- The byte `v` moved by `movw` and stored by `strb`. -/
theorem byte16 (v : Nat) : ((BitVec.ofNat 16 v).setWidth 32).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s)
include hs

/-! ## A byte -/

theorem setB_ok {q : Ptr} (pq : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L q 1) (hw : VG.Proof.MlDsa.Arm.KeyGen.ix q.1 ∈ Wb) (ho : q.2 < 4096) (v : Nat) :
    WP isa (.block (setB q v)) s fun s' =>
      Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri q 1]) s s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L q) 1 = [BitVec.ofNat 8 v] := by
  have gb := hs.val pq.1
  simp only [VG.Proof.MlDsa.Arm.KeyGen.argVal] at gb
  have ea := hs.addrE pq (by decide)
  have hi : InRegions s.wr (State.addr (s.gpr q.1 + BitVec.ofNat 32 q.2)) 1 := by
    rw [gb, ea]; exact hs.cwE pq hw _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have n12 : q.1 ≠ .r12 := by
    have := pq.1; simp only [VG.Proof.MlDsa.Arm.KeyGen.argOk, Bool.or_eq_true, beq_iff_eq] at this
    rcases this with ((h | h) | h) | h <;> rw [h] <;> decide
  have n12' : ¬ q.1 = .r12 := n12
  rw [gb, ea] at hi
  run_block [setB, hi, ho, n12', gb, ea]
  refine ⟨⟨fun r hr hl => ?_, rfl, rfl, rfl, ?_⟩, ?_⟩
  · have : r ≠ .r12 := by revert r; decide
    simp only [this, ite_false]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [show ∀ (m : Mem) (a : Addr), bytesAt m a 1 = [m a] from fun _ _ => by simp [bytesAt], VG.WriteBytes.writeW8_apply,
      ite_eq_left rfl, VG.Proof.MlDsa.Arm.KeyGen.byte16 v]

omit hs in
/-- A register of the layout is callee-saved (and not `lr`). -/
theorem base_pres {r : Reg} (h : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr (r, 0)) = true) : r ∈ preserved ∧ r ≠ .lr := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.argOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

/-! ## A copy -/

theorem copyS {sb db : Reg} {so dO len : Nat} (ps : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L (sb, so) len) (pd : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L (db, dO) len)
    (wd : VG.Proof.MlDsa.Arm.KeyGen.ix db ∈ Wb) (hse : encodable (BitVec.ofNat 32 so) = true) (hde : encodable (BitVec.ofNat 32 dO) = true)
    (hle : encodable (BitVec.ofNat 32 len) = true) (hlen : len < 2 ^ 32) (hl0 : 0 < len)
    (hd : sepB L.sizes (VG.Proof.MlDsa.Arm.KeyGen.tri (sb, so) len) (VG.Proof.MlDsa.Arm.KeyGen.tri (db, dO) len) = true) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri (db, dO) len]) s s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L (db, dO)) len = bytesAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L (sb, so)) len := by
  have gs := hs.val ps.1
  have gd := hs.val pd.1
  simp only [VG.Proof.MlDsa.Arm.KeyGen.argVal] at gs gd
  obtain ⟨ea, fa⟩ := hs.addr ps.2 hl0
  obtain ⟨eb, fb⟩ := hs.addr pd.2 hl0
  refine WP.seq (WP.mono (copy_setup (VG.Proof.MlDsa.Arm.KeyGen.base_pres (by simpa [VG.Proof.MlDsa.Arm.KeyGen.argOk] using ps.1))
    (VG.Proof.MlDsa.Arm.KeyGen.base_pres (by simpa [VG.Proof.MlDsa.Arm.KeyGen.argOk] using pd.1)) hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs] at g0; rw [gd] at g1
  have hdj := hs.dE hd (.inr wd)
  refine WP.mono (copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact hdj)
    (by rw [ea, o₁.rd, o₁.wr]; exact hs.crE ps)
    (by rw [eb, o₁.wr]; exact hs.cwE pd wd) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## The sponge -/

omit hs in
theorem ix_ne1 (r : Reg) : VG.Proof.MlDsa.Arm.KeyGen.ix r ≠ 1 := by cases r <;> decide

theorem hashS {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) (hsfx : sfx < 256) {ins : List VG.Impl.MlKem.Arm.Piece} {q : VG.Impl.MlKem.Arm.Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K) VG.Proof.MlDsa.Arm.KeyGen.ix s false p) (hq : PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K) VG.Proof.MlDsa.Arm.KeyGen.ix s true q) :
    WP isa (hash rate sfx ins [q]) s fun s' =>
      Kept (L.RL [(0, 0, 200), (0, 200, 640), (1, 0, STK), (VG.Proof.MlDsa.Arm.KeyGen.ix q.base, q.off, q.len)]) s s' ∧
      bytesAt s'.mem (L.A (VG.Proof.MlDsa.Arm.KeyGen.ix q.base) q.off) q.len = squeezeFrom rate (absorb rate
        (pad rate (BitVec.ofNat 8 sfx) (ins.map ((VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).pb VG.Proof.MlDsa.Arm.KeyGen.ix s.mem)).flatten)) 0 q.len := by
  refine WP.mono (hash_ok hrate hre hse hsfx (hs.ctx hK) hne hin (fun p hp => by
    rw [List.mem_singleton] at hp; subst hp; exact hq) (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ => ⟨?_, ?_⟩
  · refine ⟨k.cs, k.sp, k.rd, k.wr, k.frame.sub fun r hr => ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
        rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      have := hs.belowSub (n := 8) hs.s8
      intro x hx
      apply this
      have := hs.spk; have := hs.s8
      have := addr_toNat' s.sp
      have := addr_toNat' (s.sp - BitVec.ofNat 32 8)
      simp only [Region.Contains, VG.Proof.MlDsa.Arm.KeyGen.hashLay, ite_true] at hx ⊢
      bv_omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), by
        rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_R L s K (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)]; exact fun _ h => h⟩
  · have := o.1
    simp only [Lay.pb, VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr L s K (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)] at this
    exact this

/-- A piece of the sponge, in a buffer of the layout. -/
theorem pieceS {K : Nat → Bool} {w : Bool} {p : VG.Impl.MlKem.Arm.Piece} (hb : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr (p.base, 0)) = true)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K).sizes (VG.Proof.MlDsa.Arm.KeyGen.ix p.base, p.off, p.len) kRegs = true)
    (hK : VG.Proof.MlDsa.Arm.KeyGen.ix p.base = 0 ∨ K (VG.Proof.MlDsa.Arm.KeyGen.ix p.base) = true) (hw : w = true → VG.Proof.MlDsa.Arm.KeyGen.ix p.base ∈ Wb) :
    PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K) VG.Proof.MlDsa.Arm.KeyGen.ix s w p := by
  have hi5 : VG.Proof.MlDsa.Arm.KeyGen.ix p.base < 5 := by
    simp only [VG.Proof.MlDsa.Arm.KeyGen.argOk, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((h | h) | h) | h <;> rw [h] <;> decide
  have e := VG.Proof.MlDsa.Arm.KeyGen.hashLay_size L s (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 p.base) hK hi5
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.base_pres hb, by rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr L s K (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)]; exact hs.base hb, hoe, hle, hpos, hlt, hsep, ?_⟩
  rw [VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr L s K (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _), e]
  cases w with
  | true => exact hs.cw _ (hw rfl) (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)
  | false => exact hs.cr _ hi5 (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)

end

/-! ## What a part keeps -/

section
variable {L : Lay} {Wb : List Nat} (hL : VG.Proof.MlDsa.Arm.KeyGen.OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
  (hf : Frame (L.RL W) m m') {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : i ∈ Wb)
include hL hf h hw

omit hf in
theorem keepD : ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := fun r hr => by
  obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
  exact VG.Proof.MlDsa.Arm.KeyGen.disjW hL (List.all_eq_true.mp h w hw') (.inl hw)

theorem bytes_keepW (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (VG.Proof.MlDsa.Arm.KeyGen.keepD hL h hw) hl

section
variable (hl : l = 1024)
include hl

theorem polyIs_keepW {f : Spec.MlDsa.Poly} (hp : Spec.MlDsa.PolyIs m (L.A i o) f) : Spec.MlDsa.PolyIs m' (L.A i o) f :=
  Proof.MlDsa.Verify.polyIs_frame hf (fun r hr => by have := VG.Proof.MlDsa.Arm.KeyGen.keepD hL h hw r hr; subst hl; exact this) hp

theorem reduced_keepW (hp : Spec.MlDsa.Reduced m (L.A i o)) : Spec.MlDsa.Reduced m' (L.A i o) :=
  Proof.MlDsa.Verify.reduced_frame hf (fun r hr => by have := VG.Proof.MlDsa.Arm.KeyGen.keepD hL h hw r hr; subst hl; exact this) hp

theorem polyAt_keepW : Spec.MlDsa.polyAt m' (L.A i o) = Spec.MlDsa.polyAt m (L.A i o) :=
  Proof.MlDsa.Verify.polyAt_frame hf (fun r hr => by have := VG.Proof.MlDsa.Arm.KeyGen.keepD hL h hw r hr; subst hl; exact this)

theorem natPolyAt_keepW : Spec.MlDsa.natPolyAt m' (L.A i o) = Spec.MlDsa.natPolyAt m (L.A i o) :=
  Proof.MlDsa.Verify.natPolyAt_frame hf (fun r hr => by have := VG.Proof.MlDsa.Arm.KeyGen.keepD hL h hw r hr; subst hl; exact this)

end

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Seeds`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: the seeds

`(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed of `RejNTTPoly` and
`ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`, `K1`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece)
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte :=
  Spec.MlDsa.H (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds. -/
structure K1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  kc : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s
  hx : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oHX) 128 = VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ
  sa : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32 = VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ
  sb : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 64 = VG.Proof.MlDsa.Arm.KeyGen.rho'Of p σ
  z : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 65)) 1 = [0]

/-- A part that writes the regions `W` keeps `K1`. -/
def k1Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  VG.Proof.MlDsa.Arm.KeyGen.kcChk p STK W && sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oHX, 128) W &&
    sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSA, 32) W &&
    sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSB, 64) W &&
    sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSB + 65, 1) W

theorem K1.keep {p : Params} {STK : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.KeyGen.k1Chk p STK W = true) : VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s' := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.kc.site.ok
  exact ⟨h.kc.keep hk h0, by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL hk.frame h1 (by decide) (by decide)]; exact h.hx,
    by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL hk.frame h2 (by decide) (by decide)]; exact h.sa,
    by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL hk.frame h3 (by decide) (by decide)]; exact h.sb,
    by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL hk.frame h4 (by decide) (by decide)]; exact h.z⟩

theorem shake31 : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem hx_eq (p : Params) (σ : State) :
    VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ = Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 31)
      (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ])))) 0 128 := by
  rw [VG.Proof.MlDsa.Arm.KeyGen.hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, VG.Proof.MlDsa.Arm.KeyGen.shake31,
    List.append_assoc]
  exact Proof.MlKem.shake256_eq _ _

theorem rho_eq (p : Params) (σ : State) : VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ = (VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : VG.Proof.MlDsa.Arm.KeyGen.rho'Of p σ = ((VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : VG.Proof.MlDsa.Arm.KeyGen.kOf p σ = ((VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ).drop 96).take 32 := rfl

theorem sc_ok (o : Nat) : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr (sc o)) = true := rfl

theorem seeds_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ : State} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s) (h11 : s.gpr .r11 = 1) : WP isa (seeds p) s fun s' => VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s' ∧ s'.gpr .r11 = 1 := by
  have hk := hF.k; have hl := hF.l
  have hs := h.site
  unfold seeds
  -- `k` and `ℓ`
  have blk : WP isa (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ)) s fun s₂ =>
      VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s₂ ∧ s₂.gpr .r11 = 1 ∧
        bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oKL) 2 = [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
    refine WP.block_append (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok hs (q := sc oKL) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide) p.k)
      fun s₁ ⟨k₁, b₁⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok (hs.kept k₁) (q := sc (oKL + 1)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide)
        (by decide) p.ℓ) fun s₂ ⟨k₂, b₂⟩ => ⟨(h.keep k₁ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk])).keep k₂ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk]), ?_, ?_⟩)
    · rw [k₂.cs .r11 (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), h11]
    · have b₁' := VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hs.ok k₂.frame (i := 0) (o := oKL) (l := 1) (by lsep hF) (by decide) (by decide)
      rw [show (2 : Nat) = 1 + 1 from rfl, Proof.MlKem.bytesAt_add, b₁'.trans b₁, add_ofNat_add]
      exact congrArg _ b₂
  refine WP.seq (WP.mono blk fun s₂ ⟨h₂, r₂, b₂⟩ => ?_)
  -- `H(ξ ‖ k ‖ ℓ, 128)`
  have hs₂ := h₂.site
  have hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → (fun _ => true) i = true → (fun _ => true) j = true →
      i ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb ∨ j ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb := fun i hi j hj hij _ _ _ _ => by
    simp only [VG.Proof.MlDsa.Arm.KeyGen.kWb, List.mem_cons, List.not_mem_nil, or_false]; omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.hashS hs₂ hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
      (ins := [⟨.r4, 0, 32⟩, ⟨.r7, oKL, 2⟩]) (q := ⟨.r7, oHX, 128⟩) (by simp) (fun pc hpc => ?_)
      (VG.Proof.MlDsa.Arm.KeyGen.pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size]) (.inl rfl)
        fun _ => by decide)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact VG.Proof.MlDsa.Arm.KeyGen.pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact VG.Proof.MlDsa.Arm.KeyGen.pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  have h₃ := h₂.keep k₃ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk])
  have hs₃ := h₃.site
  have hx₃ : bytesAt s₃.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oHX) 128 = VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ := by
    have o₃' : bytesAt s₃.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oHX) 128 = _ := o₃
    rw [o₃', VG.Proof.MlDsa.Arm.KeyGen.hx_eq]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr _ _ _ (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)]
    have e1 : bytesAt s₂.mem (State.addr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).ptr (VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r4)) + 0#64) 32 = VG.Proof.MlDsa.Arm.KeyGen.xiOf σ := h₂.xi
    have e2 : bytesAt s₂.mem (State.addr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).ptr (VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7)) + BitVec.ofNat 64 oKL) 2 =
      [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := b₂
    rw [e1, e2]; rfl
  -- `ρ` and `ρ′ ‖ 0` to the seeds
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS hs₃ (sb := .r7) (so := oHX) (db := .r7) (dO := oSA) (len := 32) ⟨rfl, by lsep hF⟩
    ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
    fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep k₄ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk])
  have hx₄ := (VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hs₃.ok k₄.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide)).trans hx₃
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS h₄.site (sb := .r7) (so := oHX + 32) (db := .r7) (dO := oSB) (len := 64)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by lsep hF)) fun s₅ ⟨k₅, b₅⟩ => ?_)
  have h₅ := h₄.keep k₅ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk])
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok h₅.site (q := sc (oSB + 65)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide) 0)
    fun s₆ ⟨k₆, b₆⟩ => ⟨⟨h₅.keep k₆ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk]), ?_, ?_, ?_, b₆⟩, ?_⟩
  · rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide),
      VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW h₄.site.ok k₅.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide)]
    exact hx₄
  · rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide),
      VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW h₄.site.ok k₅.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)]
    show bytesAt s₄.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (.r7, oSA)) 32 = _
    rw [b₄, VG.Proof.MlDsa.Arm.KeyGen.rho_eq, ← hx₃]
    exact (Proof.MlKem.bytesAt_take _ _ (by decide)).symm
  · rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)]
    show bytesAt s₅.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (.r7, oSB)) 64 = _
    rw [b₅, VG.Proof.MlDsa.Arm.KeyGen.rho'_eq, ← hx₄, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide), add_ofNat_add]
    rfl
  · rw [k₆.cs .r11 (by decide) (by decide), k₅.cs .r11 (by decide) (by decide), k₄.cs .r11 (by decide) (by decide),
      k₃.cs .r11 (by decide) (by decide), r₂]

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.StepsCT`. -/
section

/-!
# ML-DSA on 32-bit ARM: two runs in the buffers of a `Site`

Two runs in the same layout, with the same stack pointer (`Two`): a part that
leaks the same, and changes only what `Kept` allows, leaves two runs in it
(`RelCT.two`); and two runs of a part leak the same by taint analysis from
the pointers (`taint7`, `taint4`), or, for the sponge, by `hashS_tr`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece hash copy)
open VG.Spec.Sha3 (rates)

/-- Two runs in the layout `L`, with the same stack pointer. -/
def Two (L : Lay) (Wb : List Nat) (STK : Nat) (x y : State) : Prop :=
  VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x ∧ VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK y ∧ x.sp = y.sp

section
variable {L : Lay} {Wb : List Nat} {STK : Nat}

theorem Two.r7 {x y : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK x y) : ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr; rw [h.1.r7, h.2.1.r7]

theorem Two.regs {x y : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK x y) : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], x.gpr r = y.gpr r :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.r4, h.2.1.r4]
    · rw [h.1.r5, h.2.1.r5]
    · rw [h.1.r6, h.2.1.r6]
    · rw [h.1.r7, h.2.1.r7]

/-- A part that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x, VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK x → WP isa c x fun x' => ∃ rs, Kept rs x x') : RelCT isa P c (VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK) :=
  (RelCT.wpDep htr (F := fun x x' => ∃ rs, Kept rs x x')
    fun x y h => ⟨hok x (hP x y h).1, hok y (hP x y h).2.1⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩ => ⟨(hP σ₁ σ₂ hp).1.kept hx, (hP σ₁ σ₂ hp).2.1.kept hy, by
      rw [hx.sp, hy.sp]; exact (hP σ₁ σ₂ hp).2.2⟩

/-- Taint analysis, from the pointer to `scratch`. -/
theorem taint7 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.Arm.taint.T} (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  taint_prog [.r7] (fun x y hxy => (hP x y hxy).r7) h

/-- Taint analysis, from the pointers of the layout. -/
theorem taint4 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  taint_prog [.r4, .r5, .r6, .r7] (fun x y hxy => (hP x y hxy).regs) h

/-- Two runs of the sponge. -/
theorem hashS_tr {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) {ins : List VG.Impl.MlKem.Arm.Piece} {q : VG.Impl.MlKem.Arm.Piece} (hne : ins ≠ [])
    (hin : ∀ s, VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s → ∀ p ∈ ins, PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K) VG.Proof.MlDsa.Arm.KeyGen.ix s false p)
    (hq : ∀ s, VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s → PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay L s K) VG.Proof.MlDsa.Arm.KeyGen.ix s true q) {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.Arm.KeyGen.Two L Wb STK x y) : RelCT isa P (hash rate sfx ins [q]) fun _ _ => True :=
  RelCT.mono (RelCT.exists_ fun (s₀ : State) =>
    hash_ct (P := fun a b => s₀ = a ∧ P a b) (L := VG.Proof.MlDsa.Arm.KeyGen.hashLay L s₀ K) (idx := VG.Proof.MlDsa.Arm.KeyGen.ix) hrate hre hse hne
      fun a b ⟨e, hab⟩ => by
        subst e
        have ⟨ha, hb, hsp⟩ := hP s₀ b hab
        have hl : VG.Proof.MlDsa.Arm.KeyGen.hashLay L s₀ K = VG.Proof.MlDsa.Arm.KeyGen.hashLay L b K := by simp only [VG.Proof.MlDsa.Arm.KeyGen.hashLay, hsp]
        refine ⟨⟨ha.ctx hK, hin s₀ ha, fun p hp => ?_⟩, ⟨hl ▸ hb.ctx hK, hl ▸ hin b hb, fun p hp => ?_⟩, hsp⟩ <;>
          rw [List.mem_singleton] at hp <;> subst hp
        · exact hq s₀ ha
        · exact hl ▸ hq b hb)
    (fun a b h => ⟨a, rfl, h⟩) fun _ _ h => h

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.SeedsCT`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: the seeds leak nothing

Two runs of the seeds in the same layout leak the same (`seeds_two`): the
bytes `k` and `ℓ` are public, and every access is through the pointers of the
layout; which gives the piece of the seeds (`seeds_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params)

/-- Two runs whose entry states have the same layout. -/
def KTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y

theorem kc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : VG.Proof.MlDsa.Arm.KeyGen.kgPub p σ₁ σ₂) (h₁ : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ₁ x)
    (h₂ : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ₂ y) : VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ₁) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y :=
  ⟨h₁.site, VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem kc_two {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : VG.Proof.MlDsa.Arm.KeyGen.kgPub p σ₁ σ₂) (h₁ : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ₁ x)
    (h₂ : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ₂ y) : VG.Proof.MlDsa.Arm.KeyGen.KTwo p STK x y :=
  ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁ h₂⟩

/-- A part that leaks the same in two runs in every layout of key generation. -/
theorem ktwo {p : Params} {STK : Nat} {c : Prog isa} (h : ∀ σ, RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.KTwo p STK) c fun _ _ => True :=
  RelCT.exists_ h

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem ktrue : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → (fun _ => true) i = true → (fun _ => true) j = true →
    i ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb ∨ j ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb := fun i _ j _ hij _ _ _ _ => by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.kWb, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem seeds_two {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (σ : State) :
    RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK) (seeds p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  have hP : ∀ x y, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y → VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y := fun _ _ h => h
  unfold seeds
  refine RelCT.seq (RelCT.two hP (VG.Proof.MlDsa.Arm.KeyGen.taint7 hP (VG.Proof.MlDsa.Arm.KeyGen.setKL_taint p.k (by omega) p.ℓ (by omega))) fun x hs => ?_) ?_
  · refine WP.block_append (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok hs (q := sc oKL) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide) p.k)
      fun s₁ ⟨k₁, _⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok (hs.kept k₁) (q := sc (oKL + 1)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide)
        (by decide) p.ℓ) fun s₂ ⟨k₂, _⟩ => ⟨_, (k₁.monoL (W' := [VG.Proof.MlDsa.Arm.KeyGen.tri (sc oKL) 1, VG.Proof.MlDsa.Arm.KeyGen.tri (sc (oKL + 1)) 1])
          (by simp)).trans (k₂.monoL (by simp))⟩)
  have hin : ∀ s, VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK s → ∀ pc ∈ ([⟨.r4, 0, 32⟩, ⟨.r7, oKL, 2⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) s fun _ => true) VG.Proof.MlDsa.Arm.KeyGen.ix s false pc := fun s hs pc hpc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact VG.Proof.MlDsa.Arm.KeyGen.pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact VG.Proof.MlDsa.Arm.KeyGen.pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  have hq : ∀ s, VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK s →
      PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) s fun _ => true) VG.Proof.MlDsa.Arm.KeyGen.ix s true (⟨.r7, oHX, 128⟩ : Impl.MlKem.Arm.Piece) := fun s hs =>
    VG.Proof.MlDsa.Arm.KeyGen.pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size]) (.inl rfl)
      fun _ => by decide
  refine RelCT.seq (RelCT.two hP (VG.Proof.MlDsa.Arm.KeyGen.hashS_tr VG.Proof.MlDsa.Arm.KeyGen.ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide)
    (by simp) hin hq hP) fun x hs => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.hashS hs VG.Proof.MlDsa.Arm.KeyGen.ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by decide) (by decide) (by simp) (hin x hs) (hq x hs)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (VG.Proof.MlDsa.Arm.KeyGen.taint7 hP (by taint_decide)) fun x hs =>
    WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS hs (sb := .r7) (so := oHX) (db := .r7) (dO := oSA) (len := 32) ⟨rfl, by lsep hF⟩
      ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (VG.Proof.MlDsa.Arm.KeyGen.taint7 hP (by taint_decide)) fun x hs =>
    WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS hs (sb := .r7) (so := oHX + 32) (db := .r7) (dO := oSB) (len := 64) ⟨rfl, by lsep hF⟩
      ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  exact VG.Proof.MlDsa.Arm.KeyGen.taint7 hP (by taint_decide)

theorem seeds_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s ∧ s.gpr .r11 = 1) (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s ∧ s.gpr .r11 = 1) (seeds p) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.KeyGen.seeds_ok hF h.1 h.2,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (VG.Proof.MlDsa.Arm.KeyGen.ktwo fun σ => VG.Proof.MlDsa.Arm.KeyGen.seeds_two hF σ) fun _ _ _ _ _ _ pub h₁ h₂ => VG.Proof.MlDsa.Arm.KeyGen.kc_two pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Mask`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: masking a sampled polynomial

After each sampler, `r11` is ANDed with its result (0 or 1, in `r0`), and each
coefficient of the polynomial it wrote with `-r0`: the polynomial is kept if
the sampler succeeded, and zeroed if it failed (`mask_ok`), without a branch
(`mask_tr`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients after masking with `-r`, for `r` 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) : x &&& (0 - r) = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [ifp rfl, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

/-! ## One coefficient -/

section
variable {s : State} {x c M : BitVec 32}

theorem maskBody_ok (h1 : s.gpr .r1 = x) (h2 : s.gpr .r2 = c) (h12 : s.gpr .r12 = M)
    (ir : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ow : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block maskBody) s fun s' =>
      s'.gpr .r1 = x + 4 ∧ s'.gpr .r2 = c - 1 ∧ s'.gpr .r12 = M ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 &&& M) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [maskBody, h1, h2, h12, ir, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After masking `k` coefficients of the polynomial at `P` with `M`. -/
structure MaskInv (P M : BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = P + BitVec.ofNat 32 (4 * k)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - k))
  r12 : s.gpr .r12 = M
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regA P 1024] s₀.mem s.mem
  co : ∀ t < 256, coeffAt s.mem (State.addr P) t =
    if t < k then coeffAt s₀.mem (State.addr P) t &&& M else coeffAt s₀.mem (State.addr P) t

theorem mask_step {P M : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32) (cw : Covers [regA P 1024] s₀.wr)
    {k : Nat} (hk : k < 256) {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.MaskInv P M s₀ k s) :
    WP isa (.block maskBody) s fun s' => VG.Proof.MlDsa.Arm.KeyGen.MaskInv P M s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have eP : State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 (4 * k) := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cP : (regA P 1024).Contains (State.addr P + BitVec.ofNat 64 (4 * k)) 4 := contains_off (by omega) (by omega)
  have ow : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 := by
    rw [eP, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩
  have ir : InRegions (s.rd ++ s.wr) (State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 :=
    let ⟨r, hr, hc⟩ := ow; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.maskBody_ok h.r1 h.r2 h.r12 ir ow)
    fun s' ⟨r1, r2, r12, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, r12, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r1]; exact VG.Proof.MlKem.Arm.Add.ptr_succ _ 4 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eP]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, eP, VG.Proof.MlDsa.Arm.KeyGen.coeffAt_writeW32 _ _ ht hk]
    by_cases e : k = t
    · subst e
      have := h.co k hk
      rw [ifn (Nat.lt_irrefl _)] at this
      rw [ifp rfl, ifp (Nat.lt_succ_self _), ← this]; rfl
    · rw [ifn e, h.co t ht]
      by_cases htk : t < k
      · rw [ifp htk, ifp (by omega)]
      · rw [ifn htk, ifn (by omega)]
  · rw [z]; exact count_z (k := 1) hk (by decide) (by decide)

theorem mask_loop {P M : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32) (cw : Covers [regA P 1024] s₀.wr)
    (h1 : s₀.gpr .r1 = P) (h2 : s₀.gpr .r2 = BitVec.ofNat 32 256) (h12 : s₀.gpr .r12 = M) :
    WP isa (.loop (.block maskBody) .ne) s₀ fun s =>
      Kept [regA P 1024] s₀ s ∧ ∀ t < 256, coeffAt s.mem (State.addr P) t = coeffAt s₀.mem (State.addr P) t &&& M :=
  wp_loop_ne (VG.Proof.MlDsa.Arm.KeyGen.MaskInv P M s₀) (N := 256) (by decide) (fun k hk s h => VG.Proof.MlDsa.Arm.KeyGen.mask_step fP cw hk h)
    (fun s h => ⟨⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, h.frame⟩, fun t ht => by
      rw [h.co t ht, ifp ht]⟩)
    ⟨by rw [h1]; simp, by rw [h2], h12, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t _ => by rw [ifn (Nat.not_lt_zero t)]⟩

/-! ## The polynomial -/

abbrev maskPre (a : Ptr) : List Instr :=
  [.mov .r12 (.imm 0), .dp .sub .r12 .r12 (.reg .r0)] ++ Arg.instrs .r1 (.ptr a) ++ [.mov .r2 (.imm 256)]

theorem maskPre_ok {a : Ptr} (ha : VG.Proof.MlDsa.Arm.KeyGen.argOk (.ptr a) = true) (s : State) :
    WP isa (.block (VG.Proof.MlDsa.Arm.KeyGen.maskPre a)) s fun s' =>
      Only s s' ∧ s'.gpr .r12 = 0 - s.gpr .r0 ∧ s'.gpr .r1 = s.gpr a.1 + BitVec.ofNat 32 a.2 ∧
        s'.gpr .r2 = BitVec.ofNat 32 256 := by
  obtain ⟨-, n1, -, -, n12⟩ := pres_ne (VG.Proof.MlDsa.Arm.KeyGen.base_pres (r := a.1) (by simpa [VG.Proof.MlDsa.Arm.KeyGen.argOk] using ha)).1
    (VG.Proof.MlDsa.Arm.KeyGen.base_pres (r := a.1) (by simpa [VG.Proof.MlDsa.Arm.KeyGen.argOk] using ha)).2
  have n1' : ¬ a.1 = .r1 := n1
  have n12' : ¬ a.1 = .r12 := n12
  run_block [VG.Proof.MlDsa.Arm.KeyGen.maskPre, Arg.instrs, ldc, n1', n12', VG.Proof.MlDsa.Arm.KeyGen.ldc_eq]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, ?_⟩
  · obtain ⟨-, m1, m2, -, m12⟩ := pres_ne hr hl
    simp only [m1, m2, m12, ite_false]
  · simp

theorem mask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {a : Ptr}
    (pa : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L a 1024) (hw : VG.Proof.MlDsa.Arm.KeyGen.ix a.1 ∈ Wb) (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) :
    WP isa (mask a) s fun s' => Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri a 1024]) s s' ∧
      ∀ t < 256, coeffAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a) t = if s.gpr .r0 = 1 then coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a) t else 0 := by
  have gb := hs.val pa.1
  simp only [VG.Proof.MlDsa.Arm.KeyGen.argVal] at gb
  have ea := hs.addrE pa (by decide)
  have fa := hs.fitE pa (by decide)
  have cw := hs.cwE pa hw
  rw [← hs.regE pa (by decide)] at cw
  unfold mask
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.maskPre_ok pa.1 s) fun s₁ ⟨o₁, g12, g1, g2⟩ => ?_)
  rw [gb] at g1
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.mask_loop fa (by rw [o₁.wr]; exact cw) g1 g2 g12) fun s' ⟨k, co⟩ => ⟨?_, fun t ht => ?_⟩
  · refine (o₁.kept _).trans (k.mono fun r hr => ?_)
    rw [List.mem_singleton] at hr; subst hr
    rw [hs.regE pa (by decide)]
    exact List.mem_singleton_self _
  · rw [← ea, co t ht, o₁.mem, VG.Proof.MlDsa.Arm.KeyGen.and_mask hr]

/-! ## Constant time -/

/-- The check is the same for every offset: its hint is computed once. -/
theorem mask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (mask (sc (oP j)))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (mask (sc 0)))).isSome = true := by decide +kernel

theorem mask_tr {j : Nat} (hj : j < 128) {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .r7 = y.gpr .r7) :
    RelCT isa P (mask (sc (oP j))) fun _ _ => True :=
  taint_prog [.r7] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (VG.Proof.MlDsa.Arm.KeyGen.mask_taint j hj)

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: the samplers

The primitives key generation calls, verified with at most `S` bytes of stack
(`PrimsOk`); and the entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂`
(`expS_piece`): after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`
(`KSamp`), each polynomial is reduced (and those of `s₁ ‖ s₂` small), and
`r11` is what `Good` says.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly toRq polyAt coeffAt Reduced
  PolyIs Outcome)
open VG.Proof.MlDsa.KeyGen (seedA seedS Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : VG.Proof.MlDsa.Arm.KeyGen.Callee P.ntt (fun stk => Spec.MlDsa.nttContract Arm.abi stk) S
  invNtt : VG.Proof.MlDsa.Arm.KeyGen.Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract Arm.abi stk) S
  mul : VG.Proof.MlDsa.Arm.KeyGen.Callee P.mul (fun stk => Spec.MlDsa.mulContract Arm.abi stk) S
  mulAdd : VG.Proof.MlDsa.Arm.KeyGen.Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract Arm.abi stk) S
  add : VG.Proof.MlDsa.Arm.KeyGen.Callee P.add (fun stk => Spec.MlDsa.addContract Arm.abi stk) S
  rejNtt : VG.Proof.MlDsa.Arm.KeyGen.Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract Arm.abi stk) S
  rejBounded : VG.Proof.MlDsa.Arm.KeyGen.Callee P.rejBounded (fun stk => Spec.MlDsa.rejBoundedContract Arm.abi stk) S
  power2Round : VG.Proof.MlDsa.Arm.KeyGen.Callee P.power2Round (fun stk => Spec.MlDsa.power2RoundContract Arm.abi stk) S
  simpleBitPack : VG.Proof.MlDsa.Arm.KeyGen.Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract Arm.abi stk) S
  bitPack : VG.Proof.MlDsa.Arm.KeyGen.Callee P.bitPack (fun stk => Spec.MlDsa.bitPackContract Arm.abi stk) S

/-! ## `r11` -/

theorem and11_ok (s : State) :
    WP isa (.block and11) s (· = s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)) := by
  apply WP.of_runBlock
  simp only [and11, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
    Option.some.injEq, exists_eq_left']

theorem Site.setReg {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {r : Reg}
    (hr : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7) (v : BitVec 32) : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK (s.setReg r v) :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, h.p1, h.s8, h.spk,
    by rw [gpr_setReg_of_ne _ _ hr.2.2.2.symm]; exact h.r7, by rw [gpr_setReg_of_ne _ _ hr.1.symm]; exact h.r4,
    by rw [gpr_setReg_of_ne _ _ hr.2.1.symm]; exact h.r5, by rw [gpr_setReg_of_ne _ _ hr.2.2.1.symm]; exact h.r6,
    h.cw, h.cr⟩

theorem K1.r11 {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s) (v : BitVec 32) :
    VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ (s.setReg .r11 v) :=
  ⟨⟨h.kc.site.setReg (by decide) v, h.kc.rd, h.kc.wr, h.kc.sp, h.kc.sav, h.kc.lr, h.kc.xi⟩, h.hx, h.sa, h.sb, h.z⟩

/-! ## What the samplers leave -/

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (STK : Nat) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s
  ex : ∃ (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r'))) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ) e r A S (s.gpr .r11)

/-- A part that keeps `K1`, the polynomials sampled so far and `r11` keeps `KSamp`. -/
theorem KSamp.keep {p : Params} {STK : Nat} {σ : State} {e r : Nat} {s s' : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ e r s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.KeyGen.k1Chk p STK W = true)
    (ha : ∀ e' < e, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e', 1024) W = true)
    (hs : ∀ r' < r, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + r'), 1024) W = true)
    (h11 : s'.gpr .r11 = s.gpr .r11) : VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ e r s' := by
  have hL := h.k1.kc.site.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.keep hk hc, A, S, fun e' he' => ?_, fun r' hr' => ?_, by rw [h11]; exact hG⟩
  · exact VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL hk.frame (ha e' he') (by decide) rfl (hA e' he')
  · exact ⟨VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL hk.frame (hs r' hr') (by decide) rfl (hS r' hr').1, (hS r' hr').2⟩

theorem KSamp.zero {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s) (h11 : s.gpr .r11 = 1) :
    VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h11]; exact Proof.MlDsa.KeyGen.good_zero _ _ _ _⟩

/-! ## A sampled polynomial, masked -/

/-- `and11` and `mask`, after a sampler whose result `r0` is 0 or 1. -/
theorem andMask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site L Wb STK s) {a : Ptr}
    (pa : VG.Proof.MlDsa.Arm.KeyGen.PtrIn L a 1024) (hw : VG.Proof.MlDsa.Arm.KeyGen.ix a.1 ∈ Wb) (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) :
    WP isa (.seq (.block and11) (mask a)) s fun s' =>
      Kept (L.RL [VG.Proof.MlDsa.Arm.KeyGen.tri a 1024]) (s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)) s' ∧
      s'.gpr .r11 = s.gpr .r11 &&& s.gpr .r0 ∧
      ∀ t < 256, coeffAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a) t = if s.gpr .r0 = 1 then coeffAt s.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa L a) t else 0 := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.and11_ok s) fun s₁ e₁ => ?_)
  subst e₁
  have h0 : (s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)).gpr .r0 = s.gpr .r0 := gpr_setReg_of_ne _ _ (by decide)
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.mask_ok (hs.setReg (by decide) _) pa hw (by rw [h0]; exact hr)) fun s' ⟨k, co⟩ =>
    ⟨k, ?_, fun t ht => by rw [co t ht, h0]; rfl⟩
  rw [k.cs .r11 (by decide) (by decide)]
  exact gpr_setReg_self _ _ _

/-- What a sampler and its mask leave in entry `j` of the polynomials, from
the facts the sampler's contract gives. -/
theorem masked_poly {m m' : Mem} {q : Addr} {r : BitVec 32} (hred : r = 1 → Reduced m q)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (polyAt m' q) ∧ (r = 1 → polyAt m' q = polyAt m q) ∧
      (r ≠ 1 → PolyIs m' q (toRq (Vector.replicate 256 0))) := by
  by_cases h1 : r = 1
  · have := Proof.MlDsa.KeyGen.masked_one h1 h
    exact ⟨⟨this.2 (hred h1), rfl⟩, fun _ => this.1, fun h => absurd h1 h⟩
  · have := Proof.MlDsa.KeyGen.masked_zero h1 h
    exact ⟨⟨this.1, rfl⟩, fun h => absurd h h1, fun _ => this⟩

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) : seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-- The seed and the call of `RejNTTPoly`. -/
theorem rnA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK s) {Q : State → Prop}
    (hQ : ∀ s', Kept ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL [VG.Proof.MlDsa.Arm.KeyGen.tri (aP e) 1024, VG.Proof.MlDsa.Arm.KeyGen.tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP e))) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 34)) (s'.gpr .r0)
        (polyAt s'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP e))) → Q s') :
    WP isa (rejNttAt P (sc oSA) (aP e)) s Q := by
  have := hF.kl
  exact VG.Proof.MlDsa.Arm.KeyGen.rn_ok hP.rejNtt hs (by omega) (sd := sc oSA) (a := aP e) (w := sc oSS)
    ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF,
      by lsep hF, by lsep hF⟩ hQ

theorem expA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ e 0 s) :
    WP isa (expA P p e) s (VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  have hs := h.k1.kc.site
  unfold expA sampled
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok hs (q := sc (oSA + 32)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide)
    (by decide) (e % p.ℓ)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok (hs.kept k₁) (q := sc (oSA + 33))
      ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide) (e / p.ℓ)) fun s₂ ⟨k₂, b₂⟩ => ?_))
  have h₁ := h.keep k₁ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₁.cs .r11 (by decide) (by decide))
  have h₂ := h₁.keep k₂ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₂.cs .r11 (by decide) (by decide))
  have hs₂ := h₂.k1.kc.site
  have hseed : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 34 = seedA (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    have b₁' := VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hs.ok k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₂.k1.sa,
      add_ofNat_add, add_ofNat_add, VG.Proof.MlDsa.Arm.KeyGen.seedA_eq, List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSA + 32 + 1)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
    rw [e1, e2]; rfl
  -- the call
  refine WP.seq (VG.Proof.MlDsa.Arm.KeyGen.rnA_ok hP hF hS he hs₂ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have hs₃ := hs₂.kept k₃
  -- the result and the mask
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.andMask_ok hs₃ (a := aP e) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) hr01) fun s₄ ⟨k₄, r₄, co⟩ => ?_
  have h₃ := h₂.keep k₃ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₃.cs .r11 (by decide) (by decide))
  obtain ⟨A, S', hA, _, hG⟩ := h₃.ex
  obtain ⟨pi, p1, _⟩ := VG.Proof.MlDsa.Arm.KeyGen.masked_poly hred co
  have hL := hs.ok
  refine ⟨(h₃.k1.r11 _).keep k₄ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]),
    fun e' => if e' = e then polyAt s₄.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP e)) else A e', S', fun e' he' => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]; exact VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hA e' he')
    · rw [ifp rfl]; exact pi
  · rw [r₄]; exact Proof.MlDsa.KeyGen.good_A he hG hout p1

/-! ## An entry of `s₁ ‖ s₂` -/

omit hP hF hS in
theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) : seedS ρ' r = ρ' ++ [BitVec.ofNat 8 r, 0] := by
  simp only [seedS, Proof.MlDsa.KeyGen.integerToBytes_two hr]

omit hP hS in
theorem eta_of : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

/-- The call of `RejBoundedPoly`. -/
theorem rbS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK s)
    {Q : State → Prop}
    (hQ : ∀ s', Kept ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL [VG.Proof.MlDsa.Arm.KeyGen.tri (sP p r) 1024, VG.Proof.MlDsa.Arm.KeyGen.tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) →
      Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 66)).map toRq)
        (s'.gpr .r0) (polyAt s'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) → Q s') :
    WP isa (rejBoundedAt P (sc oSB) p.η (sP p r)) s Q := by
  have := hF.kl
  exact VG.Proof.MlDsa.Arm.KeyGen.rb_ok hP.rejBounded hs (by omega) (sd := sc oSB) (a := sP p r) (w := sc oSS)
    ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
      show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩ (VG.Proof.MlDsa.Arm.KeyGen.eta_of hF) hQ

theorem expS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) (r + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold expS sampled
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok hs (q := sc (oSB + 64)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide) r)
    fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h.keep k₁ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
    (k₁.cs .r11 (by decide) (by decide))
  have hs₁ := h₁.k1.kc.site
  have hseed : bytesAt s₁.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 66 = seedS (VG.Proof.MlDsa.Arm.KeyGen.rho'Of p σ) r := by
    rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₁.k1.sb,
      add_ofNat_add, add_ofNat_add, VG.Proof.MlDsa.Arm.KeyGen.seedS_eq _ (by omega), List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₁.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
    have e2 : bytesAt s₁.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 64 + 1)) 1 = [0] := h₁.k1.z
    rw [e1, e2]; rfl
  refine WP.seq (VG.Proof.MlDsa.Arm.KeyGen.rbS_ok hP hF hS hr hs₁ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have hs₃ := hs₁.kept k₃
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.andMask_ok hs₃ (a := sP p r) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) hr01)
    fun s₄ ⟨k₄, r₄, co⟩ => ?_
  have h₃ := h₁.keep k₃ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
    (k₃.cs .r11 (by decide) (by decide))
  obtain ⟨A, S', hA, hS', hG⟩ := h₃.ex
  obtain ⟨pi, p1, p0⟩ := VG.Proof.MlDsa.Arm.KeyGen.masked_poly hred co
  obtain ⟨z, hz, hz1, hz0, hG'⟩ := Proof.MlDsa.KeyGen.good_S hr hG hout
  have hL := hs.ok
  refine ⟨(h₃.k1.r11 _).keep k₄ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk]), A, fun r' => if r' = r then z else S' r',
    fun e' he' => VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hA e' he'), fun r' hr' => ?_,
    by rw [r₄]; exact hG'⟩
  dsimp only
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · rw [ifn (by omega)]
    exact ⟨VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hS' r' hr').1, (hS' r' hr').2⟩
  · rw [ifp rfl]
    refine ⟨?_, hz⟩
    show PolyIs s₄.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (sP p r')) (toRq z)
    by_cases h1 : s₃.gpr .r0 = 1
    · rw [hz1 h1, ← p1 h1]; exact pi
    · rw [hz0 h1]; exact p0 h1

/-! ## Constant time -/

omit hP hF hS in
theorem rho_pub {σ₁ σ₂ : State} (pub : VG.Proof.MlDsa.Arm.KeyGen.kgPub p σ₁ σ₂) : VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ₁ = VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).1

omit hP hF hS in
theorem rej_pub {σ₁ σ₂ : State} (pub : VG.Proof.MlDsa.Arm.KeyGen.kgPub p σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (VG.Proof.MlDsa.Arm.KeyGen.rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (VG.Proof.MlDsa.Arm.KeyGen.rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).2 r hr

omit hP hF hS in
theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
theorem setS_taint : ∀ v < 16, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block (setB (sc (oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem andMask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP j))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem expA_two {e : Nat} (he : e < p.k * p.ℓ) (σ : State) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32) (expA P p e)
      fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 34 = bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32 ++
      [BitVec.ofNat 8 (e % p.ℓ), BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x hs =>
    WP.block_append (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok hs (q := sc (oSA + 32)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide)
      (e % p.ℓ)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok (hs.kept k₁) (q := sc (oSA + 33)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩
        (by decide) (by decide) (e / p.ℓ)) fun s₂ ⟨k₂, b₂⟩ => ⟨⟨_, (k₁.monoL (W' := [VG.Proof.MlDsa.Arm.KeyGen.tri (sc (oSA + 32)) 1,
          VG.Proof.MlDsa.Arm.KeyGen.tri (sc (oSA + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩, by
        have hL := hs.ok
        have b₁' := VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
        have b₀ := (VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₂.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)).trans
          (VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₁.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSA + 32 + 1)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32)
    (VG.Proof.MlDsa.Arm.KeyGen.taint7 (fun _ _ h => h.1) (VG.Proof.MlDsa.Arm.KeyGen.setIJ_taint _ (by omega) _ (by omega))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
        bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 34 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  have ok := fun x (hs : VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x) =>
    VG.Proof.MlDsa.Arm.KeyGen.rnA_ok hP hF hS he hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (VG.Proof.MlDsa.Arm.KeyGen.rn_tr hP.rejNtt (by omega) (sd := sc oSA) (a := aP e) (w := sc oSS)
      ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
        show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact VG.Proof.MlDsa.Arm.KeyGen.taint7 (fun _ _ h => h) (VG.Proof.MlDsa.Arm.KeyGen.andMask_taint _ (by omega))

theorem expA_tr {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 (VG.Proof.MlDsa.Arm.KeyGen.Pre p STK) (VG.Proof.MlDsa.Arm.KeyGen.kgPub p) fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ e 0 s) (expA P p e) fun _ _ => True :=
  VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSA) 32)
    (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.expA_two hP hF hS he σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
      ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.k1.kc h₂.k1.kc, by
        rw [h₁.k1.sa, VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub, h₂.k1.sa, VG.Proof.MlDsa.Arm.KeyGen.rho_pub pub]⟩

theorem expS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧ bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 64) r)) (expS P p r)
      fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold expS sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    (bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 65)) 1 = [0] →
      bytesAt x'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 66 = seedS (bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 64) r)
  have hF1 : ∀ x, VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x → WP isa (.block (setB (sc (oSB + 64)) r)) x (F x) := fun x hs =>
    WP.mono (VG.Proof.MlDsa.Arm.KeyGen.setB_ok hs (q := sc (oSB + 64)) ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩ (by decide) (by decide) r) fun x' ⟨k₁, b₁⟩ =>
      ⟨⟨_, k₁⟩, fun hz => by
        have hL := hs.ok
        have b₀ := VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)
        have b₂ := VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₁.frame (i := 0) (o := oSB + 64 + 1) (l := 1) (by lsep hF) (by decide) (by decide)
        rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, VG.Proof.MlDsa.Arm.KeyGen.seedS_eq _ (by omega), List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt x'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
        have e2 : bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 64 + 1)) 1 = [0] := hz
        rw [e1, b₂, e2]; rfl⟩
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧ bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 64) r))
    (VG.Proof.MlDsa.Arm.KeyGen.taint7 (fun _ _ h => h.1) (VG.Proof.MlDsa.Arm.KeyGen.setS_taint _ (by omega))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
        Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 66) =
          Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oSB) 66))
      fun x' y' ⟨_, x, y, ⟨T, zx, zy, hl⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx zx, by' zy, hl]⟩) ?_
  have ok := fun x (hs : VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x) =>
    VG.Proof.MlDsa.Arm.KeyGen.rbS_ok hP hF hS hr hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (VG.Proof.MlDsa.Arm.KeyGen.rb_tr hP.rejBounded (by omega) (sd := sc oSB) (a := sP p r)
      (w := sc oSS) ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩,
        show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      (VG.Proof.MlDsa.Arm.KeyGen.eta_of hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact VG.Proof.MlDsa.Arm.KeyGen.taint7 (fun _ _ h => h) (VG.Proof.MlDsa.Arm.KeyGen.andMask_taint _ (by omega))

theorem expS_tr {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.Rel2 (VG.Proof.MlDsa.Arm.KeyGen.Pre p STK) (VG.Proof.MlDsa.Arm.KeyGen.kgPub p) fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) r s) (expS P p r)
      fun _ _ => True :=
  VG.Proof.MlDsa.Arm.KeyGen.rel_of (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.expS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.k1.kc h₂.k1.kc, h₁.k1.z, by rw [VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub]; exact h₂.k1.z, by
      rw [h₁.k1.sb, VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub, h₂.k1.sb]; exact VG.Proof.MlDsa.Arm.KeyGen.rej_pub pub hr⟩

/-! ## The pieces -/

theorem expA_piece {e : Nat} (he : e < p.k * p.ℓ) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ e 0 s) (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (e + 1) 0 s) (expA P p e) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.KeyGen.expA_ok hP hF hS he h, VG.Proof.MlDsa.Arm.KeyGen.expA_tr hP hF hS he⟩

theorem expS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) r s) (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) (r + 1) s)
      (expS P p r) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.KeyGen.expS_ok hP hF hS hr h, VG.Proof.MlDsa.Arm.KeyGen.expS_tr hP hF hS hr⟩

/-- The entries of `Â`. -/
theorem sampA_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.K1 p STK σ s ∧ s.gpr .r11 = 1) (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) 0 s)
      (VG.Impl.MlDsa.Arm.KeyGen.seqR (expA P p) 0 (p.k * p.ℓ)) := by
  refine Piece.mono (Piece.seqR (I := fun e σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ e 0 s) (p.k * p.ℓ) 0
    fun e _ he => VG.Proof.MlDsa.Arm.KeyGen.expA_piece hP hF hS (by omega)) (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
  simpa using h

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) 0 s) (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (VG.Impl.MlDsa.Arm.KeyGen.seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => VG.Proof.MlDsa.Arm.KeyGen.expS_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestBase`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
and `r11` as `R` (`Good`), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed to
`pk` and `sk`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (STK : Nat) (σ : State) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (R : BitVec 32)
    (np nj nr : Nat) (s : State) : Prop where
  kc : VG.Proof.MlDsa.Arm.KeyGen.KC p STK σ s
  r11 : s.gpr .r11 = R
  good : Good p (VG.Proof.MlDsa.Arm.KeyGen.xiOf σ) (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i)))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))
    (if j < nj then VG.Spec.MlDsa.ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 3 0) 32 = VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ
  sk0 : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 0) 32 = VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ
  sk1 : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 32) 32 = VG.Proof.MlDsa.Arm.KeyGen.kOf p σ
  packs : ∀ r < np, bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 (128 + lenS p * r)) (lenS p) = VG.Spec.MlDsa.bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 3 (32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 (oT0 p + 416 * i)) 416 = VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096

/-- A part that writes `W` keeps what `KR` says. -/
structure KRChk (p : Params) (STK : Nat) (np nj nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  kc : VG.Proof.MlDsa.Arm.KeyGen.kcChk p STK W = true
  aS : ∀ e < p.k * p.ℓ, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e, 1024) W = true
  s2 : ∀ i < p.k, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + (p.ℓ + i)), 1024) W = true
  s1 : ∀ j < p.ℓ, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + j), 1024) W = true
  pk0 : sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (3, 0, 32) W = true
  sk0 : sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (4, 0, 32) W = true
  sk1 : sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (4, 32, 32) W = true
  packs : ∀ r < np, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p) W = true
  rows : ∀ i < nr, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (3, 32 + 320 * i, 320) W = true ∧
    sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (4, oT0 p + 416 * i, 416) W = true

/-- Proves a `KRChk`, in each case of `η`. -/
syntax "krchk " term:max : tactic
macro_rules
  | `(tactic| krchk $hF) => `(tactic| (
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      first
        | lsep $hF [kcChk, ($hF).pk, ($hF).sk]
        | rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep $hF [kcChk, ($hF).pk, ($hF).sk, hlen]))

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : sepAll sz a W₁ = true) (h₂ : sepAll sz a W₂ = true) : sepAll sz a (W₁ ++ W₂) = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁, h₂⟩

theorem kcChk_append {p : Params} {STK : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : VG.Proof.MlDsa.Arm.KeyGen.kcChk p STK W₁ = true)
    (h₂ : VG.Proof.MlDsa.Arm.KeyGen.kcChk p STK W₂ = true) : VG.Proof.MlDsa.Arm.KeyGen.kcChk p STK (W₁ ++ W₂) = true := by
  simp only [VG.Proof.MlDsa.Arm.KeyGen.kcChk, Bool.and_eq_true] at *
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.sepAll_append h₁.1 h₂.1, VG.Proof.MlDsa.Arm.KeyGen.sepAll_append h₁.2 h₂.2⟩

/-- The checks of two pieces of writes, for both. -/
theorem KRChk.append {p : Params} {STK np nj nr : Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr W₁) (h₂ : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr W₂) : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr (W₁ ++ W₂) :=
  ⟨VG.Proof.MlDsa.Arm.KeyGen.kcChk_append h₁.kc h₂.kc, fun e he => VG.Proof.MlDsa.Arm.KeyGen.sepAll_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => VG.Proof.MlDsa.Arm.KeyGen.sepAll_append (h₁.s2 i hi) (h₂.s2 i hi), fun j hj => VG.Proof.MlDsa.Arm.KeyGen.sepAll_append (h₁.s1 j hj) (h₂.s1 j hj),
    VG.Proof.MlDsa.Arm.KeyGen.sepAll_append h₁.pk0 h₂.pk0, VG.Proof.MlDsa.Arm.KeyGen.sepAll_append h₁.sk0 h₂.sk0, VG.Proof.MlDsa.Arm.KeyGen.sepAll_append h₁.sk1 h₂.sk1,
    fun r hr => VG.Proof.MlDsa.Arm.KeyGen.sepAll_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨VG.Proof.MlDsa.Arm.KeyGen.sepAll_append (h₁.rows i hi).1 (h₂.rows i hi).1, VG.Proof.MlDsa.Arm.KeyGen.sepAll_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! The checks of a write to one region, proved once for any region (`krchk` on a
literal list of writes costs seconds). -/

/-- The stack below the function's frame. -/
theorem KRChk.stk {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr [(1, 0, STK)] := by
  krchk hF

/-- A write to `scratch` outside the saved registers and the polynomials. -/
theorem KRChk.c0 {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k)
    {o n : Nat} (h1 : o + n ≤ 840 ∨ 876 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o)
    (h3 : o + n ≤ VG.Proof.MlDsa.Arm.KeyGen.scrLen p) : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr [(0, o, n)] := by
  simp only [oP] at h2
  krchk hF

/-- A write to `pk` after the rows so far. -/
theorem KRChk.c3 {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k)
    {o n : Nat} (h1 : 32 + 320 * nr ≤ o) (h2 : o + n ≤ p.pkLen) : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr [(3, o, n)] := by
  rw [hF.pk] at h2
  krchk hF

/-- A write to `sk` after `ρ` and `K`, outside the entries packed and the rows so far. -/
theorem KRChk.c4 {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k)
    {o n : Nat} (h0 : 64 ≤ o) (hp : o + n ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + n ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + n ≤ p.skLen) : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr [(4, o, n)] := by
  rw [hF.sk] at h2
  simp only [oT0] at hr h2
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> rw [hlen] at hp hr h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
  lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk, hF.pk, hF.sk, hlen]

theorem KR.keep {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nj nr : Nat} {s s' : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np nj nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK np nj nr W) : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np nj nr s' := by
  have hL := h.kc.site.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have kb : ∀ {i o l : Nat}, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (i, o, l) W = true → i ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb →
      l ≤ 2 ^ 64 → bytesAt s'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A i o) l = bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A i o) l :=
    fun hs hi hl => VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL hk.frame hs hi hl
  exact ⟨h.kc.keep hk hc.kc, (hk.cs .r11 (by decide) (by decide)).trans h.r11, h.good, h.small,
    fun e he => VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL hk.frame (hc.aS e he) (by decide) rfl (h.aS e he),
    fun i hi => VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL hk.frame (hc.s2 i hi) (by decide) rfl (h.s2 i hi),
    fun j hj => VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL hk.frame (hc.s1 j hj) (by decide) rfl (h.s1 j hj),
    by rw [kb hc.pk0 (by decide) (by decide)]; exact h.pk0,
    by rw [kb hc.sk0 (by decide) (by decide)]; exact h.sk0,
    by rw [kb hc.sk1 (by decide) (by decide)]; exact h.sk1,
    fun r hr => by
      rw [kb (hc.packs r hr) (by decide) hle]
      exact h.packs r hr,
    fun i hi => ⟨by rw [kb (hc.rows i hi).1 (by decide) (by decide)]; exact (h.rows i hi).1,
      by rw [kb (hc.rows i hi).2 (by decide) (by decide)]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (STK : Nat) (σ s : State) : Prop := ∃ A S R, VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R 0 0 0 s

theorem copies_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa copies s (VG.Proof.MlDsa.Arm.KeyGen.KR0 p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold copies
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS hs (sb := .r7) (so := oHX) (db := .r5) (dO := 0) (len := 32) ⟨rfl, by lsep hF⟩
    ⟨rfl, by lsep hF [hF.pk]⟩ (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r5 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by lsep hF [hF.pk])) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h.keep k₁ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk, hF.pk]) (fun e' he' => by lsep hF [hF.pk])
    (fun r' hr' => by lsep hF [hF.pk]) (k₁.cs .r11 (by decide) (by decide))
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS h₁.k1.kc.site (sb := .r7) (so := oHX) (db := .r6) (dO := 0) (len := 32)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF [hF.sk]⟩ (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r6 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by lsep hF [hF.sk])) fun s₂ ⟨k₂, b₂⟩ => ?_)
  have h₂ := h₁.keep k₂ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk]) (k₂.cs .r11 (by decide) (by decide))
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.copyS h₂.k1.kc.site (sb := .r7) (so := oHX + 96) (db := .r6) (dO := 32) (len := 32)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF [hF.sk]⟩ (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r6 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by lsep hF [hF.sk])) fun s₃ ⟨k₃, b₃⟩ => ?_
  have h₃ := h₂.keep k₃ (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.k1Chk, VG.Proof.MlDsa.Arm.KeyGen.kcChk, hF.sk]) (fun e' he' => by lsep hF [hF.sk])
    (fun r' hr' => by lsep hF [hF.sk]) (k₃.cs .r11 (by decide) (by decide))
  have hL := hs.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h₃.ex
  have e1 : ∀ {m : Mem}, bytesAt m ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oHX) 128 = VG.Proof.MlDsa.Arm.KeyGen.hxOf p σ →
      bytesAt m ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 oHX) 32 = VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ := fun hx => by
    rw [VG.Proof.MlDsa.Arm.KeyGen.rho_eq, ← hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  refine ⟨A, S, s₃.gpr .r11, ⟨h₃.k1.kc, rfl, hG, fun r hr => (hS r hr).2, hA,
    fun i hi => (hS (p.ℓ + i) (by omega)).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact (hS j (by omega)).1, ?_, ?_, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₃.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide),
      VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₂.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk, hF.sk]) (by decide) (by decide)]
    exact b₁.trans (e1 h.k1.hx)
  · rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k₃.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
    exact b₂.trans (e1 h₁.k1.hx)
  · show bytesAt s₃.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (.r6, 32)) 32 = _
    rw [b₃, VG.Proof.MlDsa.Arm.KeyGen.kOf_eq, ← h₂.k1.hx, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), add_ofNat_add]
    rfl

/-- Two runs in every layout of key generation, from the taint analysis of
the pointers of the layout. -/
theorem ktaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.KTwo p STK) c fun _ _ => True :=
  VG.Proof.MlDsa.Arm.KeyGen.ktwo fun _ => VG.Proof.MlDsa.Arm.KeyGen.taint4 (fun _ _ h => h) h

theorem copies_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (VG.Proof.MlDsa.Arm.KeyGen.KR0 p STK) copies :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.KeyGen.copies_ok hF h,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (VG.Proof.MlDsa.Arm.KeyGen.ktaint4 (by taint_decide)) fun _ _ _ _ _ _ pub h₁ h₂ => VG.Proof.MlDsa.Arm.KeyGen.kc_two pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestPack`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack modPm q n)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : VG.Spec.MlDsa.Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem small_coeff {m : Mem} {a : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m a (toRq x))
    (hs : Small η x) : ∀ i < n, -(η : Int) ≤ modPm (coeffAt m a i).toNat VG.Spec.MlDsa.q ∧ modPm (coeffAt m a i).toNat VG.Spec.MlDsa.q ≤ η :=
  fun i hi => by
    have hx := VG.Proof.MlDsa.Arm.KeyGen.small_mem hs hi
    rw [VG.Proof.MlDsa.Arm.KeyGen.coeff_val h hi]
    simp only [toRq, Vector.getElem_map]
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem eta_params {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) : (p.η, p.η) ∈ Spec.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nr : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

/-- The states after the copies, and the first `np` entries packed, `nj` in
the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (STK : Nat) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np nj nr s

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-! ## `BitPack` of `s₁ ‖ s₂` -/

omit hP hS in
theorem packS_m {σ : State} {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.BpOk (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb (sP p r) p.η p.η (.r6, 128 + lenS p * r) (lenS p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.sk, hlen]⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r6 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
    by lsep hF [hF.sk, hlen], VG.Proof.MlDsa.Arm.KeyGen.eta_params hF, VG.Proof.MlDsa.Arm.KeyGen.lenS_eq p⟩

theorem packS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R r 0 0 s) : WP isa (packS P p r) s (VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (r + 1) 0 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSp := h.sPoly hr
  unfold packS bitPackAt
  refine VG.Proof.MlDsa.Arm.KeyGen.bp_ok hP.bitPack hs (by omega) (VG.Proof.MlDsa.Arm.KeyGen.packS_m hF hr) hSp.1 (VG.Proof.MlDsa.Arm.KeyGen.small_coeff (VG.Proof.MlDsa.Arm.KeyGen.eta_le hF) hSp (h.small r hr))
    fun s' k' hb => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF k' ((KRChk.c4 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr) (Nat.zero_le _)
    (by omega) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega)).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_of_lt hr) (Nat.zero_le _)))
  refine ⟨hk'.kc, hk'.r11, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · show bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (.r6, 128 + lenS p * r')) (lenS p) = _
    rw [hb]
    show VG.Spec.MlDsa.bitPack ((polyAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r')))).map _) _ _ = _
    rw [hSp.2, Proof.MlDsa.KeyGen.modPm_toRq (VG.Proof.MlDsa.Arm.KeyGen.small_big (VG.Proof.MlDsa.Arm.KeyGen.eta_le hF) (h.small r' hr))]

theorem packS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      PolyIs x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (polyAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) ∧
      PolyIs y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (polyAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) ∧
      (∃ x' : IPoly, PolyIs x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq x') ∧ Small p.η x') ∧
      (∃ y' : IPoly, PolyIs y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq y') ∧ Small p.η y'))
      (packS P p r) fun _ _ => True := by
  unfold packS bitPackAt
  exact VG.Proof.MlDsa.Arm.KeyGen.bp_tr hP.bitPack (by omega) (VG.Proof.MlDsa.Arm.KeyGen.packS_m hF hr) fun x y ⟨T, rx, ry, ⟨x', hx, sx⟩, ⟨y', hy, sy⟩⟩ =>
    ⟨T.1, T.2.1, T.2.2, rx.1, ry.1, VG.Proof.MlDsa.Arm.KeyGen.small_coeff (VG.Proof.MlDsa.Arm.KeyGen.eta_le hF) hx sx, VG.Proof.MlDsa.Arm.KeyGen.small_coeff (VG.Proof.MlDsa.Arm.KeyGen.eta_le hF) hy sy⟩

theorem packS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK r 0 0) (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.packS_ok hP hF hS hr h) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.packS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, rfl⟩, by rw [VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub]; exact ⟨(h₂.sPoly hr).1, rfl⟩,
        ⟨_, h₁.sPoly hr, h₁.small r hr⟩, by rw [VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub]; exact ⟨_, h₂.sPoly hr, h₂.small r hr⟩⟩⟩

/-! ## `NTT` of `s₁` -/

omit hP hS in
theorem nttS_m {σ : State} {j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.Arm.KeyGen.PtrIn (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (sP p j) 1024 ∧ VG.Proof.MlDsa.Arm.KeyGen.PtrIn (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (sc oSS) 1024 ∧
    sepB (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).sizes (VG.Proof.MlDsa.Arm.KeyGen.tri (sP p j) 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, by lsep hF⟩

theorem nttS_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) j 0 s) :
    WP isa (nttS P p j) s (VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSj := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hSj
  obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.KeyGen.nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  refine VG.Proof.MlDsa.Arm.KeyGen.ip_ok (t := VG.Spec.MlDsa.ntt) hP.ntt hs (by omega) m1 m2 (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide)
    (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) m3 hSj.1 fun s' k' hb => ?_
  have hL := hs.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hpk : ∀ r < p.ℓ + p.k, sepAll [VG.Proof.MlDsa.Arm.KeyGen.scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p)
      [VG.Proof.MlDsa.Arm.KeyGen.tri (sP p j) 1024, VG.Proof.MlDsa.Arm.KeyGen.tri (sc oSS) 1024, (1, 0, STK)] = true := fun r hr => by
    rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.sk, hlen]
  refine ⟨h.kc.keep k' (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.kcChk]), (k'.cs .r11 (by decide) (by decide)).trans h.r11, h.good, h.small,
    fun e he => VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.aS e he),
    fun i hi => VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.s2 i hi), fun j' hj' => ?_,
    by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k'.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk]) (by decide) (by decide)]
       exact h.pk0,
    by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k'.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
       exact h.sk0,
    by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k'.frame (i := 4) (o := 32) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
       exact h.sk1,
    fun r hr => by rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW hL k'.frame (hpk r hr) (by decide) hle]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  by_cases e : j' = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (sP p j')) _
    rw [← hSj.2]; exact hb
  · have := VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.s1 j' hj')
    by_cases hlt : j' < j
    · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S' j'))) (toRq (S' j'))] at this
    · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S' j'))) (toRq (S' j'))] at this

theorem nttS_two {j : Nat} (hj : j < p.ℓ) (σ : State) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧ Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) ∧
      Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))) (nttS P p j) fun _ _ => True := by
  obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.KeyGen.nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  exact VG.Proof.MlDsa.Arm.KeyGen.ip_tr (t := VG.Spec.MlDsa.ntt) hP.ntt (by omega) m1 m2 (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide)
    m3 fun x y ⟨T, rx, ry⟩ => ⟨T.1, T.2.1, T.2.2, rx, ry⟩

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) j 0) (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.nttS_ok hP hF hS hj h) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.nttS_two hP hF hS hj σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, (h₁.s1 j hj).1, by rw [VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub]; exact (h₂.s1 j hj).1⟩⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestRow`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: the rows of `t`

Row `i` of `t`: the sum of the products `Â[i, j] ŝ₁[j]` in `t` (`rowMul_ok`,
`rowMulAdd_ok`), `NTT⁻¹` of it plus `s₂[i]` (`rowInv_ok`, `rowAdd_ok`), then
`Power2Round` (`rowP2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`rowSbp_ok`, `rowBp_ok`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs
  NatPolyIs bitPack simpleBitPack power2Round ofInt modPm q n)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K ifp ifn idx_lt)
open VG.Spec.Sha3 (bytesAt)

/-- The polynomial `t`, `t₁` and `t₀` of the layout. -/
abbrev oT (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k)
abbrev oT1 (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 1)
abbrev oT0' (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 2)

/-- The `t` so far. -/
abbrev tIs (p : Params) (STK : Nat) (g : (Nat → VG.Spec.MlDsa.Poly) → (Nat → IPoly) → VG.Spec.MlDsa.Poly) (σ : State) (A : Nat → VG.Spec.MlDsa.Poly)
    (S : Nat → IPoly) (s : State) : Prop := PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) (g A S)

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (STK : Nat) (i : Nat)
    (f : State → (Nat → VG.Spec.MlDsa.Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f σ A S s

theorem KR.polyA {p : Params} {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nj nr : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nr : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) (VG.Spec.MlDsa.ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem modPm_t0 (t : VG.Spec.MlDsa.Poly) :
    ((t.map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2).map fun c => modPm c.val VG.Spec.MlDsa.q) = t.map fun c => (VG.Spec.MlDsa.power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem t0_coeff {m : Mem} {a : Addr} {t : VG.Spec.MlDsa.Poly} (h : PolyIs m a (t.map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)) :
    ∀ i < n, -((4095 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat VG.Spec.MlDsa.q ∧ modPm (coeffAt m a i).toNat VG.Spec.MlDsa.q ≤ ((4096 : Nat) : Int) :=
  fun j hj => by
    rw [VG.Proof.MlDsa.Arm.KeyGen.coeff_val h hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    omega

theorem t1_bound {m : Mem} {a : Addr} {p : Params} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m a (t1K p A S i)) : ∀ j < n, (coeffAt m a j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m a j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((VG.Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega

/-! ## The checks of the writes of a row, once each -/

theorem chk_poly {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k + j), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  exact KRChk.c0 hF (by omega) (by omega) (.inr (by simp only [oP]; omega))
    (.inr (by simp only [oP]; omega)) (by simp only [oP]; omega)

theorem chk_t {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k), 1024), (1, 0, STK)] := by
  have := (VG.Proof.MlDsa.Arm.KeyGen.chk_poly hF (STK := STK) hi (j := 0) (by decide)).append (W₂ := [_]) (KRChk.stk hF (by omega) (by omega))
  rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k), 1024), (0, oSS, 1024), (1, 0, STK)] := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  have := (VG.Proof.MlDsa.Arm.KeyGen.chk_poly hF (STK := STK) hi (j := 0) (by decide)).append (W₁ := [_])
    ((KRChk.c0 (o := oSS) (n := 1024) hF (by omega) (by omega) (.inr (by decide)) (.inl (by decide))
      (by simp only [oSS]; omega)).append (W₁ := [_]) (KRChk.stk hF (by omega) (by omega)))
  rwa [Nat.add_zero] at this

theorem chk_p2r {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK (p.ℓ + p.k) p.ℓ i [(0, oP (p.k * p.ℓ + p.ℓ + p.k + 1), 1024),
      (0, oP (p.k * p.ℓ + p.ℓ + p.k + 2), 1024), (1, 0, STK)] :=
  (VG.Proof.MlDsa.Arm.KeyGen.chk_poly hF hi (j := 1) (by decide)).append (W₁ := [_])
    ((VG.Proof.MlDsa.Arm.KeyGen.chk_poly hF hi (j := 2) (by decide)).append (W₁ := [_]) (KRChk.stk hF (by omega) (by omega)))

theorem chk_sbp {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK (p.ℓ + p.k) p.ℓ i [(3, 32 + 320 * i, 320), (1, 0, STK)] :=
  (KRChk.c3 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega)).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_refl _) (Nat.le_of_lt hi))

theorem chk_bp {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KRChk p STK (p.ℓ + p.k) p.ℓ i [(4, oT0 p + 416 * i, 416), (1, 0, STK)] := by
  have := hF.k; have := hF.l
  exact (KRChk.c4 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega) (.inr (by simp only [oT0]; omega))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega)).append (W₁ := [_]) (KRChk.stk hF (Nat.le_refl _) (Nat.le_of_lt hi))

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
  {i : Nat} (hi : i < p.k)
include hP hF hS hi

/-! ## The calls, one by one -/

/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem rowMul_ok {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => dotK p A S i 1) σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega)
  have hA := h.polyA hi (j := 0) (by omega)
  rw [Nat.add_zero] at hx0 hA
  have hS0 := h.polyS (j := 0) (by omega)
  rw [Nat.add_zero] at hS0
  refine VG.Proof.MlDsa.Arm.KeyGen.mul_ok hP.mul h.kc.site (by omega) (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
    ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
      by lsep hF, by lsep hF⟩ hA.1 hS0.1 fun s' k' hb => ⟨h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_t hF hi), ?_⟩
  show PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS0.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem rowMulAdd_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => dotK p A S i j) σ A S' s) :
    WP isa (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => dotK p A S i (j + 1)) σ A S' s' := by
  dsimp only [VG.Proof.MlDsa.Arm.KeyGen.tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  have hA := h.polyA hi hj
  have hSj := h.polyS hj
  refine VG.Proof.MlDsa.Arm.KeyGen.mulAdd_ok hP.mulAdd h.kc.site (by omega) (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
    ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
      by lsep hF, by lsep hF⟩ ht.1 hA.1 hSj.1 fun s' k' hb => ⟨h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_t hF hi), ?_⟩
  show PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hSj.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem tP_m {σ : State} : VG.Proof.MlDsa.Arm.KeyGen.PtrIn (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (tP p) 1024 ∧ VG.Proof.MlDsa.Arm.KeyGen.PtrIn (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (sc oSS) 1024 ∧
    sepB (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).sizes (VG.Proof.MlDsa.Arm.KeyGen.tri (tP p) 1024) (VG.Proof.MlDsa.Arm.KeyGen.tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, by lsep hF⟩

/-- `t = NTT⁻¹(t)`. -/
theorem rowInv_ok {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => dotK p A S i p.ℓ) σ A S' s) :
    WP isa (invNttAt P (tP p)) s fun s' =>
      VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) σ A S' s' := by
  dsimp only [VG.Proof.MlDsa.Arm.KeyGen.tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.KeyGen.tP_m hF (σ := σ)
  unfold invNttAt
  refine VG.Proof.MlDsa.Arm.KeyGen.ip_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt h.kc.site (by omega) m1 m2 (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide)
    (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) m3 ht.1 fun s' k' hb => ⟨h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_inv hF hi), ?_⟩
  show PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (tP p)) _
  dsimp only
  rw [← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem rowAdd_ok {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s)
    (ht : VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) σ A S' s) :
    WP isa (addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => VG.Proof.MlDsa.KeyGen.tK p A S i) σ A S' s' := by
  dsimp only [VG.Proof.MlDsa.Arm.KeyGen.tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hS2 := h.s2 i hi
  refine VG.Proof.MlDsa.Arm.KeyGen.add_ok hP.add h.kc.site (by omega) (f := tP p) (g := sP p (p.ℓ + i))
    ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF⟩ ht.1 hS2.1
    fun s' k' hb => ⟨h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_t hF hi), ?_⟩
  show PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.tK, ← hS2.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem p2r_m {σ : State} : VG.Proof.MlDsa.Arm.KeyGen.P2rOk (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb (tP p) (t1P p) (t0P p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
    show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT1 p)) (t1K p A S i) ∧
    PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) ((VG.Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)

/-- `Power2Round` of `t`. -/
theorem rowP2r_ok {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.Arm.KeyGen.tIs p STK (fun A S => VG.Proof.MlDsa.KeyGen.tK p A S i) σ A S' s) :
    WP isa (power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.Arm.KeyGen.p2rIs p STK i σ A S' s' := by
  dsimp only [VG.Proof.MlDsa.Arm.KeyGen.tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine VG.Proof.MlDsa.Arm.KeyGen.p2r_ok hP.power2Round h.kc.site (by omega) (VG.Proof.MlDsa.Arm.KeyGen.p2r_m hF) ht.1 fun s' k' h1 h0 =>
    ⟨h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_p2r hF hi), ?_, ?_⟩
  · show NatPolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (t1P p)) _
    rw [t1K, ← ht.2]; exact h1
  · show PolyIs s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (t0P p)) _
    rw [← ht.2]; exact h0

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) ((VG.Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) ∧
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 3 (32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023

omit hP hS in
theorem sbp_m {σ : State} : VG.Proof.MlDsa.Arm.KeyGen.SbpOk (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb (t1P p) 1023 (.r5, 32 + 320 * i) 320 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.pk]⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r5 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF [hF.pk],
    by decide, by decide⟩

/-- `t₁[i]` to `pk`. -/
theorem rowSbp_ok {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h1 : VG.Proof.MlDsa.Arm.KeyGen.p2rIs p STK i σ A S' s) :
    WP isa (simpleBitPackAt P (t1P p) 1023 (.r5, 32 + 320 * i) 320) s fun s' =>
      VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.Arm.KeyGen.sbpIs p STK i σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine VG.Proof.MlDsa.Arm.KeyGen.sbp_ok hP.simpleBitPack h.kc.site (by omega) (VG.Proof.MlDsa.Arm.KeyGen.sbp_m hF hi) (VG.Proof.MlDsa.Arm.KeyGen.t1_bound h1.1) fun s' k' hb =>
    ⟨h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_sbp hF hi), VG.Proof.MlDsa.Arm.KeyGen.polyIs_keepW h.kc.site.ok k'.frame (by lsep hF [hF.pk]) (by decide) rfl h1.2, ?_⟩
  show bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (.r5, 32 + 320 * i)) 320 = _
  rw [hb]
  exact congrArg (VG.Spec.MlDsa.simpleBitPack · 1023) h1.1

omit hP hS in
theorem bp_m {σ : State} : VG.Proof.MlDsa.Arm.KeyGen.BpOk (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.sk, hlen]⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r6 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
    by lsep hF [hF.sk, hlen], by decide, by decide⟩

/-- `t₀[i]` to `sk`. -/
theorem rowBp_ok {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h0 : VG.Proof.MlDsa.Arm.KeyGen.sbpIs p STK i σ A S' s) :
    WP isa (bitPackAt P (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416) s
      (VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S' R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold bitPackAt
  refine VG.Proof.MlDsa.Arm.KeyGen.bp_ok hP.bitPack h.kc.site (by omega) (VG.Proof.MlDsa.Arm.KeyGen.bp_m hF hi) h0.1.1 (VG.Proof.MlDsa.Arm.KeyGen.t0_coeff h0.1) fun s' k' hb => ?_
  have hk' := h.keep hF k' (VG.Proof.MlDsa.Arm.KeyGen.chk_bp hF hi)
  refine ⟨hk'.kc, hk'.r11, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨?_, ?_⟩
    · rw [VG.Proof.MlDsa.Arm.KeyGen.bytes_keepW h.kc.site.ok k'.frame (i := 3) (o := 32 + 320 * i') (l := 320)
        (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.pk, hF.sk, hlen]) (by decide) (by decide)]
      exact h0.2
    · show bytesAt s'.mem (VG.Proof.MlDsa.Arm.KeyGen.lpa (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) (.r6, oT0 p + 416 * i')) 416 = _
      rw [hb]
      show VG.Spec.MlDsa.bitPack ((polyAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p))).map _) _ _ = _
      rw [h0.1.2, VG.Proof.MlDsa.Arm.KeyGen.modPm_t0]
      rfl

/-! ## The pieces of a row -/

theorem rowMul_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => dotK p A S i 1))
      (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowMul_ok hP hF hS hi h) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      (Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ)))) ∧
      (Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ)))))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.mul_tr hP.mul (by omega) (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
        ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
          by lsep hF, by lsep hF⟩ fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩
  have a₁ := h₁.polyA hi (j := 0) (by omega); have a₂ := h₂.polyA hi (j := 0) (by omega)
  have s₁ := h₁.polyS (j := 0) (by omega); have s₂ := h₂.polyS (j := 0) (by omega)
  rw [Nat.add_zero] at a₁ a₂ s₁ s₂
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at a₂ s₂
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, ⟨a₁.1, s₁.1⟩, ⟨a₂.1, s₂.1⟩⟩

theorem rowMulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => dotK p A S i j))
      (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => dotK p A S i (j + 1))) (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowMulAdd_ok hP hF hS hi hj h ht) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      (Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) ∧ Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.ℓ * i + j))) ∧
        Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))) ∧
      (Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) ∧ Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.ℓ * i + j))) ∧
        Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.mulAdd_tr hP.mulAdd (by omega) (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
        ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide,
          by lsep hF, by lsep hF⟩ fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have a₂ := (h₂.polyA hi hj).1; have s₂ := (h₂.polyS hj).1; have t₂' := t₂.1
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at a₂ s₂ t₂'
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩, ⟨t₂', a₂, s₂⟩⟩

theorem rowInv_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => dotK p A S i p.ℓ))
      (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ))) (invNttAt P (tP p)) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowInv_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧ Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) ∧
      Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.KeyGen.tP_m hF (σ := σ)
        unfold invNttAt
        exact VG.Proof.MlDsa.Arm.KeyGen.ip_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt (by omega) m1 m2 (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide)
          (show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at t₂'
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowAdd_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)))
      (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => VG.Proof.MlDsa.KeyGen.tK p A S i)) (addAt P (tP p) (sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowAdd_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      (Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) ∧ Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i))))) ∧
      (Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) ∧ Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i))))))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.add_tr hP.add (by omega) (f := tP p) (g := sP p (p.ℓ + i))
        ⟨⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, ⟨VG.Proof.MlDsa.Arm.KeyGen.sc_ok _, by lsep hF⟩, show VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.KeyGen.kWb by decide, by lsep hF⟩
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1; have s₂ := (h₂.s2 i hi).1
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at t₂' s₂
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂', s₂⟩⟩

theorem rowP2r_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => VG.Proof.MlDsa.KeyGen.tK p A S i)) (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.p2rIs p STK i))
      (power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowP2r_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧ Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)) ∧
      Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT p)))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.p2r_tr hP.power2Round (by omega) (VG.Proof.MlDsa.Arm.KeyGen.p2r_m hF)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at t₂'
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowSbp_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.p2rIs p STK i)) (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.sbpIs p STK i))
      (simpleBitPackAt P (t1P p) 1023 (.r5, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h1⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowSbp_ok hP hF hS hi h h1) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      (∀ j < n, (coeffAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT1 p)) j).toNat ≤ 1023) ∧
      (∀ j < n, (coeffAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT1 p)) j).toNat ≤ 1023))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.sbp_tr hP.simpleBitPack (by omega) (VG.Proof.MlDsa.Arm.KeyGen.sbp_m hF hi)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := VG.Proof.MlDsa.Arm.KeyGen.t1_bound t₂.1
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at t₂'
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, VG.Proof.MlDsa.Arm.KeyGen.t1_bound t₁.1, t₂'⟩

theorem rowBp_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.sbpIs p STK i)) (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ (i + 1))
      (bitPackAt P (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h0⟩ => WP.mono (VG.Proof.MlDsa.Arm.KeyGen.rowBp_ok hP hF hS hi h h0) fun _ h => ⟨A, S', R, h⟩,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK x y ∧
      (Reduced x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) ∧ ∀ j < n, -((4095 : Nat) : Int) ≤
        modPm (coeffAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) j).toNat VG.Spec.MlDsa.q ∧
        modPm (coeffAt x.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) j).toNat VG.Spec.MlDsa.q ≤ ((4096 : Nat) : Int)) ∧
      (Reduced y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) ∧ ∀ j < n, -((4095 : Nat) : Int) ≤
        modPm (coeffAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) j).toNat VG.Spec.MlDsa.q ∧
        modPm (coeffAt y.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 (VG.Proof.MlDsa.Arm.KeyGen.oT0' p)) j).toNat VG.Spec.MlDsa.q ≤ ((4096 : Nat) : Int)))
      (RelCT.exists_ fun σ => by
        unfold bitPackAt
        exact VG.Proof.MlDsa.Arm.KeyGen.bp_tr hP.bitPack (by omega) (VG.Proof.MlDsa.Arm.KeyGen.bp_m hF hi)
          fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, c, b, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have r₂ := t₂.1.1; have c₂ := VG.Proof.MlDsa.Arm.KeyGen.t0_coeff t₂.1
  rw [← VG.Proof.MlDsa.Arm.KeyGen.lay_pub pub] at r₂ c₂
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.KeyGen.kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1.1, VG.Proof.MlDsa.Arm.KeyGen.t0_coeff t₁.1⟩, ⟨r₂, c₂⟩⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Top`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The rows (`row_piece`), the keys in memory (`pk_bytes`, `sk_bytes`), `tr =
H(pk, 64)` (`trHash_piece`), and the whole function, piece by piece, for any
parameter set of Table 1 and any verified implementations of the primitives
(`keyGen_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (topEnd)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK Good)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (VG.Proof.MlDsa.Arm.KeyGen.rowMul_piece hP hF hS hi).seq (Piece.seq ?_ ((VG.Proof.MlDsa.Arm.KeyGen.rowInv_piece hP hF hS hi).seq ((VG.Proof.MlDsa.Arm.KeyGen.rowAdd_piece hP hF hS hi).seq
    ((VG.Proof.MlDsa.Arm.KeyGen.rowP2r_piece hP hF hS hi).seq ((VG.Proof.MlDsa.Arm.KeyGen.rowSbp_piece hP hF hS hi).seq (VG.Proof.MlDsa.Arm.KeyGen.rowBp_piece hP hF hS hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.Arm.KeyGen.RowI p STK i (VG.Proof.MlDsa.Arm.KeyGen.tIs p STK fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => VG.Proof.MlDsa.Arm.KeyGen.rowMulAdd_piece hP hF hS hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.Arm.KeyGen.flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pk_bytes {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly}
    {R : BitVec 32} {np nj : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R np nj p.k s) :
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 3 0) p.pkLen = pkK p A S (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ) := by
  rw [hF.pk, Proof.MlKem.bytesAt_add, h.pk0, Lay.A, add_ofNat_add, Nat.zero_add,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK, VG.Proof.MlDsa.Arm.KeyGen.t1Max_eq]
  exact congrArg _ (VG.Proof.MlDsa.Arm.KeyGen.flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly}
    {R : BitVec 32} {nj : Nat} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ)) 64) :
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 0) p.skLen = skK p A S (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ) (VG.Proof.MlDsa.Arm.KeyGen.kOf p σ) := by
  have h0 := h.sk0
  have h1 := h.sk1
  simp only [Lay.A, add_ofNat_zero] at h0 h1 htr ⊢
  have h2 : bytesAt s.mem (State.addr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).ptr 4) + BitVec.ofNat 64 (32 + 32)) 64 =
    Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ)) 64 := htr
  have hp : ∀ r ∈ List.range (p.ℓ + p.k), bytesAt s.mem (State.addr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).ptr 4) +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * r)) (lenS p) = VG.Spec.MlDsa.bitPack (S r) p.η p.η := fun r hr =>
    h.packs r (List.mem_range.mp hr)
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem (State.addr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).ptr 4) +
      BitVec.ofNat 64 (oT0 p + 416 * i)) 416 = VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096 := fun i hi =>
    (h.rows i (List.mem_range.mp hi)).2
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (oT0 p) 416 p.k, skK, VG.Proof.MlDsa.Arm.KeyGen.flatMap_congr_mem hp,
    VG.Proof.MlDsa.Arm.KeyGen.flatMap_congr_mem hr]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ)) 64

theorem trPieces {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ s : State} (hs : VG.Proof.MlDsa.Arm.KeyGen.Site (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) VG.Proof.MlDsa.Arm.KeyGen.kWb STK s) :
    (∀ pc ∈ ([⟨.r5, 0, p.pkLen⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) s fun _ => true) VG.Proof.MlDsa.Arm.KeyGen.ix s false pc) ∧
    PieceOk (VG.Proof.MlDsa.Arm.KeyGen.hashLay (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) s fun _ => true) VG.Proof.MlDsa.Arm.KeyGen.ix s true (⟨.r6, 64, 64⟩ : Impl.MlKem.Arm.Piece) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hpk := hF.lens
  refine ⟨fun pc hpc => ?_, VG.Proof.MlDsa.Arm.KeyGen.pieceS hs rfl (by decide) (by decide) (by decide) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size, hF.sk, hlen, ite_true]) (.inr rfl)
    fun _ => by decide⟩
  rw [List.mem_singleton] at hpc; subst hpc
  exact VG.Proof.MlDsa.Arm.KeyGen.pieceS hs rfl (show encodable (BitVec.ofNat 32 0) = true by decide) hF.encPk
    (show 0 < p.pkLen by rw [hF.pk]; omega) (show 0 + p.pkLen < 2 ^ 32 by omega)
    (by lsep hF [VG.Proof.MlDsa.Arm.KeyGen.hashLay, Lay.size, hF.pk, ite_true]) (.inr rfl) fun h => absurd h (by decide)

theorem trHash_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly}
    {R : BitVec 32} {s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s) :
    WP isa (trHash p) s (VG.Proof.MlDsa.Arm.KeyGen.KFin p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  obtain ⟨hin, hq⟩ := VG.Proof.MlDsa.Arm.KeyGen.trPieces hF hs
  unfold trHash
  refine WP.mono (VG.Proof.MlDsa.Arm.KeyGen.hashS hs VG.Proof.MlDsa.Arm.KeyGen.ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
    (by simp) hin hq) fun s' ⟨k', o'⟩ => ⟨A, S, R, h.keep hF k' ?_, ?_⟩
  · have := hF.scr
    exact (KRChk.c0 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide)) (by omega)).append
      (W₁ := [_]) ((KRChk.c0 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
      (by omega)).append (W₁ := [_]) ((KRChk.stk hF (Nat.le_refl _) (Nat.le_refl _)).append (W₁ := [_])
      (KRChk.c4 (o := 64) (n := 64) hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega)) (by rw [hF.sk, oT0]; omega))))
  have o₃ : bytesAt s'.mem ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 64) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr _ _ _ (VG.Proof.MlDsa.Arm.KeyGen.ix_ne1 _)]
  have e : bytesAt s.mem (State.addr ((VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).ptr (VG.Proof.MlDsa.Arm.KeyGen.ix Reg.r5)) + 0#64) p.pkLen = pkK p A S (VG.Proof.MlDsa.Arm.KeyGen.rhoOf p σ) :=
    VG.Proof.MlDsa.Arm.KeyGen.pk_bytes hF h
  rw [e, VG.Proof.MlDsa.Arm.KeyGen.shake31]
  exact (Proof.MlKem.shake256_eq _ _).symm

theorem trHash_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ p.k) (VG.Proof.MlDsa.Arm.KeyGen.KFin p STK) (trHash p) :=
  ⟨fun _ _ _ ⟨_, _, _, h⟩ => VG.Proof.MlDsa.Arm.KeyGen.trHash_ok hF h,
    VG.Proof.MlDsa.Arm.KeyGen.rel_of (VG.Proof.MlDsa.Arm.KeyGen.ktwo fun σ => VG.Proof.MlDsa.Arm.KeyGen.hashS_tr VG.Proof.MlDsa.Arm.KeyGen.ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by simp)
      (fun s hs => (VG.Proof.MlDsa.Arm.KeyGen.trPieces hF hs).1) (fun s hs => (VG.Proof.MlDsa.Arm.KeyGen.trPieces hF hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => VG.Proof.MlDsa.Arm.KeyGen.kc_two pub h₁.kc h₂.kc⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.KeyGen.KFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      Arm.target.abiPreserved σ s' ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s' := by
  obtain ⟨A, S, R, h, htr⟩ := h
  have hs := h.kc.site
  have e0 : ∀ o, (VG.Proof.MlDsa.Arm.KeyGen.hashLay (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ) s fun _ => true).A 0 o = (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 0 o := fun o => by
    simp only [Lay.A, VG.Proof.MlDsa.Arm.KeyGen.hashLay_ptr _ _ _ (show (0 : Nat) ≠ 1 by decide)]
  refine WP.mono (topEnd_ok (hs.ctx VG.Proof.MlDsa.Arm.KeyGen.ktrue) (by rw [e0]; exact h.kc.sav) (by rw [e0]; exact h.kc.lr))
    fun s' ⟨pr, r0, m', sp'⟩ => ⟨⟨pr, sp'.trans h.kc.sp⟩, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  have e3 : BitVec.setWidth 64 (σ.gpr .r1) = (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 3 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  have e4 : BitVec.setWidth 64 (σ.gpr .r2) = (VG.Proof.MlDsa.Arm.KeyGen.lay p STK σ).A 4 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  rw [setWidth_append32, r0, h.r11, m', e3, e4, VG.Proof.MlDsa.Arm.KeyGen.pk_bytes hF h, VG.Proof.MlDsa.Arm.KeyGen.sk_bytes hF h htr]
  exact Proof.MlDsa.KeyGen.outcome_keyGen (by have := hF.l; omega) h.good

theorem ktaint7 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) : RelCT isa (VG.Proof.MlDsa.Arm.KeyGen.KTwo p STK) c fun _ _ => True :=
  VG.Proof.MlDsa.Arm.KeyGen.ktwo fun _ => VG.Proof.MlDsa.Arm.KeyGen.taint7 (fun _ _ h => h) h

theorem epi_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (VG.Proof.MlDsa.Arm.KeyGen.KFin p STK)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.KeyGen.epi_ok hF h, VG.Proof.MlDsa.Arm.KeyGen.rel_of (VG.Proof.MlDsa.Arm.KeyGen.ktaint7 (by taint_decide))
    fun _ _ _ _ _ _ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => VG.Proof.MlDsa.Arm.KeyGen.kc_two pub h₁.kc h₂.kc⟩

/-! ## The function -/

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.KeyGen.PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem rest_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.KeyGen.KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (VG.Proof.MlDsa.Arm.KeyGen.KFin p STK) (rest P p) := by
  unfold rest
  refine (VG.Proof.MlDsa.Arm.KeyGen.copies_piece hF).seq (Piece.seq (J := VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ p.k) ?_
      (VG.Proof.MlDsa.Arm.KeyGen.trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => VG.Proof.MlDsa.Arm.KeyGen.KRx p STK r 0 0) (p.ℓ + p.k) 0
      fun r _ hr => VG.Proof.MlDsa.Arm.KeyGen.packS_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => VG.Proof.MlDsa.Arm.KeyGen.nttS_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => VG.Proof.MlDsa.Arm.KeyGen.KRx p STK (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => VG.Proof.MlDsa.Arm.KeyGen.row_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece :
    VG.Proof.MlDsa.Arm.KeyGen.KPiece p STK (fun σ s => s = σ)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s)
      (keyGen P p) :=
  (VG.Proof.MlDsa.Arm.KeyGen.pro_piece hF (by omega)).seq ((VG.Proof.MlDsa.Arm.KeyGen.seeds_piece hF).seq ((VG.Proof.MlDsa.Arm.KeyGen.sampA_piece hP hF hS).seq ((VG.Proof.MlDsa.Arm.KeyGen.sampS_piece hP hF hS).seq
    ((VG.Proof.MlDsa.Arm.KeyGen.rest_piece hP hF hS).seq (VG.Proof.MlDsa.Arm.KeyGen.epi_piece hF)))))

end

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | .r3 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, VG.Proof.MlDsa.Arm.KeyGen.scrLen p⟩]

end VG.Proof.MlDsa.Arm.KeyGen

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen (Prims keyGen)

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract with
36 bytes of stack, for any verified implementations `P` of the primitives
it calls with at most 28 bytes of stack. -/
theorem keyGen_verified {P : Prims} (hP : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk P 28) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified Arm.target (keyGen P p) (Spec.MlDsa.keyGenContract p Arm.abi 36) := by
  have hF := VG.Proof.MlDsa.Arm.KeyGen.pfacts hp
  have hk := VG.Proof.MlDsa.Arm.KeyGen.keyGen_piece hP hF (Nat.le_refl _)
  refine ⟨fun s hs => hk.ok s s (VG.Proof.MlDsa.Arm.KeyGen.pre_of (n := 35) hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    exact VG.Proof.MlDsa.Arm.KeyGen.relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (VG.Proof.MlDsa.Arm.KeyGen.pre_of (n := 35) h₁) (VG.Proof.MlDsa.Arm.KeyGen.pre_of (n := 35) h₂)
      ⟨hsp, h0, h1, h2, h3, hl⟩ e₁ e₂
  · refine ⟨VG.Proof.MlDsa.Arm.KeyGen.keyGenSat p, ?_⟩
    rcases hp with rfl | rfl | rfl <;>
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, VG.Proof.MlDsa.Arm.KeyGen.keyGenSat]

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst`. -/
section

/-!
# ML-DSA key generation on 32-bit ARM, with this library's primitives

The ARM implementations of the primitives (`prims`) are verified with at most
28 bytes of stack, and their frames use no more (`prims_ok`), so key
generation with them is verified with 36 (`keyGen44_verified`, …).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen

theorem prims_ok : VG.Proof.MlDsa.Arm.KeyGen.PrimsOk prims 28 where
  ntt := ⟨⟨28, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨28, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨24, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨24, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨8, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨8, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨4, by decide, Round.P2R.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨4, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

theorem keyGen44_verified :
    Verified Arm.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 Arm.abi 36) :=
  VG.Proof.MlDsa.Arm.KeyGen.keyGen_verified VG.Proof.MlDsa.Arm.KeyGen.prims_ok _ (.inl rfl)

theorem keyGen65_verified :
    Verified Arm.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 Arm.abi 36) :=
  VG.Proof.MlDsa.Arm.KeyGen.keyGen_verified VG.Proof.MlDsa.Arm.KeyGen.prims_ok _ (.inr (.inl rfl))

theorem keyGen87_verified :
    Verified Arm.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 Arm.abi 36) :=
  VG.Proof.MlDsa.Arm.KeyGen.keyGen_verified VG.Proof.MlDsa.Arm.KeyGen.prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.KeyGen

end
