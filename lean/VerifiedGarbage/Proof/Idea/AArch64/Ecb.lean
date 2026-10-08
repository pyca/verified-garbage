import VerifiedGarbage.Proof.Idea.AArch64.Block
import VerifiedGarbage.Proof.Idea.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA ECB on AArch64

`ecb_verified`: `Impl.Idea.AArch64.ecb` meets the shared ECB contract, with
no stack. The blocks are transformed in a loop (`loop_ok`) whose invariant
(`LoopInv`) says how many remain, that the ones before are transformed and
the ones after not yet; each iteration is `cryptBlock_run`.
-/

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-! ## The loop -/

theorem advance_run (s : State) :
    ∃ s', runBlock isa [.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 8 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      Keep [.x1, .x2] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ofNat_one,
    Option.some.injEq, exists_eq_left', true_and]
  keep_tac

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
  .x13, .x14]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `x0`, readable, and `n` blocks at `a`, writable, apart
from it and not wrapping around, and the mask in `x15`. -/
structure LoopCtx (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨o.gpr .x0, 104⟩ ∈ o.rd ++ o.wr
  data : ⟨a, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (o.gpr .x0) = z
  sep : (⟨o.gpr .x0, 104⟩ : Region).Disjoint ⟨a, 8 * n⟩
  bound : 8 * n ≤ 2 ^ 64
  mask : MaskOk o

/-- `r` blocks remain, at `a + 8 (n - r)` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  x1 : t.gpr .x1 = a + BitVec.ofNat 64 (8 * (n - r))
  x2 : t.gpr .x2 = BitVec.ofNat 64 r
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))

/-- After the loop: every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))

theorem step_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (r : Nat) (t : State) (hi : LoopInv z a n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] : List Instr))) t
      (fun t' => (isa.eval (.nonzero .x .x2) t' = some false ∧ LoopPost z a n m₀ o t') ∨
        (isa.eval (.nonzero .x .x2) t' = some true ∧ ∃ r' < r, LoopInv z a n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.rd
  have hwr : t.wr = o.wr := hi.keep.wr
  have hx0 : t.gpr .x0 = o.gpr .x0 := hi.keep.reg .x0 (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega
  -- The block and the schedule.
  have hread : BlockRead t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data,
      block_contains hj (by omega) (by decide) hc.bound⟩
  have hwrite : BlockWrite t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega) (by decide) hc.bound⟩
  have hk : KeyOk z t := by
    refine ⟨by rw [hx0, hrd, hwr]; exact hc.sched, ?_⟩
    rw [hx0, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  have hm : MaskOk t := (hi.keep.reg .x15 (by decide)).trans hc.mask
  obtain ⟨t₁, h₁, b₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := cryptBlock_run z t hi.x1 hread hwrite hk hm
  obtain ⟨t₂, h₂, x1₂, x2₂, e₂⟩ := advance_run t₁
  refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
  -- What holds after the iteration, whether it is the last or not.
  have keep₂ : Keep loopWrites o { t₂ with mem := o.mem } := by
    refine ⟨fun q hq => ?_, rfl, ?_, ?_, ?_⟩
    · show t₂.gpr q = o.gpr q
      have s₁ : ∀ q, q ∈ [Reg.x1, .x2] → q ∈ loopWrites := by decide
      have s₂ : ∀ q, q ∈ roundWrites → q ∈ loopWrites := by decide
      rw [e₂.reg q (fun h => hq (s₁ q h)), g₁ q (fun h => hq (s₂ q h))]
      exact hi.keep.reg q hq
    · show t₂.rd = o.rd; rw [e₂.rd, rd₁, hrd]
    · show t₂.wr = o.wr; rw [e₂.wr, wr₁, hwr]
    · show t₂.sp = o.sp; rw [e₂.sp, sp₁]; exact hi.keep.sp
  have mem₂ : t₂.mem = t₁.mem := e₂.mem
  have frame₂ : Frame [⟨a, 8 * n⟩] o.mem t₂.mem := by
    rw [mem₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base a (by omega)
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) := by
    rw [mem₂]
    exact blockAt_congr (frame_bytes f₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact blocks_disjoint hj hjn (Ne.symm hne) hc.bound) (by decide))
  have done₂ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      rw [mem₂, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega) he]
      exact hi.done j (by have := hi.pos; omega)
  have hx2 : t₂.gpr .x2 = BitVec.ofNat 64 (r - 1) := by
    rw [x2₂, g₁ .x2 (by decide), hi.x2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le; have := hc.bound
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one]
    omega
  have hev : isa.eval (.nonzero .x .x2) t₂ = some (decide (r - 1 ≠ 0)) := by
    have := hi.le; have := hc.bound
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2, bne,
      beq_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r - 1 < 2 ^ 64 by omega), decide_not]
  by_cases hlast : r = 1
  · subst hlast
    left
    exact ⟨hev, keep₂, frame₂, fun j hjn => done₂ j (by omega)⟩
  · right
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega,
      r - 1, by have := hi.pos; omega, ?_⟩
    refine ⟨by have := hi.pos; omega, by have := hi.le; omega, ?_, hx2, keep₂, frame₂, done₂, ?_⟩
    · rw [x1₂, g₁ .x1 (by decide), hi.x1, Offset.add_ofNat_add_ofNat]
      congr 2
      have := hi.pos; have := hi.le
      omega
    · intro j hj₁ hj₂
      have := hi.pos
      have := hi.le
      have hne : j ≠ n - r := by omega
      rw [other j hj₂ hne]
      exact hi.todo j (by omega) hj₂

theorem loop_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (hn : 1 ≤ n) (ho : o.gpr .x1 = a) (hx2 : o.gpr .x2 = BitVec.ofNat 64 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.addImm .x .x1 .x1 8, .subImm .x .x2 .x2 1] : List Instr)))
      (.nonzero .x .x2)) o (LoopPost z a n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z a n m₀ o) (fun r t hi => step_ok hc r t hi) n o
    ⟨hn, Nat.le_refl _, ?_, hx2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, Frame.refl _ _,
      fun j hj => by omega, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, ho]; exact (BitVec.add_zero a).symm

/-! ## The function -/

/-- The ECB contract on AArch64. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 104⟩
    let data : Region := ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧
      (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' := Spec.Idea.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (s.gpr .x0))
      (Spec.Idea.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2]

theorem setMask_run (s : State) :
    ∃ s', runBlock isa [setMask] s = some s' ∧ MaskOk s' ∧ Keep [.x15] s s' := by
  simp only [setMask, runBlock_cons, runStep_some, runBlock_nil, exec, isa, Size.bits,
    Nat.mul_zero, Nat.reduceLT, ↓reduceIte, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, by keep_tac⟩

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => GprAbi s s' ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, dSched, hbound⟩ := hs
  have hz : isa.eval (.zero .x .x2) s = some (decide ((s.gpr .x2).toNat = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, beq_zero]
  apply WP.ite _ hz
  · -- No blocks.
    intro h0
    have hn : (s.gpr .x2).toNat = 0 := by simpa using h0
    refine WP.block_nil ⟨⟨fun r _ => rfl, rfl⟩, ?_⟩
    show Spec.Idea.blocksAt s.mem _ _ = _
    rw [hn]; rfl
  · intro h0
    have hn : (s.gpr .x2).toNat ≠ 0 := by simpa using h0
    apply WP.seq
    apply WP.of_runBlock
    obtain ⟨s₁, h₁, m₁, e₁⟩ := setMask_run s
    refine ⟨s₁, h₁, ?_⟩
    have ctx : LoopCtx (Spec.Idea.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1) (s.gpr .x2).toNat s₁ := by
      refine ⟨?_, ?_, ?_, ?_, by omega, m₁⟩
      · rw [e₁.reg .x0 (by decide), e₁.rd, e₁.wr, hrd]; simp
      · rw [e₁.wr, hwr]; simp
      · rw [e₁.reg .x0 (by decide), e₁.mem]
      · rw [e₁.reg .x0 (by decide)]; exact dSched
    refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero hn) (e₁.reg .x1 (by decide))
      (by rw [e₁.reg .x2 (by decide), ofNat_toNat64]) (m₀ := s.mem)
      (fun j _ => by rw [e₁.mem])) fun t ht => ?_
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have hr' : r ∉ loopWrites := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hr₁ : r ∉ [Reg.x15] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.keep.reg r hr').trans (e₁.reg r hr₁)
    · exact ht.keep.sp.trans e₁.sp
    · show Spec.Idea.blocksAt t.mem (s.gpr .x1) (s.gpr .x2).toNat = _
      exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_wp s hs
  exact ⟨t, s', he, ⟨ha.1, ha.2, Exec.preservedV he (by lit_decide)⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 1 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩]

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [PublicRegs]

theorem ecb_verified : Verified target ecb (Spec.Idea.ecbContract abi 0) := by
  refine Verified.of_correct ecb_correct (ecb_constantTime _) ?_
  sig_implies [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, abi, argRegs, contract,
    publicRegs_three] [satState] using satState

end VG.Proof.Idea.AArch64
