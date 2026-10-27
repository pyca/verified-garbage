module

import VerifiedGarbage.Proof.Idea.RISCV64.Block
import VerifiedGarbage.Proof.Idea.RISCV64.Mul
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Idea.RISCV64.Block
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
public import VerifiedGarbage.Proof.Idea.RISCV64.Round

/-!
# IDEA ECB on RISC-V

`ecb_verified`: `Impl.Idea.RISCV64.ecb` meets the shared ECB contract. The
blocks are transformed in a loop (`loop_ok`) whose invariant (`LoopInv`)
says how many remain, that the ones before are transformed and the ones
after not yet; each iteration is `cryptBlock_ok`.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-- `KeyOk` of the schedule in a readable region at `a0`, with the mask in `t2`. -/
theorem keyOk_of (s : State) (hr : ⟨s.gpr .a0, 104⟩ ∈ s.rd ++ s.wr) (h2 : s.gpr .t2 = 65535) :
    KeyOk (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) s :=
  ⟨fun i hi => ⟨_, hr, Offset.contains_base _ (by omega) (by omega)⟩,
    fun k hk => (scheduleAt_getD _ _ hk).symm, h2⟩

/-! ## The loop -/

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t3]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `r3`, readable, the mask in `r0`, and `n` blocks at `a`,
writable, apart from it and not wrapping around. -/
structure LoopCtx (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨o.gpr .a0, 104⟩ ∈ o.rd ++ o.wr
  data : ⟨a, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (o.gpr .a0) = z
  sep : (⟨o.gpr .a0, 104⟩ : Region).Disjoint ⟨a, 8 * n⟩
  bound : 8 * n ≤ 2 ^ 64
  mask : o.gpr .t2 = 65535

/-- `r` blocks remain, at `a + 8 (n - r)` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  a1 : t.gpr .a1 = a + BitVec.ofNat 64 (8 * (n - r))
  a2 : t.gpr .a2 = BitVec.ofNat 64 r
  keep : Keep loopWrites o t
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))

/-- After the loop: every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  keep : Keep loopWrites o t
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))

theorem tail_ok (s : State) :
    WP isa (.block [.addi .a1 .a1 8, .addi .a2 .a2 (-1)]) s fun t =>
      t.gpr .a1 = s.gpr .a1 + 8#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧ t.mem = s.mem ∧
      Keep [.a1, .a2] s t := by
  refine WP.mono (WP.keep [.a1, .a2] (Q := fun t =>
      t.gpr .a1 = s.gpr .a1 + 8#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧ t.mem = s.mem) ?_ (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  mrun

theorem step_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (r : Nat) (t : State) (hi : LoopInv z a n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.addi .a1 .a1 8, .addi .a2 .a2 (-1)] : List Instr))) t
      (fun t' => (isa.eval (.nonzero .a2) t' = some false ∧ LoopPost z a n m₀ o t') ∨
        (isa.eval (.nonzero .a2) t' = some true ∧ ∃ r' < r, LoopInv z a n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.2.1
  have hwr : t.wr = o.wr := hi.keep.2.2
  have ha0 : t.gpr .a0 = o.gpr .a0 := hi.keep.gpr (by decide)
  have ht2 : t.gpr .t2 = o.gpr .t2 := hi.keep.gpr (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega
  have hread : BlockRead t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data, block_contains hj (by omega) (by decide) hc.bound⟩
  have hwrite : BlockWrite t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega) (by decide) hc.bound⟩
  have hz : Spec.Idea.scheduleAt t.mem (t.gpr .a0) = z := by
    rw [ha0, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  have hk : KeyOk z t := by
    have h := keyOk_of t (by rw [ha0, hrd, hwr]; exact hc.sched) (ht2.trans hc.mask)
    rwa [hz] at h
  rw [WP.block_append_iff]
  refine WP.mono (cryptBlock_ok z t hi.a1 hread hwrite hk) fun t₁ ⟨b₁, f₁, e₁⟩ => ?_
  refine WP.mono (tail_ok t₁) fun t₂ ⟨a1₂, a2₂, m₂, e₂⟩ => ?_
  have keep₂ : Keep loopWrites o t₂ := ((hi.keep.trans e₁).trans e₂).mono (by decide)
  have frame₂ : Frame [⟨a, 8 * n⟩] o.mem t₂.mem := by
    rw [m₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base a (by omega)
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) := by
    rw [m₂]
    exact blockAt_congr (frame_bytes f₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact blocks_disjoint hj hjn (Ne.symm hne) hc.bound) (by decide))
  have done₂ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      rw [m₂, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega) he]
      exact hi.done j (by have := hi.pos; omega)
  have ha2 : t₂.gpr .a2 = BitVec.ofNat 64 (r - 1) := by
    rw [a2₂, e₁.gpr (by decide), hi.a2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le; have := hc.bound
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  by_cases hlast : r = 1
  · subst hlast
    left
    refine ⟨?_, keep₂, frame₂, fun j hjn => done₂ j (by omega)⟩
    rw [Steps.eval_nonzero_ofNat _ _ (by omega) ha2]
    rfl
  · right
    refine ⟨?_, r - 1, by have := hi.pos; omega, ?_⟩
    · have := hi.pos; have := hi.le; have := hc.bound
      rw [Steps.eval_nonzero_ofNat _ _ (by omega) ha2]
      simp only [Option.some.injEq, decide_eq_true_eq]
      omega
    · refine ⟨by have := hi.pos; omega, by have := hi.le; omega, ?_, ha2, keep₂, frame₂, done₂, ?_⟩
      · rw [a1₂, e₁.gpr (by decide), hi.a1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
          Offset.add_ofNat_add_ofNat]
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
    (hc : LoopCtx z a n o) (hn : 1 ≤ n) (ho : o.gpr .a1 = a) (ha2 : o.gpr .a2 = BitVec.ofNat 64 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.addi .a1 .a1 8, .addi .a2 .a2 (-1)] : List Instr)))
      (.nonzero .a2)) o (LoopPost z a n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z a n m₀ o) (fun r t hi => step_ok hc r t hi) n o ⟨hn, Nat.le_refl _, ?_,
    ha2, Keep.refl _ _, Frame.refl _ _, fun j hj => by omega, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, ho]; exact (BitVec.add_zero a).symm

/-! ## The function -/

/-- The ECB contract on RISC-V. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 104⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  post s s' := Spec.Idea.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (s.gpr .a0))
      (Spec.Idea.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

/-- The registers `ecb` writes: all volatile. -/
abbrev ecbWrites : List Reg := [.t2, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t3]

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => contract.post s s') := by
  obtain ⟨hrd, hwr, dSched, hbound⟩ := hs
  unfold ecb
  apply WP.seq
  have h1 : WP isa (.block setMask) s fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem ∧
      Keep [.t2] s t := by
    refine WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    exact WP.mono (setMask_ok s) fun t ⟨a, b⟩ => ⟨a, b⟩
  refine WP.mono h1 fun s₁ ⟨h0₁, m₁, e₁⟩ => ?_
  refine WP.ite ((s.gpr .a2) == 0) (by rw [Steps.eval_zero, e₁.gpr (show Reg.a2 ∉ [Reg.t2] by decide)])
    (fun h0 => ?_) (fun h0 => ?_)
  · -- No blocks.
    have hn : s.gpr .a2 = 0 := beq_iff_eq.mp h0
    refine WP.block_nil ?_
    show Spec.Idea.blocksAt s₁.mem _ _ = _
    rw [hn, m₁]; rfl
  · have hn : (s.gpr .a2).toNat ≠ 0 := fun h =>
      (beq_eq_false_iff_ne.mp h0) (BitVec.eq_of_toNat_eq h)
    have ctx : LoopCtx (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) (s.gpr .a1) (s.gpr .a2).toNat s₁ := by
      refine ⟨?_, ?_, ?_, ?_, by omega, h0₁⟩
      · rw [e₁.gpr (by decide), e₁.2.1, e₁.2.2, hrd]; simp
      · rw [e₁.2.2, hwr]; simp
      · rw [e₁.gpr (by decide), m₁]
      · rw [e₁.gpr (by decide)]; exact dSched
    refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero hn) (e₁.gpr (by decide))
      (by rw [e₁.gpr (by decide), ofNat_toNat64]) (m₀ := s.mem) (fun j _ => by rw [m₁]))
      fun t ht => ?_
    show Spec.Idea.blocksAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = _
    exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ := WP.keep ecbWrites (ecb_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem ecb_ct : ConstantTime isa contract.pre contract.pub ecb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 1 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩]

theorem ecb_verified : Verified RISCV64.target ecb (Spec.Idea.ecbContract RISCV64.abi) :=
  Verified.of_correct ecb_correct ecb_ct (by
    sig_implies [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, RISCV64.abi, RISCV64.argRegs, contract]
      [ecbSat] using ecbSat)

end VG.Proof.Idea.RISCV64
