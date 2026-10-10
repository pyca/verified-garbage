import VerifiedGarbage.Proof.Idea.Arm.Block
import VerifiedGarbage.Proof.Idea.Arm.ConstantTime
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Idea.Scratch32

/-!
# IDEA ECB on ARMv7

`ecb_wp`: with the scratch buffer as an argument (at `r3`, 32 bytes),
`Impl.Idea.Arm.ecb` saves `r4`–`r11` in it, transforms the blocks in a loop
(`loop_ok`) whose invariant (`LoopInv`) says how many remain, that the ones
before are transformed and the ones after not yet (each iteration is
`cryptBlock_run`), and restores the registers.
-/

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Spill VG.Impl.Idea.Arm

/-! ## The loop -/

theorem advance_run (s : State) :
    ∃ s', runBlock isa [.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      Keep [.r1, .r2] s s' := by
  have e8 : encodable 8 = true := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e8, enc_one, ↓reduceIte,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, Option.some.injEq, exists_eq_left', true_and]
  refine ⟨rfl, rfl, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  show (if q = .r2 then _ else (subFlags (s.setReg .r1 _) _ _).gpr q) = _
  simp only [hq.2, ite_false]
  exact RegUpd.gpr_setReg_of_ne _ _ hq.1

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `r0`, readable, and `n` blocks at `r1` (address `A`),
writable, apart from it, neither wrapping around. -/
structure LoopCtx (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨State.addr (o.gpr .r0), 104⟩ ∈ o.rd ++ o.wr
  fit0 : (o.gpr .r0).toNat + 104 ≤ 2 ^ 32
  data : ⟨A, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (State.addr (o.gpr .r0)) = z
  sep : (⟨State.addr (o.gpr .r0), 104⟩ : Region).Disjoint ⟨A, 8 * n⟩
  addr : State.addr (o.gpr .r1) = A
  fit1 : (o.gpr .r1).toNat + 8 * n ≤ 2 ^ 32

/-- `r` blocks remain, from block `n - r` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  r1 : t.gpr .r1 = o.gpr .r1 + BitVec.ofNat 32 (8 * (n - r))
  r2 : t.gpr .r2 = BitVec.ofNat 32 r
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨A, 8 * n⟩] o.mem t.mem
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))

/-- After the loop: every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨A, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j)))

theorem step_ok {z : Spec.Idea.Schedule} {A : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z A n o) (r : Nat) (t : State) (hi : LoopInv z A n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] : List Instr))) t
      (fun t' => (isa.eval .ne t' = some false ∧ LoopPost z A n m₀ o t') ∨
        (isa.eval .ne t' = some true ∧ ∃ r' < r, LoopInv z A n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.rd
  have hwr : t.wr = o.wr := hi.keep.wr
  have hr0 : t.gpr .r0 = o.gpr .r0 := hi.keep.reg .r0 (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega
  have hb64 : 8 * n ≤ 2 ^ 64 := by have := hc.fit1; omega
  have hfit : (o.gpr .r1).toNat + 8 * (n - r) < 2 ^ 32 := by have := hc.fit1; omega
  have hr1n : (t.gpr .r1).toNat = (o.gpr .r1).toNat + 8 * (n - r) := by
    rw [hi.r1, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (n - r)) (by omega),
      Nat.mod_eq_of_lt hfit]
  have hat : BlockAt t (A + BitVec.ofNat 64 (8 * (n - r))) :=
    ⟨by rw [hi.r1, addr_add hfit, hc.addr], by rw [hr1n]; have := hc.fit1; omega⟩
  have hread : BlockRead t (A + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data,
      block_contains hj (by omega) (by decide) hb64⟩
  have hwrite : BlockWrite t (A + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega) (by decide) hb64⟩
  have hk : KeyOk z t := by
    refine ⟨by rw [hr0, hrd, hwr]; exact hc.sched, by rw [hr0]; exact hc.fit0, ?_⟩
    rw [hr0, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  obtain ⟨t₁, h₁, b₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := cryptBlock_run z t hat hread hwrite hk
  obtain ⟨t₂, h₂, r1₂, r2₂, z₂, e₂⟩ := advance_run t₁
  refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
  have keep₂ : Keep loopWrites o { t₂ with mem := o.mem } := by
    refine ⟨fun q hq => ?_, rfl, ?_, ?_, ?_⟩
    · show t₂.gpr q = o.gpr q
      have s₁ : ∀ q, q ∈ [Reg.r1, .r2] → q ∈ loopWrites := by decide
      have s₂ : ∀ q, q ∈ blockWrites → q ∈ loopWrites := by decide
      rw [e₂.reg q (fun h => hq (s₁ q h)), g₁ q (fun h => hq (s₂ q h))]
      exact hi.keep.reg q hq
    · show t₂.rd = o.rd; rw [e₂.rd, rd₁, hrd]
    · show t₂.wr = o.wr; rw [e₂.wr, wr₁, hwr]
    · show t₂.sp = o.sp; rw [e₂.sp, sp₁]; exact hi.keep.sp
  have mem₂ : t₂.mem = t₁.mem := e₂.mem
  have frame₂ : Frame [⟨A, 8 * n⟩] o.mem t₂.mem := by
    rw [mem₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base A (by omega)
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₂.mem (A + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) := by
    rw [mem₂]
    exact blockAt_congr (frame_bytes f₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact blocks_disjoint hj hjn (Ne.symm hne) hb64) (by decide))
  have done₂ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₂.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      rw [mem₂, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega) he]
      exact hi.done j (by have := hi.pos; omega)
  have hn32 : n < 2 ^ 32 := by have := hc.fit1; omega
  have hr2 : t₂.gpr .r2 = BitVec.ofNat 32 (r - 1) := by
    rw [r2₂, g₁ .r2 (by decide), hi.r2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  have hev : isa.eval .ne t₂ = some (decide (r - 1 ≠ 0)) := by
    show some (!t₂.z) = _
    rw [z₂, ← r2₂, hr2]
    congr 1
    by_cases h0 : r - 1 = 0
    · simp only [h0]; rfl
    · have hne : BitVec.ofNat 32 (r - 1) ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hi.le; omega)] at this
        exact this)
      rw [show (BitVec.ofNat 32 (r - 1) == 0) = false from by simpa using hne]
      simp [h0]
  by_cases hlast : r = 1
  · subst hlast
    left
    exact ⟨hev, keep₂, frame₂, fun j hjn => done₂ j (by omega)⟩
  · right
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega,
      r - 1, by have := hi.pos; omega, ?_⟩
    refine ⟨by have := hi.pos; omega, by have := hi.le; omega, ?_, hr2, keep₂, frame₂, done₂, ?_⟩
    · rw [r1₂, g₁ .r1 (by decide), hi.r1]
      apply BitVec.eq_of_toNat_eq
      have := hi.pos; have := hi.le; have := hc.fit1
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (8 : BitVec 32).toNat = 8 from rfl, Nat.mod_eq_of_lt (a := 8 * (n - r)) (by omega),
        Nat.mod_eq_of_lt (a := 8 * (n - (r - 1))) (by omega), Nat.mod_eq_of_lt hfit,
        show 8 * (n - (r - 1)) = 8 * (n - r) + 8 by omega, Nat.add_assoc]
    · intro j hj₁ hj₂
      have := hi.pos
      have := hi.le
      have hne : j ≠ n - r := by omega
      rw [other j hj₂ hne]
      exact hi.todo j (by omega) hj₂

end VG.Proof.Idea.Arm

namespace VG.Proof.Idea.Arm

open VG VG.Arm VG.Arm.Spill VG.Impl.Idea.Arm

theorem loop_ok {z : Spec.Idea.Schedule} {A : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z A n o) (hn : 1 ≤ n) (hr2 : o.gpr .r2 = BitVec.ofNat 32 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)] : List Instr)))
      .ne) o (LoopPost z A n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z A n m₀ o) (fun r t hi => step_ok hc r t hi) n o
    ⟨hn, Nat.le_refl _, ?_, hr2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, Frame.refl _ _,
      fun j hj => by omega, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero]; exact (BitVec.add_zero _).symm

/-! ## The function -/

/-- The ECB contract on ARMv7, with the scratch buffer (32 bytes) at `r3`. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 104⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 32⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 104 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 32 ≤ 2 ^ 32
  post s s' := Spec.Idea.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0)))
      (Spec.Idea.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

/-- What the loop (or no loop) leaves, before the registers are restored. -/
structure Mid (z : Spec.Idea.Schedule) (A : Addr) (n : Nat) (m₀ : Mem) (o t : State) : Prop where
  keep : Keep loopWrites o { t with mem := o.mem }
  frame : Frame [⟨A, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j)))

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, fit0, fit1, fit3⟩ := hs
  have hb64 : 8 * (s.gpr .r2).toNat ≤ 2 ^ 64 := by omega
  have hslots : Slots 0 32 ecbSaved := by decide
  have hinS : ∀ d, 0 ≤ d → d + 4 ≤ 32 → InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 d) 4 :=
    fun d _ h => ⟨⟨State.addr (s.gpr .r3), 32⟩, by rw [hwr]; simp, Offset.contains_base _ h (by omega)⟩
  unfold ecb
  refine WP.seq (save_slots_ok hslots fit3 hinS ?_)
  -- After saving.
  have hf₁ : Frame [⟨State.addr (s.gpr .r3), 32⟩] s.mem
      (saveMem s.mem (State.addr (s.gpr .r3)) s.gpr ecbSaved) :=
    saveMem_frame _ _ _ (by decide) _ (by decide)
  have hsv₁ := saveMem_saved (State.addr (s.gpr .r3)) s.gpr s.mem ecbSaved hslots
  generalize saveMem s.mem (State.addr (s.gpr .r3)) s.gpr ecbSaved = M₁ at hf₁ hsv₁
  -- `cmp r2, #0`.
  have e0 : encodable 0 = true := by decide
  refine WP.of_runBlock ⟨subFlags { s with mem := M₁ } (s.gpr .r2) 0, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, e0, ↓reduceIte,
      Option.map_some], ?_⟩
  generalize hs₂ : subFlags { s with mem := M₁ } (s.gpr .r2) 0 = s₂
  have g₂ : s₂.gpr = s.gpr := by rw [← hs₂]; rfl
  have mem₂ : s₂.mem = M₁ := by rw [← hs₂]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [← hs₂]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [← hs₂]; rfl
  have z₂ : s₂.z = (s.gpr .r2 - 0 == 0) := by rw [← hs₂]; rfl
  let z := Spec.Idea.scheduleAt s.mem (State.addr (s.gpr .r0))
  let A := State.addr (s.gpr .r1)
  let n := (s.gpr .r2).toNat
  have blocks₂ : ∀ j < n, Spec.Idea.blockAt s₂.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt s.mem (A + BitVec.ofNat 64 (8 * j)) := fun j hj => by
    rw [mem₂]
    exact blockAt_congr (frame_bytes hf₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact dDS.sub_left (Offset.sub_base A (by omega))) (by decide))
  refine WP.seq (WP.mono (Q := Mid z A n s.mem s₂) ?_ fun t ht => ?_)
  · -- The blocks.
    have hz : isa.eval .eq s₂ = some (decide (n = 0)) := by
      show some s₂.z = _
      rw [z₂, show s.gpr .r2 - 0 = s.gpr .r2 from BitVec.sub_zero _]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    refine WP.ite _ hz (fun h0 => ?_) (fun h0 => ?_)
    · have h0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, Frame.refl _ _, fun j hj => by omega⟩
    · have h0 : n ≠ 0 := by simpa using h0
      have ctx : LoopCtx z A n s₂ := by
        refine ⟨?_, by rw [g₂]; exact fit0, by rw [wr₂, hwr]; simp [A, n], ?_, ?_, by rw [g₂],
          by rw [g₂]; exact fit1⟩
        · rw [g₂, rd₂, hrd]; simp
        · rw [g₂, mem₂]
          exact scheduleAt_congr (frame_bytes hf₁ (by
            intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact dSS) (by decide))
        · rw [g₂]; exact dSD
      refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero h0) (by rw [g₂]; simp [n]) blocks₂)
        fun t ht => ⟨ht.keep, ht.frame, ht.done⟩
  · -- Restoring the registers.
    have r3t : t.gpr .r3 = s.gpr .r3 := (ht.keep.reg .r3 (by decide)).trans (by rw [g₂])
    have hsv : Saved t.mem (State.addr (t.gpr .r3)) s.gpr ecbSaved := by
      rw [r3t]
      refine hsv₁.frame hslots (mem₂ ▸ ht.frame) fun q hq => ?_
      simp only [List.mem_singleton] at hq; subst hq
      rw [BitVec.add_zero]
      exact dDS.symm
    have hin : ∀ d, 0 ≤ d → d + 4 ≤ 32 →
        InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r3) + BitVec.ofNat 64 d) 4 := fun d h0 h => by
      obtain ⟨R, hR, hc⟩ := hinS d h0 h
      rw [ht.keep.rd, ht.keep.wr, rd₂, wr₂, r3t]
      exact ⟨R, List.mem_append_right _ hR, hc⟩
    refine WP.mono (restore_block_ok hslots (by decide) (by rw [r3t]; exact fit3) hin hsv)
      fun u hu' => ?_
    obtain ⟨hu, ho, hm, -⟩ := hu'
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hu (.r4, 0) (by decide)
      · exact hu (.r5, 4) (by decide)
      · exact hu (.r6, 8) (by decide)
      · exact hu (.r7, 12) (by decide)
      · exact hu (.r8, 16) (by decide)
      · exact hu (.r9, 20) (by decide)
      · exact hu (.r10, 24) (by decide)
      · exact hu (.r11, 28) (by decide)
      · rw [ho .lr (by decide)]
        exact (ht.keep.reg .lr (by decide)).trans (by rw [g₂])
    · show Spec.Idea.blocksAt u.mem _ _ = _
      rw [hm]
      exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_wp s hs
  exact ⟨t, s', he, ⟨ha, Exec.sp he⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 1 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 32⟩]

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 := by
  simp [PublicRegs]

theorem ecb_verified : Verified target ecb (Proof.Idea.ecbScratchContract32 abi 8) := by
  refine Verified.of_correct ecb_correct (ecb_constantTime _) ?_
  sig_implies [Proof.Idea.ecbScratchContract32, Proof.Idea.ecbScratchSig32, Spec.Idea.ecbPost, abi,
    argRegs, reduceClassify, Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

end VG.Proof.Idea.Arm
