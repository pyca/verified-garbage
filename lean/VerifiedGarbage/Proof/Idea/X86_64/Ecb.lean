import VerifiedGarbage.Proof.Idea.X86_64.Block
import VerifiedGarbage.Proof.Idea.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA ECB on x86-64

`ecb_correct`: `Impl.Idea.X86_64.ecb` meets `contract`, the ECB contract
with a 16-byte scratch buffer in `rcx`, where it saves `rbx` and `rbp`. The
blocks are transformed in a loop (`loop_ok`) whose invariant (`LoopInv`)
says how many remain, that the ones before are transformed and the ones
after not yet; each iteration is `cryptBlock_run`. `ecb_verified` relates
it to the shared contract with the scratch buffer as an argument.
-/

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

/-! ## Memory -/

/-- `KeyOk` of the schedule in a readable region at `rdi`. -/
theorem keyOk_of (s : State) (hr : ⟨s.gpr .rdi, 104⟩ ∈ s.rd ++ s.wr) :
    KeyOk (Spec.Idea.scheduleAt s.mem (s.gpr .rdi)) s := by
  have hin : ∀ d, d + 8 ≤ 104 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact ⟨_, hr, Offset.contains_base _ hd (by omega)⟩
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · rw [ea_at]; exact hin _ (by omega)
  · rw [ea_at]; exact subkey_read _ _ (by omega)
  · rw [ea_at]; exact subkey_read96 _ _ hj

/-! ## The loop -/

theorem signExtend_eight : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide

theorem tail_run (s : State) :
    ∃ s', runBlock isa [.alu .add .rsi (.imm 8), .alu .sub .rbp (.imm 1)] s = some s' ∧
      s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rbp = s.gpr .rbp - 1 ∧
      s'.zf = some (s.gpr .rbp - 1 == 0) ∧ Keep [.rsi, .rbp] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
    Option.bind_some, signExtend_eight, signExtend_one, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.zf_setReg, RegUpd.zf_arithFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq,
    exists_eq_left', true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq.1, hq.2, ite_false]

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.rax, .rdx, .rbx, .r8, .r9, .r10, .r11, .rsi, .rbp]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `rdi`, readable, and `n` blocks at `a`, writable, apart
from it and not wrapping around. -/
structure LoopCtx (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨o.gpr .rdi, 104⟩ ∈ o.rd ++ o.wr
  data : ⟨a, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (o.gpr .rdi) = z
  sep : (⟨o.gpr .rdi, 104⟩ : Region).Disjoint ⟨a, 8 * n⟩
  bound : 8 * n ≤ 2 ^ 64

/-- `r` blocks remain, at `a + 8 (n - r)` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  rsi : t.gpr .rsi = a + BitVec.ofNat 64 (8 * (n - r))
  rbp : t.gpr .rbp = BitVec.ofNat 64 r
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
    WP isa (.block (cryptBlock ++ ([.alu .add .rsi (.imm 8), .alu .sub .rbp (.imm 1)] : List Instr))) t
      (fun t' => (isa.eval .ne t' = some false ∧ LoopPost z a n m₀ o t') ∨
        (isa.eval .ne t' = some true ∧ ∃ r' < r, LoopInv z a n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.rd
  have hwr : t.wr = o.wr := hi.keep.wr
  have hrdi : t.gpr .rdi = o.gpr .rdi := hi.keep.reg .rdi (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega
  -- The block and the schedule.
  have hread : BlockRead t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data, block_contains hj (by omega) (by decide) hc.bound⟩
  have hwrite : BlockWrite t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega) (by decide) hc.bound⟩
  have hz : Spec.Idea.scheduleAt t.mem (t.gpr .rdi) = z := by
    rw [hrdi, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  have hk : KeyOk z t := by
    have h := keyOk_of t (by rw [hrdi, hrd, hwr]; exact hc.sched)
    rwa [hz] at h
  obtain ⟨t₁, h₁, b₁, f₁, g₁, rd₁, wr₁⟩ := cryptBlock_run z t hi.rsi hread hwrite hk
  obtain ⟨t₂, h₂, rsi₂, rbp₂, zf₂, e₂⟩ := tail_run t₁
  refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
  -- What holds after the iteration, whether it is the last or not.
  have keep₂ : Keep loopWrites o { t₂ with mem := o.mem } := by
    refine ⟨fun q hq => ?_, rfl, ?_, ?_⟩
    · show t₂.gpr q = o.gpr q
      have s₁ : ∀ q, q ∈ [Reg.rsi, .rbp] → q ∈ loopWrites := by decide
      have s₂ : ∀ q, q ∈ roundWrites → q ∈ loopWrites := by decide
      rw [e₂.reg q (fun h => hq (s₁ q h)), g₁ q (fun h => hq (s₂ q h)), ← hi.keep.reg q hq]
    · show t₂.rd = o.rd; rw [e₂.rd, rd₁, hrd]
    · show t₂.wr = o.wr; rw [e₂.wr, wr₁, hwr]
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
  have hrbp : t₂.gpr .rbp = BitVec.ofNat 64 (r - 1) := by
    rw [rbp₂, g₁ .rbp (by decide), hi.rbp]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le; have := hc.bound
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one]
    omega
  by_cases hlast : r = 1
  · subst hlast
    left
    refine ⟨?_, keep₂, frame₂, fun j hjn => done₂ j (by omega)⟩
    simp only [eval, zf₂, g₁ .rbp (by decide), hi.rbp]
    rfl
  · right
    refine ⟨?_, r - 1, by have := hi.pos; omega, ?_⟩
    · simp only [eval, zf₂, g₁ .rbp (by decide), hi.rbp, Option.map_some, Option.some.injEq]
      have := hi.pos; have := hi.le; have := hc.bound
      have h : (BitVec.ofNat 64 r - 1 == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one, toNat_zero] at this
        omega
      rw [h]; rfl
    · refine ⟨by have := hi.pos; omega, by have := hi.le; omega, ?_, hrbp, keep₂, frame₂, done₂, ?_⟩
      · rw [rsi₂, g₁ .rsi (by decide), hi.rsi]
        rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_ofNat_add_ofNat]
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
    (hc : LoopCtx z a n o) (hn : 1 ≤ n) (ho : o.gpr .rsi = a) (hrbp : o.gpr .rbp = BitVec.ofNat 64 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.alu .add .rsi (.imm 8), .alu .sub .rbp (.imm 1)] : List Instr))) .ne) o
      (LoopPost z a n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z a n m₀ o) (fun r t hi => step_ok hc r t hi) n o ⟨hn, Nat.le_refl _, ?_,
    hrbp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Frame.refl _ _, fun j hj => by omega,
    fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, ho]; exact (BitVec.add_zero a).symm

/-! ## The function -/

/-- The ECB contract on x86-64, with the scratch buffer (16 bytes) in `rcx`. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 104⟩
    let data : Region := ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨s.gpr .rcx, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧
      data.Disjoint scr ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := Spec.Idea.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (s.gpr .rdi))
      (Spec.Idea.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx]

theorem prologue_run (s : State) (h0 : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 0) 8)
    (h8 : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.store (at_ .rcx 0) .rbx, .store (at_ .rcx 8) .rbp, .mov .rbp (.reg .rdx)] s =
        some s' ∧
      s'.mem = (s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 0) (s.gpr .rbx)).writeW
        (s.gpr .rcx + BitVec.ofNat 64 8) (s.gpr .rbp) ∧
      s'.gpr .rbp = s.gpr .rdx ∧ (∀ q, q ≠ .rbp → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.store64, isa,
    Option.map_some, ea_at, h0, h8, ↓reduceIte, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, Option.some.injEq, exists_eq_left', true_and]
  exact ⟨fun q hq => by simp only [hq, ite_false], trivial⟩

theorem epilogue_run (t : State) (h0 : InRegions (t.rd ++ t.wr) (t.gpr .rcx + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (t.rd ++ t.wr) (t.gpr .rcx + BitVec.ofNat 64 8) 8) :
    ∃ t', runBlock isa [.mov .rbx (.mem (at_ .rcx 0)), .mov .rbp (.mem (at_ .rcx 8))] t = some t' ∧
      t'.gpr .rbx = t.mem.readW (t.gpr .rcx + BitVec.ofNat 64 0) 64 ∧
      t'.gpr .rbp = t.mem.readW (t.gpr .rcx + BitVec.ofNat 64 8) 64 ∧ Keep [.rbx, .rbp] t t' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, isa,
    Option.map_some, ea_at, h0, h8, ↓reduceIte, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, reduceCtorEq, Option.some.injEq, exists_eq_left', true_and]
  refine keep_reg_of (fun q hq => ?_) rfl rfl rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  simp only [RegUpd.gpr_setReg, hq.1, hq.2, ite_false]

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => gprPreserved s s' ∧ contract.post s s') := by
  obtain ⟨hrd, hwr, dSched, sSched, dScr, rData, rScr, hbound⟩ := hs
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨arithFlags s (s.gpr .rdx &&& s.gpr .rdx) false false, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa,
      Option.bind_some], ?_⟩
  have hz₁ : isa.eval .e (arithFlags s (s.gpr .rdx &&& s.gpr .rdx) false false) =
      some (decide ((s.gpr .rdx).toNat = 0)) := by
    simp only [eval, RegUpd.zf_arithFlags, BitVec.and_self, beq_zero]
  apply WP.ite _ hz₁
  · -- No blocks.
    intro h0
    have hn : (s.gpr .rdx).toNat = 0 := by simpa using h0
    refine WP.block_nil ⟨⟨fun r _ => rfl, rfl⟩, ?_⟩
    show Spec.Idea.blocksAt s.mem _ _ = _
    rw [hn]; rfl
  · intro h0
    have hn : (s.gpr .rdx).toNat ≠ 0 := by simpa using h0
    -- The prologue.
    have scrW : ∀ d, d + 8 ≤ 16 → InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 d) 8 := fun d hd =>
      ⟨_, by rw [hwr]; simp, Offset.contains_base _ hd (by omega)⟩
    apply WP.seq
    apply WP.of_runBlock
    obtain ⟨s₂, h₂, m₂, rbp₂, g₂, rd₂, wr₂⟩ := prologue_run
      (arithFlags s (s.gpr .rdx &&& s.gpr .rdx) false false) (scrW 0 (by decide)) (scrW 8 (by decide))
    refine ⟨s₂, h₂, ?_⟩
    simp only [RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags] at m₂ rbp₂ g₂ rd₂ wr₂
    have frame₂ : Frame [⟨s.gpr .rcx, 16⟩] s.mem s₂.mem := by
      rw [m₂]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))
    have ctx : LoopCtx (Spec.Idea.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rsi) (s.gpr .rdx).toNat s₂ := by
      refine ⟨?_, ?_, ?_, ?_, by omega⟩
      · rw [g₂ .rdi (by decide), rd₂, hrd]; simp
      · rw [wr₂, hwr]; simp
      · rw [g₂ .rdi (by decide)]
        exact scheduleAt_congr (frame_bytes frame₂ (by simpa using sSched) (by decide))
      · rw [g₂ .rdi (by decide)]; exact dSched
    apply WP.seq
    refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero hn) (g₂ .rsi (by decide))
      (by rw [rbp₂, ofNat_toNat64]) (m₀ := s.mem) ?_) fun t ht => ?_
    · intro j hj
      exact blockAt_congr (frame_bytes frame₂ (by
        intro q hq; simp only [List.mem_singleton] at hq; subst hq
        exact dScr.sub_left (Offset.sub_base _ (by omega))) (by decide))
    · -- The epilogue.
      have rcx_t : t.gpr .rcx = s.gpr .rcx :=
        (ht.keep.reg .rcx (by decide)).trans (g₂ .rcx (by decide))
      have scrR : ∀ d, d + 8 ≤ 16 → InRegions (t.rd ++ t.wr) (t.gpr .rcx + BitVec.ofNat 64 d) 8 :=
        fun d hd => by
          rw [ht.keep.rd, ht.keep.wr, rd₂, wr₂, rcx_t]
          exact ⟨_, by rw [hwr]; simp, Offset.contains_base _ hd (by omega)⟩
      apply WP.of_runBlock
      obtain ⟨t', h', rbx', rbp', e'⟩ := epilogue_run t (scrR 0 (by decide)) (scrR 8 (by decide))
      refine ⟨t', h', ?_, ?_⟩
      · have scrT : ∀ d, d < 16 → t.mem (s.gpr .rcx + BitVec.ofNat 64 d) =
            s₂.mem (s.gpr .rcx + BitVec.ofNat 64 d) := fun d hd =>
          frame_bytes ht.frame (by
            intro q hq; simp only [List.mem_singleton] at hq; subst hq
            exact dScr.symm) (by decide) d hd
        have rdT : ∀ d, d + 8 ≤ 16 → t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 d) 64 =
            s₂.mem.readW (s.gpr .rcx + BitVec.ofNat 64 d) 64 := fun d hd => by
          simp only [Mem.readW]
          congr 1
          refine Mem.read_congr fun i hi => ?_
          rw [Offset.add_ofNat_add_ofNat, scrT _ (by omega)]
        have frameAll : Frame [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 16⟩] s.mem t'.mem := by
          rw [e'.mem]
          exact (frame₂.mono (by simp)).trans (ht.frame.mono (by simp))
        refine ⟨fun r hr => ?_, ?_⟩
        · by_cases hb : r = .rbx
          · subst hb
            rw [rbx', rcx_t, rdT 0 (by decide), m₂, Mem.readW_writeW_sep
              (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
          · by_cases hp : r = .rbp
            · subst hp
              rw [rbp', rcx_t, rdT 8 (by decide), m₂, Mem.readW_writeW_self64]
            · rw [e'.reg r (by simp [hb, hp]), ht.keep.reg r (by
                intro h; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
              exact g₂ r hp
        · exact frameAll.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
            intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact rData
            · exact rScr) (by decide)
      · show Spec.Idea.blocksAt t'.mem (s.gpr .rsi) (s.gpr .rdx).toNat = _
        rw [e'.mem]
        exact blocksAt_eq _ _ _ _ _ ht.done

end VG.Proof.Idea.X86_64
