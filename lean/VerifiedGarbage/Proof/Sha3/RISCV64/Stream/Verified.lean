module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.AbsorbWs
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
meta import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Sha3.Contract

import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Sha3.RISCV64.Permute
import VerifiedGarbage.Proof.Sha3.RISCV64.Call
/-!
# The SHA-3 sponge on RISC-V: `Verified`

`absorb`, `absorbWs`, `pad` and `squeeze` (`Stream/`): correctness,
constant time, and a state satisfying
each precondition, against the per-target contracts, then moved to the
shared ones of `Spec/Sha3/Contract.lean` with the stack they use: their
frame and the permutation's (608 bytes), or for `absorbWs`, which has no
frame, the permutation's alone. `absorb` has no shared contract: it is an internal
function, which RISC-V's verified code (ML-KEM, ML-DSA, Ed448, the SHA-3
pieces) calls by its per-target contract (`Calls.lean`).

The constant-time proofs compose taint-checked sponge operations with the
permutation's relational proof and register-preservation contract. The
permutation temporarily uses saved registers for secret lanes, then restores
the public pointers and counters before the sponge resumes.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64

namespace CT

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64

private def scratch (ws : Bool) (s : State) : Addr := if ws then s.gpr .s7 else s.sp

/-- The permutation's contract, independently of the sponge contents and counters. -/
private structure Safe (ws : Bool) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  room : 608 ≤ s.sp.toNat
  sep : Region.Disjoint ⟨s.gpr .s2, 200⟩ ⟨scratch ws s, 512⟩
  belowState : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨s.gpr .s2, 200⟩
  belowScratch : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨scratch ws s, 512⟩
  covers : Covers [⟨s.gpr .s2, 200⟩, ⟨scratch ws s, 512⟩] s.wr

private theorem Safe.congr {ws : Bool} {s t : State} (h : Safe ws s)
    (h2 : t.gpr .s2 = s.gpr .s2) (h7 : t.gpr .s7 = s.gpr .s7) (hsp : t.sp = s.sp)
    (hwr : t.wr = s.wr) : Safe ws t := by
  have hsc : scratch ws t = scratch ws s := by simp only [scratch, h7, hsp]
  exact ⟨by rw [hsp]; exact h.al, by rw [hsp]; exact h.room,
    by rw [h2, hsc]; exact h.sep, by rw [hsp, h2]; exact h.belowState,
    by rw [hsp, hsc]; exact h.belowScratch, by rw [h2, hsc, hwr]; exact h.covers⟩

private def regs (ws : Bool) : VG.RISCV64.Taint.T := VG.RISCV64.Taint.ofRegs ([.s2, .s3, .s4, .s5, .s6] ++ if ws then [.s7] else [])
private def callRegs (ws : Bool) : VG.RISCV64.Taint.T := ((regs ws).insert .a0).insert .a1

private def Pair (ws : Bool) (τ : VG.RISCV64.Taint.T) (a b : State) : Prop := Safe ws a ∧ Safe ws b ∧ VG.RISCV64.Taint.Agree τ a b

private theorem regs_preserved {ws : Bool} {r : Reg} (hr : r ∈ regs ws) : r ∈ preserved := by
  cases ws <;> simp only [regs, VG.RISCV64.Taint.mem_ofRegs, ite_true, Bool.false_eq_true, ite_false,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The ordinary taint checker, retaining a checked postcondition on public registers. -/
private theorem taint_post (τ σ : taint.T) {c : Prog isa} {hc : VG.Taint.Hint taint.T}
    (h : (taint.check τ c hc).any (fun t => taint.le σ t) = true) :
    RelCT isa (VG.RISCV64.Taint.Agree τ) c (VG.RISCV64.Taint.Agree σ) := by
  cases he : taint.check τ c hc with
  | none => rw [he, Option.any_none] at h; cases h
  | some t =>
    have hle : taint.le σ t = true := by
      rw [he, Option.any_some] at h
      exact h
    intro a b t₁ t₂ a' b' hab e₁ e₂
    obtain ⟨ht, ha⟩ := VG.Taint.check_sound he hab e₁ e₂
    exact ⟨ht, taint.le_sound hle ha⟩

/-- Call-free pieces keep the permutation's safety facts through their fixed pointers. -/
private theorem step (ws : Bool) (τ σ : VG.RISCV64.Taint.T) {c : Prog isa}
    (hn : c.noFrames = true) (hcall : c.noCalls = true)
    (hk : c.allInstrs (fun i => dstOf i != some .s2 && dstOf i != some .s7) = true)
    {hc : VG.Taint.Hint taint.T}
    (h : (taint.check τ c hc).any (fun t => taint.le σ t) = true) :
    RelCT isa (Pair ws τ) c (Pair ws σ) := by
  intro a b t₁ t₂ a' b' ⟨sa, sb, hab⟩ e₁ e₂
  obtain ⟨ht, ha⟩ := taint_post τ σ h _ _ _ _ _ _ hab e₁ e₂
  have keep : ∀ i ∈ instrs c, dstOf i ≠ some .s2 ∧ dstOf i ≠ some .s7 := by
    intro i hi
    have hh := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans hk) i hi
    simpa only [Bool.and_eq_true, bne_iff_ne] using hh
  obtain ⟨_, wa, spa, _⟩ := VG.RISCV64.Exec.regions e₁ hn
  obtain ⟨_, wb, spb, _⟩ := VG.RISCV64.Exec.regions e₂ hn
  exact ⟨ht, sa.congr (VG.RISCV64.Exec.gpr (fun i hi => (keep i hi).1) e₁ (.inl hcall))
    (VG.RISCV64.Exec.gpr (fun i hi => (keep i hi).2) e₁ (.inl hcall)) spa wa,
    sb.congr (VG.RISCV64.Exec.gpr (fun i hi => (keep i hi).1) e₂ (.inl hcall))
      (VG.RISCV64.Exec.gpr (fun i hi => (keep i hi).2) e₂ (.inl hcall)) spb wb, ha⟩

/-- Grouping sequential pieces changes neither trace nor the final relation. -/
private theorem seq_assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

/-- A relational loop invariant needs no termination assumption: both executions are finite. -/
private theorem loop_inv {I : State → State → Prop} {body : Prog isa} {c : Cond}
    (hb : RelCT isa I body I) (hc : ∀ a b, I a b → eval c a = eval c b) :
    RelCT isa I (.loop body c) I := by
  have aux : ∀ {p : Prog isa} {a a' : State} {t : List Leak}, Exec isa p a t a' →
      p = .loop body c → ∀ b u b', I a b → Exec isa (.loop body c) b u b' → t = u ∧ I a' b' := by
    intro p a a' t e
    induction e with
    | loopExit e₁ k₁ _ =>
      intro he b u b' hi e₂
      cases he
      cases e₂ with
      | loopExit e₂ _ =>
        obtain ⟨ht, hI⟩ := hb _ _ _ _ _ _ hi e₁ e₂
        exact ⟨by rw [ht], hI⟩
      | loopNext e₂ k₂ _ =>
        obtain ⟨_, hi'⟩ := hb _ _ _ _ _ _ hi e₁ e₂
        have heq : isa.eval c _ = isa.eval c _ := hc _ _ hi'
        rw [k₁, k₂] at heq
        cases heq
    | loopNext e₁ k₁ _ _ ih =>
      intro he b u b' hi e₂
      cases he
      cases e₂ with
      | loopExit e₂ k₂ =>
        obtain ⟨_, hi'⟩ := hb _ _ _ _ _ _ hi e₁ e₂
        have heq : isa.eval c _ = isa.eval c _ := hc _ _ hi'
        rw [k₁, k₂] at heq
        cases heq
      | loopNext e₂ _ rest =>
        obtain ⟨ht, hi'⟩ := hb _ _ _ _ _ _ hi e₁ e₂
        obtain ⟨hu, hf⟩ := ih rfl _ _ _ hi' rest
        exact ⟨by rw [ht, hu], hf⟩
    | _ => intro he; cases he
  intro a b t u a' b' hi e₁ e₂
  exact aux e₁ rfl b u b' hi e₂

private def args (ws : Bool) : List Instr :=
  [mov .a0 .s2, if ws then mov .a1 .s7 else .addSp .a1 0]

private def Args (ws : Bool) (s : State) : Prop := s.gpr .a0 = s.gpr .s2 ∧ s.gpr .a1 = scratch ws s

private theorem args_ok (ws : Bool) (s : State) : WP isa (.block (args ws)) s (Args ws) := by
  cases ws
  · simp only [args, Bool.false_eq_true, ite_false, mov]
    refine wp_mv fun t u => wp_addSp (by decide) fun t' u' => WP.block_nil ⟨?_, ?_⟩
    · rw [u'.other _ (by decide), u.gpr, u'.other _ (by decide), u.other _ (by decide)]
    · simp only [scratch, Bool.false_eq_true, ite_false]
      rw [u'.gpr, u'.sp, BitVec.add_zero]
  · simp only [args, ite_true, mov]
    refine wp_mv fun t u => wp_mv fun t' u' => WP.block_nil ⟨?_, ?_⟩
    · rw [u'.other _ (by decide), u.gpr, u'.other _ (by decide), u.other _ (by decide)]
    · simp only [scratch, ite_true]
      rw [u'.gpr, u'.other _ (by decide)]

private def CallPair (ws : Bool) (a b : State) : Prop := Pair ws (callRegs ws) a b ∧ Args ws a ∧ Args ws b

private theorem call_pre {ws : Bool} {s : State} (hs : Safe ws s) (ha : Args ws s) :
    Proof.Sha3.permuteRISCV64.pre
      (s.callEntry.withRegions [] [⟨s.gpr .a0, 200⟩, ⟨s.gpr .a1, 512⟩]) := by
  have h0 := State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs)
  have h1 := State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs)
  simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, h0, h1]
  exact ⟨trivial, trivial, by rw [ha.1, ha.2]; exact hs.sep, hs.al, hs.room,
    by rw [ha.1]; exact hs.belowState, by rw [ha.2]; exact hs.belowScratch⟩

private theorem call_wp {ws : Bool} {s : State} (hs : Safe ws s) (ha : Args ws s) :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) s fun t =>
      Safe ws t ∧ t.sp = s.sp ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  refine callWs_ok ha.1 ha.2 hs.al hs.room hs.sep hs.belowState hs.belowScratch hs.covers
    fun t _ hw hp hc _ _ => ?_
  exact ⟨hs.congr (hc .s2 (by decide)) (hc .s7 (by decide)) hp hw, hp, hc⟩

private theorem call_traces (ws : Bool) :
    RelCT isa (CallPair ws) (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) fun _ _ => True := by
  intro a b t u a' b' ⟨⟨sa, sb, hab⟩, aa, ab⟩ e₁ e₂
  have h0 : a.gpr .a0 = b.gpr .a0 := hab.reg (by change Reg.a0 ∈ callRegs ws; simp only [callRegs, RegSet.mem_insert]; simp)
  have h1 : a.gpr .a1 = b.gpr .a1 := hab.reg (by change Reg.a1 ∈ callRegs ws; simp only [callRegs, RegSet.mem_insert]; simp)
  have ca : Covers [⟨a.gpr .a0, 200⟩, ⟨a.gpr .a1, 512⟩] a.wr := by rw [aa.1, aa.2]; exact sa.covers
  have cb : Covers [⟨a.gpr .a0, 200⟩, ⟨a.gpr .a1, 512⟩] b.wr := by rw [h0, h1, ab.1, ab.2]; exact sb.covers
  have hct : RelCT isa (fun x y => x = a ∧ y = b)
      (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) (fun _ _ => True) := by
    refine RelCT.call (k := Proof.Sha3.permuteRISCV64) permute_correct permute_ct []
      [⟨a.gpr .a0, 200⟩, ⟨a.gpr .a1, 512⟩] fun x y ⟨rfl, rfl⟩ => ?_
    refine ⟨call_pre sa aa, ?_, ?_, ca.right, ca, cb.right, cb⟩
    · rw [h0, h1]; exact call_pre sb ab
    · simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
      exact ⟨h0, h1, hab.1⟩
  exact hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

private theorem call_ct (ws : Bool) :
    RelCT isa (CallPair ws) (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) (Pair ws (regs ws)) := by
  intro a b t u a' b' h e₁ e₂
  have ht := (call_traces ws _ _ _ _ _ _ h e₁ e₂).1
  obtain ⟨_, x, ex, sx, px, cx⟩ := call_wp h.1.1 h.2.1
  obtain ⟨_, rfl⟩ := Exec.det e₁ ex
  obtain ⟨_, y, ey, sy, py, cy⟩ := call_wp h.1.2.1 h.2.2
  obtain ⟨_, rfl⟩ := Exec.det e₂ ey
  refine ⟨ht, sx, sy, (px.trans h.1.2.2.1).trans py.symm, fun r hr => ?_⟩
  rw [cx r (regs_preserved hr), cy r (regs_preserved hr)]
  exact h.1.2.2.2 r (by simp only [callRegs, RegSet.mem_insert]; exact .inr (.inr hr))

private def atCode (ws : Bool) : Prog isa := .seq (.block (args ws)) (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute)

private theorem at_ct (ws : Bool) : RelCT isa (Pair ws (regs ws)) (atCode ws) (Pair ws (regs ws)) := by
  have hs : RelCT isa (Pair ws (regs ws)) (.block (args ws)) (Pair ws (callRegs ws)) := by
    cases ws <;> exact step _ _ _ (by decide) (by decide) (by decide) (by taint_decide)
  intro a b t u a' b' h e₁ e₂
  cases e₁ with
  | seq ea ec =>
    cases e₂ with
    | seq eb ed =>
      obtain ⟨ht, hp⟩ := hs _ _ _ _ _ _ h ea eb
      obtain ⟨_, x, ex, ax⟩ := args_ok ws a
      obtain ⟨_, rfl⟩ := Exec.det ea ex
      obtain ⟨_, y, ey, ay⟩ := args_ok ws b
      obtain ⟨_, rfl⟩ := Exec.det eb ey
      obtain ⟨hu, hq⟩ := call_ct ws _ _ _ _ _ _ ⟨hp, ax, ay⟩ ec ed
      exact ⟨by rw [ht, hu], hq⟩

private def fullCode (ws : Bool) : Prog isa :=
  .seq (.block [.sub .t1 .s4 .s3])
    (.ite (.zero .t1) (.seq (.block [.li .s4 0]) (atCode ws)) (.block []))

private theorem full_ct (ws : Bool) : RelCT isa (Pair ws (regs ws)) (fullCode ws) (Pair ws (regs ws)) := by
  let mid := (regs ws).insert .t1
  have hsub : RelCT isa (Pair ws (regs ws)) (.block [.sub .t1 .s4 .s3]) (Pair ws mid) := by
    cases ws <;> exact step _ _ _ (by decide) (by decide) (by decide) (by taint_decide)
  have hli : RelCT isa (Pair ws mid) (.block [.li .s4 0]) (Pair ws (regs ws)) := by
    dsimp only [mid]
    cases ws <;> exact step _ _ _ (by decide) (by decide) (by decide) (by taint_decide)
  have hnil : RelCT isa (Pair ws mid) (.block []) (Pair ws (regs ws)) := by
    dsimp only [mid]
    cases ws <;> exact step _ _ _ (by decide) (by decide) (by decide) (by taint_decide)
  refine RelCT.seq hsub (RelCT.ite (c := Cond.zero .t1) (fun a b h => ?_)
    ((RelCT.seq hli (at_ct ws)).mono (fun _ _ h => h.1) (fun _ _ h => h))
    (hnil.mono (fun _ _ h => h.1) (fun _ _ h => h)))
  exact VG.RISCV64.Taint.cond_sound (c := .zero .t1) h.2.2 (by
    change Reg.t1 ∈ mid
    simp only [mid, RegSet.mem_insert, true_or])

private theorem absorb_body_ct (ws : Bool) :
    RelCT isa (Pair ws (regs ws)) (if ws then absorbWsBody else absorbBody) (Pair ws (regs ws)) := by
  have hs : RelCT isa (Pair ws (regs ws))
      (.seq (.block laneCheck) (Impl.Sha3.RISCV64.Stream.step absorbLane absorbByte)) (Pair ws (regs ws)) := by
    cases ws <;> exact step _ _ _ (by decide) (by decide) (by decide) (by taint_decide)
  have h := seq_assoc (RelCT.seq hs (full_ct ws))
  cases ws <;> exact h

private theorem squeeze_body_ct : RelCT isa (Pair false (regs false)) squeezeBody (Pair false (regs false)) := by
  have hs : RelCT isa (Pair false (regs false))
      (.seq (.block laneCheck) (Impl.Sha3.RISCV64.Stream.step squeezeLane squeezeByte)) (Pair false (regs false)) :=
    step _ _ _ (by decide) (by decide) (by decide) (by taint_decide)
  exact RelCT.seq (full_ct false) hs

private theorem runLoop_ct (ws : Bool) {body : Prog isa}
    (hb : RelCT isa (Pair ws (regs ws)) body (Pair ws (regs ws))) :
    RelCT isa (Pair ws (regs ws))
      (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6))) (Pair ws (regs ws)) := by
  have hpub : VG.RISCV64.Taint.pub (regs ws) .s6 = true := by cases ws <;> decide
  have hl := loop_inv hb (fun a b h => VG.RISCV64.Taint.cond_sound h.2.2 (show VG.RISCV64.Taint.condPub (regs ws) (.nonzero .s6) = true from hpub))
  exact RelCT.ite (c := Cond.zero .s6) (fun a b h => VG.RISCV64.Taint.cond_sound (c := .zero .s6) h.2.2 hpub)
    (relct_nil.mono (fun _ _ h => h.1) (fun _ _ h => h))
    (hl.mono (fun _ _ h => h.1) (fun _ _ h => h))

private theorem main_ct (ws : Bool) (τ : VG.RISCV64.Taint.T) {P : State → State → Prop}
    {setup tail : List Instr} {body : Prog isa}
    (ha : ∀ a b, P a b → VG.RISCV64.Taint.Agree τ a b)
    (hw : ∀ a b, P a b → WP isa (.block setup) a (Safe ws) ∧ WP isa (.block setup) b (Safe ws))
    (hb : RelCT isa (Pair ws (regs ws)) body (Pair ws (regs ws)))
    {hsetup htail : VG.Taint.Hint taint.T}
    (hsc : (taint.check τ (.block setup) hsetup).any (fun t => taint.le (regs ws) t) = true)
    (htc : (taint.check (regs ws) (.block tail) htail).isSome = true) :
    RelCT isa P (.seq (.block setup)
      (.seq (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6))) (.block tail))) (fun _ _ => True) := by
  have hs : RelCT isa P (.block setup) (Pair ws (regs ws)) :=
    ((taint_post τ (regs ws) hsc).mono ha (fun _ _ h => h) |>.wp hw).mono
      (fun _ _ h => h) (fun _ _ ⟨hag, sa, sb⟩ => ⟨sa, sb, hag⟩)
  exact RelCT.seq hs (RelCT.seq (runLoop_ct ws hb)
    (RelCT.taint (A := taint) (regs ws) (fun _ _ h => h.2.2) htc))

private theorem stackSafe {s₀ s : State} (hk : Stk s₀) (st : Addr)
    (hsp : s.sp = B s₀) (h2 : s.gpr .s2 = st) (hd : (KR s₀).Disjoint ⟨st, 200⟩)
    (hm : ⟨st, 200⟩ ∈ s.wr) (hf : BR s₀ ∈ s.wr) : Safe false s := by
  refine ⟨by rw [hsp]; exact hk.B_al, by rw [hsp]; exact hk.B_608, ?_, ?_, ?_, ?_⟩
  · simpa only [scratch, Bool.false_eq_true, ite_false, h2, hsp] using hd.symm.sub_right hk.scr_sub
  · rw [hsp, h2]; exact hd.sub_left hk.below_sub
  · simp only [scratch, Bool.false_eq_true, ite_false, hsp]
    exact (Offset.base_disjoint_below (B s₀) (n := 608) (k := 512) (by omega)).symm
  · simp only [scratch, Bool.false_eq_true, ite_false, h2, hsp]
    refine Covers.pair (Covers.of_mem (fun r hr => ?_)) (Covers.of_sub (fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst r; exact hm
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨BR s₀, hf, 0, by simp, by change 0 + 512 ≤ 560; decide⟩

private theorem absorb_setup_safe {s : State} (hp : Absorb.Pre s) :
    WP isa (.block setup) (allocd 560 s) (Safe false) :=
  WP.mono (Absorb.prologue_ok hp) fun t h => stackSafe hp.stk (s.gpr .a0) h.sp h.s2 hp.k_st
    (by rw [h.wr]; simp [Absorb.stR, Absorb.st]) (by rw [h.wr]; exact List.mem_cons_self ..)

private theorem squeeze_setup_safe {s : State} (hp : Squeeze.SPre s) :
    WP isa (.block setup) (allocd 560 s) (Safe false) :=
  WP.mono (Squeeze.prologue_ok hp) fun t h => stackSafe hp.stk (s.gpr .a0) h.sp h.s2 hp.k_st
    (by rw [h.wr]; simp [Squeeze.SR, Squeeze.stp]) (by rw [h.wr]; exact List.mem_cons_self ..)

private theorem ws_setup_safe {s : State} (hp : AbsorbWs.Pre s) : WP isa (.block setupWs) s (Safe true) := by
  refine WP.mono (AbsorbWs.prologue_ok hp) fun t h => ?_
  refine ⟨by rw [h.sp]; exact hp.sp_al, by rw [h.sp]; exact hp.sp, ?_, ?_, ?_, ?_⟩
  · simpa only [scratch, ite_true, h.s2, h.s7] using hp.st_scr
  · rw [h.sp, h.s2]; exact hp.p_st
  · simpa only [scratch, ite_true, h.sp, h.s7] using hp.p_scr
  · simp only [scratch, ite_true, h.s2, h.s7, h.wr]
    refine Covers.pair (Covers.of_mem (fun r hr => ?_)) (Covers.of_sub (fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self ..
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨AbsorbWs.wsR s, by simp, 0, by simp, by change 0 + 512 ≤ 640; decide⟩

private theorem alloc_eq {s t : State} (h : isa.push (.alloc 560) s = some t) : t = allocd 560 s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

private theorem withLoop_ct {Pre : State → Prop} {Pub : State → State → Prop} {body : Prog isa}
    (hb : RelCT isa (Pair false (regs false)) body (Pair false (regs false)))
    (hs : ∀ s, Pre s → WP isa (.block setup) (allocd 560 s) (Safe false))
    (hp : ∀ a b, Pub a b → VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) a b) :
    ConstantTime isa Pre Pub (withLoop body) := by
  intro a b t u a' b' pa pb hpab e₁ e₂
  have hab := hp a b hpab
  have hm : RelCT isa (fun x y => x = allocd 560 a ∧ y = allocd 560 b)
      (.seq (.block setup)
        (.seq (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6))) (.block (mov .a0 .s4 :: restore))))
      (fun _ _ => True) := by
    refine main_ct (P := fun x y => x = allocd 560 a ∧ y = allocd 560 b) false (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ ?_ hb
      (by taint_decide) (by taint_decide)
    · intro x y hxy
      rw [hxy.1, hxy.2]
      exact ⟨congrArg (fun p : Addr => p - 560) hab.1, fun r hr => hab.2 r hr⟩
    · intro x y hxy
      rw [hxy.1, hxy.2]
      exact ⟨hs a pa, hs b pb⟩
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_eq p₁
      obtain rfl := alloc_eq p₂
      have heq := (hm _ _ _ _ _ _ ⟨rfl, rfl⟩ b₁ b₂).1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using heq

private theorem ws_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hs : ∀ s, Pre s → WP isa (.block setupWs) s (Safe true))
    (hp : ∀ a b, Pub a b → VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) a b) :
    ConstantTime isa Pre Pub absorbWs := by
  apply RelCT.constantTime
  refine main_ct (P := fun a b => Pre a ∧ Pre b ∧ Pub a b) true (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) ?_ ?_ (absorb_body_ct true)
    (by taint_decide) (by taint_decide)
  · intro a b h; exact hp a b h.2.2
  · intro a b h; exact ⟨hs a h.1, hs b h.2.1⟩

end CT

/-! ## `absorb` -/

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbRISCV64.pre Proof.Sha3.absorbRISCV64.pub
    Impl.Sha3.RISCV64.Stream.absorb := by
  refine CT.withLoop_ct (CT.absorb_body_ct false) (fun s hs => CT.absorb_setup_safe (Absorb.pre_of hs)) ?_
  intro s₁ s₂ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- A state satisfying `absorb`'s precondition, with no data. -/
def absorbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩]

theorem absorb_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.absorb Proof.Sha3.absorbRISCV64 := by
  refine ⟨fun s hs => ?_, absorb_ct, absorbSat, rfl, rfl, ?_, by decide, by decide, ?_, ?_,
    by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Absorb.correct (Absorb.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `absorbWs` -/

theorem absorbWs_ct : ConstantTime isa Proof.Sha3.absorbWsRISCV64.pre Proof.Sha3.absorbWsRISCV64.pub
    Impl.Sha3.RISCV64.Stream.absorbWs := by
  refine CT.ws_ct (fun s hs => CT.ws_setup_safe (AbsorbWs.pre_of hs)) ?_
  intro s₁ s₂ ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

/-- A state satisfying `absorbWs`'s precondition, with no data. -/
def absorbWsSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | .a5 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorbWs_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.absorbWs Proof.Sha3.absorbWsRISCV64 := by
  refine ⟨fun s hs => ?_, absorbWs_ct, absorbWsSat, rfl, rfl, ?_, ?_, ?_, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_, by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := AbsorbWs.correct (AbsorbWs.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

/-! ## `pad` -/

theorem pad_ct : ConstantTime isa Proof.Sha3.padRISCV64.pre Proof.Sha3.padRISCV64.pub
    Impl.Sha3.RISCV64.Stream.pad := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

/-- A state satisfying `pad`'s precondition. -/
def padSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 136 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩]

theorem pad_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.pad Proof.Sha3.padRISCV64 := by
  refine ⟨fun s hs => ?_, pad_ct, padSat, rfl, rfl, by decide, by decide, ?_, by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Pad.correct (Pad.pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact Region.disjoint_of_sep (by decide)

/-! ## `squeeze` -/

theorem squeeze_ct : ConstantTime isa Proof.Sha3.squeezeRISCV64.pre Proof.Sha3.squeezeRISCV64.pub
    Impl.Sha3.RISCV64.Stream.squeeze := by
  refine CT.withLoop_ct CT.squeeze_body_ct (fun s hs => CT.squeeze_setup_safe (Squeeze.pre_of hs)) ?_
  intro s₁ s₂ ⟨h0, h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- A state satisfying `squeeze`'s precondition, with no output. -/
def squeezeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 72 | .a3 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩]

theorem squeeze_verified' :
    Verified RISCV64.target Impl.Sha3.RISCV64.Stream.squeeze Proof.Sha3.squeezeRISCV64 := by
  refine ⟨fun s hs => ?_, squeeze_ct, squeezeSat, rfl, rfl, ?_, by decide, by decide, ?_, ?_,
    by decide, by decide⟩
  · obtain ⟨t, s', he, h⟩ := Squeeze.correct (Squeeze.pre_of hs)
    exact ⟨t, s', he, h⟩
  all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.RISCV64.Stream
