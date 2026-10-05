import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Rounds`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (innerBlock)
abbrev Rows := VG.Proof.ChaCha20.AArch64.Rows6.Rows
abbrev N := VG.Proof.ChaCha20.AArch64.Rows6.Holds
abbrev C := VG.Proof.ChaCha20.AArch64.Holds
abbrev RI := VG.Proof.ChaCha20.AArch64.RI
abbrev VS := (Nat → VG.Proof.ChaCha20.AArch64.Mixed8.Rows) × CState

variable {sve : Bool}

def step (v : VG.Proof.ChaCha20.AArch64.Mixed8.VS) : Op → VG.Proof.ChaCha20.AArch64.Mixed8.VS
  | .vector op => (VG.Proof.ChaCha20.AArch64.Rows6.step v.1 op,v.2)
  | .scalar op => (v.1,VG.Proof.ChaCha20.AArch64.Neon4.step v.2 op)

def Valid : Op → Prop
  | .vector _ => True
  | .scalar op => VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op

theorem op_ok (op : Op) (hp : VG.Proof.ChaCha20.AArch64.Mixed8.Valid op) {v : VG.Proof.ChaCha20.AArch64.Mixed8.VS} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed8.N v.1 s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v.2 s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block (op.code sve)) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Mixed8.step v op).1 u ∧ VG.Proof.ChaCha20.AArch64.Mixed8.RI (VG.Proof.ChaCha20.AArch64.Mixed8.step v op).2 s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  cases op with
  | vector op =>
    refine (VG.Proof.ChaCha20.AArch64.Rows6.op_ok_for sve op hn ht).mono fun u ⟨hu,hs⟩ => ?_
    have hcu : VG.Proof.ChaCha20.AArch64.Mixed8.C v.2 u := by simpa only [VG.Proof.ChaCha20.AArch64.Mixed8.C,VG.Proof.ChaCha20.AArch64.Holds,hs.gpr] using hc
    exact ⟨hu,⟨hcu,hs.mem,hs.rd,hs.wr,fun r _ => congrFun hs.gpr r⟩,hs.sp,hs.v30.trans ht⟩
  | scalar op =>
    refine (VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.scalar_op op hp hc).mono
      fun u ⟨hu,hv,hsp⟩ => ?_
    have hnu : VG.Proof.ChaCha20.AArch64.Mixed8.N v.1 u := by simpa only [VG.Proof.ChaCha20.AArch64.Mixed8.N,VG.Proof.ChaCha20.AArch64.Rows6.Holds,hv] using hn
    exact ⟨hnu,hu,hsp,by rw [hv]; exact ht⟩

theorem ops_ok (ops : List Op) (hp : ∀ op ∈ ops, VG.Proof.ChaCha20.AArch64.Mixed8.Valid op) {v : VG.Proof.ChaCha20.AArch64.Mixed8.VS} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed8.N v.1 s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v.2 s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (scheduled sve ops) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.N (ops.foldl VG.Proof.ChaCha20.AArch64.Mixed8.step v).1 u ∧ VG.Proof.ChaCha20.AArch64.Mixed8.RI (ops.foldl VG.Proof.ChaCha20.AArch64.Mixed8.step v).2 s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  induction ops generalizing v s with
  | nil => exact WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | cons op ops ih =>
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.op_ok op (hp _ (List.mem_cons_self ..)) hn hc ht).mono fun a ⟨ha,hr,hsp,hat⟩ => ?_
    refine (ih (fun p h => hp p (List.mem_cons_of_mem _ h)) ha hr.holds hat).mono
      fun u ⟨hu,hau,hsp',hut⟩ => ?_
    exact ⟨hu,⟨hau.holds,hau.mem.trans hr.mem,hau.rd.trans hr.rd,hau.wr.trans hr.wr,
      fun r hr' => (hau.keep r hr').trans (hr.keep r hr')⟩,hsp'.trans hsp,hut⟩

theorem scalar_fold (ss : List VG.Impl.ChaCha20.AArch64.Neon4.Op) (v : VG.Proof.ChaCha20.AArch64.Mixed8.VS) :
    ((ss.map Op.scalar).foldl VG.Proof.ChaCha20.AArch64.Mixed8.step v) =
      (v.1,ss.foldl VG.Proof.ChaCha20.AArch64.Neon4.step v.2) := by
  induction ss generalizing v with
  | nil => rfl
  | cons op ss ih => simpa only [List.map_cons,List.foldl_cons,VG.Proof.ChaCha20.AArch64.Mixed8.step] using ih (VG.Proof.ChaCha20.AArch64.Mixed8.step v (.scalar op))

theorem interleave_fold (vs : List VG.Impl.ChaCha20.AArch64.Rows6.Op)
    (ss : List VG.Impl.ChaCha20.AArch64.Neon4.Op) (v : VG.Proof.ChaCha20.AArch64.Mixed8.VS) :
    (interleave vs ss).foldl VG.Proof.ChaCha20.AArch64.Mixed8.step v =
      (vs.foldl VG.Proof.ChaCha20.AArch64.Rows6.step v.1,
        ss.foldl VG.Proof.ChaCha20.AArch64.Neon4.step v.2) := by
  induction vs generalizing ss v with
  | nil => exact VG.Proof.ChaCha20.AArch64.Mixed8.scalar_fold ss v
  | cons op vs ih =>
    cases ss with
    | nil => simpa only [interleave,List.foldl_cons,List.foldl_nil,VG.Proof.ChaCha20.AArch64.Mixed8.step] using ih [] (VG.Proof.ChaCha20.AArch64.Mixed8.step v (.vector op))
    | cons p ss =>
      simpa only [interleave,List.foldl_cons,VG.Proof.ChaCha20.AArch64.Mixed8.step] using ih ss (VG.Proof.ChaCha20.AArch64.Mixed8.step (VG.Proof.ChaCha20.AArch64.Mixed8.step v (.vector op)) (.scalar p))

theorem interleave_valid (vs : List VG.Impl.ChaCha20.AArch64.Rows6.Op)
    (ss : List VG.Impl.ChaCha20.AArch64.Neon4.Op)
    (hp : ∀ op ∈ ss, VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op) :
    ∀ op ∈ interleave vs ss, VG.Proof.ChaCha20.AArch64.Mixed8.Valid op := by
  induction vs generalizing ss with
  | nil =>
    intro op h
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp h
    exact hp p hp'
  | cons p vs ih =>
    cases ss with
    | nil =>
      intro op h
      simp only [interleave,List.mem_cons] at h
      rcases h with rfl | h
      · trivial
      · exact ih [] hp op h
    | cons q ss =>
      intro op h
      simp only [interleave,List.mem_cons] at h
      rcases h with rfl | rfl | h
      · trivial
      · exact hp q (List.mem_cons_self ..)
      · exact ih ss (fun q h => hp q (List.mem_cons_of_mem _ h)) op h

theorem parallelRound_ok {blocks : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (parallelRound sve) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => innerBlock (blocks b))) u ∧
      VG.Proof.ChaCha20.AArch64.Mixed8.RI (innerBlock (innerBlock v)) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  have hv : ∀ op ∈ roundOps, VG.Proof.ChaCha20.AArch64.Mixed8.Valid op := VG.Proof.ChaCha20.AArch64.Mixed8.interleave_valid _ _ (by
    intro op h
    rcases List.mem_append.mp h with h | h <;>
      exact VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.roundOps_valid op h)
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.ops_ok roundOps hv (v := (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks,v)) hn hc ht).mono
    fun u ⟨hu,hr,hsp,hut⟩ => ?_
  have hf := VG.Proof.ChaCha20.AArch64.Mixed8.interleave_fold VG.Impl.ChaCha20.AArch64.Rows6.roundOps
    (VG.Impl.ChaCha20.AArch64.Mixed5.roundOps ++ VG.Impl.ChaCha20.AArch64.Mixed5.roundOps)
    (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks,v)
  change roundOps.foldl VG.Proof.ChaCha20.AArch64.Mixed8.step (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks,v) = _ at hf
  rw [hf] at hu hr
  have hs : (VG.Impl.ChaCha20.AArch64.Mixed5.roundOps ++
      VG.Impl.ChaCha20.AArch64.Mixed5.roundOps).foldl
      VG.Proof.ChaCha20.AArch64.Neon4.step v = innerBlock (innerBlock v) := by
    rw [List.foldl_append]
    simp only [VG.Impl.ChaCha20.AArch64.Mixed5.roundOps,
      VG.Proof.ChaCha20.AArch64.Neon4.innerBlock_eq]
  change VG.Proof.ChaCha20.AArch64.Mixed8.RI ((VG.Impl.ChaCha20.AArch64.Mixed5.roundOps ++
      VG.Impl.ChaCha20.AArch64.Mixed5.roundOps).foldl
      VG.Proof.ChaCha20.AArch64.Neon4.step v) s u at hr
  rw [hs] at hr
  refine ⟨?_,hr,hsp,hut⟩
  intro k j hj
  exact (hu k j hj).trans (VG.Proof.ChaCha20.AArch64.Rows6.round_eq blocks k j hj)

theorem rounds_ok {blocks : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    ∀ n, WP isa (rounds sve n) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack
        (fun b => Nat.repeat innerBlock n (blocks b))) u ∧
      VG.Proof.ChaCha20.AArch64.Mixed8.RI (Nat.repeat (fun x => innerBlock (innerBlock x)) n v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  | 0 => WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | n + 1 => by
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.rounds_ok hn hc ht n).mono fun a ⟨ha,hra,hspa,hat⟩ => ?_
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.parallelRound_ok ha hra.holds hat).mono fun u ⟨hu,hru,hspu,hut⟩ => ?_
    exact ⟨hu,⟨hru.holds,hru.mem.trans hra.mem,hru.rd.trans hra.rd,hru.wr.trans hra.wr,
      fun r hr => (hru.keep r hr).trans (hra.keep r hr)⟩,hspu.trans hspa,hut⟩

theorem phase_ok {blocks : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (rounds sve 5) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack
        (fun b => Nat.repeat innerBlock 5 (blocks b))) u ∧
      VG.Proof.ChaCha20.AArch64.Mixed8.RI (Nat.repeat innerBlock 10 v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  have he (f : CState → CState) (x : CState) :
      Nat.repeat (fun x => f (f x)) 5 x = Nat.repeat f 10 x := rfl
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.rounds_ok hn hc ht 5).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  rw [he innerBlock v] at hr
  exact ⟨hu,hr,hsp,hut⟩

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (innerBlock)
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1)

variable {sve : Bool}

/-- Arithmetic state during the counted phase; x1 holds its public counter. -/
structure PhaseInv (blocks : Nat → CState) (v : CState) (s₀ s : State) (i : Nat) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun b => Nat.repeat innerBlock i (blocks b))) s
  scalar : VG.Proof.ChaCha20.AArch64.Mixed8.C (Nat.repeat (fun x => innerBlock (innerBlock x)) i v) s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table

theorem PhaseInv.writeCounter {blocks : Nat → CState} {v : CState} {s₀ s : State} {i : Nat}
    (h : VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ s i) (c : BitVec 64) :
    VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ (s.write .x .x1 c) i := by
  refine ⟨h.vec,?_,h.mem,h.rd,h.wr,?_,h.sp,h.table⟩
  · intro k hk
    rw [RegUpd.gpr_write_of_ne s .x c (by
      intro he; exact not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  · intro r hr hn
    rw [RegUpd.gpr_write_of_ne s .x c hn]
    exact h.keep r hr hn

theorem phase_loop_ok {blocks : Nat → CState} {v : CState} {s₀ s : State}
    (h : VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ s 0) (hx : s.gpr .x1 = 5) :
    WP isa (.loop (.seq (parallelRound sve) (.block [.subImm .x .x1 .x1 1])) (.nonzero .x .x1)) s
      (fun u => VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ u 5) := by
  let Inv : Nat → State → Prop := fun n a =>
    ∃ i, i < 5 ∧ n = 5 - i ∧ VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ a i ∧
      a.gpr .x1 = BitVec.ofNat 64 (5 - i)
  have hstep : ∀ n a, Inv n a → WP isa
      (.seq (parallelRound sve) (.block [.subImm .x .x1 .x1 1])) a (fun u =>
      (eval (.nonzero .x .x1) u = some false ∧ VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ u 5) ∨
      (eval (.nonzero .x .x1) u = some true ∧ ∃ m < n, Inv m u)) := by
    rintro n a ⟨i,hi,rfl,ha,hcount⟩
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.parallelRound_ok ha.vec ha.scalar ha.table).mono fun b ⟨hb,hc,hsp,ht⟩ => ?_
    have hnext : VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s₀ b (i + 1) :=
      ⟨hb,hc.holds,hc.mem.trans ha.mem,hc.rd.trans ha.rd,hc.wr.trans ha.wr,
        fun r hr hn => (hc.keep r hr).trans (ha.keep r hr hn),hsp.trans ha.sp,ht⟩
    have hbc : b.gpr .x1 = BitVec.ofNat 64 (5 - i) :=
      (hc.keep _ not_words_x1).trans hcount
    let u := b.write .x .x1 (b.gpr .x1 - BitVec.ofNat 64 1)
    have hu := hnext.writeCounter (b.gpr .x1 - BitVec.ofNat 64 1)
    have huc : u.gpr .x1 = BitVec.ofNat 64 (5 - (i + 1)) := by
      rw [RegUpd.gpr_write_self,BitVec.setWidth_eq,hbc,
        Offset.ofNat_sub_ofNat (by omega : 1 ≤ 5 - i)]
      simp only [Nat.sub_sub]
    apply WP.block_cons_iff.mpr
    refine ⟨u,?_,WP.block_nil ?_⟩
    · simpa only [State.read,BitVec.setWidth_eq] using
        exec_subImm_x (s := b) (d := .x1) (n := .x1) (imm := 1) (by decide)
    · have he : eval (.nonzero .x .x1) u = some (BitVec.ofNat 64 (5 - (i + 1)) != 0) := by
        simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,huc]
      by_cases hl : i + 1 = 5
      · exact .inl ⟨by rw [he,hl]; rfl,hl ▸ hu⟩
      · have hn : BitVec.ofNat 64 (5 - (i + 1)) ≠ 0 := by
          intro hz
          have hz' := congrArg BitVec.toNat hz
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 5 - (i + 1) < 2 ^ 64)] at hz'
          change 5 - (i + 1) = 0 at hz'
          omega
        exact .inr ⟨by rw [he]; simpa using hn,
          5 - (i + 1),by omega,i + 1,by omega,rfl,hu,huc⟩
  exact WP.loop (M := isa) Inv hstep 5 s ⟨0,by decide,rfl,h,hx⟩

theorem counted_phase_ok {blocks : Nat → CState} {v : CState} {s : State} {restore : Reg}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hr : ¬ Words restore) (hr1 : restore ≠ .x1)
    (hx : s.gpr .x1 = s.gpr restore) :
    WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.phase sve restore) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.N (VG.Proof.ChaCha20.AArch64.Rows6.pack
        (fun b => Nat.repeat innerBlock 5 (blocks b))) u ∧
      VG.Proof.ChaCha20.AArch64.Mixed8.RI (Nat.repeat innerBlock 10 v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  unfold VG.Impl.ChaCha20.AArch64.Mixed8.phase
  apply WP.seq
  have hi : VG.Proof.ChaCha20.AArch64.Mixed8.PhaseInv blocks v s s 0 := ⟨hn,hc,rfl,rfl,rfl,fun _ _ _ => rfl,rfl,ht⟩
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x .x1 5,?_,WP.block_nil ?_⟩
  · rfl
  · apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.phase_loop_ok (hi.writeCounter 5) (by rw [RegUpd.gpr_write_self,BitVec.setWidth_eq])).mono
      fun a ha => ?_
    apply WP.block_cons_iff.mpr
    refine ⟨a.write .x .x1 (a.gpr restore),?_,WP.block_nil ?_⟩
    · simpa only [State.read,BitVec.setWidth_eq,BitVec.add_zero] using
        exec_addImm_x (s := a) (d := .x1) (n := restore) (imm := 0) (by decide)
    · have hu := ha.writeCounter (a.gpr restore)
      have hs := hu.scalar
      have he (f : CState → CState) (x : CState) :
          Nat.repeat (fun x => f (f x)) 5 x = Nat.repeat f 10 x := rfl
      rw [he innerBlock v] at hs
      refine ⟨hu.vec,⟨hs,hu.mem,hu.rd,hu.wr,?_⟩,hu.sp,hu.table⟩
      intro r hnr
      by_cases h1 : r = .x1
      · subst r
        rw [RegUpd.gpr_write_self,BitVec.setWidth_eq,ha.keep restore hr hr1,hx]
      · exact hu.keep r hnr h1

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Prepare`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs saveArgs_ok counter_ok keeps_vectors scalarLoad_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock)

abbrev source (s : State) : CState := stateAt s.mem (s.gpr .x0)
abbrev sr (s : State) : Region := ⟨s.gpr .x0,64⟩
abbrev br (s : State) : Region := ⟨s.gpr .x3,320⟩
abbrev dr (s : State) : Region := ⟨s.gpr .x1,512⟩

structure CP (s : State) : Prop where
  x20 : s.gpr .x20 = s.gpr .x3
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  vectorRead : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
    (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 512 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (VG.Proof.ChaCha20.AArch64.Mixed8.sr s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed8.br s)
  st_d : (VG.Proof.ChaCha20.AArch64.Mixed8.sr s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed8.dr s)
  d_b : (VG.Proof.ChaCha20.AArch64.Mixed8.dr s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed8.br s)

structure Prepared (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun j => Nat.repeat innerBlock n (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock (2 * n) (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6)) s
  cnt : VG.Proof.ChaCha20.AArch64.Mixed8.source s = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀] s₀.mem s.mem

 theorem prepare_ok (s : State) (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s) : WP isa prepare s (VG.Proof.ChaCha20.AArch64.Mixed8.Prepared s) := by
  apply WP.seq
  refine (saveArgs_ok s).mono fun a ⟨hsaved,hg,hm₀,hr,hw,hv,hsp⟩ => ?_
  have ha : VG.Proof.ChaCha20.AArch64.Mixed8.source a = VG.Proof.ChaCha20.AArch64.Mixed8.source s := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hm₀,hg _ (by decide) (by decide)]
  have hi : ∀ k : Fin 24, InRegions (a.rd ++ a.wr)
      (a.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [hg _ (by decide) (by decide),hr,hw]; exact hp.vectorRead k
  have hca : InRegions (a.rd ++ a.wr) (a.gpr .x0 + 48) 4 := by
    change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4
    rw [hg _ (by decide) (by decide),hr,hw]; exact hp.read 12
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.setup_ok a hi hca).mono fun b ⟨hb,hab,hbt⟩ => ?_
  have h0 : b.gpr .x0 = s.gpr .x0 := by rw [hab.gpr _ (by decide),hg _ (by decide) (by decide)]
  have hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.rd,hab.wr,h0,hr,hw]; exact hp.read 12
  have hco : InRegions b.wr (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.wr,hw,h0]; exact hp.counter
  apply WP.seq
  refine (counter_ok b (n := 6) (by decide) false hc hco).mono fun c
    ⟨hcm,hcg,hcr,hcw,hcv,hcsp⟩ => ?_
  have hcnt : VG.Proof.ChaCha20.AArch64.Mixed8.source c = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s) 6 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hcg _ (by decide),hcm]
    change stateAt (b.mem.writeW (b.gpr .x0 + BitVec.ofNat 64 48)
      (b.mem.readW (b.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 6)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    change ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source b) 6 = _
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hab.mem,hab.gpr _ (by decide)]
    exact congrArg (fun v => ctr v 6) ha
  have hfc : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s] b.mem c.mem := by
    rw [hcm,h0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hcs : SavedArgs (s.gpr .x2) (s.gpr .x1) c := by
    exact ⟨by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.len,
      by rw [hcg _ (by decide),hab.gpr _ (by decide)]; exact hsaved.data⟩
  have hpc : VG.Proof.ChaCha20.AArch64.Pre c := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (c.rd ++ c.wr) (c.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcr,hcw,hab.rd,hab.wr,hr,hw,hcg _ (by decide),h0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hcw,hab.wr,hw,hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide)]
      exact hp.data _ _ (by omega)
    · change (⟨c.gpr .x1,256⟩ : Region).Disjoint ⟨c.gpr .x0,64⟩
      rw [hcg _ (by decide),hcg _ (by decide),hab.gpr _ (by decide),hg _ (by decide) (by decide),h0]
      exact hp.st_d.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 512))
  have hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i
    rfl
  refine (keeps_vectors hload (scalarLoad_ok c hpc)).mono fun d ⟨⟨hd,hm,hdrr,hdwr,hdk⟩,hdv,hdsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,hdrr.trans (hcr.trans (hab.rd.trans hr)),
    hdwr.trans (hcw.trans (hab.wr.trans hw)),hdsp.trans (hcsp.trans (hab.sp.trans hsp)),?_⟩
  · intro k j hj
    rw [hdv,hcv]
    have hbb : VG.Proof.ChaCha20.AArch64.Rows6.Holds
        (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source a) j)) b := hb
    rw [ha] at hbb
    exact hbb k j hj
  · rw [hdv,hcv,hbt]
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat] using hd
  · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hm,hdk _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact hcnt
  · exact ⟨by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.len,
      by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.data⟩
  · intro r hnr h21 h22
    rw [hdk r hnr,hcg r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),
      hab.gpr r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),hg r h21 h22]
  · rw [hm]
    rw [hab.mem,hm₀] at hfc
    exact hfc

theorem compute_ok {sve : Bool} (s : State) (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s) :
    WP isa (.seq prepare (rounds sve 5)) s fun u => VG.Proof.ChaCha20.AArch64.Mixed8.Prepared s u 5 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.prepare_ok s hp).mono fun a h => ?_
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.phase_ok h.vec h.scalar h.table).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
  refine ⟨hv,ht,hc.holds,?_,?_,?_,hc.rd.trans h.rd,hc.wr.trans h.wr,hsp.trans h.sp,?_⟩
  · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact h.cnt
  · exact ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩
  · intro r hr h21 h22; rw [hc.keep r hr,h.keep r hr h21 h22]
  · rw [hc.mem]; exact h.frame

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Spill`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs move_ok keeps_vectors scalarFinish_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev lowBuf (s : State) : Region := ⟨s.gpr .x3,64⟩

structure Spilled (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds
    (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 5 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  cnt : VG.Proof.ChaCha20.AArch64.Mixed8.source s = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  words : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.lowBuf s₀] s₀.mem s.mem

theorem spill_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Prepared s₀ s 5) :
    WP isa (spill 0) s (VG.Proof.ChaCha20.AArch64.Mixed8.Spilled s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide)
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (move_ok s .x1 .x20).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6)) a := by
    intro k hk
    rw [ha.other _ (by
      intro he; exact VG.Proof.ChaCha20.AArch64.not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  have hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.rd,ha.wr,h.rd,h.wr,ha.other _ (by decide),hx0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.wr,h.wr,ha.gpr,hx20]
      exact hp.buffer _ _ (by omega)
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by
    decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  have hfb : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.lowBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  have hcntₐ : VG.Proof.ChaCha20.AArch64.Mixed8.source a = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  have hcntb : VG.Proof.ChaCha20.AArch64.Mixed8.source b = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))]
    exact hcntₐ
  have hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,?_,hcntb,hsavedb,?_,?_,?_,
    hr.trans (ha.rd.trans h.rd),hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  · rw [hbv,hav]; exact h.table
  · intro k hkk
    have he := hb k hkk
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,VG.Spec.ChaCha20.block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr hr1 h21 h22; rw [hk r hnr,ha.other r hr1,h.keep r hnr h21 h22]
  · rw [hk _ VG.Proof.ChaCha20.AArch64.not_words_x1,ha.gpr,hx20]
  · rw [ha.mem] at hfb
    exact (h.frame.mono (by simp)).trans (hfb.mono (by simp))

theorem Spilled.read16 {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.Spilled s₀ s) (r : Fin 4) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6)) r := by
  rw [VG.AArch64.read16]
  have hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6))[4 * r.val + e]'(by omega) := by
    intro e he
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega]
    exact h.words _ (by omega)
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.mod_eq_of_lt r.isLt,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Second`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs counter_ok scalarLoad_ok keeps_vectors)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

variable {sve : Bool}

structure Second (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun j => Nat.repeat innerBlock (5 + n) (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock (2 * n) (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7)) s
  cnt : VG.Proof.ChaCha20.AArch64.Mixed8.source s = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  first : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 →
    s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.lowBuf s₀] s₀.mem s.mem

theorem reload_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Spilled s₀ s) :
    WP isa (.seq (.block (VG.Impl.ChaCha20.AArch64.Mixed5.counter 1))
      (.block VG.Impl.ChaCha20.AArch64.load)) s (VG.Proof.ChaCha20.AArch64.Mixed8.Second s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 :=
    h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.rd,h.wr,hx0]; exact hp.read 12
  have ho : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.wr,hx0]; exact hp.counter
  apply WP.seq
  refine (counter_ok s (n := 1) (by decide) false hc ho).mono fun a
    ⟨hm,hg,hr,hw,hv,hsp⟩ => ?_
  have hcnt : VG.Proof.ChaCha20.AArch64.Mixed8.source a = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hg _ (by decide),hm]
    change stateAt (s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 48)
      (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 1)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    change ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s) 1 = _
    rw [h.cnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add]
  have hf : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀] s.mem a.mem := by
    rw [hm,hx0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hfirst : ∀ k (hk : k < 16),
      a.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
        (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6))[k] := by
    intro k hk
    rw [hf.readW (r := VG.Proof.ChaCha20.AArch64.Mixed8.lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro r hr'; have he := List.mem_singleton.mp hr'; subst r
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide)]
    exact h.words k hk
  have hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [hr,hw,h.rd,h.wr,hg _ (by decide),hx0]; exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [hw,h.wr,hg _ (by decide),h.x1]; exact hp.buffer _ _ (by omega)
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [hg _ (by decide),h.x1,hg _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i; rfl
  refine (keeps_vectors hload (scalarLoad_ok a hpₐ)).mono fun b
    ⟨⟨hb,hbm,hbr,hbw,hbk⟩,hbv,hbsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hbr.trans (hr.trans h.rd),
    hbw.trans (hw.trans h.wr),hbsp.trans (hsp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hv,Nat.add_zero] using h.vec
  · rw [hbv,hv]; exact h.table
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat,Nat.mul_zero] using hb
  · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hbm,hbk _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact hcnt
  · exact ⟨by rw [hbk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),hg _ (by decide)]; exact h.saved.len,
      by rw [hbk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),hg _ (by decide)]; exact h.saved.data⟩
  · rw [hbm]; exact hfirst
  · intro r hnr h1 h19 h26
    rw [hbk r hnr,hg r (by intro he; subst r; exact hnr ⟨2,by decide,rfl⟩)]
    exact h.keep r hnr h1 h19 h26
  · rw [hbk _ VG.Proof.ChaCha20.AArch64.not_words_x1,hg _ (by decide)]; exact h.x1
  · rw [hbm]; exact h.frame.trans (hf.mono (by simp))

theorem second_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Prepared s₀ s 5) :
    WP isa second s (VG.Proof.ChaCha20.AArch64.Mixed8.Second s₀) := by
  apply WP.seq
  exact (VG.Proof.ChaCha20.AArch64.Mixed8.spill_ok hp h).mono fun _ h => VG.Proof.ChaCha20.AArch64.Mixed8.reload_ok hp h

theorem compute_second_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Second s₀ s) :
    WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.phase sve .x20) s fun u => VG.Proof.ChaCha20.AArch64.Mixed8.Second s₀ u 5 := by
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.counted_phase_ok h.vec h.scalar h.table
    (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)) (by decide)
    (h.x1.trans ((h.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))
      (by decide) (by decide) (by decide)).trans hp.x20).symm)).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  have he (f : CState → CState) (x : CState) : Nat.repeat f 5 (Nat.repeat f 5 x) = Nat.repeat f 10 x := rfl
  have hv : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) u := by
    have he' : (fun j => Nat.repeat innerBlock 5 (Nat.repeat innerBlock 5 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) =
        (fun j => Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j)) :=
      funext fun j => he innerBlock (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j)
    rw [he'] at hu
    exact hu
  refine ⟨hv,hut,hr.holds,?_,?_,?_,?_,?_,hr.rd.trans h.rd,hr.wr.trans h.wr,hsp.trans h.sp,?_⟩
  · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hr.mem,hr.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact h.cnt
  · exact ⟨by rw [hr.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hr.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩
  · rw [hr.mem]; exact h.first
  · intro r hnr h1 h19 h26; rw [hr.keep r hnr]; exact h.keep r hnr h1 h19 h26
  · rw [hr.keep _ VG.Proof.ChaCha20.AArch64.not_words_x1]; exact h.x1
  · rw [hr.mem]; exact h.frame

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Spill2`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs keeps_vectors scalarFinish_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev scalarBuf (s : State) : Region := ⟨s.gpr .x3,128⟩
abbrev highBuf (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 64,64⟩

theorem move_offset_ok (s : State) (d n : Reg) (offset : Nat) (ho : offset < 4096) :
    WP isa (.block [.addImm .x d n offset]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u d (s.gpr n + BitVec.ofNat 64 offset) ∧
      u.v = s.v ∧ u.sp = s.sp := by
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 offset),?_,
    WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
  simpa only [State.read,BitVec.setWidth_eq] using
    exec_addImm_x (s := s) (d := d) (n := n) (imm := offset) ho

structure Spilled2 (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds
    (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) s
  cnt : VG.Proof.ChaCha20.AArch64.Mixed8.source s = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  first : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 6))[k]
  last : ∀ k (hk : k < 16), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k)) 32 =
    (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 →
    s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀] s₀.mem s.mem

theorem spill2_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Second s₀ s 5) :
    WP isa (spill 64) s (VG.Proof.ChaCha20.AArch64.Mixed8.Spilled2 s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 :=
    h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 :=
    (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.move_offset_ok s .x1 .x20 64 (by decide)).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7)) a := by
    intro k hk
    rw [ha.other _ (by
      intro he; exact VG.Proof.ChaCha20.AArch64.not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  have hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.rd,ha.wr,h.rd,h.wr,ha.other _ (by decide),hx0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.wr,h.wr,ha.gpr,hx20,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hp.buffer _ _ (by omega)
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Offset.sub_base _ (by decide : 64 + 256 ≤ 320))
  have hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  have hfb : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.highBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  have hcntₐ : VG.Proof.ChaCha20.AArch64.Mixed8.source a = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  have hcntb : VG.Proof.ChaCha20.AArch64.Mixed8.source b = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Offset.sub_base _ (by decide : 64 + 64 ≤ 320)))]
    exact hcntₐ
  have hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,hcntb,hsavedb,?_,?_,?_,hr.trans (ha.rd.trans h.rd),
    hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  · intro k hk'
    rw [hfb.readW (r := VG.Proof.ChaCha20.AArch64.Mixed8.lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro r hr'; have he := List.mem_singleton.mp hr'; subst r
          exact Offset.base_disjoint _ (by decide : 64 ≤ 64) (by decide : 64 + 64 ≤ 2 ^ 64)) (by decide),ha.mem]
    exact h.first k hk'
  · intro k hk'
    have he := hb k hk'
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,VG.Spec.ChaCha20.block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr h1 h19 h26; rw [hk r hnr,ha.other r h1]; exact h.keep r hnr h1 h19 h26
  · rw [ha.mem] at hfb
    have hf₀ : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr'; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,by simp,fun _ h => h⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀,by simp,Region.sub_prefix (by decide : 64 ≤ 128)⟩)
    exact hf₀.trans (hfb.sub (by
      intro r hr'; have he := List.mem_singleton.mp hr'; subst r
      exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀,by simp,Offset.sub_base _ (by decide : 64 + 64 ≤ 128)⟩))

theorem Spilled2.words {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.Spilled2 s₀ s) (k : Nat) (hk : k < 32) :
    s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
      (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) (6 + k / 16)))[k % 16]'(by omega) := by
  by_cases hk' : k < 16
  · simpa only [Nat.div_eq_of_lt hk',Nat.mod_eq_of_lt hk',Nat.add_zero] using h.first k hk'
  · have he := h.last (k - 16) (by omega)
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 64 + 4 * (k - 16) = 4 * k by omega] at he
    simpa only [show k / 16 = 1 by omega,show k % 16 = k - 16 by omega] using he

theorem Spilled2.read16 {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.Spilled2 s₀ s) (r : Fin 8) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun j => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) (6 + j))) r := by
  rw [VG.AArch64.read16]
  have hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) (6 + r.val / 4)))[4 * (r.val % 4) + e]'(by omega) := by
    intro e he
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega,
      h.words _ (by omega)]
    simp only [show (4 * r.val + e) / 16 = r.val / 4 by omega,
      show (4 * r.val + e) % 16 = 4 * (r.val % 4) + e by omega]
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Finish`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (restoreArgs_ok counter_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev firstR (s : State) : Region := ⟨s.gpr .x1,384⟩

structure Finished (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : VG.Proof.ChaCha20.AArch64.Mixed8.source s = VG.Proof.ChaCha20.AArch64.Mixed8.source s₀
  buf : ∀ r : Fin 8, s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
    VG.Proof.ChaCha20.AArch64.Neon4.output (fun j => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) (6 + j))) r
  data : ∀ k < 384, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀,VG.Proof.ChaCha20.AArch64.Mixed8.firstR s₀] s₀.mem s.mem

theorem finish_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Spilled2 s₀ s) :
    WP isa vectorFinish s (VG.Proof.ChaCha20.AArch64.Mixed8.Finished s₀) := by
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  apply WP.seq
  refine (restoreArgs_ok s h.saved).mono fun a
    ⟨ha1,ha2,ha3,hag,ham,har,haw,hav,hasp⟩ => ?_
  have ha0 : a.gpr .x0 = s₀.gpr .x0 := (hag _ (by decide) (by decide) (by decide)).trans hx0
  have ha₃ : a.gpr .x3 = s₀.gpr .x3 := ha3.trans hx20
  have har' : a.rd = s₀.rd := har.trans h.rd
  have haw' : a.wr = s₀.wr := haw.trans h.wr
  have hcnta : VG.Proof.ChaCha20.AArch64.Mixed8.source a = ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) 7 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,ham,hag _ (by decide) (by decide) (by decide)]; exact h.cnt
  have hc : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [har',haw',ha0]; exact hp.read 12
  have hco : InRegions a.wr (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [haw',ha0]; exact hp.counter
  apply WP.seq
  refine (counter_ok a (n := 7) (by decide) true hc hco).mono fun b
    ⟨hbm,hbg,hbr,hbw,hbv,hbsp⟩ => ?_
  have hb0 : b.gpr .x0 = s₀.gpr .x0 := (hbg _ (by decide)).trans ha0
  have hcntb : VG.Proof.ChaCha20.AArch64.Mixed8.source b = VG.Proof.ChaCha20.AArch64.Mixed8.source s₀ := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hbg _ (by decide),hbm]
    change stateAt (a.mem.writeW (a.gpr .x0 + BitVec.ofNat 64 48)
      (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 48) 32 - BitVec.ofNat 32 7)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      ← VG.Proof.ChaCha20.AArch64.Xor.stateAt_getElem_counter]
    change (VG.Proof.ChaCha20.AArch64.Mixed8.source a).set 12 ((VG.Proof.ChaCha20.AArch64.Mixed8.source a)[12] - BitVec.ofNat 32 7) = _
    rw [hcnta,ctr,Vector.getElem_set_self,BitVec.add_sub_cancel,Vector.set_set,
      Vector.set_getElem_self]
  have hfb : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀] a.mem b.mem := by
    rw [hbm,ha0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hv : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) b := by
    simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  have hin : ∀ k : Fin 24, InRegions (b.rd ++ b.wr)
      (b.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [hbr,hbw,har',haw',hb0]; exact hp.vectorRead k
  have hctr : InRegions (b.rd ++ b.wr) (b.gpr .x0 + 48) 4 := by
    change InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4
    rw [hbr,hbw,har',haw',hb0]; exact hp.read 12
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.feedForward_ok b hin hctr).mono fun c ⟨hvc,hbc⟩ => ?_
  have hcb0 : c.gpr .x0 = s₀.gpr .x0 := (hbc.gpr _ (by decide)).trans hb0
  have hcb1 : c.gpr .x1 = s₀.gpr .x1 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha1)
  have hcb3 : c.gpr .x3 = s₀.gpr .x3 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha₃)
  have hrc : c.rd = s₀.rd := hbc.rd.trans (hbr.trans har')
  have hwc : c.wr = s₀.wr := hbc.wr.trans (hbw.trans haw')
  have hvc' : VG.Proof.ChaCha20.AArch64.Rows6.Holds
      (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) j))) c := by
    intro k j hj
    rw [hvc k j hj,hv k j hj,VG.Proof.ChaCha20.AArch64.Rows6.input_ctr b k j hj]
    change _ + (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun q => ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source b) q) j)[k] = _
    rw [hcntb]
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.pack_get,VG.Spec.ChaCha20.block,Vector.getElem_zipWith]
  have hout : ∀ k : Fin 24, InRegions c.wr
      (c.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [hwc,hcb1]; exact hp.data _ _ (by omega)
  refine (VG.Proof.ChaCha20.AArch64.Rows6.finishBlocks_ok hvc' hout).mono fun d ⟨hd,hfd,hcd⟩ => ?_
  have hfd' : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.firstR s₀] c.mem d.mem := by simpa only [hcb1] using hfd
  have hfc : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀] s.mem c.mem := by rw [hbc.mem,← ham]; exact hfb
  have hpre : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀] s₀.mem c.mem :=
    h.frame.trans (hfc.mono (by simp))
  refine ⟨(congrFun hcd.gpr _).trans hcb0,(congrFun hcd.gpr _).trans hcb1,?_,
    (congrFun hcd.gpr _).trans hcb3,?_,hcd.rd.trans hrc,hcd.wr.trans hwc,
    hcd.sp.trans (hbc.sp.trans (hbsp.trans (hasp.trans h.sp))),?_,?_,?_,
    (hpre.mono (by simp)).trans (hfd'.mono (by simp))⟩
  · rw [hcd.gpr,hbc.gpr _ (by decide),hbg _ (by decide),ha2]
  · intro r hr h21 h22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n3 : r ≠ .x3 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    rw [hcd.gpr,hbc.gpr r n4,hbg r n4,hag r n1 n2 n3]
    exact h.keep r (VG.Proof.ChaCha20.AArch64.not_words_preserved hr) n1 h21 h22
  · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hcd.gpr,hcb0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfd' (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right (Region.sub_prefix (by decide : 384 ≤ 512))),hbc.mem]
    rw [← hb0]; exact hcntb
  · intro r
    rw [hfd'.read (r := VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact (hp.d_b.sub_left (Region.sub_prefix (by decide : 384 ≤ 512))).symm.sub_left
            (Region.sub_prefix (by decide : 128 ≤ 320))) (by decide),
      hfc.read (r := VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 128 ≤ 320))) (by decide)]
    exact h.read16 r
  · intro k hk
    rw [hcb1] at hd
    rw [hd k hk,hpre.bytes (R := VG.Proof.ChaCha20.AArch64.Mixed8.dr s₀) (by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      · exact hp.st_d.symm
      · exact hp.d_b.sub_right (Region.sub_prefix (by decide : 128 ≤ 320)))
      (by change 512 ≤ 2 ^ 64; decide) (by change k < 512; omega)]

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Rows6 (Data)

structure Same (s u : State) : Prop where
  gpr : u.gpr = s.gpr
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp

theorem Same.trans {s a u : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.Same s a) (h' : VG.Proof.ChaCha20.AArch64.Mixed8.Same a u) : VG.Proof.ChaCha20.AArch64.Mixed8.Same s u :=
  ⟨h'.gpr.trans h.gpr,h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp⟩

theorem xorScalarRow_ok (s : State) (k : Fin 8)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16) :
    WP isa (.block (xorScalarRow k)) s fun u =>
      u.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 ^^^
          s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16) ∧ VG.Proof.ChaCha20.AArch64.Mixed8.Same s u := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    obtain ⟨q,hq,hc⟩ := hout; exact ⟨q,List.mem_append_right _ hq,hc⟩
  have ha : (16 * k.val) % 16 = 0 ∧ 16 * k.val < 4096 * 16 := by omega
  have hb : (384 + 16 * k.val) % 16 = 0 ∧ 384 + 16 * k.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorScalarRow,runBlock_cons,runBlock_nil,exec,addr,
    ha,hb,and_self,ite_true,State.load,hin,hi,State.setV,VOp.eval,State.store,hout,
    Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem data_frame128 {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) (hd : ∀ k ∈ done, k < 8) : Frame [⟨p,128⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 128 := by
    have hh := hx ⟨p,128⟩ (by simp)
    simp only [Region.Contains] at hh
    omega
  rw [h x,ite_eq_right]
  intro hh
  have := hd _ hh.1
  omega

theorem xorScalarList_ok (ks : List (Fin 8)) (hn : ks.Nodup)
    {m₀ : Mem} {p b : Addr} {done : List Nat} {s : State}
    (h : Data m₀ s.mem p (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16) done)
    (hd : ∀ k ∈ done, k < 8) (hp : s.gpr .x1 + BitVec.ofNat 64 384 = p) (hbp : s.gpr .x3 = b)
    (hdis : (⟨b,128⟩ : Region).Disjoint ⟨p,128⟩)
    (hf : ∀ k ∈ ks, k.val ∉ done)
    (hin : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : ∀ k : Fin 8, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16) :
    WP isa (.block (ks.flatMap xorScalarRow)) s fun u =>
      Data m₀ u.mem p (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16)
        (ks.map Fin.val ++ done) ∧ VG.Proof.ChaCha20.AArch64.Mixed8.Same s u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h,⟨rfl,rfl,rfl,rfl⟩⟩
  | cons k ks ih =>
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.xorScalarRow_ok s k (hin k) (hout k)).mono fun a ⟨hm,hs⟩ => ?_
    have he : s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val) =
        p + BitVec.ofNat 64 (16 * k.val) := by rw [BitVec.ofNat_add,← BitVec.add_assoc,hp]
    have hr : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16 =
        m₀.read (b + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hbp]
      exact (VG.Proof.ChaCha20.AArch64.Mixed8.data_frame128 h hd).read (r := ⟨b,128⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hdis) (by decide)
    have ha : Data m₀ a.mem p (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16) (k.val :: done) := by
      rw [hm,he,hr]
      exact h.store (by omega) (hf k (List.mem_cons_self ..))
    have hf' : ∀ l ∈ ks, l.val ∉ k.val :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 ((Fin.ext he) ▸ hl),
        hf l (List.mem_cons_of_mem _ hl)⟩
    have hin' : ∀ l : Fin 8, InRegions (a.rd ++ a.wr) (a.gpr .x3 + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l; rw [hs.rd,hs.wr,hs.gpr]; exact hin l
    have hout' : ∀ l : Fin 8, InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (384 + 16 * l.val)) 16 := by
      intro l; rw [hs.wr,hs.gpr]; exact hout l
    refine (ih (List.nodup_cons.mp hn).2 ha (by
      intro l hl; simp only [List.mem_cons] at hl; rcases hl with rfl | hl
      · exact k.isLt
      · exact hd l hl) (by rw [hs.gpr]; exact hp) (by rw [hs.gpr]; exact hbp)
      hf' hin' hout').mono fun u ⟨hu,hsu⟩ => ⟨?_,hs.trans hsu⟩
    intro x
    simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Data,List.map_cons,List.cons_append,
      List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu x

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Chunk`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (serialize block)

variable {sve : Bool}

abbrev lastR (s : State) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 384,128⟩

structure Chunked (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : VG.Proof.ChaCha20.AArch64.Mixed8.source s = VG.Proof.ChaCha20.AArch64.Mixed8.source s₀
  data : ∀ k < 512, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed8.source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀,VG.Proof.ChaCha20.AArch64.Mixed8.dr s₀] s₀.mem s.mem

theorem last_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.Finished s₀ s) :
    WP isa (.block ((List.finRange 8).flatMap xorScalarRow)) s (VG.Proof.ChaCha20.AArch64.Mixed8.Chunked s₀) := by
  have hi : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k
    rw [h.rd,h.wr,h.x3]
    obtain ⟨r,hr,hc⟩ := hp.buffer (16 * k.val) 16 (by omega)
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have ho : ∀ k : Fin 8, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    intro k; rw [h.wr,h.x1]; exact hp.data _ _ (by omega)
  have hdis : (VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀) :=
    (hp.d_b.symm.sub_left (Region.sub_prefix (by decide : 128 ≤ 320))).sub_right
      (Offset.sub_base _ (by decide : 384 + 128 ≤ 512))
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.xorScalarList_ok (List.finRange 8) (List.nodup_finRange 8)
    (VG.Proof.ChaCha20.AArch64.Rows6.Data.nil s.mem (VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀).base _)
    (by intro k hk; cases hk) (by rw [h.x1]) h.x3 hdis
    (fun _ _ => List.not_mem_nil) hi ho).mono fun u ⟨hu,hs⟩ => ?_
  have hf : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀] s.mem u.mem := VG.Proof.ChaCha20.AArch64.Mixed8.data_frame128 hu (by
    intro k hk
    simp only [List.append_nil,List.mem_map] at hk
    obtain ⟨j,_,rfl⟩ := hk; exact j.isLt)
  have hst : (VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀) :=
    hp.st_d.sub_right (Offset.sub_base _ (by decide : 384 + 128 ≤ 512))
  refine ⟨(congrFun hs.gpr _).trans h.x0,(congrFun hs.gpr _).trans h.x1,
    (congrFun hs.gpr _).trans h.x2,(congrFun hs.gpr _).trans h.x3,?_,
    hs.rd.trans h.rd,hs.wr.trans h.wr,hs.sp.trans h.sp,?_,?_,?_⟩
  · intro r hr h19 h26; rw [hs.gpr]; exact h.cs r hr h19 h26
  · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hs.gpr,h.x0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
      intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hst)]
    rw [← h.x0]; exact h.cnt
  · intro k hk
    by_cases hk' : k < 384
    · rw [hf.bytes (R := VG.Proof.ChaCha20.AArch64.Mixed8.firstR s₀) (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r
        exact Offset.base_disjoint _ (by decide : 384 ≤ 384) (by decide : 384 + 128 ≤ 2 ^ 64))
        (by decide : 384 ≤ 2 ^ 64) hk',h.data k hk']
    · have htail : k - 384 < 128 := by omega
      have he : (VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀).base + BitVec.ofNat 64 (k - 384) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        dsimp [VG.Proof.ChaCha20.AArch64.Mixed8.lastR]; rw [BitVec.add_assoc,← BitVec.ofNat_add,show 384 + (k - 384) = k by omega]
      have hm := hu ((VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀).base + BitVec.ofNat 64 (k - 384))
      rw [Mem.sub_ofNat_toNat _ (by omega : k - 384 < 2 ^ 64)] at hm
      have hslot : (k - 384) / 16 ∈ (List.finRange 8).map Fin.val ++ [] := by
        apply List.mem_append_left
        exact List.mem_map_of_mem (f := Fin.val)
          (List.mem_finRange (⟨(k - 384) / 16,by omega⟩ : Fin 8))
      rw [ite_eq_left ⟨hslot,by omega⟩,he] at hm
      dsimp only at hm
      have hbuf := h.buf (⟨(k - 384) / 16,by omega⟩ : Fin 8)
      rw [hbuf,
        VG.Proof.ChaCha20.AArch64.Rows6.output_byte] at hm
      have hplain : s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) = s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) := by
        have hp' := h.frame.bytes (R := VG.Proof.ChaCha20.AArch64.Mixed8.lastR s₀) (by
          intro r hr
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hst.symm
          · exact hdis.symm
          · exact Offset.disjoint_base _ (by decide : 384 ≤ 384) (by decide : 384 + 128 ≤ 2 ^ 64))
          (by decide : 128 ≤ 2 ^ 64) htail
        rwa [he] at hp'
      rw [hplain,show 6 + (k - 384) / 64 = k / 64 by omega,
        show (k - 384) % 64 = k % 64 by omega] at hm
      exact hm
  · have hpre : Frame [VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀,VG.Proof.ChaCha20.AArch64.Mixed8.dr s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.sr s₀,by simp,fun _ h => h⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s₀,by simp,fun _ h => h⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.dr s₀,by simp,Region.sub_prefix (by decide : 384 ≤ 512)⟩)
    exact hpre.trans (hf.sub (by
      intro r hr; have he := List.mem_singleton.mp hr; subst r
      exact ⟨VG.Proof.ChaCha20.AArch64.Mixed8.dr s₀,by simp,Offset.sub_base _ (by decide : 384 + 128 ≤ 512)⟩))

theorem chunk_ok (s : State) (hp : VG.Proof.ChaCha20.AArch64.Mixed8.CP s) : WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.chunk sve) s (VG.Proof.ChaCha20.AArch64.Mixed8.Chunked s) := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.prepare_ok s hp).mono fun a ha => ?_
  apply WP.seq
  have first : WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.phase sve .x26) a fun b => VG.Proof.ChaCha20.AArch64.Mixed8.Prepared s b 5 := by
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.counted_phase_ok ha.vec ha.scalar ha.table
      (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)) (by decide)
      ((ha.keep _ VG.Proof.ChaCha20.AArch64.not_words_x1 (by decide) (by decide)).trans ha.saved.data.symm)).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
    refine ⟨hv,ht,hc.holds,?_,?_,?_,hc.rd.trans ha.rd,hc.wr.trans ha.wr,hsp.trans ha.sp,?_⟩
    · rw [VG.Proof.ChaCha20.AArch64.Mixed8.source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact ha.cnt
    · exact ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact ha.saved.len,
        by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact ha.saved.data⟩
    · intro r hr h19 h26; rw [hc.keep r hr]; exact ha.keep r hr h19 h26
    · rw [hc.mem]; exact ha.frame
  refine first.mono fun b hb => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.second_ok hp hb).mono fun c hc => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.compute_second_ok hp hc).mono fun d hd => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.spill2_ok hp hd).mono fun e he => ?_
  apply WP.seq
  exact (VG.Proof.ChaCha20.AArch64.Mixed8.finish_ok hp he).mono fun f hf => VG.Proof.ChaCha20.AArch64.Mixed8.last_ok hp hf

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (stateAt)

/-- The high bit tests the public number of complete blocks against eight.
Dividing the byte count by 64 first makes the test valid for every u64 length. -/
theorem less8 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n >>> 6) - BitVec.ofNat 64 8) >>> 63 =
      BitVec.ofNat 64 (if n < 512 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  have hd : n / 2 ^ 6 < 2 ^ 58 := by omega
  by_cases h : n < 512
  · rw [ite_eq_left h]
    have hb : n / 2 ^ 6 < 8 := by omega
    omega
  · rw [ite_eq_right h]
    have hb : 8 ≤ n / 2 ^ 6 := by omega
    omega

theorem check_ok (s : State) :
    WP isa (.block check) s fun u =>
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x5 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, check, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, isa, runStep_some, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_,fun r hr => by simp only [hr,ite_false],rfl,rfl,rfl,rfl,rfl⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using VG.Proof.ChaCha20.AArch64.Mixed8.less8 (s.gpr .x2).toNat (s.gpr .x2).isLt

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit`. -/
section

namespace VG
materialize_code ChaCha20.AArch64.Mixed8.xorNeon := Impl.ChaCha20.AArch64.Mixed8.xor false
materialize_code ChaCha20.AArch64.Mixed8.xorSve2 := Impl.ChaCha20.AArch64.Mixed8.xor true
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Loop`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

variable {sve : Bool}

structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 512 * t ≤ L s₀
  cs : ∀ r ∈ preserved, r ≠ .x20 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (8 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 512 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀,dR s₀,bR s₀] s₀.mem s.mem

structure GPInv (s₀ : State) (t : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t s where
  x20 : s.gpr .x20 = bp s₀
  saved : ∀ j : Fin 3, s.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
    s₀.gpr ([.x20,.x19,.x26].getD j .x20)

structure BulkInv (s₀ : State) (t : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ t s where
  savedV : ∀ j : Fin 2, s.mem.read (bp s₀ + BitVec.ofNat 64 (128 + 16 * j)) 16 =
    s₀.v (#[VReg.v8,VReg.v9][j])

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 512 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (VG.Spec.ChaCha20.block (ctr (ctr S (8 * t)) ((k - 512 * t) / 64)))).getD
        ((k - 512 * t) % 64) 0 := by
  rw [keystream_getD _ hk,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show 8 * t + (k - 512 * t) / 64 = k / 64 by omega,
    show (k - 512 * t) % 64 = k % 64 by omega]

 theorem next_ok (s : State) (hlen : 512 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block next) s fun u =>
      u.gpr .x1 = s.gpr .x1 + 512 ∧ u.gpr .x2 = s.gpr .x2 - 512 ∧
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat - 512 < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 8 ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, next,VG.Impl.ChaCha20.AArch64.Mixed5.counter,check,
    List.cons_append,List.nil_append,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,?_,?_,?_,trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 512 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 512) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he,VG.Proof.ChaCha20.AArch64.Mixed8.less8 _ (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5; simp only [h1,h2,h4,h5,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) 8
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (512 * t),512⟩
theorem win_sub {s₀ : State} {t : Nat} (h : 512 * t + 512 ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Mixed8.win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem cp_of_inv {s₀ s : State} (hp : XPre s₀) {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) : VG.Proof.ChaCha20.AArch64.Mixed8.CP s := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hw : s.wr = [stR s₀,dR s₀,bR s₀] := h.wr.trans hp.wr
  refine ⟨h.x20.trans h.x3.symm,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k; rw [h.rd,hp.rd,hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · intro k; rw [h.rd,hp.rd,hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hw,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  · intro d n hn; rw [hw,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hn (by omega)⟩
  · intro d n hn; rw [hw,h.x1,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x0,h.x3]; exact hp.st_b
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x1,512⟩
    rw [h.x0,h.x1]; exact hp.st_d.sub_right (VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge)
  · change (⟨s.gpr .x1,512⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x1,h.x3]; exact hp.d_b.sub_left (VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge)

 theorem chunkData {s₀ s u : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) (hu : VG.Proof.ChaCha20.AArch64.Mixed8.Chunked s u) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 512 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  by_cases hin : 512 * t ≤ k ∧ k < 512 * t + 512
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 512 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1,BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' hin.1]
    have hh := hu.data (k - 512 * t) (by omega)
    rw [he,h.data k hk,ite_eq_right (by omega),VG.Proof.ChaCha20.AArch64.Mixed8.source,h.x0,h.cnt, ← VG.Proof.ChaCha20.AArch64.Mixed8.ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (VG.Proof.ChaCha20.AArch64.Mixed8.win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains,Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega),Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hu.frame (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change ¬ (⟨s.gpr .x0,64⟩ : Region).Contains _ 1
        rw [h.x0]; exact fun hc => hp.st_d _ hc (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)
      · exact fun hc => hp.d_b _ (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)
          (Region.sub_prefix (by decide : 128 ≤ 320) _ (by simpa only [VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf,h.x3] using hc))
      · change ¬ (⟨s.gpr .x1,512⟩ : Region).Contains _ 1
        rw [h.x1]; exact hx)
    rw [hh,h.data k hk]
    by_cases hold : k < 512 * t
    · rw [ite_eq_left hold,ite_eq_left (by omega)]
    · rw [ite_eq_right hold,ite_eq_right (by omega)]

abbrev guardR (s₀ : State) (j : Fin 3) : Region := ⟨bp s₀ + BitVec.ofNat 64 (256 + 8 * j),8⟩

theorem guard_chunk {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) (j : Fin 3) :
    ∀ r ∈ [VG.Proof.ChaCha20.AArch64.Mixed8.sr s,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s,VG.Proof.ChaCha20.AArch64.Mixed8.dr s], (VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j).Disjoint ⟨s.gpr .x0,64⟩
    rw [h.x0]
    exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))
  · change (VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j).Disjoint ⟨s.gpr .x3,128⟩
    rw [h.x3]
    exact Offset.disjoint_base _ (by have hj := j.isLt; omega) (by have hj := j.isLt; omega)
  · change (VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j).Disjoint ⟨s.gpr .x1,512⟩
    rw [h.x1]
    exact (hp.d_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))).sub_right
      (VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge)

abbrev guardVR (s₀ : State) (j : Fin 2) : Region :=
  ⟨bp s₀ + BitVec.ofNat 64 (128 + 16 * j),16⟩

theorem guardV_chunk {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) (j : Fin 2) :
    ∀ r ∈ [VG.Proof.ChaCha20.AArch64.Mixed8.sr s,VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf s,VG.Proof.ChaCha20.AArch64.Mixed8.dr s], (VG.Proof.ChaCha20.AArch64.Mixed8.guardVR s₀ j).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (VG.Proof.ChaCha20.AArch64.Mixed8.guardVR s₀ j).Disjoint ⟨s.gpr .x0,64⟩
    rw [h.x0]
    exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))
  · change (VG.Proof.ChaCha20.AArch64.Mixed8.guardVR s₀ j).Disjoint ⟨s.gpr .x3,128⟩
    rw [h.x3]
    exact Offset.disjoint_base _ (by have hj := j.isLt; omega) (by have hj := j.isLt; omega)
  · change (VG.Proof.ChaCha20.AArch64.Mixed8.guardVR s₀ j).Disjoint ⟨s.gpr .x1,512⟩
    rw [h.x1]
    exact (hp.d_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))).sub_right
      (VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge)

 theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s) :
    WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.body sve) s fun u => VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ (t + 1) u ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.chunk_ok s (VG.Proof.ChaCha20.AArch64.Mixed8.cp_of_inv hp h hge)).mono fun u hu => ?_
  have hx0 : u.gpr .x0 = st s₀ := hu.x0.trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * t) := hu.x1.trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t) := hu.x2.trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := hu.x3.trans h.x3
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (8 * t) := by
    have hc := hu.cnt
    change stateAt u.mem (u.gpr .x0) = stateAt s.mem (s.gpr .x0) at hc
    rw [hx0,h.x0,h.cnt] at hc
    exact hc
  have hdata := VG.Proof.ChaCha20.AArch64.Mixed8.chunkData hp h hge hu
  have hw : u.wr = [stR s₀,dR s₀,bR s₀] := hu.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hu.rd,h.rd,hp.rd,hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 512 * t := by
    rw [hx2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hsaved : ∀ j : Fin 3, u.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      s₀.gpr ([.x20,.x19,.x26].getD j .x20) := by
    intro j
    rw [hu.frame.readW (r := VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (VG.Proof.ChaCha20.AArch64.Mixed8.guard_chunk hp h hge j) (by decide),h.saved j]
  have hsavedV : ∀ j : Fin 2, u.mem.read (bp s₀ + BitVec.ofNat 64 (128 + 16 * j)) 16 =
      s₀.v (#[VReg.v8,VReg.v9][j]) := by
    intro j
    rw [hu.frame.read (r := VG.Proof.ChaCha20.AArch64.Mixed8.guardVR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (VG.Proof.ChaCha20.AArch64.Mixed8.guardV_chunk hp h hge j) (by decide),h.savedV j]
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1,hv2,hv5,hkeep,hctr,hframe,hrd,hwr,hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * (t + 1)) := by
    rw [hv1,hx1,BitVec.add_assoc]
    change _ + (BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 512) = _
    rw [← BitVec.ofNat_add,show 512 * t + 512 = 512 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * (t + 1)) := by
    rw [hv2,hx2]
    change BitVec.ofNat 64 (L s₀ - 512 * t) - BitVec.ofNat 64 512 = _
    rw [Offset.ofNat_sub_ofNat (by omega),show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega]
  refine ⟨⟨⟨⟨?_,hptr,hrem,?_,by omega,?_,hrd.trans (hu.rd.trans h.rd),
    hwr.trans (hu.wr.trans h.wr),hsp.trans (hu.sp.trans h.sp),?_,?_,?_⟩,?_,?_⟩,?_⟩,?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx3]
  · intro r hr hr20 hr21 hr22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [hkeep r n1 n2 n4 n5,hu.cs r hr hr21 hr22,h.cs r hr hr20 hr21 hr22]
  · rw [hx0,hcnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega] at hctr
    exact hctr
  · intro k hk
    rw [hframe _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact fun hc => hp.st_d _ hc (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)),hdata k hk]
  · have hf' : Frame [stR s₀,dR s₀,bR s₀] s.mem u.mem := hu.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀,by simp,by change (⟨s.gpr .x0,64⟩ : Region).Sub (stR s₀); rw [h.x0]; exact fun _ hx => hx⟩
      · exact ⟨bR s₀,by simp,by simpa only [VG.Proof.ChaCha20.AArch64.Mixed8.scalarBuf,h.x3] using Region.sub_prefix (base := bp s₀) (by decide : 128 ≤ 320)⟩
      · exact ⟨dR s₀,by simp,by simpa only [VG.Proof.ChaCha20.AArch64.Mixed8.dr,h.x1] using VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge⟩)
    have hn' : Frame [stR s₀,dR s₀,bR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hu.cs _ (by decide) (by decide) (by decide),h.x20]
  · intro j
    rw [hframe.readW (r := VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsaved j]
  · intro j
    rw [hframe.read (r := VG.Proof.ChaCha20.AArch64.Mixed8.guardVR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; have he := List.mem_singleton.mp hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsavedV j]
  · rw [hv5,hlen,show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega]

theorem init_ok (s : State) : WP isa (.block check) s fun u =>
    VG.Proof.ChaCha20.AArch64.Mixed8.LInv s 0 u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s < 512 then 1 else 0) ∧ u.v = s.v := by
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.check_ok s).mono fun u ⟨h5,hg,hm,hr,hw,hv,hsp⟩ => ?_
  refine ⟨⟨hg _ (by decide),?_,?_,hg _ (by decide),by omega,?_,hr,hw,hsp,?_,?_,?_⟩,
    ?_,h5,hv⟩
  · rw [hg _ (by decide)]; simp only [Nat.mul_zero,BitVec.add_zero]
  · rw [hg _ (by decide)]
    simp only [Nat.mul_zero,Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
  · intro r hr _ _ _
    have nr : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    exact hg r nr
  · rw [hm]; exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; rw [hm]; simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]
  · rw [hm]; exact Frame.refl _ _
  · intro r hr
    have nr : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    exact hg r nr

 theorem zero_batches {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (512 ≤ n)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s .x5,h]
  by_cases hn : n < 512
  · simp only [ite_eq_left hn]
    have hnn : ¬ 512 ≤ n := by omega
    simp [hnn]
  · simp only [ite_eq_right hn]
    have hnn : 512 ≤ n := by omega
    simp [hnn]

 theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ 0 s)
    (hge : 512 ≤ L s₀) : WP isa (.loop (VG.Impl.ChaCha20.AArch64.Mixed8.body sve) (.zero .x .x5)) s fun u =>
      ∃ t, L s₀ - 512 * t < 512 ∧ VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t u := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ t, n = L s₀ - 512 * t ∧ 512 ≤ n ∧ VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s
  refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0,by omega,hge,h⟩
  intro n s ⟨t,hn,hge,hi⟩
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.body_ok hp (by omega) hi).mono fun u ⟨hu,h5⟩ => ?_
  have hc := VG.Proof.ChaCha20.AArch64.Mixed8.zero_batches h5
  by_cases he : L s₀ - 512 * (t + 1) < 512
  · left
    refine ⟨?_,t + 1,he,hu⟩
    have hne : ¬ 512 ≤ L s₀ - 512 * (t + 1) := by omega
    simpa only [decide_eq_false hne] using hc
  · right
    refine ⟨?_,L s₀ - 512 * (t + 1),by omega,t + 1,rfl,by omega,hu⟩
    have hne : 512 ≤ L s₀ - 512 * (t + 1) := by omega
    simpa only [decide_eq_true hne] using hc

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

 theorem enterGP_ok {s₀ s : State} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ 0 s)
    (hold : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) : WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.enter) s (VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ 0) := by
  have ho (d : Nat) (hd : d + 8 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  unfold VG.Impl.ChaCha20.AArch64.Mixed5.enter
  apply WP.block_cons_iff.mpr
  let m₁ := s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 256) (s.gpr .x20)
  refine ⟨{s with mem := m₁},exec_str_x (by decide) (ho 256 (by decide)),?_⟩
  apply WP.block_cons_iff.mpr
  let m₂ := m₁.writeW (s.gpr .x3 + BitVec.ofNat 64 264) (s.gpr .x19)
  refine ⟨{s with mem := m₂},exec_str_x (s := {s with mem := m₁}) (by decide) (ho 264 (by decide)),?_⟩
  apply WP.block_cons_iff.mpr
  let m₃ := m₂.writeW (s.gpr .x3 + BitVec.ofNat 64 272) (s.gpr .x26)
  refine ⟨{s with mem := m₃},exec_str_x (s := {s with mem := m₂}) (by decide) (ho 272 (by decide)),?_⟩
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.move_ok _ .x20 .x3).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hm : a.mem = (((s.mem.writeW (bp s₀ + BitVec.ofNat 64 256) (s₀.gpr .x20)).writeW
      (bp s₀ + BitVec.ofNat 64 264) (s₀.gpr .x19)).writeW
      (bp s₀ + BitVec.ofNat 64 272) (s₀.gpr .x26)) := by
    simpa only [m₃,m₂,m₁,h.x3,hold .x20 (by decide),hold .x19 (by decide),hold .x26 (by decide)] using ha.mem
  have hf : Frame [bR s₀] s.mem a.mem := by
    rw [hm]
    exact (((Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 256 + 8 ≤ 320) (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide : 264 + 8 ≤ 320) (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide : 272 + 8 ≤ 320) (by decide))
  refine ⟨⟨(ha.other _ (by decide)).trans h.x0,(ha.other _ (by decide)).trans h.x1,
    (ha.other _ (by decide)).trans h.x2,(ha.other _ (by decide)).trans h.x3,h.le,?_,
    ha.rd.trans h.rd,ha.wr.trans h.wr,hasp.trans h.sp,?_,?_,
    h.frame.trans (hf.mono (by simp))⟩,ha.gpr.trans h.x3,?_⟩
  · intro r hr nr nr21 nr22; rw [ha.other r nr]; exact h.cs r hr nr nr21 nr22
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by simpa using hp.st_b)]; exact h.cnt
  · intro k hk
    rw [hf.bytes (R := dR s₀) (by simpa using hp.d_b)
      (by have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀; change L s₀ ≤ 2 ^ 64; omega) hk]
    exact h.data k hk
  · intro j
    rw [hm,VG.Proof.ChaCha20.AArch64.Mixed5.read_saved]
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
    rcases hj with rfl | rfl | rfl <;> rfl

 theorem leaveGP_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ t s) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.leave) s fun u => VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t u ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) := by
  have hi (d : Nat) (hd : d + 8 ≤ 320) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [h.rd,hp.rd,h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  have hm₀ : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 256) 8 = s₀.gpr .x20 := by
    rw [h.x3]; exact h.saved 0
  have hm₁ : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 264) 8 = s₀.gpr .x19 := by
    rw [h.x3]; exact h.saved 1
  have hm₂ : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 272) 8 = s₀.gpr .x26 := by
    rw [h.x3]; exact h.saved 2
  unfold VG.Impl.ChaCha20.AArch64.Mixed5.leave
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, runBlock_cons,runBlock_nil,exec,addr,Size.bytes,Size.bits,
    State.load,hi 256 (by decide),hi 264 (by decide),hi 272 (by decide),
    RegUpd.gpr_write,BitVec.setWidth_eq,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,
    Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,exists_eq_left',
    hm₀,hm₁,hm₂]
  refine ⟨⟨?_,?_,?_,?_,h.le,?_,h.rd,h.wr,h.sp,h.cnt,h.data,h.frame⟩,?_⟩
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x0 ≠ .x26 by decide,
      show Reg.x0 ≠ .x19 by decide,show Reg.x0 ≠ .x20 by decide,ite_false]; exact h.x0
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x1 ≠ .x26 by decide,
      show Reg.x1 ≠ .x19 by decide,show Reg.x1 ≠ .x20 by decide,ite_false]; exact h.x1
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x2 ≠ .x26 by decide,
      show Reg.x2 ≠ .x19 by decide,show Reg.x2 ≠ .x20 by decide,ite_false]; exact h.x2
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x3 ≠ .x26 by decide,
      show Reg.x3 ≠ .x19 by decide,show Reg.x3 ≠ .x20 by decide,ite_false]; exact h.x3
  · intro r hr n20 n21 n22
    simp only [RegUpd.gpr_write,n20,n21,n22,ite_false]
    exact h.cs r hr n20 n21 n22
  · intro r hr
    by_cases n20 : r = .x20
    · subst r; simp
    by_cases n21 : r = .x19
    · subst r; simp
    by_cases n22 : r = .x26
    · subst r; simp
    simp only [n20,n21,n22,ite_false]
    exact h.cs r hr n20 n21 n22

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

abbrev saveV : List Instr := [.strq .v8 .x3 128,.strq .v9 .x3 144]
abbrev restoreV : List Instr := [.ldrq .v8 .x3 128,.ldrq .v9 .x3 144]
abbrev savedVR (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 128,32⟩

theorem saveV_ok (s : State)
    (ho0 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 128) 16)
    (ho1 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 144) 16) :
    WP isa (.block VG.Proof.ChaCha20.AArch64.Mixed8.saveV) s fun u =>
      u.gpr = s.gpr ∧ u.v = s.v ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR s] s.mem u.mem ∧
      u.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s.v .v8 ∧
      u.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s.v .v9 := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.ChaCha20.AArch64.Mixed8.saveV,runBlock_cons,runBlock_nil,exec,addr,
    State.store,ho0,ho1,Option.bind_some,Option.some.injEq,exists_eq_left',isa,runStep_some]
  refine ⟨trivial,trivial,trivial,trivial,trivial,?_,?_,?_⟩
  · have h0 : (VG.Proof.ChaCha20.AArch64.Mixed8.savedVR s).Contains (s.gpr .x3 + BitVec.ofNat 64 128) 16 := by
      simp only [Region.Contains,BitVec.sub_self]; decide
    have h1 : (VG.Proof.ChaCha20.AArch64.Mixed8.savedVR s).Contains (s.gpr .x3 + BitVec.ofNat 64 144) 16 := by
      exact Offset.contains (s.gpr .x3) (by decide : 128 ≤ 144)
        (by decide : 144 + 16 ≤ 128 + 32) (by decide)
    exact ((Frame.refl _ _).write (List.mem_cons_self ..) _ h0).write
      (List.mem_cons_self ..) _ h1
  · rw [Mem.read_write_sep (Offset.sep (s.gpr .x3) (d := 128) (n := 16) (e := 144) (k := 16)
      (by decide) (by decide) (by decide)) (by decide),VG.Proof.ChaCha20.AArch64.Rows6.read_write_self]
  · exact VG.Proof.ChaCha20.AArch64.Rows6.read_write_self _ _ _

theorem restoreV_ok {s : State} (v8 v9 : BitVec 128)
    (hi0 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 128) 16)
    (hi1 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 144) 16)
    (hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = v8)
    (hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = v9) :
    WP isa (.block VG.Proof.ChaCha20.AArch64.Mixed8.restoreV) s fun u =>
      u.v .v8 = v8 ∧ u.v .v9 = v9 ∧ u.gpr = s.gpr ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.AArch64.Mixed8.restoreV,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.load,hi0,hi1,State.setV,hm0,hm1,Option.bind_some,Option.map_some,
    Option.some.injEq,exists_eq_left',isa,runStep_some]
  trivial

theorem gp_same {s₀ s u : State} {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ t s)
    (hg : u.gpr = s.gpr) (hm : u.mem = s.mem) (hr : u.rd = s.rd)
    (hw : u.wr = s.wr) (hsp : u.sp = s.sp) : VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ t u := by
  refine ⟨⟨?_,?_,?_,?_,h.le,?_,hr.trans h.rd,hw.trans h.wr,hsp.trans h.sp,?_,?_,?_⟩,?_,?_⟩
  · rw [hg]; exact h.x0
  · rw [hg]; exact h.x1
  · rw [hg]; exact h.x2
  · rw [hg]; exact h.x3
  · intro r hr n20 n19 n26; rw [hg]; exact h.cs r hr n20 n19 n26
  · rw [hm]; exact h.cnt
  · rw [hm]; exact h.data
  · rw [hm]; exact h.frame
  · rw [hg]; exact h.x20
  · rw [hm]; exact h.saved

theorem enterV_ok {s₀ s : State} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ 0 s)
    (hv : s.v = s₀.v) : WP isa (.block VG.Proof.ChaCha20.AArch64.Mixed8.saveV) s (VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ 0) := by
  have ho (d : Nat) (hd : d + 16 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok s (ho 128 (by decide)) (ho 144 (by decide))).mono fun u
    ⟨hg,_,hr,hw,hsp,hf,hm0,hm1⟩ => ?_
  have hsub : (VG.Proof.ChaCha20.AArch64.Mixed8.savedVR s).Sub (bR s₀) := by
    rw [show VG.Proof.ChaCha20.AArch64.Mixed8.savedVR s = ⟨bp s₀ + BitVec.ofNat 64 128,32⟩ by rw [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR,h.x3]]
    exact Offset.sub_base _ (by decide)
  have hfb : Frame [bR s₀] s.mem u.mem := hf.sub (by
    intro r hr; have he := List.mem_singleton.mp hr; subst r
    exact ⟨bR s₀,by simp,hsub⟩)
  refine ⟨⟨⟨?_,?_,?_,?_,h.le,?_,hr.trans h.rd,hw.trans h.wr,hsp.trans h.sp,?_,?_,
    h.frame.trans (hfb.mono (by simp))⟩,?_,?_⟩,?_⟩
  · rw [hg]; exact h.x0
  · rw [hg]; exact h.x1
  · rw [hg]; exact h.x2
  · rw [hg]; exact h.x3
  · intro r hr n20 n19 n26; rw [hg]; exact h.cs r hr n20 n19 n26
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb (by simpa using hp.st_b)]; exact h.cnt
  · intro k hk
    rw [hfb.bytes (R := dR s₀) (by simpa using hp.d_b)
      (by have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀; change L s₀ ≤ 2 ^ 64; omega) hk]
    exact h.data k hk
  · rw [hg]; exact h.x20
  · intro j
    rw [hf.readW (r := VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; have he := List.mem_singleton.mp hr; subst r
          change (VG.Proof.ChaCha20.AArch64.Mixed8.guardR s₀ j).Disjoint ⟨s.gpr .x3 + BitVec.ofNat 64 128,32⟩
          rw [h.x3]
          exact Offset.disjoint _ (by have hj := j.isLt; omega)
            (by have hj := j.isLt; omega) (by decide)) (by decide),h.saved j]
  · intro j
    have hj : j = 0 ∨ j = 1 := by simp only [Fin.ext_iff]; omega
    rcases hj with rfl | rfl
    · change u.mem.read (bp s₀ + BitVec.ofNat 64 128) 16 = s₀.v .v8
      simpa only [h.x3,hv] using hm0
    · change u.mem.read (bp s₀ + BitVec.ofNat 64 144) 16 = s₀.v .v9
      simpa only [h.x3,hv] using hm1

theorem enter_ok {s₀ s : State} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ 0 s)
    (hold : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) (hv : s.v = s₀.v) :
    WP isa (.block enter) s (VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ 0) := by
  unfold enter
  apply WP.block_append_iff.mpr
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by
    intro i hi; simp only [VG.Impl.ChaCha20.AArch64.Mixed5.enter,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) (VG.Proof.ChaCha20.AArch64.Mixed8.enterGP_ok hp h hold)).mono fun u ⟨hu,huv,_,_,_⟩ => ?_
  exact VG.Proof.ChaCha20.AArch64.Mixed8.enterV_ok hp hu (huv.trans hv)

theorem leaveV_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s) :
    WP isa (.block VG.Proof.ChaCha20.AArch64.Mixed8.restoreV) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed8.GPInv s₀ t u ∧ u.v .v8 = s₀.v .v8 ∧ u.v .v9 = s₀.v .v9 := by
  have hi (d : Nat) (hd : d + 16 ≤ 320) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [h.rd,hp.rd,h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  have hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s₀.v .v8 := by
    rw [h.x3]; exact h.savedV 0
  have hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s₀.v .v9 := by
    rw [h.x3]; exact h.savedV 1
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.restoreV_ok _ _ (hi 128 (by decide)) (hi 144 (by decide)) hm0 hm1).mono fun u
    ⟨hv8,hv9,hg,hm,hr,hw,hsp⟩ => ⟨VG.Proof.ChaCha20.AArch64.Mixed8.gp_same h.toGPInv hg hm hr hw hsp,hv8,hv9⟩

theorem leave_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed8.BulkInv s₀ t s) :
    WP isa (.block leave) s fun u => VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t u ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ u.v .v8 = s₀.v .v8 ∧ u.v .v9 = s₀.v .v9 := by
  unfold leave
  apply WP.block_append_iff.mpr
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.leaveV_ok hp h).mono fun u ⟨hu,hv8,hv9⟩ => ?_
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by
    intro i hi; simp only [VG.Impl.ChaCha20.AArch64.Mixed5.leave,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl) (VG.Proof.ChaCha20.AArch64.Mixed8.leaveGP_ok hp hu)).mono fun v ⟨⟨hl,hcs⟩,hv,_,_,_⟩ => ?_
  exact ⟨hl,hcs,by rw [hv]; exact hv8,by rw [hv]; exact hv9⟩
end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)
open VG.Proof.ChaCha20.AArch64.Neon4 (data_in)

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

abbrev tailR (s₀ : State) (t : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (512 * t), L s₀ - 512 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 512 * t ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Mixed8.tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 512 * t) (ht : 512 * t ≤ L s₀) :
    ¬ (VG.Proof.ChaCha20.AArch64.Mixed8.tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem tail_ok {s₀ : State} (hp : XPre s₀) {t : Nat} {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t s) (hcs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hle := h.le
  have hn : (BitVec.ofNat 64 (L s₀ - 512 * t)).toNat = L s₀ - 512 * t :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, VG.Proof.ChaCha20.AArch64.Mixed8.tailR s₀ t, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := VG.Proof.ChaCha20.AArch64.Mixed8.tail_sub h.le
    exact ⟨trivial, rfl, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts, by
      have := hp.nowrap
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega⟩
  have hc : Covers wr s.wr := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s₀, by simp, 512 * t, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hw : WP isa Impl.ChaCha20.AArch64.Small.xor (s.withRegions [] wr) fun u =>
      abiPreserved (s.withRegions [] wr) u ∧ xorAArch64.post (s.withRegions [] wr) u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
    VG.Proof.ChaCha20.AArch64.Small.correct _ hs
  refine WP.narrow hw ?_ hc ?_ VG.Proof.ChaCha20.AArch64.Small.xor_noFrames
  · rw [h.rd, hp.rd]; exact hc
  · intro u _ _ hsp hf ⟨ha, hpost, h0, h1⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, abiPreserved] at ha
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      h.x0, h.x1, h.x2, hn, h.cnt] at hpost
    refine ⟨⟨?_, hsp.trans h.sp⟩, ?_, h0.trans h.x0, h1.trans h.x3⟩
    · intro r hr
      rw [ha.1 r hr]
      exact hcs r hr
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < L s₀ := hk
      have ns : ¬ (stR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.st_d _ hh (data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (data_in hk) hh
      by_cases hk' : k < 512 * t
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact VG.Proof.ChaCha20.AArch64.Mixed8.not_tail hk' h.le
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := VG.Proof.ChaCha20.AArch64.Mixed8.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 512 * t) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, VG.Proof.ChaCha20.AArch64.Mixed8.ks_shift _ hk (t := t) (by omega)]

end VG.Proof.ChaCha20.AArch64.Mixed8

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre L)

variable {sve : Bool}

theorem nonzero_short {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 512)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 512 <;> simp [hn]

theorem correct_aux (s : State) (hs : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s fun u => GprAbi s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 ∧
      (u.v .v8).extractLsb' 0 64 = (s.v .v8).extractLsb' 0 64 ∧
      (u.v .v9).extractLsb' 0 64 = (s.v .v9).extractLsb' 0 64 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.init_ok s).mono fun a ⟨hi,hcs,h5,hv⟩ => ?_
  apply WP.seq
  have hb : WP isa (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block enter) (.seq (.loop (VG.Impl.ChaCha20.AArch64.Mixed8.body sve) (.zero .x .x5)) (.block leave)))) a fun u =>
      ∃ t, VG.Proof.ChaCha20.AArch64.Mixed8.LInv s t u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
        u.v .v8 = s.v .v8 ∧ u.v .v9 = s.v .v9 := by
    apply WP.ite (decide (L s < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short h5)
    · intro _; exact WP.block_nil ⟨0,hi,hcs,congrFun hv .v8,congrFun hv .v9⟩
    · intro hshort
      have hge : 512 ≤ L s := by have hh := of_decide_eq_false hshort; omega
      apply WP.seq
      refine (VG.Proof.ChaCha20.AArch64.Mixed8.enter_ok (XPre.of s hs) hi hcs hv).mono fun b hb => ?_
      apply WP.seq
      refine (VG.Proof.ChaCha20.AArch64.Mixed8.bulk_ok (XPre.of s hs) hb hge).mono fun c ⟨t,_,hc⟩ => ?_
      exact (VG.Proof.ChaCha20.AArch64.Mixed8.leave_ok (XPre.of s hs) hc).mono fun _ ⟨hd,hcs,h8,h9⟩ => ⟨t,hd,hcs,h8,h9⟩
  refine hb.mono fun u ⟨t,hu,hcs,h8,h9⟩ => ?_
  refine (WP.preservedV (VG.Proof.ChaCha20.AArch64.Mixed8.tail_ok (XPre.of s hs) hu hcs) (hc := by lit_decide)).mono ?_
  intro v ⟨⟨ha,hp,h0,h1⟩,hvec⟩
  exact ⟨ha,hp,h0,h1,by rw [hvec .v8 (by decide),h8],by rw [hvec .v9 (by decide),h9]⟩

theorem correct (s : State) (hs : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s fun u => abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  obtain ⟨t,u,he,ha,hp,h0,h1,h8,h9⟩ := VG.Proof.ChaCha20.AArch64.Mixed8.correct_aux s hs
  refine ⟨t,u,he,⟨ha.1,ha.2,?_⟩,hp,h0,h1⟩
  intro r hr
  by_cases he8 : r = .v8
  · subst r; exact h8
  by_cases he9 : r = .v9
  · subst r; exact h9
  have hc : (Impl.ChaCha20.AArch64.Mixed8.xor sve).allInstrs Rows6.keepsOtherV = true := by cases sve <;> lit_decide
  rw [Exec.vec (fun i hi => Rows6.keepsOtherV_ne (List.all_eq_true.mp
    ((Code.allInstrs_eq Rows6.keepsOtherV (Impl.ChaCha20.AArch64.Mixed8.xor sve)) ▸ hc) i hi) hr he8 he9) he]

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s t u ∧ abiPreserved s u ∧ xorAArch64.post s u :=
  (VG.Proof.ChaCha20.AArch64.Mixed8.correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : (Impl.ChaCha20.AArch64.Mixed8.xor sve).noFrames = true := by cases sve <;> lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub (Impl.ChaCha20.AArch64.Mixed8.xor sve) := by
  cases sve <;>
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

theorem xor_verified : Verified AArch64.target (Impl.ChaCha20.AArch64.Mixed8.xor sve)
    (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.AArch64.Mixed8.xor_correct VG.Proof.ChaCha20.AArch64.Mixed8.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract,Spec.ChaCha20.xorSig,AArch64.abi,AArch64.argRegs,
      xorAArch64] [Xor.sat] using Xor.sat)
end VG.Proof.ChaCha20.AArch64.Mixed8

end
