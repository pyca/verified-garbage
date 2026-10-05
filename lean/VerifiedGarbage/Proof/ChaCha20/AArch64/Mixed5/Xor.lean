import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Schedule`. -/
section

/-! Interleaving independent integer and vector operations preserves both streams. -/
namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
namespace Scheduled
open VG.Impl.ChaCha20.AArch64.Neon4 (Op)
open VG.Proof.ChaCha20.AArch64.Neon4 (step)
abbrev N := VG.Proof.ChaCha20.AArch64.Neon4.Holds
abbrev C := VG.Proof.ChaCha20.AArch64.Holds
abbrev RI := VG.Proof.ChaCha20.AArch64.RI
abbrev wreg := VG.Impl.ChaCha20.AArch64.wreg

def Valid : VG.Impl.ChaCha20.AArch64.Neon4.Op → Prop
  | .add .. => True
  | .xorRol _ _ _ n => 0 < n.val

theorem wreg_eq (a b : Fin 16) : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.wreg a = VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.wreg b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (VG.Proof.ChaCha20.AArch64.wreg_inj a.isLt b.isLt h)
  · intro h; rw [h]

theorem scalar_op (op : VG.Impl.ChaCha20.AArch64.Neon4.Op) (hv : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op) {v : CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.C v s) :
    WP isa (.block (scalarCode op)) s fun u => VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.RI (step v op) s u ∧ u.v = s.v ∧ u.sp = s.sp := by
  have hh (k : Fin 16) : s.read .w (VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.wreg k) = v[k] := by
    simp only [Nat.reduceLeDiff, State.read, Size.bits, h k.val k.isLt, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Fin.getElem_fin]
  have keep (r : Reg) (hr : ¬ VG.Proof.ChaCha20.AArch64.Words r) (d : Fin 16) : r ≠ VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.wreg d := by
    intro e; exact hr ⟨d.val,d.isLt,e⟩
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [scalarCode, runBlock_cons, runBlock_nil, exec_add, isa, runStep_some,
      Option.some.injEq, exists_eq_left', hh]
    refine ⟨⟨?_,rfl,rfl,rfl,?_⟩,rfl,rfl⟩
    · intro k hk
      have he := VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.wreg_eq (⟨k,hk⟩ : Fin 16) d
      simp only [State.write, Size.bits, step, Vector.getElem_set, he, Fin.ext_iff, eq_comm (a := d.val)]
      split
      · rfl
      · exact h k hk
    · intro r hr
      simp [State.write, keep r hr d]
  | xorRol d a b n =>
    have hn : 32 - n.val < 32 := by change 0 < n.val at hv; omega
    apply WP.of_runBlock
    simp only [↓reduceIte, Nat.reduceLeDiff, and_self, scalarCode, runBlock_cons, runBlock_nil, exec_logic, exec_ror_w hn, isa,
      runStep_some, Option.some.injEq, exists_eq_left',
      State.read, State.write, Size.bits, h a.val a.isLt, h b.val b.isLt,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    refine ⟨⟨?_,rfl,rfl,rfl,?_⟩, trivial⟩
    · intro k hk
      have he := VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.wreg_eq (⟨k,hk⟩ : Fin 16) d
      simp only [step, Vector.getElem_set, he, Fin.ext_iff, eq_comm (a := d.val)]
      split
      · simp only [VG.Proof.ChaCha20.rotateLeft_eq _ hv n.isLt, Fin.getElem_fin]
      · exact h k hk
    · intro r hr
      simp [keep r hr d]

theorem ops_ok (ops : List VG.Impl.ChaCha20.AArch64.Neon4.Op) (hp : ∀ op ∈ ops, VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op)
    {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.N vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) (hc : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.C v s) :
    WP isa (VG.Impl.ChaCha20.AArch64.Mixed5.scheduled ops) s fun u =>
      VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.N (fun j => ops.foldl step (vs j)) u ∧ VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.RI (ops.foldl step v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  induction ops generalizing vs v s with
  | nil => exact WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | cons op ops ih =>
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Neon4.op_ok op hn ht).mono fun a ⟨ha,hsa⟩ => ?_
    have hca : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.C v a := by simpa only [VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.C, VG.Proof.ChaCha20.AArch64.Holds,hsa.gpr] using hc
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.scalar_op op (hp _ (List.mem_cons_self ..)) hca).mono fun b ⟨hb,hav,hsp⟩ => ?_
    have hnb : VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.N (fun j => step (vs j) op) b := by
      simpa only [VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.N, VG.Proof.ChaCha20.AArch64.Neon4.Holds,hav] using ha
    have htb : b.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by rw [hav,hsa.v30,ht]
    refine (ih (fun p h => hp p (List.mem_cons_of_mem _ h)) hnb htb hb.holds).mono
      fun u ⟨hu,hbu,hsp',hut⟩ => ?_
    refine ⟨hu,?_,hsp'.trans (hsp.trans hsa.sp),hut⟩
    refine ⟨hbu.holds,hbu.mem.trans (hb.mem.trans hsa.mem),
        hbu.rd.trans (hb.rd.trans hsa.rd),hbu.wr.trans (hb.wr.trans hsa.wr),?_⟩
    intro r hr
    exact (hbu.keep r hr).trans ((hb.keep r hr).trans (congrFun hsa.gpr r))

theorem roundOps_valid : ∀ op ∈ VG.Impl.ChaCha20.AArch64.Mixed5.roundOps, VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op := by
  have h : roundOps.all (fun op => match op with
    | .add .. => true | .xorRol _ _ _ n => decide (0 < n.val)) = true := by decide +kernel
  intro op hp
  have hh := List.all_eq_true.mp h op hp
  cases op
  · trivial
  · change 0 < _
    exact of_decide_eq_true hh
end Scheduled
end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Spec.ChaCha20 (innerBlock)

def scalarKeepsV : Bool := (VG.Impl.ChaCha20.AArch64.doubleRound.allInstrs fun i =>
  match vdstOf i with | none => true | _ => false)

theorem scalar_round_vectors {v : CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Holds v s) :
    WP isa VG.Impl.ChaCha20.AArch64.doubleRound s fun u =>
      VG.Proof.ChaCha20.AArch64.RI (innerBlock v) s u ∧ u.v = s.v ∧ u.sp = s.sp := by
  have hp := VG.Proof.ChaCha20.AArch64.doubleRound_ok (s₀ := s) ⟨h,rfl,rfl,rfl,fun _ _ => rfl⟩
  obtain ⟨t,u,he,hu⟩ := hp
  have hv : VG.Proof.ChaCha20.AArch64.Mixed5.scalarKeepsV = true := by decide +kernel
  rw [VG.Proof.ChaCha20.AArch64.Mixed5.scalarKeepsV, Code.allInstrs_eq] at hv
  refine ⟨t,u,he,hu,?_,Exec.sp he⟩
  apply funext
  intro r
  apply Exec.vec (c := VG.Impl.ChaCha20.AArch64.doubleRound) (r := r) ?_ he
  intro i hi
  have h' := List.all_eq_true.mp hv i hi
  cases hdst : vdstOf i <;> simp only [hdst, Bool.false_eq_true] at h'
  simp

theorem parallelRound_ok {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hc : VG.Proof.ChaCha20.AArch64.Holds v s) :
    WP isa VG.Impl.ChaCha20.AArch64.Mixed5.parallelRound s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => innerBlock (vs j)) u ∧ VG.Proof.ChaCha20.AArch64.Holds (innerBlock v) u ∧
      VG.Proof.ChaCha20.AArch64.RI (innerBlock v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  refine (Scheduled.ops_ok VG.Impl.ChaCha20.AArch64.Mixed5.roundOps Scheduled.roundOps_valid hn ht hc).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  simp only [VG.Impl.ChaCha20.AArch64.Mixed5.roundOps, VG.Proof.ChaCha20.AArch64.Neon4.innerBlock_eq] at hu hr
  exact ⟨hu,hr.holds,hr,hsp,hut⟩

theorem rounds_ok {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hc : VG.Proof.ChaCha20.AArch64.Holds v s) :
    ∀ n, WP isa (VG.Impl.ChaCha20.AArch64.Mixed5.rounds n) s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (vs j)) u ∧
      VG.Proof.ChaCha20.AArch64.RI (Nat.repeat innerBlock n v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  | 0 => WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | n + 1 => by
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed5.rounds_ok hn ht hc n).mono fun a ⟨ha,hca,hsp,hat⟩ => ?_
    refine (VG.Proof.ChaCha20.AArch64.Mixed5.parallelRound_ok ha hat hca.holds).mono fun b ⟨hb,_,hab,hsp',hbt⟩ =>
      ⟨hb,⟨hab.holds,hab.mem.trans hca.mem,hab.rd.trans hca.rd,hab.wr.trans hca.wr,
        fun r hr => (hab.keep r hr).trans (hca.keep r hr)⟩,hsp'.trans hsp,hbt⟩

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64 (load finish addWord wreg)
open VG.Proof.ChaCha20.AArch64

/-- Reuse the scalar load proof with the stream caller's permitted regions. -/
theorem scalarLoad_ok (s : State) (hp : Pre s) :
    WP isa (.block load) s fun u =>
      Holds (V s) u ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r, ¬ Words r → u.gpr r = s.gpr r) := by
  have hi : LI s 0 s := ⟨fun _ _ h => by omega, rfl,rfl,rfl,fun _ _ => rfl⟩
  have hl : WP isa (.block load) s (LI s 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s) (fun k u hk h => load_step hp hk h)
      16 (Nat.le_refl _) s hi
  exact hl.mono fun _ h => ⟨fun k hk => h.loaded k hk hk,h.mem,h.rd,h.wr,h.keep⟩

/-- Feed forward and serialize the scalar block into the existing scratch. -/
theorem scalarFinish_ok (s : State) (hp : Pre s) {R : CState} (hh : Holds R s) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.finish) s fun u =>
      (∀ k (hk : k < 16), u.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * k)) 32 =
        R[k] + (V s)[k]) ∧ Frame [⟨s.gpr .x1,64⟩] s.mem u.mem ∧
      (∀ r, ¬ Words r → u.gpr r = s.gpr r) := by
  rw [finish_split, WP.block_append_iff, WP.block_append_iff]
  refine (first_ok hp hh rfl rfl rfl (fun _ _ => rfl)).mono fun a ha => ?_
  refine (wp_range_flatMap (M := isa) (FI s R s) (fun i u hi h => add_step hp hi h)
    15 (Nat.le_refl _) a ha).mono fun b hb => ?_
  exact (VG.Proof.ChaCha20.AArch64.last_ok hp hb).mono fun _ ⟨ho,hk,hf⟩ => ⟨ho,hf,hk⟩

/-- Scalar instructions retain every vector, including the four NEON states. -/
theorem keeps_vectors {is : List Instr} (hv : ∀ i ∈ is, vdstOf i = none)
    {s : State} {Q : State → Prop} (hp : WP isa (.block is) s Q) :
    WP isa (.block is) s fun u => Q u ∧ u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain ⟨t,u,he,hq⟩ := hp
  refine ⟨t,u,he,hq,funext fun r => Exec.vec (fun i hi => by simp [hv i hi]) he,Exec.sp he,(Exec.regions he rfl).1,(Exec.regions he rfl).2.1⟩

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Spec.ChaCha20 (stateAt)

/-- The high bit tests the public number of complete blocks against five.
Dividing the byte count by 64 first makes the test valid for every u64 length. -/
theorem less5 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n >>> 6) - BitVec.ofNat 64 5) >>> 63 =
      BitVec.ofNat 64 (if n < 320 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  have hd : n / 2 ^ 6 < 2 ^ 58 := by omega
  by_cases h : n < 320
  · rw [ite_eq_left h]
    have hb : n / 2 ^ 6 < 5 := by omega
    omega
  · rw [ite_eq_right h]
    have hb : 5 ≤ n / 2 ^ 6 := by omega
    omega

theorem check_ok (s : State) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.check) s fun u =>
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < 320 then 1 else 0) ∧
      (∀ r, r ≠ .x5 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, VG.Impl.ChaCha20.AArch64.Mixed5.check, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, isa, runStep_some, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_,fun r hr => by simp only [hr,ite_false],rfl,rfl,rfl,rfl,rfl⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using VG.Proof.ChaCha20.AArch64.Mixed5.less5 (s.gpr .x2).toNat (s.gpr .x2).isLt

theorem counter_ok (s : State) {n : Nat} (hn : n < 4096) (subtract : Bool)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (ho : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (counter n subtract)) s fun u =>
      u.mem = s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 48)
        (if subtract then s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 48) 32 - BitVec.ofNat 32 n
         else s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 n) ∧
      (∀ r, r ≠ .x4 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  cases subtract <;> apply WP.of_runBlock <;>
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, counter,
      List.cons_append, List.nil_append, runBlock_cons, runBlock_nil,
      exec, addr, Size.bytes, State.load, hi, ho, State.store,
      State.read, Size.bits, hn, isa, runStep_some, RegUpd.gpr_write,
      RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write, RegUpd.sp_write,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals refine ⟨rfl,fun r hr => by simp only [hr,ite_false],trivial⟩

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Impl.ChaCha20.AArch64.Neon4 (vreg rowWord)
open VG.Proof.ChaCha20.AArch64.Neon4

/-- Only the first four slots of this data view have been written. -/
theorem Data.frame64 {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) (hd : ∀ k ∈ done, k < 4) : Frame [⟨p,64⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 64 := by
    have hh := hx ⟨p,64⟩ (by simp)
    simp only [Region.Contains] at hh
    omega
  rw [h x,ite_eq_right]
  rintro ⟨hslot,hlt⟩
  have hs := hd _ hslot
  omega

theorem loadLast_ok (s : State) (r : Fin 4)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block [.ldrq (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0)) .x3 (16 * r)]) s fun u =>
      u.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0)) = s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 ∧
      Same s u := by
  have ha : (16 * r.val) % 16 = 0 ∧ 16 * r.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceMul, runBlock_cons,runBlock_nil,exec,addr,ha,and_self,
    State.load,hi,Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,
    exists_eq_left',RegUpd.v_setV_self]
  exact ⟨trivial,rfl,rfl,rfl,rfl,rfl⟩

theorem xorLastRows_ok (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p b : Addr} {v : CState} {done : List Nat}
    (hd : Data m₀ s.mem p (output (fun _ => v)) done)
    (hdone : ∀ k ∈ done, k < 4) (hp : s.gpr .x1 = p) (hb : s.gpr .x3 = b)
    (hbuf : ∀ r : Fin 4, s.mem.read (b + BitVec.ofNat 64 (16 * r)) 16 =
      output (fun _ => v) r)
    (hsep : (⟨b,64⟩ : Region).Disjoint ⟨p,64⟩)
    (hfresh : ∀ r ∈ rs, r.val ∉ done)
    (hin : ∀ r : Fin 4, InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (16 * r)) 16)
    (hout : ∀ r : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block (rs.flatMap xorLastRow)) s fun u =>
      Data m₀ u.mem p (output (fun _ => v)) (rs.map Fin.val ++ done) ∧
      Keep s u := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd,⟨rfl,rfl,rfl,rfl⟩⟩
  | cons r rs ih =>
    apply WP.block_append
    apply WP.block_append
    have hi : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 := hb ▸ hin r
    refine (VG.Proof.ChaCha20.AArch64.Mixed5.loadLast_ok s r hi).mono fun a ⟨ha,hsa⟩ => ?_
    have hda : Data m₀ a.mem p (output (fun _ => v)) done := hsa.mem ▸ hd
    have hpa : a.gpr .x1 = p := by rw [hsa.gpr,hp]
    have hva : a.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0)) = output (fun _ => v) (slot r 0) := by
      simpa only [slot,Fin.val_zero,Nat.mul_zero,Nat.zero_add,hb,hbuf r] using ha
    have hoa : InRegions a.wr (p + BitVec.ofNat 64 (64 * (0 : Fin 4) + 16 * r)) 16 := by
      rw [hsa.wr]; simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hout r
    have hoa' : InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (64 * (0 : Fin 4) + 16 * r)) 16 := by
      rw [hpa]; exact hoa
    refine (xorRow_ok a r 0 hoa').mono fun u ⟨hm,hau⟩ => ?_
    have hu : Data m₀ u.mem p (output (fun _ => v)) (slot r 0 :: done) := by
      rw [hm,hpa,hva,show 64 * (0 : Fin 4).val + 16 * r.val = 16 * slot r 0 by simp [slot]]
      exact hda.store (slot_lt r 0) (by simpa [slot] using hfresh r (by simp))
    have hsu : Keep s u := ⟨hau.gpr.trans hsa.gpr,hau.rd.trans hsa.rd,
      hau.wr.trans hsa.wr,hau.sp.trans hsa.sp⟩
    have hdone' : ∀ k ∈ slot r 0 :: done, k < 4 := by
      intro k hk
      rcases List.mem_cons.mp hk with he | he
      · subst k; simp [slot]
      · exact hdone k he
    have hf := Data.frame64 hu hdone'
    have hf₀ := Data.frame64 hd hdone
    have hbu : ∀ q : Fin 4, u.mem.read (b + BitVec.ofNat 64 (16 * q)) 16 =
        output (fun _ => v) q := by
      intro q
      rw [hf.read (r := ⟨b,64⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro z hz; simpa using (List.mem_singleton.mp hz ▸ hsep)) (by decide), ← hf₀.read (r := ⟨b,64⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro z hz; simpa using (List.mem_singleton.mp hz ▸ hsep)) (by decide),hbuf q]
    have hpu : u.gpr .x1 = p := by rw [hsu.gpr,hp]
    have hpb : u.gpr .x3 = b := by rw [hsu.gpr,hb]
    have hiu : ∀ q : Fin 4, InRegions (u.rd ++ u.wr) (b + BitVec.ofNat 64 (16 * q)) 16 := by
      intro q; rw [hsu.rd,hsu.wr]; exact hin q
    have hou : ∀ q : Fin 4, InRegions u.wr (p + BitVec.ofNat 64 (16 * q)) 16 := by
      intro q; rw [hsu.wr]; exact hout q
    have hfr : ∀ q ∈ rs, q.val ∉ slot r 0 :: done := by
      intro q hq
      simp only [List.mem_cons,not_or]
      refine ⟨?_,hfresh q (by simp [hq])⟩
      intro he
      have hne := (List.nodup_cons.mp hn).1
      apply hne
      have eq : q = r := Fin.ext (by simpa [slot] using he)
      exact eq ▸ hq
    refine (ih (List.nodup_cons.mp hn).2 hu hdone' hpu hpb hbu hfr hiu hou).mono
      fun z ⟨hz,huz⟩ => ⟨?_,hsu.trans huz⟩
    intro x
    simpa only [Data,List.map_cons,List.mem_append,List.mem_cons,slot,Fin.val_zero,
      Nat.mul_zero,Nat.zero_add,or_assoc,or_left_comm] using hz x

theorem xorLast_ok (s : State) (v : CState)
    (hbuf : ∀ r : Fin 4, s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      output (fun _ => v) r)
    (hsep : (⟨s.gpr .x3,64⟩ : Region).Disjoint ⟨s.gpr .x1,64⟩)
    (hin : ∀ r : Fin 4, InRegions (s.rd ++ s.wr)
      (s.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16)
    (hout : ∀ r : Fin 4, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap xorLastRow)) s fun u =>
      (∀ k < 64, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^ (VG.Spec.ChaCha20.serialize v).getD k 0) ∧
      Frame [⟨s.gpr .x1,64⟩] s.mem u.mem ∧ Keep s u := by
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.xorLastRows_ok (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (output (fun _ => v))) (by simp) rfl rfl hbuf hsep
    (by simp) hin hout).mono fun u ⟨hd,hk⟩ => ⟨?_,?_,hk⟩
  · intro k hk
    have hm : k / 16 ∈ (List.finRange 4).map Fin.val ++ ([] : List Nat) := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨⟨k / 16,by omega⟩,List.mem_finRange _,rfl⟩
    rw [hd _,Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64),ite_eq_left ⟨hm,by omega⟩,
      output_byte (fun _ => v) (by omega),Nat.mod_eq_of_lt hk]
  · apply Data.frame64 hd
    intro k hk
    simp only [List.append_nil,List.mem_map] at hk
    obtain ⟨r,_,rfl⟩ := hk
    exact r.isLt

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Args`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5

structure SavedArgs (len data : Addr) (s : State) : Prop where
  len : s.gpr .x19 = len
  data : s.gpr .x26 = data

theorem saveArgs_ok (s : State) : WP isa (.block saveArgs) s fun u =>
    VG.Proof.ChaCha20.AArch64.Mixed5.SavedArgs (s.gpr .x2) (s.gpr .x1) u ∧
    (∀ r, r ≠ .x19 → r ≠ .x26 → u.gpr r = s.gpr r) ∧
    u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, saveArgs,runBlock_cons,runBlock_nil,exec,
    State.read,Size.bits,isa,runStep_some,RegUpd.gpr_write,
    BitVec.setWidth_eq,BitVec.add_zero,Option.some.injEq,exists_eq_left']
  exact ⟨⟨rfl,rfl⟩,fun r h21 h22 => by simp only [h21,h22,ite_false],rfl,rfl,rfl,rfl,rfl⟩

theorem restoreArgs_ok (s : State) {len data : Addr} (h : VG.Proof.ChaCha20.AArch64.Mixed5.SavedArgs len data s) :
    WP isa (.block restoreArgs) s fun u =>
      u.gpr .x1 = data ∧ u.gpr .x2 = len ∧ u.gpr .x3 = s.gpr .x20 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restoreArgs,runBlock_cons,runBlock_nil,exec,
    State.read,Size.bits,ite_true,isa,runStep_some,RegUpd.gpr_write,
    BitVec.setWidth_eq,BitVec.add_zero,Option.some.injEq,exists_eq_left',h.len,h.data]
  exact ⟨rfl,rfl,rfl,fun r h1 h2 h3 => by simp only [h1,h2,h3,ite_false],rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Prepare`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock)

abbrev source (s : State) : CState := stateAt s.mem (s.gpr .x0)
abbrev sr (s : State) : Region := ⟨s.gpr .x0,64⟩
abbrev br (s : State) : Region := ⟨s.gpr .x3,320⟩
abbrev dr (s : State) : Region := ⟨s.gpr .x1,320⟩

structure CP (s : State) : Prop where
  x20 : s.gpr .x20 = s.gpr .x3
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (VG.Proof.ChaCha20.AArch64.Mixed5.sr s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed5.br s)
  st_d : (VG.Proof.ChaCha20.AArch64.Mixed5.sr s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed5.dr s)
  d_b : (VG.Proof.ChaCha20.AArch64.Mixed5.dr s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed5.br s)

structure Prepared (s₀ s : State) (n : Nat := 0) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) j)) s
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  scalar : VG.Proof.ChaCha20.AArch64.Holds (Nat.repeat innerBlock n (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4)) s
  cnt : VG.Proof.ChaCha20.AArch64.Mixed5.source s = ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4
  saved : VG.Proof.ChaCha20.AArch64.Mixed5.SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀] s₀.mem s.mem

 theorem prepare_ok (s : State) (hp : VG.Proof.ChaCha20.AArch64.Mixed5.CP s) : WP isa VG.Impl.ChaCha20.AArch64.Mixed5.prepare s (VG.Proof.ChaCha20.AArch64.Mixed5.Prepared s) := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.saveArgs_ok s).mono fun a ⟨hsaved,hg,hm₀,hr,hw,hv,hsp⟩ => ?_
  have ha : VG.Proof.ChaCha20.AArch64.Mixed5.source a = VG.Proof.ChaCha20.AArch64.Mixed5.source s := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hm₀,hg _ (by decide) (by decide)]
  have hi : ∀ k : Fin 16, InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hg _ (by decide) (by decide),hr,hw]; exact hp.read k
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setup_ok a hi).mono fun b ⟨hb,hab,hbt⟩ => ?_
  have h0 : b.gpr .x0 = s.gpr .x0 := by rw [hab.gpr _ (by decide),hg _ (by decide) (by decide)]
  have hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.rd,hab.wr,h0,hr,hw]; exact hp.read 12
  have hco : InRegions b.wr (b.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hab.wr,hw,h0]; exact hp.counter
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.counter_ok b (n := 4) (by decide) false hc hco).mono fun c
    ⟨hcm,hcg,hcr,hcw,hcv,hcsp⟩ => ?_
  have hcnt : VG.Proof.ChaCha20.AArch64.Mixed5.source c = ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s) 4 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hcg _ (by decide),hcm]
    change stateAt (b.mem.writeW (b.gpr .x0 + BitVec.ofNat 64 48)
      (b.mem.readW (b.gpr .x0 + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 4)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr]
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hab.mem,hab.gpr _ (by decide)]
    exact congrArg (fun v => ctr v 4) ha
  have hfc : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s] b.mem c.mem := by
    rw [hcm,h0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hcs : VG.Proof.ChaCha20.AArch64.Mixed5.SavedArgs (s.gpr .x2) (s.gpr .x1) c := by
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
      exact hp.st_d.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hload : ∀ i ∈ VG.Impl.ChaCha20.AArch64.load, vdstOf i = none := by
    intro i hi
    simp only [VG.Impl.ChaCha20.AArch64.load,List.mem_flatMap] at hi
    obtain ⟨k,_,hi⟩ := hi
    simp only [List.mem_singleton] at hi
    subst i
    rfl
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hload (VG.Proof.ChaCha20.AArch64.Mixed5.scalarLoad_ok c hpc)).mono fun d ⟨⟨hd,hm,hdrr,hdwr,hdk⟩,hdv,hdsp,_,_⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,?_,hdrr.trans (hcr.trans (hab.rd.trans hr)),
    hdwr.trans (hcw.trans (hab.wr.trans hw)),hdsp.trans (hcsp.trans (hab.sp.trans hsp)),?_⟩
  · intro k j hj
    rw [hdv,hcv]
    have hbb : VG.Proof.ChaCha20.AArch64.Neon4.Holds (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source a)) b := hb
    rw [ha] at hbb
    exact hbb k j hj
  · rw [hdv,hcv,hbt]
  · simpa only [VG.Proof.ChaCha20.AArch64.V,hcnt,Nat.repeat] using hd
  · rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hm,hdk _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact hcnt
  · exact ⟨by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.len,
      by rw [hdk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact hcs.data⟩
  · intro r hnr h21 h22
    rw [hdk r hnr,hcg r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),
      hab.gpr r (by intro he; subst r; exact hnr ⟨2,by decide,by rfl⟩),hg r h21 h22]
  · rw [hm]
    rw [hab.mem,hm₀] at hfc
    exact hfc

theorem compute_ok (s : State) (hp : VG.Proof.ChaCha20.AArch64.Mixed5.CP s) :
    WP isa (.seq VG.Impl.ChaCha20.AArch64.Mixed5.prepare (VG.Impl.ChaCha20.AArch64.Mixed5.rounds 10)) s fun u => VG.Proof.ChaCha20.AArch64.Mixed5.Prepared s u 10 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.prepare_ok s hp).mono fun a h => ?_
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.rounds_ok h.vec h.table h.scalar 10).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
  refine ⟨hv,ht,hc.holds,?_,?_,?_,hc.rd.trans h.rd,hc.wr.trans h.wr,hsp.trans h.sp,?_⟩
  · rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]
    exact h.cnt
  · exact ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩
  · intro r hr h21 h22; rw [hc.keep r hr,h.keep r hr h21 h22]
  · rw [hc.mem]; exact h.frame

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Spill`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev lowBuf (s : State) : Region := ⟨s.gpr .x3,64⟩

/-- Move a public pointer, preserving all other state. -/
theorem move_ok (s : State) (d n : Reg) :
    WP isa (.block [.addImm .x d n 0]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u d (s.gpr n) ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x d (s.gpr n),?_,WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
  simpa only [State.read,BitVec.setWidth_eq,BitVec.add_zero] using
    exec_addImm_x (s := s) (d := d) (n := n) (imm := 0) (by decide)

structure Spilled (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Neon4.Holds
    (fun j => Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) j)) s
  cnt : VG.Proof.ChaCha20.AArch64.Mixed5.source s = ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4
  saved : VG.Proof.ChaCha20.AArch64.Mixed5.SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  words : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀] s₀.mem s.mem

theorem spill_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed5.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.Prepared s₀ s 10) :
    WP isa VG.Impl.ChaCha20.AArch64.Mixed5.spill s (VG.Proof.ChaCha20.AArch64.Mixed5.Spilled s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide)
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.move_ok s .x1 .x20).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4)) a := by
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
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hfinish (VG.Proof.ChaCha20.AArch64.Mixed5.scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  have hfb : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  have hcntₐ : VG.Proof.ChaCha20.AArch64.Mixed5.source a = ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  have hcntb : VG.Proof.ChaCha20.AArch64.Mixed5.source b = ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))]
    exact hcntₐ
  have hsavedb : VG.Proof.ChaCha20.AArch64.Mixed5.SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,hcntb,hsavedb,?_,?_,?_,
    hr.trans (ha.rd.trans h.rd),hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds,hbv,hav] using h.vec
  · intro k hkk
    have he := hb k hkk
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,VG.Spec.ChaCha20.block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr hr1 h21 h22; rw [hk r hnr,ha.other r hr1,h.keep r hnr h21 h22]
  · rw [hk _ VG.Proof.ChaCha20.AArch64.not_words_x1,ha.gpr,hx20]
  · rw [ha.mem] at hfb
    exact (h.frame.mono (by simp)).trans (hfb.mono (by simp))

theorem Spilled.read16 {s₀ s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed5.Spilled s₀ s) (r : Fin 4) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4)) r := by
  rw [VG.AArch64.read16]
  have hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4))[4 * r.val + e]'(by omega) := by
    intro e he
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega]
    exact h.words _ (by omega)
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.mod_eq_of_lt r.isLt,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Finish`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev firstR (s : State) : Region := ⟨s.gpr .x1,256⟩

structure Finished (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : VG.Proof.ChaCha20.AArch64.Mixed5.source s = VG.Proof.ChaCha20.AArch64.Mixed5.source s₀
  buf : ∀ r : Fin 4, s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
    VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4)) r
  data : ∀ k < 256, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀,VG.Proof.ChaCha20.AArch64.Mixed5.firstR s₀] s₀.mem s.mem

theorem finish_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed5.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.Spilled s₀ s) :
    WP isa VG.Impl.ChaCha20.AArch64.Mixed5.finish s (VG.Proof.ChaCha20.AArch64.Mixed5.Finished s₀) := by
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.restoreArgs_ok s h.saved).mono fun a
    ⟨ha1,ha2,ha3,hag,ham,har,haw,hav,hasp⟩ => ?_
  have ha0 : a.gpr .x0 = s₀.gpr .x0 := (hag _ (by decide) (by decide) (by decide)).trans hx0
  have ha₃ : a.gpr .x3 = s₀.gpr .x3 := ha3.trans hx20
  have har' : a.rd = s₀.rd := har.trans h.rd
  have haw' : a.wr = s₀.wr := haw.trans h.wr
  have hcnta : VG.Proof.ChaCha20.AArch64.Mixed5.source a = ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4 := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,ham,hag _ (by decide) (by decide) (by decide)]; exact h.cnt
  have hc : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [har',haw',ha0]; exact hp.read 12
  have hco : InRegions a.wr (a.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [haw',ha0]; exact hp.counter
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.counter_ok a (n := 4) (by decide) true hc hco).mono fun b
    ⟨hbm,hbg,hbr,hbw,hbv,hbsp⟩ => ?_
  have hb0 : b.gpr .x0 = s₀.gpr .x0 := (hbg _ (by decide)).trans ha0
  have hcntb : VG.Proof.ChaCha20.AArch64.Mixed5.source b = VG.Proof.ChaCha20.AArch64.Mixed5.source s₀ := by
    rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hbg _ (by decide),hbm]
    change stateAt (a.mem.writeW (a.gpr .x0 + BitVec.ofNat 64 48)
      (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 48) 32 - BitVec.ofNat 32 4)) _ = _
    rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      ← VG.Proof.ChaCha20.AArch64.Xor.stateAt_getElem_counter]
    change (VG.Proof.ChaCha20.AArch64.Mixed5.source a).set 12 ((VG.Proof.ChaCha20.AArch64.Mixed5.source a)[12] - BitVec.ofNat 32 4) = _
    rw [hcnta,ctr,Vector.getElem_set_self,BitVec.add_sub_cancel,Vector.set_set,
      Vector.set_getElem_self]
  have hfb : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀] a.mem b.mem := by
    rw [hbm,ha0]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))
  have hv : VG.Proof.ChaCha20.AArch64.Neon4.Holds
      (fun j => Nat.repeat innerBlock 10 (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) j)) b := by
    simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds,hbv,hav] using h.vec
  have hin : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hbr,hbw,har',haw',hb0]; exact hp.read k
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv hin).mono fun c ⟨hvc,hbc⟩ => ?_
  have hcb0 : c.gpr .x0 = s₀.gpr .x0 := (hbc.gpr _ (by decide)).trans hb0
  have hcb1 : c.gpr .x1 = s₀.gpr .x1 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha1)
  have hcb3 : c.gpr .x3 = s₀.gpr .x3 := (hbc.gpr _ (by decide)).trans ((hbg _ (by decide)).trans ha₃)
  have hrc : c.rd = s₀.rd := hbc.rd.trans (hbr.trans har')
  have hwc : c.wr = s₀.wr := hbc.wr.trans (hbw.trans haw')
  have hvc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) j)) c := by
    intro k j hj
    rw [hvc k j hj,VG.Proof.ChaCha20.AArch64.Neon4.input_eq]
    change _ + (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source b) j)[k] = _
    rw [hcntb]
    simp only [VG.Spec.ChaCha20.block,Vector.getElem_zipWith,Fin.getElem_fin]
  have hout : ∀ r j : Fin 4, InRegions c.wr
      (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hwc,hcb1]; exact hp.data _ _ (by omega)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hvc' hout).mono fun d ⟨hd,hfd,hcd⟩ => ?_
  have hfd' : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.firstR s₀] c.mem d.mem := by simpa only [hcb1] using hfd
  have hfc : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀] s.mem c.mem := by rw [hbc.mem,← ham]; exact hfb
  have hpre : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀] s₀.mem c.mem :=
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
  · rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hcd.gpr,hcb0,VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfd' (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right (Region.sub_prefix (by decide : 256 ≤ 320))),hbc.mem]
    rw [← hb0]; exact hcntb
  · intro r
    rw [hfd'.read (r := VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact (hp.d_b.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))).symm.sub_left
            (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide),
      hfc.read (r := VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst q
          exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))) (by decide)]
    exact h.read16 r
  · intro k hk
    rw [hcb1] at hd
    rw [hd k hk,hpre.bytes (R := VG.Proof.ChaCha20.AArch64.Mixed5.dr s₀) (by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      · exact hp.st_d.symm
      · exact hp.d_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))
      (by change 320 ≤ 2 ^ 64; decide) (by change k < 320; omega)]

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Chunk`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev lastR (s : State) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 256,64⟩

 theorem pointer_ok (s : State) {n : Nat} (hn : n < 4096) (sub : Bool) :
    WP isa (.block [if sub then .subImm .x .x1 .x1 n else .addImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1
        (if sub then s.gpr .x1 - BitVec.ofNat 64 n else s.gpr .x1 + BitVec.ofNat 64 n) ∧
      u.v = s.v ∧ u.sp = s.sp := by
  cases sub with
  | false =>
    change WP isa (.block [.addImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1 (s.gpr .x1 + BitVec.ofNat 64 n) ∧
        u.v = s.v ∧ u.sp = s.sp
    apply WP.block_cons_iff.mpr
    refine ⟨s.write .x .x1 (s.gpr .x1 + BitVec.ofNat 64 n),?_,
      WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
    simpa only [State.read,BitVec.setWidth_eq] using exec_addImm_x hn
  | true =>
    change WP isa (.block [.subImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1 (s.gpr .x1 - BitVec.ofNat 64 n) ∧
        u.v = s.v ∧ u.sp = s.sp
    apply WP.block_cons_iff.mpr
    refine ⟨s.write .x .x1 (s.gpr .x1 - BitVec.ofNat 64 n),?_,
      WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
    simpa only [State.read,BitVec.setWidth_eq] using exec_subImm_x hn

 theorem first_last_disjoint (s : State) : (VG.Proof.ChaCha20.AArch64.Mixed5.firstR s).Disjoint (VG.Proof.ChaCha20.AArch64.Mixed5.lastR s) := by
  exact Offset.base_disjoint (s.gpr .x1) (e := 256) (n := 64) (k := 256) (by decide) (by decide)

structure Chunked (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : VG.Proof.ChaCha20.AArch64.Mixed5.source s = VG.Proof.ChaCha20.AArch64.Mixed5.source s₀
  data : ∀ k < 320, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀,VG.Proof.ChaCha20.AArch64.Mixed5.dr s₀] s₀.mem s.mem

 theorem last_ok {s₀ s : State} (hp : VG.Proof.ChaCha20.AArch64.Mixed5.CP s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.Finished s₀ s) :
    WP isa last s (VG.Proof.ChaCha20.AArch64.Mixed5.Chunked s₀) := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.pointer_ok s (n := 256) (by decide) false).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have ha1 : a.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 256 := by simpa only [Bool.false_eq_true,ite_false,h.x1] using ha.gpr
  have ha3 : a.gpr .x3 = s₀.gpr .x3 := (ha.other _ (by decide)).trans h.x3
  have hf : ∀ r : Fin 4, a.mem.read (a.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4)) r := by
    intro r; rw [ha.mem,ha3]; exact h.buf r
  have sep : (⟨a.gpr .x3,64⟩ : Region).Disjoint ⟨a.gpr .x1,64⟩ := by
    rw [ha3,ha1]
    exact (hp.d_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))).sub_right
      (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))
  have hin : ∀ r : Fin 4, InRegions (a.rd ++ a.wr) (a.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r; rw [ha.rd,ha.wr,h.rd,h.wr,ha3]
    obtain ⟨q,hq,hc⟩ := hp.buffer (16 * r.val) 16 (by omega)
    exact ⟨q,List.mem_append_right _ hq,hc⟩
  have hout : ∀ r : Fin 4, InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r; rw [ha.wr,h.wr,ha1,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.data _ _ (by omega)
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.xorLast_ok a (VG.Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Mixed5.source s₀) 4)) hf sep hin hout).mono fun b ⟨hb,hfb,hab⟩ => ?_
  have hfb' : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.lastR s₀] s.mem b.mem := by simpa only [ha1,ha.mem] using hfb
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.pointer_ok b (n := 256) (by decide) true).mono fun c ⟨hc,hcv,hcsp⟩ => ?_
  have hc1 : c.gpr .x1 = s₀.gpr .x1 := by
    rw [hc.gpr,hab.gpr,ha.gpr]
    simp only [ite_true,Bool.false_eq_true,ite_false,BitVec.add_sub_cancel,h.x1]
  have hd (r : Reg) (hr : r ≠ .x1) : c.gpr r = s.gpr r := by
    rw [hc.other r hr,hab.gpr,ha.other r hr]
  have hm : c.mem = b.mem := hc.mem
  refine ⟨(hd _ (by decide)).trans h.x0,hc1,(hd _ (by decide)).trans h.x2,
    (hd _ (by decide)).trans h.x3,?_,hc.rd.trans (hab.rd.trans (ha.rd.trans h.rd)),
    hc.wr.trans (hab.wr.trans (ha.wr.trans h.wr)),hcsp.trans (hab.sp.trans (hasp.trans h.sp)),?_,?_,?_⟩
  · intro r hr h21 h22
    have nr : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    rw [hd r nr]; exact h.cs r hr h21 h22
  · rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hm,hd _ (by decide),h.x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb' (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact hp.st_d.sub_right (Offset.sub_base _ (by decide : 256 + 64 ≤ 320)))]
    rw [← h.x0]; exact h.cnt
  · intro k hk
    rw [hm]
    by_cases hk' : k < 256
    · have he : b.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) = s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) :=
        hfb'.bytes (R := VG.Proof.ChaCha20.AArch64.Mixed5.firstR s₀) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact VG.Proof.ChaCha20.AArch64.Mixed5.first_last_disjoint s₀) (by change 256 ≤ 2 ^ 64; decide) hk'
      rw [he]
      exact h.data k hk'
    · have he : a.gpr .x1 + BitVec.ofNat 64 (k - 256) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        rw [ha1,BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' (by omega)]
      have hh := hb (k - 256) (by omega)
      rw [he,ha.mem] at hh
      have hh₀ := h.frame.bytes (R := VG.Proof.ChaCha20.AArch64.Mixed5.lastR s₀) (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.st_d.symm.sub_left (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))
        · exact (hp.d_b.sub_left (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))).sub_right
            (Region.sub_prefix (by decide : 64 ≤ 320))
        · exact (VG.Proof.ChaCha20.AArch64.Mixed5.first_last_disjoint s₀).symm)
        (by change 64 ≤ 2 ^ 64; decide) (i := k - 256) (by change k - 256 < 64; omega)
      have he₀ : (VG.Proof.ChaCha20.AArch64.Mixed5.lastR s₀).base + BitVec.ofNat 64 (k - 256) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        change s₀.gpr .x1 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (k - 256) = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' (by omega)]
      rw [he₀] at hh₀
      rw [hh,hh₀,show k / 64 = 4 by omega,show k % 64 = k - 256 by omega]
  · rw [hm]
    have hf₁ : Frame [VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀,VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀,VG.Proof.ChaCha20.AArch64.Mixed5.dr s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed5.sr s₀,by simp,fun _ h => h⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s₀,by simp,fun _ h => h⟩
      · exact ⟨VG.Proof.ChaCha20.AArch64.Mixed5.dr s₀,by simp,Region.sub_prefix (by decide : 256 ≤ 320)⟩)
    exact hf₁.trans (hfb'.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨VG.Proof.ChaCha20.AArch64.Mixed5.dr s₀,by simp,Offset.sub_base _ (by decide : 256 + 64 ≤ 320)⟩))

 theorem chunk_ok (s : State) (hp : VG.Proof.ChaCha20.AArch64.Mixed5.CP s) : WP isa VG.Impl.ChaCha20.AArch64.Mixed5.chunk s (VG.Proof.ChaCha20.AArch64.Mixed5.Chunked s) := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.prepare_ok s hp).mono fun a h => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.rounds_ok h.vec h.table h.scalar 10).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
  have h' : VG.Proof.ChaCha20.AArch64.Mixed5.Prepared s b 10 := ⟨hv,ht,hc.holds,by
      rw [VG.Proof.ChaCha20.AArch64.Mixed5.source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact h.cnt,
    ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩,
    fun r hr h21 h22 => (hc.keep r hr).trans (h.keep r hr h21 h22),hc.rd.trans h.rd,hc.wr.trans h.wr,
    hsp.trans h.sp,by rw [hc.mem]; exact h.frame⟩
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.spill_ok hp h').mono fun c hc => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.finish_ok hp hc).mono fun d hd => VG.Proof.ChaCha20.AArch64.Mixed5.last_ok hp hd

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit`. -/
section

namespace VG
materialize_code Impl.ChaCha20.AArch64.Mixed5.xor
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Loop`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (320 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 320 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 320 * t ≤ L s₀
  cs : ∀ r ∈ preserved, r ≠ .x20 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (5 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 320 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀,dR s₀,bR s₀] s₀.mem s.mem

structure BulkInv (s₀ : State) (t : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.AArch64.Mixed5.LInv s₀ t s where
  x20 : s.gpr .x20 = bp s₀
  saved : ∀ j : Fin 3, s.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
    s₀.gpr ([.x20,.x19,.x26].getD j .x20)

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 320 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (VG.Spec.ChaCha20.block (ctr (ctr S (5 * t)) ((k - 320 * t) / 64)))).getD
        ((k - 320 * t) % 64) 0 := by
  rw [keystream_getD _ hk,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
    show 5 * t + (k - 320 * t) / 64 = k / 64 by omega,
    show (k - 320 * t) % 64 = k % 64 by omega]

 theorem next_ok (s : State) (hlen : 320 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.next) s fun u =>
      u.gpr .x1 = s.gpr .x1 + 320 ∧ u.gpr .x2 = s.gpr .x2 - 320 ∧
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat - 320 < 320 then 1 else 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 5 ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, VG.Impl.ChaCha20.AArch64.Mixed5.next,counter,VG.Impl.ChaCha20.AArch64.Mixed5.check,
    List.cons_append,List.nil_append,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,?_,?_,?_,trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 320 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 320) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he,VG.Proof.ChaCha20.AArch64.Mixed5.less5 _ (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5; simp only [h1,h2,h4,h5,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) 5
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (320 * t),320⟩
theorem win_sub {s₀ : State} {t : Nat} (h : 320 * t + 320 ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Mixed5.win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem cp_of_inv {s₀ s : State} (hp : XPre s₀) {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t s)
    (hge : 320 * t + 320 ≤ L s₀) : VG.Proof.ChaCha20.AArch64.Mixed5.CP s := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hw : s.wr = [stR s₀,dR s₀,bR s₀] := h.wr.trans hp.wr
  refine ⟨h.x20.trans h.x3.symm,?_,?_,?_,?_,?_,?_,?_⟩
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
  · change (⟨s.gpr .x0,64⟩ : Region).Disjoint ⟨s.gpr .x1,320⟩
    rw [h.x0,h.x1]; exact hp.st_d.sub_right (VG.Proof.ChaCha20.AArch64.Mixed5.win_sub hge)
  · change (⟨s.gpr .x1,320⟩ : Region).Disjoint ⟨s.gpr .x3,320⟩
    rw [h.x1,h.x3]; exact hp.d_b.sub_left (VG.Proof.ChaCha20.AArch64.Mixed5.win_sub hge)

 theorem chunkData {s₀ s u : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t s)
    (hge : 320 * t + 320 ≤ L s₀) (hu : VG.Proof.ChaCha20.AArch64.Mixed5.Chunked s u) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 320 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  by_cases hin : 320 * t ≤ k ∧ k < 320 * t + 320
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 320 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1,BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' hin.1]
    have hh := hu.data (k - 320 * t) (by omega)
    rw [he,h.data k hk,ite_eq_right (by omega),VG.Proof.ChaCha20.AArch64.Mixed5.source,h.x0,h.cnt, ← VG.Proof.ChaCha20.AArch64.Mixed5.ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (VG.Proof.ChaCha20.AArch64.Mixed5.win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
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
          (Region.sub_prefix (by decide : 64 ≤ 320) _ (by simpa only [VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf,h.x3] using hc))
      · change ¬ (⟨s.gpr .x1,320⟩ : Region).Contains _ 1
        rw [h.x1]; exact hx)
    rw [hh,h.data k hk]
    by_cases hold : k < 320 * t
    · rw [ite_eq_left hold,ite_eq_left (by omega)]
    · rw [ite_eq_right hold,ite_eq_right (by omega)]

abbrev guardR (s₀ : State) (j : Fin 3) : Region := ⟨bp s₀ + BitVec.ofNat 64 (256 + 8 * j),8⟩

theorem guard_chunk {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t s)
    (hge : 320 * t + 320 ≤ L s₀) (j : Fin 3) :
    ∀ r ∈ [VG.Proof.ChaCha20.AArch64.Mixed5.sr s,VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf s,VG.Proof.ChaCha20.AArch64.Mixed5.dr s], (VG.Proof.ChaCha20.AArch64.Mixed5.guardR s₀ j).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (VG.Proof.ChaCha20.AArch64.Mixed5.guardR s₀ j).Disjoint ⟨s.gpr .x0,64⟩
    rw [h.x0]
    exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))
  · change (VG.Proof.ChaCha20.AArch64.Mixed5.guardR s₀ j).Disjoint ⟨s.gpr .x3,64⟩
    rw [h.x3]
    exact Offset.disjoint_base _ (by have hj := j.isLt; omega) (by have hj := j.isLt; omega)
  · change (VG.Proof.ChaCha20.AArch64.Mixed5.guardR s₀ j).Disjoint ⟨s.gpr .x1,320⟩
    rw [h.x1]
    exact (hp.d_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega))).sub_right
      (VG.Proof.ChaCha20.AArch64.Mixed5.win_sub hge)

 theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 320 * t + 320 ≤ L s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t s) :
    WP isa VG.Impl.ChaCha20.AArch64.Mixed5.body s fun u => VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ (t + 1) u ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 320 * (t + 1) < 320 then 1 else 0) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.chunk_ok s (VG.Proof.ChaCha20.AArch64.Mixed5.cp_of_inv hp h hge)).mono fun u hu => ?_
  have hx0 : u.gpr .x0 = st s₀ := hu.x0.trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (320 * t) := hu.x1.trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 320 * t) := hu.x2.trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := hu.x3.trans h.x3
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (5 * t) := by
    have hc := hu.cnt
    change stateAt u.mem (u.gpr .x0) = stateAt s.mem (s.gpr .x0) at hc
    rw [hx0,h.x0,h.cnt] at hc
    exact hc
  have hdata := VG.Proof.ChaCha20.AArch64.Mixed5.chunkData hp h hge hu
  have hw : u.wr = [stR s₀,dR s₀,bR s₀] := hu.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hu.rd,h.rd,hp.rd,hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 320 * t := by
    rw [hx2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hsaved : ∀ j : Fin 3, u.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      s₀.gpr ([.x20,.x19,.x26].getD j .x20) := by
    intro j
    rw [hu.frame.readW (r := VG.Proof.ChaCha20.AArch64.Mixed5.guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (VG.Proof.ChaCha20.AArch64.Mixed5.guard_chunk hp h hge j) (by decide),h.saved j]
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1,hv2,hv5,hkeep,hctr,hframe,hrd,hwr,hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (320 * (t + 1)) := by
    rw [hv1,hx1,BitVec.add_assoc]
    change _ + (BitVec.ofNat 64 (320 * t) + BitVec.ofNat 64 320) = _
    rw [← BitVec.ofNat_add,show 320 * t + 320 = 320 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 320 * (t + 1)) := by
    rw [hv2,hx2]
    change BitVec.ofNat 64 (L s₀ - 320 * t) - BitVec.ofNat 64 320 = _
    rw [Offset.ofNat_sub_ofNat (by omega),show L s₀ - 320 * t - 320 = L s₀ - 320 * (t + 1) by omega]
  refine ⟨⟨⟨?_,hptr,hrem,?_,by omega,?_,hrd.trans (hu.rd.trans h.rd),
    hwr.trans (hu.wr.trans h.wr),hsp.trans (hu.sp.trans h.sp),?_,?_,?_⟩,?_,?_⟩,?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx3]
  · intro r hr hr20 hr21 hr22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [hkeep r n1 n2 n4 n5,hu.cs r hr hr21 hr22,h.cs r hr hr20 hr21 hr22]
  · rw [hx0,hcnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
      show 5 * t + 5 = 5 * (t + 1) by omega] at hctr
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
      · exact ⟨bR s₀,by simp,by simpa only [VG.Proof.ChaCha20.AArch64.Mixed5.lowBuf,h.x3] using Region.sub_prefix (base := bp s₀) (by decide : 64 ≤ 320)⟩
      · exact ⟨dR s₀,by simp,by simpa only [VG.Proof.ChaCha20.AArch64.Mixed5.dr,h.x1] using VG.Proof.ChaCha20.AArch64.Mixed5.win_sub hge⟩)
    have hn' : Frame [stR s₀,dR s₀,bR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hu.cs _ (by decide) (by decide) (by decide),h.x20]
  · intro j
    rw [hframe.readW (r := VG.Proof.ChaCha20.AArch64.Mixed5.guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsaved j]
  · rw [hv5,hlen,show L s₀ - 320 * t - 320 = L s₀ - 320 * (t + 1) by omega]

theorem init_ok (s : State) : WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.check) s fun u =>
    VG.Proof.ChaCha20.AArch64.Mixed5.LInv s 0 u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s < 320 then 1 else 0) := by
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.check_ok s).mono fun u ⟨h5,hg,hm,hr,hw,hv,hsp⟩ => ?_
  refine ⟨⟨hg _ (by decide),?_,?_,hg _ (by decide),by omega,?_,hr,hw,hsp,?_,?_,?_⟩,
    ?_,h5⟩
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
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 320 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (320 ≤ n)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero s .x5,h]
  by_cases hn : n < 320
  · simp only [ite_eq_left hn]
    have hnn : ¬ 320 ≤ n := by omega
    simp [hnn]
  · simp only [ite_eq_right hn]
    have hnn : 320 ≤ n := by omega
    simp [hnn]

 theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ 0 s)
    (hge : 320 ≤ L s₀) : WP isa (.loop VG.Impl.ChaCha20.AArch64.Mixed5.body (.zero .x .x5)) s fun u =>
      ∃ t, L s₀ - 320 * t < 320 ∧ VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t u := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ t, n = L s₀ - 320 * t ∧ 320 ≤ n ∧ VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t s
  refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0,by omega,hge,h⟩
  intro n s ⟨t,hn,hge,hi⟩
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.body_ok hp (by omega) hi).mono fun u ⟨hu,h5⟩ => ?_
  have hc := VG.Proof.ChaCha20.AArch64.Mixed5.zero_batches h5
  by_cases he : L s₀ - 320 * (t + 1) < 320
  · left
    refine ⟨?_,t + 1,he,hu⟩
    have hne : ¬ 320 ≤ L s₀ - 320 * (t + 1) := by omega
    simpa only [decide_eq_false hne] using hc
  · right
    refine ⟨?_,L s₀ - 320 * (t + 1),by omega,t + 1,rfl,by omega,hu⟩
    have hne : 320 ≤ L s₀ - 320 * (t + 1) := by omega
    simpa only [decide_eq_true hne] using hc

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Save`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

theorem read_saved (m : Mem) (p : Addr) (a b c : BitVec 64) (j : Fin 3) :
    (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 (256 + 8 * j)) 64 =
        [a,b,c].getD j a := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
  rcases hj with rfl | rfl | rfl
  · change (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 256) 64 = a
    rw [Mem.readW_writeW_sep (Offset.sep p (d := 256) (n := 8) (e := 272) (k := 8)
      (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (d := 256) (n := 8) (e := 264) (k := 8)
        (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
  · change (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 264) 64 = b
    rw [Mem.readW_writeW_sep (Offset.sep p (d := 264) (n := 8) (e := 272) (k := 8)
      (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _

 theorem enter_ok {s₀ s : State} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.LInv s₀ 0 s)
    (hold : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) : WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.enter) s (VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ 0) := by
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

 theorem leave_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : VG.Proof.ChaCha20.AArch64.Mixed5.BulkInv s₀ t s) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed5.leave) s fun u => VG.Proof.ChaCha20.AArch64.Mixed5.LInv s₀ t u ∧
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

end VG.Proof.ChaCha20.AArch64.Mixed5

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Xor`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
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
  ⟨dp s₀ + BitVec.ofNat 64 (320 * t), L s₀ - 320 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 320 * t ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Mixed5.tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 320 * t) (ht : 320 * t ≤ L s₀) :
    ¬ (VG.Proof.ChaCha20.AArch64.Mixed5.tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem tail_ok {s₀ : State} (hp : XPre s₀) {t : Nat} {s : State} (h : VG.Proof.ChaCha20.AArch64.Mixed5.LInv s₀ t s) (hcs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hle := h.le
  have hn : (BitVec.ofNat 64 (L s₀ - 320 * t)).toNat = L s₀ - 320 * t :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, VG.Proof.ChaCha20.AArch64.Mixed5.tailR s₀ t, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := VG.Proof.ChaCha20.AArch64.Mixed5.tail_sub h.le
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
    · exact ⟨dR s₀, by simp, 320 * t, rfl, by dsimp; omega⟩
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
      by_cases hk' : k < 320 * t
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact VG.Proof.ChaCha20.AArch64.Mixed5.not_tail hk' h.le
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (320 * t) + BitVec.ofNat 64 (k - 320 * t) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := VG.Proof.ChaCha20.AArch64.Mixed5.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 320 * t) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, VG.Proof.ChaCha20.AArch64.Mixed5.ks_shift _ hk (t := t) (by omega)]

theorem nonzero_short {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 320 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 320)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 320 <;> simp [hn]

theorem correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Mixed5.xor s fun u =>
      abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  apply WP.withPreservedV (hc := by lit_decide)
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.init_ok s).mono fun a ⟨hi,hcs,h5⟩ => ?_
  apply WP.seq
  have hb : WP isa (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block Impl.ChaCha20.AArch64.Mixed5.enter)
        (.seq (.loop Impl.ChaCha20.AArch64.Mixed5.body (.zero .x .x5))
          (.block Impl.ChaCha20.AArch64.Mixed5.leave)))) a fun u =>
      ∃ t, VG.Proof.ChaCha20.AArch64.Mixed5.LInv s t u ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) := by
    apply WP.ite (decide (L s < 320)) (VG.Proof.ChaCha20.AArch64.Mixed5.nonzero_short h5)
    · intro _; exact WP.block_nil ⟨0,hi,hcs⟩
    · intro hshort
      have hge : 320 ≤ L s := by have hh := of_decide_eq_false hshort; omega
      apply WP.seq
      refine (VG.Proof.ChaCha20.AArch64.Mixed5.enter_ok (XPre.of s hp) hi hcs).mono fun b hb => ?_
      apply WP.seq
      refine (VG.Proof.ChaCha20.AArch64.Mixed5.bulk_ok (XPre.of s hp) hb hge).mono fun c ⟨t,_,hc⟩ => ?_
      exact (VG.Proof.ChaCha20.AArch64.Mixed5.leave_ok (XPre.of s hp) hc).mono fun _ ⟨hd,hcs⟩ => ⟨t,hd,hcs⟩
  refine hb.mono fun u ⟨t,hu,hcs⟩ => VG.Proof.ChaCha20.AArch64.Mixed5.tail_ok (XPre.of s hp) hu hcs

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa Impl.ChaCha20.AArch64.Mixed5.xor s t u ∧ abiPreserved s u ∧
      xorAArch64.post s u :=
  (VG.Proof.ChaCha20.AArch64.Mixed5.correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : Impl.ChaCha20.AArch64.Mixed5.xor.noFrames = true := by lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub
    Impl.ChaCha20.AArch64.Mixed5.xor := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => VG.Proof.ChaCha20.AArch64.Xor.agree₀ hp) (by taint_decide)

theorem xor_verified : Verified AArch64.target Impl.ChaCha20.AArch64.Mixed5.xor
    (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.AArch64.Mixed5.xor_correct VG.Proof.ChaCha20.AArch64.Mixed5.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract,Spec.ChaCha20.xorSig,AArch64.abi,AArch64.argRegs,
      xorAArch64] [VG.Proof.ChaCha20.AArch64.Xor.sat] using VG.Proof.ChaCha20.AArch64.Xor.sat)

end VG.Proof.ChaCha20.AArch64.Mixed5

end
