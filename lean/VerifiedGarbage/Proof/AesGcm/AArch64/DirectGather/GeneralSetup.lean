module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GeneralFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The incoming slice list stays in two dedicated workspace slots.
The ordinary GCM workspace slots retain the destination and total length. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Impl.AesGcm.AArch64.DirectGather

structure BodyEntry (o s : State) (wn : Nat) (u : State) : Prop where
  env : Env wn (K o) (genWork o wn+16) (genWork o wn) s.sp u
  x22 : u.gpr .x22 = o.gpr .x1
  x23 : u.gpr .x23 = o.gpr .x2
  x24 : u.gpr .x24 = o.gpr .x3
  x26 : u.gpr .x26 = o.gpr .x3
  x27 : u.gpr .x27 = 0
  aad : u.mem.readW (genWork o wn+216) 64 = Ad o
  alen : u.mem.readW (genWork o wn+224) 64 = o.gpr .x5
  dst : u.mem.readW (genWork o wn+232) 64 = Dst o
  len : u.mem.readW (genWork o wn+240) 64 = BitVec.ofNat 64 (L o)
  tag : u.mem.readW (genWork o wn+248) 64 = Tg o
  desc : u.mem.readW (genWork o wn+336) 64 = Src o
  count : u.mem.readW (genWork o wn+344) 64 = BitVec.ofNat 64 (Cnt o)
  saved : SavedAt u.mem (genWork o wn) s
  frame : Frame [⟨genWork o wn,wn⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

abbrev gatherSlots : List Instr :=
  [.str .x .x6 .x19 descO, .str .x .x7 .x19 countO,
   .ldrSp .x9 0, .str .x .x9 .x19 dataO, .ldrSp .x9 8, .str .x .x9 .x19 lenO]

theorem generalSetup_ok {o s : State} {wn : Nat} (h : GeneralEntry o s wn) (hwn : 768 ≤ wn) :
    WP isa (.block (oneEntry 24 ++ gatherSlots ++ stashArg 16)) s (BodyEntry o s wn) := by
  let W := genWork o wn
  have hi := h.bound
  have wk : Covers [⟨W,wn⟩] s.wr := by
    rw [h.wr]; apply Covers.of_sub; intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self ..,32,rfl,by change 32+wn ≤ wn+32; omega⟩
  have perm : Perm wn (K o) (W+BitVec.ofNat 64 16) W s :=
    ⟨Covers.of_mem fun r hr => by rw [h.rd,h.lay.pre.1,List.mem_singleton.mp hr]; simp [kR],
      covers_off (d := 16) wk (by omega) (by omega),wk,hwn,hi⟩
  have argSep (i : Nat) (hi : i ≤ 3) :
      (⟨s.sp+BitVec.ofNat 64 (8*i),8⟩ : Region).Disjoint ⟨W,wn⟩ := by
    rw [h.sp]; exact Offset.disjoint (genBase o wn) (e := 32) (.inl (by omega)) (by omega) (by omega)
  have argRead (i : Nat) (hi : i ≤ 3) : InRegions (s.rd++s.wr) (s.sp+BitVec.ofNat 64 (8*i)) 8 := by
    rw [h.wr,h.sp]; exact ⟨_,List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ (by change 8*i+8 ≤ wn+32; omega) (by omega)⟩
  rw [List.append_assoc,WP.block_append_iff]
  refine (oneEntry_args (k := 24) (by decide) h.work (argRead 3 (by decide)) (h.regs .x0 (by decide) (by decide)) perm).mono ?_
  intro a ⟨env,ar,an,al,ac,az,aad,alen,_,_,f,saved,rd,wr,a6,a7⟩
  have fa : Frame [⟨W,wn⟩] s.mem a.mem := f.sub fun q hq => ⟨_,List.mem_singleton_self _, entryR_work W ⟨hwn,hi⟩ q hq⟩
  have arg (i : Nat) (hlt : i < 3) : a.mem.readW (a.sp+BitVec.ofNat 64 (8*i)) 64 = stackArg o i := by
    rw [env.sp, fa.readW (r := ⟨_,8⟩) (Region.contains_self _ _)
      (by simpa only [List.mem_singleton,forall_eq] using argSep i (by omega)) (by decide),
      ← h.args i hlt]
  have ia (i : Nat) (hlt : i < 3) : InRegions (a.rd++a.wr) (a.sp+BitVec.ofNat 64 (8*i)) 8 := by
    rw [rd,wr,env.sp]; exact argRead i (by omega)
  have st (d : Nat) (hd : d+8 ≤ wn) : InRegions a.wr (W+BitVec.ofNat 64 d) 8 :=
    in_off env.perm.w hd (by omega)
  let writes := fun (m : Mem) => (((m.writeW (W+BitVec.ofNat 64 336) (a.gpr .x6)).writeW (W+BitVec.ofNat 64 344) (a.gpr .x7)).writeW
    (W+BitVec.ofNat 64 232) (Dst o)).writeW (W+BitVec.ofNat 64 240) (stackArg o 1)
  have ea : a.gpr .x19 = W := env.x19
  have bmem : ∃ b, runBlock isa gatherSlots a = some b ∧ b.mem = writes a.mem ∧
      Others [.x9] a b ∧ b.sp = a.sp ∧ b.rd = a.rd ∧ b.wr = a.wr := by
    have ir0 := ia 0 (by decide)
    have ir1 := ia 1 (by decide)
    have sw (d : Nat) (hd : d+8 ≤ wn) (v : BitVec 64) (m : Mem) :
        Frame [⟨W,wn⟩] m (m.writeW (W+BitVec.ofNat 64 d) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by omega))
    have readF (m : Mem) (hf : Frame [⟨W,wn⟩] a.mem m) (i : Nat) (hlt : i < 3) :
        m.read (a.sp+BitVec.ofNat 64 (8*i)) 8 = stackArg o i := by
      rw [hf.read (r := ⟨_,8⟩) (Region.contains_self _ _) (by
        rw [env.sp]; simpa only [List.mem_singleton,forall_eq] using argSep i (by omega)) (by decide)]
      exact arg i hlt
    let q := (a.mem.writeW (W+BitVec.ofNat 64 336) (a.gpr .x6)).writeW (W+BitVec.ofNat 64 344) (a.gpr .x7)
    have f2 := (sw 336 (by omega) (a.gpr .x6) a.mem).trans (sw 344 (by omega) (a.gpr .x7) _)
    have r0 := readF q f2 0 (by decide)
    have r1 := readF _ (f2.trans (sw 232 (by omega) (Dst o) _)) 1 (by decide)
    simp only [Nat.mul_zero,BitVec.add_zero] at ir0 r0
    change InRegions (a.rd++a.wr) (a.sp+8#64) 8 at ir1
    change q.read a.sp 8 = Dst o at r0
    change (q.writeW (W+BitVec.ofNat 64 232) (Dst o)).read (a.sp+8#64) 8 = stackArg o 1 at r1
    have e : runBlock isa gatherSlots a =
        some { (a.write .x .x9 (stackArg o 1)) with mem := writes a.mem } := by
      unfold gatherSlots
      simp only [q,Mem.writeW,BitVec.setWidth_eq] at r0 r1
      arun [BitVec.add_zero,ea,descO,countO,dataO,lenO,st 336 (by omega),st 344 (by omega),
        st 232 (by omega),st 240 (by omega),ir0,ir1,r0,r1,writes,Mem.writeW,State.write,q]
      congr 2
      funext r
      by_cases hr : r = Reg.x9 <;> simp [hr]
    rw [e]
    refine ⟨_,rfl,rfl,fun r hr => ?_,rfl,rfl,rfl⟩
    have ne : r ≠ Reg.x9 := by simpa using hr
    change (a.write .x .x9 _).gpr r = _
    simp [gpr_write,ne]
  rw [WP.block_append_iff]
  obtain ⟨b,run,bm,bg,bs,br,bw⟩ := bmem
  refine WP.of_runBlock ⟨b,run,?_⟩
  have full (d : Nat) (hd : d+8 ≤ wn) := Offset.contains_base W (n := 8) hd (by omega)
  have fb : Frame [⟨W,wn⟩] a.mem b.mem := by
    rw [bm]; exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (full 336 (by omega))).writeW
      (List.mem_singleton_self _) _ (full 344 (by omega))).writeW (List.mem_singleton_self _) _ (full 232 (by omega))).writeW
      (List.mem_singleton_self _) _ (full 240 (by omega))
  have b19 := (bg .x19 (by decide)).trans env.x19
  refine (stashArg_ok (V := Tg o) (k := 16) (by decide) b19 (bw ▸ env.perm.w)
    (by rw [bs]; simpa only [br,bw] using ia 2 (by decide)) (by
      rw [bs, fb.readW (r := ⟨_,8⟩) (Region.contains_self _ _) (by
        rw [env.sp]; simpa only [List.mem_singleton,forall_eq] using argSep 2 (by decide)) (by decide)]
      exact arg 2 (by decide)) ⟨hwn,hi⟩).mono ?_
  intro u ⟨_,um,ug,us,ur,uw⟩
  have regs (r : Reg) (hr : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x28) : u.gpr r = a.gpr r :=
    (ug r (by simp [hr.2.1,hr.2.2])).trans (bg r (by simp [hr.1]))
  have U : u.mem = (writes a.mem).writeW (W+BitVec.ofNat 64 248) (Tg o) := by rw [um,bm]
  have slot (d : Nat) (hd : d+8 ≤ 232) : u.mem.readW (W+BitVec.ofNat 64 d) 64 =
      a.mem.readW (W+BitVec.ofNat 64 d) 64 := by
    rw [U]; unfold writes
    repeat rw [readW_writeW_other _ W _ (.inl (by omega)) (by omega) (by decide)]
  have savedU : SavedAt u.mem W s := by
    intro p hp
    rw [slot _ (by
      simp only [VG.Impl.AesGcm.AArch64.saved,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact saved _ hp
  refine ⟨env.keep (fun r hr => regs r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide))
    (us.trans bs) (ur.trans br) (uw.trans bw),
    (regs _ (by decide)).trans (ar.trans (h.regs _ (by decide) (by decide))),
    (regs _ (by decide)).trans (an.trans (h.regs _ (by decide) (by decide))),
    (regs _ (by decide)).trans (al.trans (h.regs _ (by decide) (by decide))),
    (regs _ (by decide)).trans (ac.trans (h.regs _ (by decide) (by decide))),
    (regs _ (by decide)).trans az,(slot 216 (by decide)).trans (aad.trans (h.regs _ (by decide) (by decide))),
    (slot 224 (by decide)).trans (alen.trans (h.regs _ (by decide) (by decide))),?_,?_,?_,?_,?_,savedU,
    ?_,ur.trans (br.trans rd),uw.trans (bw.trans wr)⟩
  · change u.mem.readW (W+BitVec.ofNat 64 232) 64 = _
    rw [U]; unfold writes
    repeat first | rw [Mem.readW_writeW_self64] | rw [readW_writeW_other _ W _ (by decide) (by decide) (by decide)]
  · change u.mem.readW (W+BitVec.ofNat 64 240) 64 = _
    rw [U]; unfold writes
    rw [readW_writeW_other _ W _ (.inl (by decide)) (by decide) (by decide),Mem.readW_writeW_self64]
    simp [L]
  · change u.mem.readW (W+BitVec.ofNat 64 248) 64 = _
    rw [U,Mem.readW_writeW_self64]
  · change u.mem.readW (W+BitVec.ofNat 64 336) 64 = _
    rw [U]; unfold writes
    repeat first | rw [Mem.readW_writeW_self64] | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
    exact a6.trans (h.regs _ (by decide) (by decide))
  · change u.mem.readW (W+BitVec.ofNat 64 344) 64 = _
    rw [U]; unfold writes
    repeat first | rw [Mem.readW_writeW_self64] | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
    simpa only [Cnt,BitVec.ofNat_toNat,BitVec.setWidth_eq] using a7.trans (h.regs .x7 (by decide) (by decide))
  · rw [um]; exact (fa.trans fb).writeW (List.mem_singleton_self _) _ (full 248 (by omega))
end VG.Proof.AesGcm.AArch64.DirectGather
