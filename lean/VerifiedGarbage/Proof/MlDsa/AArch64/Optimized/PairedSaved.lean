import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads
import VerifiedGarbage.Proof.Framework.Offset

/-! ## From `PairedExtra.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def extraSlots (off : Nat) : List (VReg × Nat) :=
  saved.zipIdx.map fun (r,i) => (r,off+16*i)

theorem save_code : save=(extraSlots 2048).map (fun p => Instr.strq p.1 .x0 p.2) := rfl
theorem restore_code : restoreCode=(extraSlots 1920).map (fun p => Instr.ldrq p.1 .x2 p.2) := rfl

theorem save_ok {s : State}
    (hr : ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VMem s t (writeSlice (extraSlots 2048) (s.gpr .x0) s.v s.mem) →
      WP isa (.block rest) t Q) : WP isa (.block (save++rest)) s Q := by
  rw [save_code]
  exact store_many_ok _ _ (by decide) hr k

theorem restore_ok {s : State}
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg saved s t →
      (∀p∈extraSlots 1920,t.v p.1=s.mem.read (s.gpr .x2+BitVec.ofNat 64 p.2) 16) →
      WP isa (.block rest) t Q) : WP isa (.block (restoreCode++rest)) s Q := by
  rw [restore_code]
  exact load_many_ok _ _ (by decide) (by decide) hr k

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedSavedMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem read_write_self (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.write a 16 v).read a 16 = v := by
  simpa only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m a 16 v (by decide)

theorem writeSlice_read_other (xs : List (VReg × Nat)) (base a : Addr)
    (v : VReg → BitVec 128) (m : Mem)
    (hs : ∀ p∈xs,Mem.Sep a 16 (base+BitVec.ofNat 64 p.2) 16) :
    (writeSlice xs base v m).read a 16=m.read a 16 := by
  induction xs generalizing m with
  | nil => rfl
  | cons p xs ih =>
    change (writeSlice xs base v (m.write (base+BitVec.ofNat 64 p.2) 16 (v p.1))).read a 16=_
    rw [ih _ (fun q hq => hs q (List.mem_cons_of_mem _ hq)),
      Mem.read_write_sep (hs p (by simp)) (by decide)]

theorem writeSlice_read_slot (xs : List (VReg × Nat)) (base : Addr)
    (v : VReg → BitVec 128) (m : Mem) (p : VReg × Nat) (hp : p∈xs)
    (hs : ∀ q∈xs,q≠p → Mem.Sep (base+BitVec.ofNat 64 p.2) 16
      (base+BitVec.ofNat 64 q.2) 16) :
    (writeSlice xs base v m).read (base+BitVec.ofNat 64 p.2) 16=v p.1 := by
  induction xs generalizing m with
  | nil => simp at hp
  | cons q xs ih =>
    change (writeSlice xs base v (m.write (base+BitVec.ofNat 64 q.2) 16 (v q.1))).read _ 16=_
    by_cases ht : p∈xs
    · exact ih _ ht (fun r hr => hs r (List.mem_cons_of_mem _ hr))
    · have he : p=q := (List.mem_cons.mp hp).resolve_right ht
      subst q
      rw [writeSlice_read_other _ _ _ _ _ (fun r hr => hs r (List.mem_cons_of_mem _ hr)
        (by intro h; subst r; exact ht hr)),read_write_self]

theorem writeSlice_frame (xs : List (VReg × Nat)) (base : Addr)
    (v : VReg → BitVec 128) (m : Mem) (r : Region)
    (hc : ∀ p∈xs,r.Contains (base+BitVec.ofNat 64 p.2) 16) :
    Frame [r] m (writeSlice xs base v m) := by
  induction xs generalizing m with
  | nil => exact Frame.refl _ _
  | cons p xs ih =>
    change Frame [r] m (writeSlice xs base v (m.write (base+BitVec.ofNat 64 p.2) 16 (v p.1)))
    exact ((Frame.refl [r] m).write (List.mem_singleton_self _) _ (hc p (by simp))).trans
      (ih _ (fun q hq => hc q (List.mem_cons_of_mem _ hq)))

/-- An explicit index for each callee-saved vector. -/
def savedReg (i : Fin 8) : VReg := saved[i.val]!

theorem extraSlots_mem (off : Nat) (p : VReg × Nat) :
    p∈extraSlots off ↔ ∃ i : Fin 8,p=(savedReg i,off+16*i.val) := by
  have he : extraSlots off = (List.finRange 8).map (fun i => (savedReg i,off+16*i.val)) := rfl
  rw [he]
  simp only [List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨i,hi.symm⟩
  · rintro ⟨i,hi⟩; exact ⟨i,hi.symm⟩
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedSaved.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Saved full-width caller vectors at the end of the paired work buffer. -/
def Saved (m : Mem) (work : Addr) (v : VReg → BitVec 128) : Prop :=
  ∀ i : Fin 8,m.read (work+BitVec.ofNat 64 (2048+16*i.val)) 16=v (savedReg i)

theorem saved_after (m : Mem) (work : Addr) (v : VReg → BitVec 128) :
    Saved (writeSlice (extraSlots 2048) work v m) work v := by
  intro i
  refine writeSlice_read_slot _ _ _ _ (savedReg i,2048+16*i.val)
    ((extraSlots_mem _ _).mpr ⟨i,rfl⟩) ?_
  intro p hp hne
  obtain ⟨j,rfl⟩ := (extraSlots_mem _ _).mp hp
  have hij : i.val≠j.val := by
    intro he
    have he' : i=j := Fin.ext he
    subst j
    exact hne rfl
  exact Offset.sep work (by omega) (by omega) (by omega)

theorem saved_frame (m : Mem) (work : Addr) (v : VReg → BitVec 128) :
    Frame [⟨work+BitVec.ofNat 64 2048,128⟩] m (writeSlice (extraSlots 2048) work v m) := by
  refine writeSlice_frame _ _ _ _ _ ?_
  intro p hp
  obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
  exact Offset.contains work (e := 2048) (by omega) (by omega) (by decide)

theorem Saved.frame {m m' : Mem} {work : Addr} {v : VReg → BitVec 128}
    {rs : List Region} (h : Saved m work v) (hf : Frame rs m m')
    (hd : ∀r∈rs,(⟨work+BitVec.ofNat 64 2048,128⟩ : Region).Disjoint r) : Saved m' work v := by
  intro i
  have hc : (⟨work+BitVec.ofNat 64 2048,128⟩ : Region).Contains
      (work+BitVec.ofNat 64 (2048+16*i.val)) (128/8) :=
    Offset.contains work (e := 2048) (by omega) (by omega) (by decide)
  have he := hf.readW hc hd (by decide : 128/8<2^64)
  have hr : m'.read (work+BitVec.ofNat 64 (2048+16*i.val)) 16 =
      m.read (work+BitVec.ofNat 64 (2048+16*i.val)) 16 := by
    simpa only [Mem.readW,BitVec.setWidth_eq] using he
  exact hr.trans (h i)

/-- The inverse passes only write the first 2048 bytes of the work buffer. -/
theorem Saved.workFrame {m m' : Mem} {work : Addr} {v : VReg → BitVec 128}
    (h : Saved m work v) (hf : Frame [⟨work,2048⟩] m m') : Saved m' work v := by
  refine h.frame hf ?_
  intro r hr
  have he : r=⟨work,2048⟩ := List.mem_singleton.mp hr
  subst r
  exact Offset.disjoint_base work (d := 2048) (by decide) (by decide)

/-- At return x2 has advanced by 128 bytes, so restore offset1920 addresses the saved area. -/
theorem restore_saved {s : State} {work : Addr} {v : VReg → BitVec 128}
    (hx : s.gpr .x2=work+BitVec.ofNat 64 128) (hs : Saved s.mem work v)
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VG.Proof.MlKem.AArch64.VChg saved s t →
      (∀r∈saved,t.v r=v r) → WP isa (.block rest) t Q) :
    WP isa (.block (restoreCode++rest)) s Q := by
  refine restore_ok hr fun t ht hv => k t ht ?_
  intro r hr'
  have hex : ∃ i : Fin 8,r=savedReg i := by
    have he : saved=(List.finRange 8).map savedReg := rfl
    rw [he] at hr'
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hr'
    exact ⟨i,hi.symm⟩
  obtain ⟨i,rfl⟩ := hex
  have hh := hv (savedReg i,1920+16*i.val) ((extraSlots_mem _ _).mpr ⟨i,rfl⟩)
  rw [hx,BitVec.add_assoc,← BitVec.ofNat_add] at hh
  have he : 128+(1920+16*i.val)=2048+16*i.val := by omega
  simpa only [he,hs i] using hh

theorem save_saved {s : State}
    (hr : ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VG.Proof.MlKem.AArch64.VMem s t
        (writeSlice (extraSlots 2048) (s.gpr .x0) s.v s.mem) →
      Saved t.mem (s.gpr .x0) s.v →
      Frame [⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩] s.mem t.mem →
      WP isa (.block rest) t Q) : WP isa (.block (save++rest)) s Q := by
  refine save_ok hr fun t ht => k t ht ?_ ?_
  · rw [ht.mem]; exact saved_after _ _ _
  · rw [ht.mem]; exact saved_frame _ _ _

theorem restore_preservedV {s₀ s : State} {work : Addr}
    (hx : s.gpr .x2=work+BitVec.ofNat 64 128) (hs : Saved s.mem work s₀.v)
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VG.Proof.MlKem.AArch64.VChg saved s t →
      (∀r∈preservedV,(t.v r).extractLsb' 0 64=(s₀.v r).extractLsb' 0 64) →
      WP isa (.block rest) t Q) : WP isa (.block (restoreCode++rest)) s Q := by
  refine restore_saved hx hs hr fun t ht hv => k t ht ?_
  intro r hr'
  rw [hv r hr']
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
