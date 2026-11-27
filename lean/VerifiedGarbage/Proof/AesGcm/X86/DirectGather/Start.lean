module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Frame
public import VerifiedGarbage.Proof.AesGcm.X86.Open
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Text
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Setup
import VerifiedGarbage.Proof.Gcm.Ctr

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86.DirectGather

variable {N : Nat}

/-- `768 ≤ N`, from the gather layout at hand. -/
macro_rules | `(tactic| wbig) => `(tactic| exact VG.Proof.AesGcm.X86.Gather.Lay.big (by with_reducible assumption))




theorem Prepared.arg_eq {s t : State} (p : Prepared N s t) (i : Nat) (hi : i<11) :
    arg t i = arg s (sourceSlot i) := by
  change t.mem.readW (addr (t.gpr .esp) (4+4*i)) 32 = _
  rw [show t.gpr .esp=SP N s from p.regs .esp (by decide)]
  exact p.slots i hi

theorem Prepared.op {s t : State} (h : Gather.Lay N s) (p : Prepared N s t) : OP N 12 11 t := by
  have sp : t.gpr .esp=SP N s := p.regs .esp (by decide)
  have b : w64 (SP N s) = Gather.Bs N s + BitVec.ofNat 64 76 := by
    change w64 (s.gpr .esp - BitVec.ofNat 32 (N + 52)) = _
    rw [Gather.w64_sub (by omega_using [h.w₁]),h.hE,Gather.add_ofNat_sub_ofNat _ (by gdec), show N + 128 - (N + 52) = 76 by omega]
  have k : 32 ≤ (SP N s).toNat := by
    change 32 ≤ (s.gpr .esp - BitVec.ofNat 32 (N + 52)).toNat
    rw [Gather.sub_toNat32 (by omega_using [h.w₁])]; omega_using [h.w₁]
  have w : w64 (work N s) = w64 (SP N s)+BitVec.ofNat 64 52 :=
    norm h (d := 52) (by gdec)
  have a : argAddr t 0 = w64 (SP N s)+BitVec.ofNat 64 4 := by
    change addr (t.gpr .esp) 4 = _; rw [sp,norm h (by gdec)]
  have ws : (⟨w64 (work N s),N⟩ : Region).Sub (Gather.stkR s N) := by
    rw [w,b,Offset.add_ofNat_add_ofNat]; exact Gather.stk_sub _ _ _ _ (by gdec)
  have ars : (⟨argAddr t 0,48⟩ : Region).Sub (Gather.stkR s N) := by
    rw [a,b,Offset.add_ofNat_add_ofNat]; exact Gather.stk_sub _ _ _ _ (by gdec)
  have rs : (⟨w64 (SP N s),4⟩ : Region).Sub (Gather.stkR s N) := by
    rw [b]; exact Gather.stk_sub _ _ _ _ (by gdec)
  have lo : below (SP N s) 32 = ⟨Gather.Bs N s+BitVec.ofNat 64 44,32⟩ := by
    rw [← below_eq k]
    change (⟨w64 (SP N s)-BitVec.ofNat 64 32,32⟩ : Region) = _
    rw [b,Gather.add_ofNat_sub_ofNat _ (by decide)]
  have lows : (below (SP N s) 32).Sub (Gather.stkR s N) := by
    rw [lo]; exact Gather.stk_sub _ _ _ _ (by gdec)
  constructor <;> (try unfold roundsOk) <;> (try rw [p.scratch]) <;>
    (try simp only [p.arg_eq _ (by decide : 0<11),p.arg_eq _ (by decide : 1<11),
      p.arg_eq _ (by decide : 2<11),p.arg_eq _ (by decide : 3<11),p.arg_eq _ (by decide : 4<11),
      p.arg_eq _ (by decide : 5<11),p.arg_eq _ (by decide : 6<11),p.arg_eq _ (by decide : 7<11),
      sourceSlot, Nat.reduceLT, ite_true, ite_false, Nat.reduceAdd]) <;> (try rw [sp])
  case cR => rw [p.rd,p.wr,h.rd]; exact covers_of_mem (by simp [Gather.kR,Gather.K])
  case nR => rw [p.rd,p.wr,h.rd]; exact covers_of_mem (by simp [Gather.nR,Gather.Nn,Gather.NL])
  case aR => rw [p.rd,p.wr,h.rd]; exact covers_of_mem (by simp [Gather.aR,Gather.Ad,Gather.AL])
  case dW => rw [p.rd,p.wr]; exact covers_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ (h.wr ▸ by simp [Gather.dR,Gather.Dst,Gather.L])))
  case wW =>
    rw [p.wr,w]; exact covers_off (k := (N + 52)) (covers_of_mem (List.mem_cons_self ..)) (by gdec) (by gdec)
  case argR =>
    rw [p.rd,p.wr,a]; exact covers_off (k := (N + 52)) (covers_of_mem (List.mem_append_right _ (List.mem_cons_self ..))) (by gdec) (by gdec)
  case c_w => exact (h.bk.sub_left ws).symm
  case n_w => exact (h.bn.sub_left ws).symm
  case a_w => exact (h.ba.sub_left ws).symm
  case d_w => exact (h.bd.sub_left ws).symm
  case d_a => exact (h.bd.sub_left ars).symm
  case w_a => rw [w,a]; exact Offset.disjoint _ (by gdec) (by gdec) (by decide)
  case r_d => exact h.bd.sub_left rs
  case r_w => rw [w]; exact (Offset.disjoint_base _ (by decide) (by gdec)).symm
  case k_c => exact h.bk.sub_left lows
  case k_n => exact h.bn.sub_left lows
  case k_a => exact h.ba.sub_left lows
  case k_d => exact h.bd.sub_left lows
  case k_w => rw [lo,w,b,Offset.add_ofNat_add_ofNat]; exact Offset.disjoint _ (by gdec) (by decide) (by gdec)
  case fc => exact h.ok
  case fn => exact h.on
  case fa => exact h.oa
  case fd => exact h.od
  case fw =>
    change (SP N s+BitVec.ofNat 32 52).toNat+N ≤ _
    rw [BitVec.toNat_add_of_lt (by omega_using [spFit h,show (BitVec.ofNat 32 52).toNat=52 by decide])]
    omega_using [spFit h,show (BitVec.ofNat 32 52).toNat=52 by decide]
  case sp => exact k
  case fg => omega_using [spFit h]
  case rounds => exact h.hR

end VG.Proof.AesGcm.X86.DirectGather

end

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86

variable {N : Nat}


@[expose] def text (N : Nat) (s : State) : Text :=
  ⟨Gather.K s, work N s, SP N s, Gather.Src s, Gather.Dst s, Gather.Cnt s, Gather.L s, (arg s 1).toNat⟩

abbrev ArgR (N : Nat) (s : State) := (⟨(text N s).dstArg,4⟩ : Region)

structure Zones (N : Nat) (s : State) : Prop where
  workspace : (⟨w64 (work N s),N⟩ : Region).Sub (Gather.stkR s N)
  ret : (⟨w64 (SP N s),4⟩ : Region).Sub (Gather.stkR s N)
  lower : (below (SP N s) 32).Sub (Gather.stkR s N)
  arg : (ArgR N s).Sub (Gather.stkR s N)
  argOutside : Text.Outside N (text N s) (ArgR N s)
  argFit : (ArgR N s).base.toNat+4 ≤ 2^32

theorem zones {s : State} (h : Gather.Lay N s) : Zones N s := by
  have b : w64 (SP N s) = Gather.Bs N s + BitVec.ofNat 64 76 := by
    change w64 (s.gpr .esp - BitVec.ofNat 32 (N + 52)) = _
    rw [Gather.w64_sub (by omega_using [h.w₁]),h.hE,Gather.add_ofNat_sub_ofNat _ (by gdec), show N + 128 - (N + 52) = 76 by omega]
  have k : 32 ≤ (SP N s).toNat := by
    change 32 ≤ (s.gpr .esp - BitVec.ofNat 32 (N + 52)).toNat
    rw [Gather.sub_toNat32 (by omega_using [h.w₁])]; omega_using [h.w₁]
  have w : w64 (work N s) = Gather.Bs N s+BitVec.ofNat 64 128 := by
    rw [show w64 (work N s)=_ from norm h (d := 52) (by gdec),b,Offset.add_ofNat_add_ofNat]
  have a : (text N s).dstArg = Gather.Bs N s+BitVec.ofNat 64 104 := by
    change addr (SP N s) 28 = _; rw [norm h (by gdec),b,Offset.add_ofNat_add_ofNat]
  have lo : below (SP N s) 32 = ⟨Gather.Bs N s+BitVec.ofNat 64 44,32⟩ := by
    rw [← below_eq k]; change (⟨w64 (SP N s)-BitVec.ofNat 64 32,32⟩ : Region) = _
    rw [b,Gather.add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨w ▸ Gather.stk_sub _ _ _ _ (by gdec),b ▸ Gather.stk_sub _ _ _ _ (by gdec),
    lo ▸ Gather.stk_sub _ _ _ _ (by gdec),?_,?_,?_⟩
  · unfold ArgR; rw [a]; exact Gather.stk_sub _ _ _ _ (by gdec)
  · constructor <;> change Region.Disjoint (ArgR N s) _ <;> unfold ArgR <;> rw [a]
    · change Region.Disjoint _ ⟨w64 (work N s),N⟩; rw [w]; exact Offset.disjoint _ (by gdec) (by decide) (by gdec)
    · change Region.Disjoint _ ⟨w64 (SP N s),4⟩; rw [b]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · change Region.Disjoint _ (below (SP N s) 32); rw [lo]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · change (w64 (SP N s+28#32)).toNat+4 ≤ 2^32
    rw [toNat_w64,BitVec.toNat_add_of_lt (by omega_using [spFit h,show (28#32).toNat=28 by decide])]
    omega_using [spFit h,show (28#32).toNat=28 by decide]

theorem Zones.outside {s : State} (z : Zones N s) {r : Region} (hr : (Gather.stkR s N).Disjoint r) :
    Text.Outside N (text N s) r := ⟨(hr.sub_left z.workspace).symm,(hr.sub_left z.ret).symm,(hr.sub_left z.lower).symm⟩

theorem input_of {s t u : State} (h : Gather.Lay N s) (p : Prepared N s t)
    (env : Env N (text N s).C (text N s).st (text N s).W (text N s).SP u)
    (rounds : RoundsAt u.mem (work N s) (arg s 1).toNat)
    (rd : u.rd=t.rd) (wr : u.wr=t.wr) (fr : Frame [Gather.stkR s N] s.mem u.mem)
    (dst : u.mem.readW (text N s).dstArg 32=Gather.Dst s) : TextInput N (text N s) u := by
  have z := zones h
  have op := p.op h
  have ol := op.ol rfl (by decide) rfl
  have lay := ol.L
  change Lay N (arg t 0) (stOf (arg t 11)) (arg t 11) (t.gpr .esp) 32 at lay
  rw [p.arg_eq _ (by decide),p.scratch,show t.gpr .esp=SP N s from p.regs _ (by decide)] at lay
  have orig : ∀ r ∈ Sig.descRegion 32 (w64 (Gather.Src s)) (Gather.Cnt s) :: Gather.lsR s,
      ∀ x, r.Contains x 1 → s.mem x = u.mem x := by
    intro r hr x hx
    have dis : (Gather.stkR s N).Disjoint r := by
      rcases List.mem_cons.mp hr with rfl|hr
      · exact h.bds
      · exact h.bls r hr
    exact (fr x fun q hq hqx => by obtain rfl := List.mem_singleton.mp hq; exact dis x hqx hx).symm
  have same := (Proof.AesGcm.listed_congr_le (Nat.le_refl _) orig).1
  have src (i) (hi : i<Gather.Cnt s) :
      (⟨w64 ((text N s).source u.mem i),(text N s).size u.mem i⟩ : Region) ∈ Gather.lsR s := by
    unfold Gather.lsR; rw [← same]; exact Gather.slice_mem u.mem h.ods hi
  have rd' : u.rd=s.rd := rd.trans p.rd
  have wr' : u.wr=(allocated N s).wr := wr.trans p.wr
  have cov (r : Region) (hr : r∈s.rd) : Covers [r] (u.rd++u.wr) :=
    covers_of_mem (List.mem_append_left _ (rd' ▸ hr))
  have dstW : Covers [Gather.dR s] u.wr := by
    rw [wr']; exact covers_of_mem (List.mem_cons_of_mem _ (h.wr ▸ by simp))
  have retW : Covers [⟨w64 (SP N s),4⟩] u.wr := by
    rw [wr']; simpa using covers_off (d := 0) (k := (N + 52)) (n := 4)
      (covers_of_mem (List.mem_cons_self (a := (⟨w64 (SP N s),(N + 52)⟩ : Region)) (l := s.wr))) (by gdec) (by gdec)
  refine ⟨lay,env,rounds,(Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) orig).trans h.hgl,
    (arg s 7).isLt,(arg s 9).isLt,h.ods,h.od,cov (Gather.dsR s) (h.rd ▸ by simp),?_,?_,dstW,z.outside h.bds,
    fun i hi => z.outside (h.bls _ (src i hi)),z.outside h.bd,z.argOutside,h.dds.symm,
    fun i hi => (h.dls _ (src i hi)).symm,h.bd.sub_left z.arg,h.kd,(h.bk.sub_left z.ret).symm,
    ?_,by change (SP N s).toNat+4 ≤ _; omega_using [spFit h],retW,?_,dst⟩
  · intro i hi; exact cov _ (h.rd ▸ List.mem_append_right _ (src i hi))
  · intro i hi; exact h.ol _ (src i hi)
  · have hh := op.r_w
    rw [show t.gpr .esp=SP N s from p.regs _ (by decide),p.scratch] at hh
    exact hh
  · rw [wr']; exact ⟨_,List.mem_append_right _ (List.mem_cons_self ..),by
      change (⟨w64 (SP N s),(N + 52)⟩ : Region).Contains (addr (SP N s) 28) 4
      rw [norm h (by gdec)]; exact Offset.contains_base _ (by gdec) (by decide)⟩

end VG.Proof.AesGcm.X86.DirectGather

end

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Spec.Gcm

variable {N : Nat}


abbrev pub (t : State) := pubSw 12 8 t
abbrev scratchAreas (N : Nat) (s : State) : List Region := [⟨w64 (work N s),N⟩,below (SP N s) 32]

structure Params (N : Nat) (s t : State) : Prop where
  sp : (pub t).1=SP N s
  w : (pub t).2 8=work N s
  c : (pub t).2 0=Gather.K s
  r : (pub t).2 1=arg s 1
  d : (pub t).2 6=Gather.Dst s
  l : (pub t).2 7=arg s 9

theorem Prepared.params {s t : State} (p : Prepared N s t) : Params N s t :=
  ⟨p.regs _ (by decide),p.scratch,p.arg_eq 0 (by decide),p.arg_eq 1 (by decide),
    p.arg_eq 6 (by decide),p.arg_eq 7 (by decide)⟩

theorem aad_frame {s t e u : State} (p : Prepared N s t) (en : OEnt N (pub t) t e)
    (aad : Frame (oF N (pub t)) e.mem u.mem) (hN : 768 ≤ N) : Frame (scratchAreas N s) t.mem u.mem := by
  have a := p.params
  have fe := en.frame
  rw [a.w] at fe
  apply Frame.trans (fe.sub ?_) (aad.sub ?_)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self ..,Lay.wSubN (by gdec)⟩
  · intro r hr; simp only [oF,a.w,a.sp,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSubN (by gdec)⟩
    · exact ⟨_,by simp [scratchAreas],fun _ hx => hx⟩

theorem private_arg_kept {s t u : State} (h : Gather.Lay N s) (p : Prepared N s t)
    (f : Frame (scratchAreas N s) t.mem u.mem) (i : Nat) (hi : i<11) :
    u.mem.readW (argA (SP N s) i) 32 = arg s (VG.Impl.AesGcm.X86.DirectGather.sourceSlot i) := by
  have op := p.op h
  have sp : t.gpr .esp=SP N s := p.regs _ (by decide)
  have argSub : (⟨argA (SP N s) i,4⟩ : Region).Sub (argsR (SP N s) 12) := by
    change Region.Sub ⟨addr (SP N s) (4+4*i),4⟩ ⟨addr (SP N s) 4,48⟩
    rw [norm h (by omega_using [hi]),norm h (by gdec)]
    exact Offset.sub _ (by omega) (by omega)
  refine (f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans (p.slots i hi)
  rcases List.mem_cons.mp hr with rfl|hr
  · have aw := op.w_a.symm; rw [← argsR_eq,sp,p.scratch] at aw; exact aw.sub_left argSub
  · obtain rfl := List.mem_singleton.mp hr
    change Region.Disjoint ⟨addr (SP N s) (4+4*i),4⟩ (below (SP N s) 32)
    rw [norm h (by omega_using [hi]),← below_eq (sp ▸ op.sp)]
    change Region.Disjoint _ ⟨w64 (SP N s)-BitVec.ofNat 64 32,32⟩
    rw [show w64 (SP N s)+BitVec.ofNat 64 (4+4*i) =
      (w64 (SP N s)-BitVec.ofNat 64 32)+BitVec.ofNat 64 (32+(4+4*i)) by
        rw [BitVec.ofNat_add (n := 64) (x := 32) (y := 4+4*i),← BitVec.add_assoc,BitVec.sub_add_cancel]]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem start_frame {s t u : State} (h : Gather.Lay N s) (p : Prepared N s t)
    (f : Frame (scratchAreas N s) t.mem u.mem) : Frame [Gather.stkR s N] s.mem u.mem := by
  have z := zones h
  apply Frame.trans (p.frame.sub ?_) (f.sub ?_)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,by
      change (⟨w64 (SP N s),52⟩ : Region).Sub (Gather.stkR s N)
      change Region.Sub ⟨w64 (s.gpr .esp - BitVec.ofNat 32 (N + 52)),52⟩ _
      rw [Gather.w64_sub (by omega_using [h.w₁]),h.hE,Gather.add_ofNat_sub_ofNat _ (by gdec), show N + 128 - (N + 52) = 76 by omega]
      exact Gather.stk_sub _ _ _ _ (by gdec)⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,List.mem_singleton_self _,z.workspace⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_singleton_self _,z.lower⟩


theorem loop_setup_frame {s u x : State}
    (hs : SetupPost u (work N s) (SP N s) 9 10 rO tglO (w64 (work N s)+BitVec.ofNat 64 xlO) x) (hN : 768 ≤ N) :
    Frame (scratchAreas N s) u.mem x.mem := hs.frame.sub fun r hr => by
  simp only [slotSetupFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  all_goals exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩

theorem setup_disjoint {W : BitVec 32} {o n : Nat}
    (h₁ : o+n≤rO ∨ rO+4≤o) (h₂ : o+n≤tglO ∨ tglO+4≤o) (h₃ : o+n≤xlO ∨ xlO+4≤o)
    (fit : o+n≤768) : ∀ r ∈ slotSetupFrame W rO tglO (w64 W+BitVec.ofNat 64 xlO),
      (⟨w64 W+BitVec.ofNat 64 o,n⟩ : Region).Disjoint r := by
  intro r hr; simp only [slotSetupFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Offset.disjoint _ h₁ (by omega) (by decide)
  · exact Offset.disjoint _ h₂ (by omega) (by decide)
  · exact Offset.disjoint _ h₃ (by omega) (by decide)

structure Begun (N : Nat) (s t x : State) : Prop where
  input : TextInput N (text N s) x
  ptr : slotv x.mem (work N s) rO = Gather.Src s
  count : slotv x.mem (work N s) tglO = BitVec.ofNat 32 (Gather.Cnt s)
  off : slotv x.mem (work N s) xlO=0
  ctr : CtrS x.mem (text N s).st (ciphOf x.mem (Gather.K s) (arg s 1).toNat) (inc32 (jOf (pub t) t)) 0
  frame : Frame (scratchAreas N s) t.mem x.mem

theorem begun {s t e u x : State} (h : Gather.Lay N s) (p : Prepared N s t)
    (en : OEnt N (pub t) t e) (aa : OAad N (pub t) t u) (f : Frame (oF N (pub t)) e.mem u.mem)
    (hs : SetupPost u (work N s) (SP N s) 9 10 rO tglO (w64 (work N s)+BitVec.ofNat 64 xlO) x) :
    Begun N s t x := by
  have fr := aad_frame p en f h.big
  have fx := fr.trans (loop_setup_frame hs h.big)
  have z := p.params
  have o := aa.o
  have eu := o.env
  rw [z.c,z.w,z.sp] at eu
  have rr := o.rounds
  rw [z.w,z.r] at rr
  have perm {W : BitVec 32} {n : Nat} (f : Frame (slotSetupFrame W rO tglO (w64 W+BitVec.ofNat 64 xlO)) u.mem x.mem)
      (d₁ : n+4≤rO ∨ rO+4≤n) (d₂ : n+4≤tglO ∨ tglO+4≤n) (d₃ : n+4≤xlO ∨ xlO+4≤n) (fit : n+4≤768) :
      slotv x.mem W n=slotv u.mem W n := slot_frame f (setup_disjoint d₁ d₂ d₃ fit)
  have ex : Env N (text N s).C (text N s).st (text N s).W (text N s).SP x :=
    ⟨(hs.regs _ (by decide)).trans eu.ebp,(hs.regs _ (by decide)).trans eu.esi,
     (hs.regs _ (by decide)).trans eu.esp,by rw [hs.rd,hs.wr]; exact eu.ctxR,
     hs.wr ▸ eu.stW,hs.wr ▸ eu.wW,(perm hs.frame (n := ctxO) (by decide) (by decide) (by decide) (by decide)).trans eu.ctx⟩
  have rx : RoundsAt x.mem (work N s) (arg s 1).toNat :=
    ⟨(perm hs.frame (n := roundsO) (by decide) (by decide) (by decide) (by decide)).trans rr.1,rr.2⟩
  have input := input_of h p ex rx (hs.rd.trans o.rd) (hs.wr.trans o.wr) (start_frame h p fx)
    (private_arg_kept h p fx 6 (by decide))
  refine ⟨input,hs.first.trans (private_arg_kept h p fr 9 (by decide)),?_,hs.zero,?_,fx⟩
  · rw [hs.second,private_arg_kept h p fr 10 (by decide)]; exact (ofNat_toNat32 _).symm
  · apply Proof.Gcm.ctr_zero
    have cb := aa.cb
    change blockAt u.mem (w64 (stOf ((pub t).2 8))+48#64) = inc32 (jOf (pub t) t) at cb
    rw [z.w] at cb
    refine (blockAt_frame hs.frame ?_).trans cb
    rw [stOf_w64 input.lay.fw,Offset.add_ofNat_add_ofNat]
    exact setup_disjoint (by decide) (by decide) (by decide) (by decide)

end VG.Proof.AesGcm.X86.DirectGather

end
