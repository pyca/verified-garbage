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


theorem Prepared.arg_eq {s t : State} (p : Prepared s t) (i : Nat) (hi : i<11) :
    arg t i = arg s (sourceSlot i) := by
  change t.mem.readW (addr (t.gpr .esp) (4+4*i)) 32 = _
  rw [show t.gpr .esp=SP s from p.regs .esp (by decide)]
  exact p.slots i hi

theorem Prepared.op {s t : State} (h : Gather.Lay s) (p : Prepared s t) : OP 2560 12 11 t := by
  have sp : t.gpr .esp=SP s := p.regs .esp (by decide)
  have b : w64 (SP s) = Gather.Bs s + BitVec.ofNat 64 76 := by
    change w64 (s.gpr .esp - BitVec.ofNat 32 2612) = _
    rw [Gather.w64_sub (by omega_using [h.w₁]),h.hE,Gather.add_ofNat_sub_ofNat _ (by decide)]
  have k : 32 ≤ (SP s).toNat := by
    change 32 ≤ (s.gpr .esp - BitVec.ofNat 32 2612).toNat
    rw [Gather.sub_toNat32 (by omega_using [h.w₁])]; omega_using [h.w₁]
  have w : w64 (work s) = w64 (SP s)+BitVec.ofNat 64 52 :=
    norm h (d := 52) (by decide)
  have a : argAddr t 0 = w64 (SP s)+BitVec.ofNat 64 4 := by
    change addr (t.gpr .esp) 4 = _; rw [sp,norm h (by decide)]
  have ws : (⟨w64 (work s),2560⟩ : Region).Sub (Gather.stkR s) := by
    rw [w,b,Offset.add_ofNat_add_ofNat]; exact Gather.stk_sub _ _ _ (by decide)
  have ars : (⟨argAddr t 0,48⟩ : Region).Sub (Gather.stkR s) := by
    rw [a,b,Offset.add_ofNat_add_ofNat]; exact Gather.stk_sub _ _ _ (by decide)
  have rs : (⟨w64 (SP s),4⟩ : Region).Sub (Gather.stkR s) := by
    rw [b]; exact Gather.stk_sub _ _ _ (by decide)
  have lo : below (SP s) 32 = ⟨Gather.Bs s+BitVec.ofNat 64 44,32⟩ := by
    rw [← below_eq k]
    change (⟨w64 (SP s)-BitVec.ofNat 64 32,32⟩ : Region) = _
    rw [b,Gather.add_ofNat_sub_ofNat _ (by decide)]
  have lows : (below (SP s) 32).Sub (Gather.stkR s) := by
    rw [lo]; exact Gather.stk_sub _ _ _ (by decide)
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
    rw [p.wr,w]; exact covers_off (k := 2612) (covers_of_mem (List.mem_cons_self ..)) (by decide) (by decide)
  case argR =>
    rw [p.rd,p.wr,a]; exact covers_off (k := 2612) (covers_of_mem (List.mem_append_right _ (List.mem_cons_self ..))) (by decide) (by decide)
  case c_w => exact (h.bk.sub_left ws).symm
  case n_w => exact (h.bn.sub_left ws).symm
  case a_w => exact (h.ba.sub_left ws).symm
  case d_w => exact (h.bd.sub_left ws).symm
  case d_a => exact (h.bd.sub_left ars).symm
  case w_a => rw [w,a]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
  case r_d => exact h.bd.sub_left rs
  case r_w => rw [w]; exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  case k_c => exact h.bk.sub_left lows
  case k_n => exact h.bn.sub_left lows
  case k_a => exact h.ba.sub_left lows
  case k_d => exact h.bd.sub_left lows
  case k_w => rw [lo,w,b,Offset.add_ofNat_add_ofNat]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
  case fc => exact h.ok
  case fn => exact h.on
  case fa => exact h.oa
  case fd => exact h.od
  case fw =>
    change (SP s+BitVec.ofNat 32 52).toNat+2560 ≤ _
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


@[expose] def text (s : State) : Text :=
  ⟨Gather.K s, work s, SP s, Gather.Src s, Gather.Dst s, Gather.Cnt s, Gather.L s, (arg s 1).toNat⟩

abbrev ArgR (s : State) := (⟨(text s).dstArg,4⟩ : Region)

structure Zones (s : State) : Prop where
  workspace : (⟨w64 (work s),2560⟩ : Region).Sub (Gather.stkR s)
  ret : (⟨w64 (SP s),4⟩ : Region).Sub (Gather.stkR s)
  lower : (below (SP s) 32).Sub (Gather.stkR s)
  arg : (ArgR s).Sub (Gather.stkR s)
  argOutside : Text.Outside 2560 (text s) (ArgR s)
  argFit : (ArgR s).base.toNat+4 ≤ 2^32

theorem zones {s : State} (h : Gather.Lay s) : Zones s := by
  have b : w64 (SP s) = Gather.Bs s + BitVec.ofNat 64 76 := by
    change w64 (s.gpr .esp - BitVec.ofNat 32 2612) = _
    rw [Gather.w64_sub (by omega_using [h.w₁]),h.hE,Gather.add_ofNat_sub_ofNat _ (by decide)]
  have k : 32 ≤ (SP s).toNat := by
    change 32 ≤ (s.gpr .esp - BitVec.ofNat 32 2612).toNat
    rw [Gather.sub_toNat32 (by omega_using [h.w₁])]; omega_using [h.w₁]
  have w : w64 (work s) = Gather.Bs s+BitVec.ofNat 64 128 := by
    rw [show w64 (work s)=_ from norm h (d := 52) (by decide),b,Offset.add_ofNat_add_ofNat]
  have a : (text s).dstArg = Gather.Bs s+BitVec.ofNat 64 104 := by
    change addr (SP s) 28 = _; rw [norm h (by decide),b,Offset.add_ofNat_add_ofNat]
  have lo : below (SP s) 32 = ⟨Gather.Bs s+BitVec.ofNat 64 44,32⟩ := by
    rw [← below_eq k]; change (⟨w64 (SP s)-BitVec.ofNat 64 32,32⟩ : Region) = _
    rw [b,Gather.add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨w ▸ Gather.stk_sub _ _ _ (by decide),b ▸ Gather.stk_sub _ _ _ (by decide),
    lo ▸ Gather.stk_sub _ _ _ (by decide),?_,?_,?_⟩
  · unfold ArgR; rw [a]; exact Gather.stk_sub _ _ _ (by decide)
  · constructor <;> change Region.Disjoint (ArgR s) _ <;> unfold ArgR <;> rw [a]
    · change Region.Disjoint _ ⟨w64 (work s),2560⟩; rw [w]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · change Region.Disjoint _ ⟨w64 (SP s),4⟩; rw [b]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · change Region.Disjoint _ (below (SP s) 32); rw [lo]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · change (w64 (SP s+28#32)).toNat+4 ≤ 2^32
    rw [toNat_w64,BitVec.toNat_add_of_lt (by omega_using [spFit h,show (28#32).toNat=28 by decide])]
    omega_using [spFit h,show (28#32).toNat=28 by decide]

theorem Zones.outside {s : State} (z : Zones s) {r : Region} (hr : (Gather.stkR s).Disjoint r) :
    Text.Outside 2560 (text s) r := ⟨(hr.sub_left z.workspace).symm,(hr.sub_left z.ret).symm,(hr.sub_left z.lower).symm⟩

theorem input_of {s t u : State} (h : Gather.Lay s) (p : Prepared s t)
    (env : Env 2560 (text s).C (text s).st (text s).W (text s).SP u)
    (rounds : RoundsAt u.mem (work s) (arg s 1).toNat)
    (rd : u.rd=t.rd) (wr : u.wr=t.wr) (fr : Frame [Gather.stkR s] s.mem u.mem)
    (dst : u.mem.readW (text s).dstArg 32=Gather.Dst s) : TextInput 2560 (text s) u := by
  have z := zones h
  have op := p.op h
  have ol := op.ol rfl (by decide) rfl
  have lay := ol.L
  change Lay 2560 (arg t 0) (stOf (arg t 11)) (arg t 11) (t.gpr .esp) 32 at lay
  rw [p.arg_eq _ (by decide),p.scratch,show t.gpr .esp=SP s from p.regs _ (by decide)] at lay
  have orig : ∀ r ∈ Sig.descRegion 32 (w64 (Gather.Src s)) (Gather.Cnt s) :: Gather.lsR s,
      ∀ x, r.Contains x 1 → s.mem x = u.mem x := by
    intro r hr x hx
    have dis : (Gather.stkR s).Disjoint r := by
      rcases List.mem_cons.mp hr with rfl|hr
      · exact h.bds
      · exact h.bls r hr
    exact (fr x fun q hq hqx => by obtain rfl := List.mem_singleton.mp hq; exact dis x hqx hx).symm
  have same := (Proof.AesGcm.listed_congr_le (Nat.le_refl _) orig).1
  have src (i) (hi : i<Gather.Cnt s) :
      (⟨w64 ((text s).source u.mem i),(text s).size u.mem i⟩ : Region) ∈ Gather.lsR s := by
    unfold Gather.lsR; rw [← same]; exact Gather.slice_mem u.mem h.ods hi
  have rd' : u.rd=s.rd := rd.trans p.rd
  have wr' : u.wr=(allocated s).wr := wr.trans p.wr
  have cov (r : Region) (hr : r∈s.rd) : Covers [r] (u.rd++u.wr) :=
    covers_of_mem (List.mem_append_left _ (rd' ▸ hr))
  have dstW : Covers [Gather.dR s] u.wr := by
    rw [wr']; exact covers_of_mem (List.mem_cons_of_mem _ (h.wr ▸ by simp))
  have retW : Covers [⟨w64 (SP s),4⟩] u.wr := by
    rw [wr']; simpa using covers_off (d := 0) (k := 2612) (n := 4)
      (covers_of_mem (List.mem_cons_self (a := (⟨w64 (SP s),2612⟩ : Region)) (l := s.wr))) (by decide) (by decide)
  refine ⟨lay,env,rounds,(Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) orig).trans h.hgl,
    (arg s 7).isLt,(arg s 9).isLt,h.ods,h.od,cov (Gather.dsR s) (h.rd ▸ by simp),?_,?_,dstW,z.outside h.bds,
    fun i hi => z.outside (h.bls _ (src i hi)),z.outside h.bd,z.argOutside,h.dds.symm,
    fun i hi => (h.dls _ (src i hi)).symm,h.bd.sub_left z.arg,h.kd,(h.bk.sub_left z.ret).symm,
    ?_,by change (SP s).toNat+4 ≤ _; omega_using [spFit h],retW,?_,dst⟩
  · intro i hi; exact cov _ (h.rd ▸ List.mem_append_right _ (src i hi))
  · intro i hi; exact h.ol _ (src i hi)
  · have hh := op.r_w
    rw [show t.gpr .esp=SP s from p.regs _ (by decide),p.scratch] at hh
    exact hh
  · rw [wr']; exact ⟨_,List.mem_append_right _ (List.mem_cons_self ..),by
      change (⟨w64 (SP s),2612⟩ : Region).Contains (addr (SP s) 28) 4
      rw [norm h (by decide)]; exact Offset.contains_base _ (by decide) (by decide)⟩

end VG.Proof.AesGcm.X86.DirectGather

end

public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Spec.Gcm


abbrev pub (t : State) := pubSw 12 8 t
abbrev scratchAreas (s : State) : List Region := [⟨w64 (work s),2560⟩,below (SP s) 32]

structure Params (s t : State) : Prop where
  sp : (pub t).1=SP s
  w : (pub t).2 8=work s
  c : (pub t).2 0=Gather.K s
  r : (pub t).2 1=arg s 1
  d : (pub t).2 6=Gather.Dst s
  l : (pub t).2 7=arg s 9

theorem Prepared.params {s t : State} (p : Prepared s t) : Params s t :=
  ⟨p.regs _ (by decide),p.scratch,p.arg_eq 0 (by decide),p.arg_eq 1 (by decide),
    p.arg_eq 6 (by decide),p.arg_eq 7 (by decide)⟩

theorem aad_frame {s t e u : State} (p : Prepared s t) (en : OEnt 2560 (pub t) t e)
    (aad : Frame (oF 2560 (pub t)) e.mem u.mem) : Frame (scratchAreas s) t.mem u.mem := by
  have a := p.params
  have fe := en.frame
  rw [a.w] at fe
  apply Frame.trans (fe.sub ?_) (aad.sub ?_)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self ..,Lay.wSubN (by decide)⟩
  · intro r hr; simp only [oF,a.w,a.sp,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩
    · exact ⟨_,List.mem_cons_self ..,Lay.wSubN (by decide)⟩
    · exact ⟨_,by simp [scratchAreas],fun _ hx => hx⟩

theorem private_arg_kept {s t u : State} (h : Gather.Lay s) (p : Prepared s t)
    (f : Frame (scratchAreas s) t.mem u.mem) (i : Nat) (hi : i<11) :
    u.mem.readW (argA (SP s) i) 32 = arg s (VG.Impl.AesGcm.X86.DirectGather.sourceSlot i) := by
  have op := p.op h
  have sp : t.gpr .esp=SP s := p.regs _ (by decide)
  have argSub : (⟨argA (SP s) i,4⟩ : Region).Sub (argsR (SP s) 12) := by
    change Region.Sub ⟨addr (SP s) (4+4*i),4⟩ ⟨addr (SP s) 4,48⟩
    rw [norm h (by omega_using [hi]),norm h (by decide)]
    exact Offset.sub _ (by omega) (by omega)
  refine (f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans (p.slots i hi)
  rcases List.mem_cons.mp hr with rfl|hr
  · have aw := op.w_a.symm; rw [← argsR_eq,sp,p.scratch] at aw; exact aw.sub_left argSub
  · obtain rfl := List.mem_singleton.mp hr
    change Region.Disjoint ⟨addr (SP s) (4+4*i),4⟩ (below (SP s) 32)
    rw [norm h (by omega_using [hi]),← below_eq (sp ▸ op.sp)]
    change Region.Disjoint _ ⟨w64 (SP s)-BitVec.ofNat 64 32,32⟩
    rw [show w64 (SP s)+BitVec.ofNat 64 (4+4*i) =
      (w64 (SP s)-BitVec.ofNat 64 32)+BitVec.ofNat 64 (32+(4+4*i)) by
        rw [BitVec.ofNat_add (n := 64) (x := 32) (y := 4+4*i),← BitVec.add_assoc,BitVec.sub_add_cancel]]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem start_frame {s t u : State} (h : Gather.Lay s) (p : Prepared s t)
    (f : Frame (scratchAreas s) t.mem u.mem) : Frame [Gather.stkR s] s.mem u.mem := by
  have z := zones h
  apply Frame.trans (p.frame.sub ?_) (f.sub ?_)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,by
      change (⟨w64 (SP s),52⟩ : Region).Sub (Gather.stkR s)
      change Region.Sub ⟨w64 (s.gpr .esp - BitVec.ofNat 32 2612),52⟩ _
      rw [Gather.w64_sub (by omega_using [h.w₁]),h.hE,Gather.add_ofNat_sub_ofNat _ (by decide)]
      exact Gather.stk_sub _ _ _ (by decide)⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,List.mem_singleton_self _,z.workspace⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_singleton_self _,z.lower⟩


theorem loop_setup_frame {s u x : State}
    (hs : SetupPost u (work s) (SP s) 9 10 rO tglO (w64 (work s)+BitVec.ofNat 64 xlO) x) :
    Frame (scratchAreas s) u.mem x.mem := hs.frame.sub fun r hr => by
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

structure Begun (s t x : State) : Prop where
  input : TextInput 2560 (text s) x
  ptr : slotv x.mem (work s) rO = Gather.Src s
  count : slotv x.mem (work s) tglO = BitVec.ofNat 32 (Gather.Cnt s)
  off : slotv x.mem (work s) xlO=0
  ctr : CtrS x.mem (text s).st (ciphOf x.mem (Gather.K s) (arg s 1).toNat) (inc32 (jOf (pub t) t)) 0
  frame : Frame (scratchAreas s) t.mem x.mem

theorem begun {s t e u x : State} (h : Gather.Lay s) (p : Prepared s t)
    (en : OEnt 2560 (pub t) t e) (aa : OAad 2560 (pub t) t u) (f : Frame (oF 2560 (pub t)) e.mem u.mem)
    (hs : SetupPost u (work s) (SP s) 9 10 rO tglO (w64 (work s)+BitVec.ofNat 64 xlO) x) :
    Begun s t x := by
  have fr := aad_frame p en f
  have fx := fr.trans (loop_setup_frame hs)
  have z := p.params
  have o := aa.o
  have eu := o.env
  rw [z.c,z.w,z.sp] at eu
  have rr := o.rounds
  rw [z.w,z.r] at rr
  have perm {W : BitVec 32} {n : Nat} (f : Frame (slotSetupFrame W rO tglO (w64 W+BitVec.ofNat 64 xlO)) u.mem x.mem)
      (d₁ : n+4≤rO ∨ rO+4≤n) (d₂ : n+4≤tglO ∨ tglO+4≤n) (d₃ : n+4≤xlO ∨ xlO+4≤n) (fit : n+4≤768) :
      slotv x.mem W n=slotv u.mem W n := slot_frame f (setup_disjoint d₁ d₂ d₃ fit)
  have ex : Env 2560 (text s).C (text s).st (text s).W (text s).SP x :=
    ⟨(hs.regs _ (by decide)).trans eu.ebp,(hs.regs _ (by decide)).trans eu.esi,
     (hs.regs _ (by decide)).trans eu.esp,by rw [hs.rd,hs.wr]; exact eu.ctxR,
     hs.wr ▸ eu.stW,hs.wr ▸ eu.wW,(perm hs.frame (n := ctxO) (by decide) (by decide) (by decide) (by decide)).trans eu.ctx⟩
  have rx : RoundsAt x.mem (work s) (arg s 1).toNat :=
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
