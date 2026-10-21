module

import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.OutsFrame

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.X86.Isa

/-! Shared cdecl boundary for Montgomery workspace helpers. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem workspaceCall_ok {s : State} {base : Addr} {size bytes : Nat}
    {rs : List (Nat × Nat)} {P Q : Mem → Prop} {code : Prog isa} {name : String}
    (hs : Scr s base size) (room : Pow.Room (s.gpr .esp) base size)
    (hused : VG.Impl.Dsa.Layout.usedBytes≤size)
    (safe : NoSp code) (depth : stackUse code=0)
    (fits : ∀ r∈rs, r.1+r.2≤size)
    (input : ∀ mem, Frame [below (s.gpr .esp) 12] s.mem mem → P mem)
    (correct : ∀ v, Pow.Entry v base size → P v.mem → WP isa code v fun w =>
      Q w.mem ∧ Outs base rs v.mem w.mem ∧
      (∀ r∈calleeSaved, w.gpr r=v.gpr r) ∧ w.rd=v.rd ∧ w.wr=v.wr) :
    WP isa (.seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (bytes/8)))])
      (.frame (.push [.eax,.edi]) (.call name code) (.pop .eax 2))) s fun t =>
      Q t.mem ∧ StackOuts base (s.gpr .esp) rs s.mem t.mem ∧ Keeps [.eax,.ecx,.edx] s t := by
  have nw := hs.nowrap
  obtain ⟨h32,sep⟩ := room
  have spBound := (s.gpr .esp).isLt
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have usp : u.gpr .esp=s.gpr .esp := U.other _ (by decide)
  have udi : u.gpr .edi=s.gpr .edi := U.other _ (by decide)
  have fit : 4*[Reg.eax,.edi].length+4≤(u.gpr .esp).toNat := by rw [usp]; simp; omega
  let t := ((pushed [Reg.eax,.edi] u).callEntry).withRegions [below (u.gpr .esp) 8] [⟨base,size⟩]
  have a0 : (arg t 0).setWidth 64=base := by
    rw [show arg t 0=u.gpr .edi from callEntry_arg fit (by decide) (by decide),udi,hs.edi]
  have tsp : (t.gpr .esp).toNat=(s.gpr .esp).toNat-12 := by
    show ((pushed _ u).callEntry.gpr .esp).toNat=_
    rw [callEntry_espNat fit,usp]; rfl
  have argA : argAddr t 0=(u.gpr .esp-BitVec.ofNat 32 8).setWidth 64 := callEntry_argAddr0 _ _
  have retN : ((t.gpr .esp).setWidth 64).toNat=(s.gpr .esp).toNat-12 := by
    rw [BitVec.toNat_setWidth,tsp]; exact Nat.mod_eq_of_lt (by omega)
  have fr : Frame [below (s.gpr .esp) 12] s.mem t.mem := by
    have H := callEntry_frame fit (rs := [Reg.eax,.edi]) (by decide)
    rw [U.mem,usp] at H
    exact H
  have E : Pow.Entry t base size := by
    refine ⟨?_,a0,List.mem_singleton_self _,nw,?_⟩
    · refine ⟨⟨argAddr t 0,8⟩,?_,?_⟩
      · change _∈[below (u.gpr .esp) 8]++[⟨base,size⟩]
        rw [argA]; exact List.mem_cons_self ..
      · simpa only [BitVec.add_zero] using Offset.contains_base (argAddr t 0)
          (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    · unfold StkOk; rw [tsp]; constructor <;> omega
  have ret : Region.Disjoint ⟨(t.gpr .esp).setWidth 64,4⟩ ⟨base,size⟩ :=
    Region.disjoint_of_le (by simp only; rw [retN]; omega)
      (by simp only; rw [retN]; omega) (by simp only; omega)
  let K : Contract isa :=
    { pre := fun v => Pow.Entry v base size ∧ Region.Disjoint ⟨(v.gpr .esp).setWidth 64,4⟩ ⟨base,size⟩ ∧ P v.mem
      post := fun v w => Q w.mem ∧ Outs base rs v.mem w.mem
      pub := fun _ _ => True }
  refine WP.callWith (k := K) (fun v ⟨Ev,Rv,Pv⟩ => ?_) safe (by decide) (by decide)
    (by rw [depth]; exact fit) (rd := [below (u.gpr .esp) 8]) (wr := [⟨base,size⟩])
    ⟨⟨E,ret,input _ fr⟩,?_,?_⟩ ?_
  · obtain ⟨tr,w,ex,V,O,R,_,_⟩ := correct v Ev Pv
    have F : Frame [⟨base,size⟩] v.mem w.mem := O.frame fits
    refine ⟨tr,w,ex,⟨R,?_⟩,V,O⟩
    exact F.readW (by simpa only [BitVec.add_zero] using
      Offset.contains_base ((v.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact Rv) (by decide)
  · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; simp
    · rw [List.mem_singleton.mp hr,U.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr,U.wr]; exact List.mem_cons_of_mem _ hs.wr
  · intro w rd wr cs _ post
    obtain ⟨v,mem,V,O⟩ := post
    refine ⟨by rw [←mem]; exact V,?_,?_⟩
    · intro x hx hxstack
      have outside : ¬(below (s.gpr .esp) 12).Contains x 1 := by
        intro hin
        rcases hxstack with hlocal|hstack
        · have := Pow.zone_ofs ⟨h32,sep⟩ nw hin; omega
        · exact hstack (below_sub (sp := s.gpr .esp) (a := 12) (b := 32) (by decide) h32 _ hin)
      rw [←mem,O x hx]
      exact fr x fun r hr => by rw [List.mem_singleton.mp hr]; exact outside
    · refine ⟨fun r hr => ?_,rd.trans U.rd,wr.trans U.wr⟩
      have cr : r∈calleeSaved := by revert hr; cases r <;> decide
      rw [cs r cr,U.other r (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr; exact hr.1)]

end VG.Proof.Dsa.X86
