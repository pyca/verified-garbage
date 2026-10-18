module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraStep
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBothTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Proof.Sha3.AArch64.Neon

structure StepReadyW (w16 : Bool) (A B : Spec.Sha3.State) (L M : List Zq) (p a b c : Addr) (s : State) : Prop where
 context : Context p a b c s
 pointer : s.gpr .x19=p
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=c
 pair : PairAt s.mem p A B
 lenLeft : L.length≤256
 lenRight : M.length≤256
 left : Rej8.Scalar.CoeffsW w16 s.mem a L
 right : Rej8.Scalar.CoeffsW w16 s.mem b M
 saveLeft : checkpointW w16 (p+1680) a L s.mem
 saveRight : checkpointW w16 (p+1696) b M s.mem

abbrev StepReady := StepReadyW false

theorem nextBlock_ready {w16 : Bool} {s : State} {A B : Spec.Sha3.State} {L M : List Zq} {p a b c : Addr}
 (h : StepReadyW w16 A B L M p a b c s) :
 WP isa nextBlock s fun u=> Keep nextRegs s u ∧ u.gpr .x16=c ∧
   BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
     (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b u := by
 rcases h with ⟨ctx,hp,sym,pair,hl,hm,ca,cb,sa,sb⟩
 refine WP.mono_syms (nextBlock_ok hp ctx.scratch pair) fun u h hsym => ?_
 rcases h with ⟨ku,fu,precise,up,pu,ra,rb,cs,ut⟩
 have fu' : Frame (stepWrites p a b) s.mem u.mem := fu.mono (by simp [stepWrites])
 have cu := ctx.frame ku.rd ku.wr fu'
 have ux : u.gpr .x16=c := by rw [ut,hsym,sym]
 have ua := coeffs_frame ca hl fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farA.symm)
 have ub := coeffs_frame cb hm fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farB.symm)
 have checkpoints {off : Nat} (ho : off=1680 ∨ off=1696) :
     ∀r∈nextWrites p,(Region.mk (p+BitVec.ofNat 64 off) 16).Disjoint r := by
  have hlo : 1680≤off := by omega
  have hhi : off≤1696 := by omega
  intro r hr
  simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact Offset.disjoint_base p (d:=off) (n:=16) (k:=400) (by omega) (by omega)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=400) (k:=168) (by omega) (by omega) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=904) (k:=168) (by omega) (by omega) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=1536) (k:=136) (by omega) (by omega) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=1408) (k:=8) (by omega) (by omega) (by decide)
 have usa := checkpoint_frame sa precise (checkpoints (Or.inl rfl))
 have usb := checkpoint_frame sb precise (checkpoints (Or.inr rfl))
 have ea := cu.envW (w16 := w16) ux (N:=56) (off:=400) (by decide) (by decide) (Or.inl rfl) (fun i hi=>ra.byte hi)
 have eb := cu.envW (w16 := w16) ux (N:=56) (off:=904) (by decide) (by decide) (Or.inr rfl) (fun i hi=>rb.byte hi)
 have iw {o l : Nat} (ho : o+l≤2048) := Noise.inScratch cu.scratch ho (by decide)
 refine ⟨ku,ux,up,cu.scratch,cu.farA,cu.farB,cu.apart,?_,?_,?_⟩
 · exact ⟨by simpa only [up] using ea,cs,hl,ua,by rw [up]; exact usa,
     by rw [up]; exact iw (by decide),by rw [up]; exact iw (by decide),
     by rw [up]; exact cu.farA.symm.sub_right (Offset.sub_base p (by decide))⟩
 · exact ⟨by simpa only [up] using eb,cs,hm,ub,by rw [up]; exact usb,
     by rw [up]; exact iw (by decide),by rw [up]; exact iw (by decide),
     by rw [up]; exact cu.farB.symm.sub_right (Offset.sub_base p (by decide))⟩
 · intro mask hm; rw [ux]; exact cu.tableScratch.sub_left (Rej8.table_sub c hm)
theorem extraStep_relCT {w16 : Bool} {s u : State} {A B : Spec.Sha3.State} {L M : List Zq} {p a b c : Addr}
 (hs : StepReadyW w16 A B L M p a b c s) (hu : StepReadyW w16 A B L M p a b c u)
 (sp : s.sp=u.sp) :
 RelCT isa (fun x y=>x=s ∧ y=u) (Impl.MlKem.AArch64.Paired.extraStep w16) (fun _ _=>True) := by
 have first : RelCT isa (fun x y=>x=s ∧ y=u) nextBlock
     (fun x y=>BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
         (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b x ∧
       BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
         (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b y ∧ x.sp=y.sp ∧ x.gpr .x16=y.gpr .x16) := by
  intro x y tx ty x' y' h ex ey
  rcases h with ⟨hx,hy⟩
  subst x; subst y
  obtain ⟨kx,tx16,px⟩ := exec_post (nextBlock_ready hs) ex
  obtain ⟨ky,ty16,py⟩ := exec_post (nextBlock_ready hu) ey
  exact ⟨nextBlock_ct s u tx ty x' y' trivial trivial
    (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact hs.pointer.trans hu.pointer.symm)) ex ey,
    px,py,kx.sp.trans (sp.trans ky.sp.symm),tx16.trans ty16.symm⟩
 have grouped : RelCT isa (fun x y=>x=s ∧ y=u) (.seq nextBlock (extraBoth w16)) (fun _ _=>True) := by
  refine RelCT.seq first ?_
  intro x y tx ty x' y' h ex ey
  exact extraBoth_relCT h.1 h.2.1 h.2.2.1 h.2.2.2 x y tx ty x' y' ⟨rfl,rfl⟩ ex ey
 intro x y tx ty x' y' h ex ey
 cases ex with
 | seq e1 ex =>
  cases ex with
  | seq e2 ex =>
   cases ex with
   | seq e3 e4 =>
    cases ey with
    | seq f1 ey =>
     cases ey with
     | seq f2 ey =>
      cases ey with
      | seq f3 f4 =>
       obtain ⟨ht,hq⟩ := grouped _ _ _ _ _ _ h
         (.seq (.seq e1 (.seq e2 e3)) e4) (.seq (.seq f1 (.seq f2 f3)) f4)
       exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

end VG.Proof.MlKem.AArch64.Paired
