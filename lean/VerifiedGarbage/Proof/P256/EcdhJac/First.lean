import VerifiedGarbage.Proof.P256.EcdhJac.Entry
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem first_split : Impl.P256.EcdhJac.first=
    ([.movz .x .x19 51 0] : List Instr)++entry++copyPt 4 K.R K.E := by
  simp only [Impl.P256.EcdhJac.first,entry,signedEntry,Impl.P256.EcdhJac.select,List.append_assoc,
    show Impl.P256.EcdhJac.K.tbl=2816 from rfl,show Impl.P256.EcdhJac.K.E.x=704 from rfl,
    show Impl.P256.EcdhJac.z2=5400 from rfl]

theorem first_ok (hC : Law C) {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hP : onCurve C P=true) (hk : k<2^256) (hf : Fixed base P k s) (ht : TblOk base P 16 s) :
    WP isa (.block Impl.P256.EcdhJac.first) s fun t=>Frame base work s t ∧ LoopInv base P k 51 t := by
  rw [first_split,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (movz_ok s .x19 51) fun u ⟨hu,ku⟩=>?_
  have fu : Frame base work s u := (AllocatedFrame.of_keeps ku).widenRegs (by decide)
  have hfu := hf.keep (frame_build fu)
  refine WP.mono (entry_ok (V:=ro) (j:=51) (by intro x hx; exact List.mem_append_right _ hx)
    (fun _ h=>h) hfu.field hfu (ht.keep fu) (by decide) (by exact hu)) fun v hv=>?_
  have hepoint : InvJ C (tmv C 4 base v K.E.x) (tmv C 4 base v K.E.y)
      (tmv C 4 base v K.E.z) (Window5.winPt C P (k+offset) 51) := by
    by_cases hz : magH 16 (Window5.nib (k+offset) 51)=0
    · rw [Window5.winPt_zero hz]
      exact Or.inl ⟨rfl,hv.zero hz⟩
    · exact (hv.point (by omega)).jac
  have hA : RcbApart K.S K.E K.E K.R := ⟨by decide,by decide⟩
  have hsl : ∀ x∈rcbW K.S K.R++rcbR K.S K.E K.E,Sl x := by decide
  have hvalid : ∀ x∈rcbR K.S K.E K.E,x∈selected++ro := by decide
  refine WP.mono (copyPoint_ok layout aligned hA hsl hv.field hvalid) fun t ⟨et,kp,it,ep⟩=>?_
  have ft : Frame base work v t := AllocatedFrame.of_prog kp clob_regs (by decide)
  have allframe := fu.trans (hv.frame.trans ft)
  have iout := it.sub (fun x (hx : x∈live)=>by
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx))
  have exyz : et K.R.x=tmv C 4 base v K.E.x ∧ et K.R.y=tmv C 4 base v K.E.y ∧
      et K.R.z=tmv C 4 base v K.E.z := by simpa only [Prod.mk.injEq] using ep
  have ip : InvJ C (et K.R.x) (et K.R.y) (et K.R.z) (Window5.winPt C P (k+offset) 51) := by
    rw [exyz.1,exyz.2.1,exyz.2.2]; exact hepoint
  refine ⟨allframe,⟨⟨Window5.winPt C P (k+offset) 51,Window5.onCurve_winPt hC hP (k+offset) 51,fun _=>?_,
    ⟨hf.keep (frame_build allframe),ht.keep allframe,iout.to_tmv,?_⟩⟩,?_⟩⟩
  · have he := Window5.win_add hC hP (k:=k+offset) (J:=52) (j:=51)
      (by rw [offset_eq]; omega) (by decide)
    have htop : Window5.winE (k+offset) 52 52=0 :=
      Window5.winE_top (by rw [offset_eq]; exact Window5.recode_lt hk)
    rw [show 51+1=52 from rfl,htop,Nat.mul_zero,Window5.mul_zero_pt,infinity_add'] at he
    exact he
  · have vals : ∀ x∈live,tmv C 4 base t x=et x := by
      intro x hx
      exact iout.val x hx
    change InvJ C (tmv C 4 base t K.R.x) (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) _
    rw [vals K.R.x (by decide),vals K.R.y (by decide),vals K.R.z (by decide)]
    exact ip
  · rw [kp.gpr _ (x19_not_clob _),hv.counter,hu]
    rfl

end VG.Proof.P256.EcdhJac
