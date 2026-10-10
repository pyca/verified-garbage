import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P256.EcdhJac.Select
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero

/-! ## `Entry` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def selected : List Nat := [704,736,768,5400,5432]

theorem selected_mem : ∀ i<5,selectedSlot i∈selected := by decide

theorem select_field_ok {base : Addr} {P : Point C} {k a : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s)
    (ha : a≤16) (hmag : s.gpr .x2=BitVec.ofNat 64 a) :
    WP isa (.block (Impl.P256.EcdhSelect.neon 2816 704 5400)) s fun t=>
      Frame base work s t ∧ t.gpr .x19=s.gpr .x19 ∧
      Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t ∧
      (1≤a→JPt base t selectedSlot (mul a P)) ∧
      (a=0→∀ i<5,wordsVal t.mem base (selectedSlot i) 4=0) ∧
      (∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4) := by
  refine WP.mono (Select.neon_ok hi.scr ha hmag) fun t ⟨hw,hkeep,ho⟩=>?_
  have fr : Frame base work s t := ⟨hkeep.mono (by decide),ho.cover (by decide)⟩
  have hv : ∀ i<5,wordsVal t.mem base (selectedSlot i) 4=
      if a=0 then 0 else wordsVal s.mem base (entrySlot a i) 4 := by
    intro i hi'
    by_cases hz : a=0
    · rw [ite_eq_left hz]
      apply (wordsVal_eq_zero_iff _ _ _ _).mpr
      intro j hj
      have hh := hw (4*i+j) (by omega)
      have hout : Select.output (4*i+j)=selectedSlot i+8*j := by
        unfold Select.output selectedSlot; split <;> split <;> omega
      simpa only [hout,hz,ite_true] using hh
    · rw [ite_eq_right hz]
      apply wordsVal_of_words₂
      intro j hj
      have hh := hw (4*i+j) (by omega)
      have hout : Select.output (4*i+j)=selectedSlot i+8*j := by
        unfold Select.output selectedSlot; split <;> split <;> omega
      have hin : 2816+160*(a-1)+8*(4*i+j)=entrySlot a i+8*j := by unfold entrySlot; omega
      simpa only [hout,hin,ite_eq_right hz] using hh
  have hfix := hf.keep (frame_build fr)
  refine ⟨fr,hkeep.gpr _ (by decide),?_,fun hnz=>(ht a hnz ha).congr (fun i hi'=>by
    rw [hv i hi',ite_eq_right (by omega)]),fun hz i hi'=>by
      simpa only [hz,ite_true] using hv i hi',?_⟩
  rotate_left
  · intro x hx
    exact ho.wordsVal (by
      have hh : ∀ x∈live,∀ w∈Select.outputRanges,x+32≤w.1 ∨ w.1+w.2≤x := by decide
      exact hh x (hV x hx)) (by
      have hh : ∀ x∈live,x+32≤2^64 := by decide
      exact hh x (hV x hx))
  refine ⟨fr.scr regs_x0 hi.scr,hfix.field.mod,?_,?_,fun _ _=>rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈selected,Sl x := by decide
      exact hh x hx
    · exact hi.sl x hx
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈selected,∃ i<5,x=selectedSlot i := by decide
      obtain ⟨i,hi',rfl⟩:=hh x hx
      change wordsVal t.mem base (selectedSlot i) 4<C.p
      rw [hv i hi']
      split
      · decide
      · exact (ht a (by omega) ha).lt i hi'
    · have hwv : wordsVal t.mem base x 4=wordsVal s.mem base x 4 :=
        ho.wordsVal (by
          have hsep : ∀ x∈live,∀ w∈Select.outputRanges,x+32≤w.1 ∨ w.1+w.2≤x := by decide
          exact hsep x (hV x hx)) (by
          have hb : ∀ x∈live,x+32≤2^64 := by decide
          exact hb x (hV x hx))
      change wordsVal t.mem base x 4<C.p
      rw [hwv]; exact hi.lt x hx

def signedEntry : List Instr :=
  Impl.P256.EcdhSelect.neon 2816 704 5400++negYW M 5 K.neg K.zero K.E.y K.bits

structure EntryPost (base : Addr) (P : Point C) (k j : Nat) (V : List Nat) (s t : State) : Prop where
  frame : Frame base work s t
  counter : t.gpr .x19=s.gpr .x19
  field : Inv M base 8192 C.p Sl (selected++V) (tmv C 4 base t) t
  zero : magH 16 (Window5.nib (k+offset) j)=0→tmv C 4 base t K.E.z=0
  cache2 : tmv C 4 base t 5400=tmv C 4 base t K.E.z*tmv C 4 base t K.E.z
  cache3 : tmv C 4 base t 5432=tmv C 4 base t 5400*tmv C 4 base t K.E.z
  same : ∀ x∈V,wordsVal t.mem base x 4=wordsVal s.mem base x 4
  point : 1≤magH 16 (Window5.nib (k+offset) j) →
    JPt base t selectedSlot (Window5.winPt C P (k+offset) j)

theorem signedEntry_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live) (hro : ∀ x∈ro,x∈V)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hmag : s.gpr .x2=BitVec.ofNat 64 (magH 16 (Window5.nib (k+offset) j))) :
    WP isa (.block signedEntry) s (EntryPost base P k j V s) := by
  have hm : magH 16 (Window5.nib (k+offset) j)≤16 := magH_le (Nat.mod_lt _ (by decide))
  rw [signedEntry,WP.block_append_iff]
  refine WP.mono (select_field_ok hV hi hf ht hm hmag) fun s₁ ⟨fr₁,c₁,i₁,p₁,z₁,same₁⟩=>?_
  have f₁ := hf.keep (frame_build fr₁)
  have hz : tmv C 4 base s₁ K.zero=0 := by unfold tmv; rw [f₁.zero,toM_zero]
  have hy : K.E.y∈selected++V := by apply List.mem_append_left; decide
  have hzero : K.zero∈selected++V := List.mem_append_right _ (hro _ (by decide))
  refine WP.mono (negFieldWindow_ok layout aligned (unitMod_pow_two (by decide) _) i₁
    (by decide : Sl K.neg) hzero hy (by decide) hz (by decide : 1≤5) (by decide)
    (by omega : 5*j+5≤260) (by decide) (by decide) (c₁.trans h19) f₁.bits
    (by decide) (by decide)) fun t ⟨kp₂,i₂⟩=>?_
  have fr₂ : Frame base work s₁ t := AllocatedFrame.of_prog kp₂ clob_regs (by decide)
  have iv := i₂.sub (fun x (hx : x∈selected++V)=>List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have hez : tmv C 4 base t K.E.z=tmv C 4 base s₁ K.E.z := by
    have hh:=iv.val K.E.z (by apply List.mem_append_left; decide)
    change tmv C 4 base t K.E.z=_ at hh
    simpa only [Function.update_of_ne (by decide : K.E.z≠K.E.y),
      Function.update_of_ne (by decide : K.E.z≠K.neg)] using hh
  have he (i : Nat) (hi' : i<5) (hne : i≠1) :
      tmv C 4 base t (selectedSlot i)=tmv C 4 base s₁ (selectedSlot i) := by
    have hv := iv.val _ (List.mem_append_left _ (selected_mem i hi'))
    have ne : selectedSlot i≠K.E.y ∧ selectedSlot i≠K.neg := by
      have hh : ∀ i<5,i≠1→selectedSlot i≠K.E.y ∧ selectedSlot i≠K.neg := by decide
      exact hh i hi' hne
    change tmv C 4 base t (selectedSlot i)=_ at hv
    simpa only [Function.update_of_ne ne.1,Function.update_of_ne ne.2] using hv
  have hc2 : tmv C 4 base s₁ 5400=tmv C 4 base s₁ K.E.z*tmv C 4 base s₁ K.E.z := by
    by_cases hz : magH 16 (Window5.nib (k+offset) j)=0
    · have e2:=z₁ hz 2 (by decide)
      have e3:=z₁ hz 3 (by decide)
      change wordsVal s₁.mem base 768 4=0 at e2
      change wordsVal s₁.mem base 5400 4=0 at e3
      change toM _ _ (wordsVal s₁.mem base 5400 4)=toM _ _ (wordsVal s₁.mem base 768 4)*toM _ _ (wordsVal s₁.mem base 768 4)
      rw [e2,e3,toM_zero]; grind
    · exact (p₁ (by omega)).z2
  have hc3 : tmv C 4 base s₁ 5432=tmv C 4 base s₁ 5400*tmv C 4 base s₁ K.E.z := by
    by_cases hz : magH 16 (Window5.nib (k+offset) j)=0
    · have e4:=z₁ hz 4 (by decide)
      have e3:=z₁ hz 3 (by decide)
      change wordsVal s₁.mem base 5432 4=0 at e4
      change wordsVal s₁.mem base 5400 4=0 at e3
      unfold tmv
      rw [e4,e3,toM_zero]; grind
    · exact (p₁ (by omega)).z3
  refine ⟨fr₁.trans fr₂,(kp₂.gpr _ (x19_not_clob _)).trans c₁,iv.to_tmv,fun hz=>?_,?_,?_,?_,fun hnz=>?_⟩
  · rw [hez]; unfold tmv; rw [show wordsVal s₁.mem base K.E.z 4=0 from z₁ hz 2 (by decide),toM_zero]
  · change tmv C 4 base t (selectedSlot 3)=tmv C 4 base t (selectedSlot 2)*tmv C 4 base t (selectedSlot 2)
    rw [he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact hc2
  · change tmv C 4 base t (selectedSlot 4)=tmv C 4 base t (selectedSlot 3)*tmv C 4 base t (selectedSlot 2)
    rw [he 4 (by decide) (by decide),he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact hc3
  · intro x hx
    rw [kp₂.unch.wordsVal (by
      have hh : ∀ x∈live,∀ w∈([K.neg,K.E.y].map (·,8*M.n)++[(M.tmp,8*M.n)]),x+32≤w.1 ∨ w.1+w.2≤x := by decide
      exact hh x (hV x hx)) (by
      have hh : ∀ x∈live,x+32≤2^64 := by decide
      exact hh x (hV x hx))]
    exact same₁ x hx
  have p := p₁ hnz
  have hey : tmv C 4 base t (selectedSlot 1)=
      if decide (Window5.nib (k+offset) j<16) then -tmv C 4 base s₁ (selectedSlot 1)
      else tmv C 4 base s₁ (selectedSlot 1) := by
    have hv := iv.val _ (List.mem_append_left _ (selected_mem 1 (by decide)))
    change tmv C 4 base t (selectedSlot 1)=_ at hv
    simpa only [show selectedSlot 1=K.E.y from rfl,Function.update_self,Window5.combWin_five,
      show 2^(5-1)=16 from rfl] using hv
  refine ⟨fun i hi'=>iv.lt _ (List.mem_append_left _ (selected_mem i hi')),?_,?_,?_,?_⟩
  · rw [he 0 (by decide) (by decide),hey,he 2 (by decide) (by decide),Window5.winPt_mag]
    split
    · exact p.jac.negY
    · exact p.jac
  · rw [he 2 (by decide) (by decide)]; exact p.z
  · rw [he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact p.z2
  · rw [he 4 (by decide) (by decide),he 3 (by decide) (by decide),he 2 (by decide) (by decide)]; exact p.z3

def entry : List Instr := tc.digit++signedEntry

theorem entry_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    {V : List Nat} (hV : ∀ x∈V,x∈live) (hro : ∀ x∈ro,x∈V)
    (hi : Inv M base 8192 C.p Sl V (tmv C 4 base s) s)
    (hf : Fixed base P k s) (ht : TblOk base P 16 s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block entry) s (EntryPost base P k j V s) := by
  rw [entry,WP.block_append_iff]
  refine WP.mono (digitW_ok tc hi.scr (k:=k+offset) (j:=j) (N:=260)
    (by decide) (by decide) (by change 5*j+5≤260; omega) (by decide) (by decide) h19 hf.bits)
    fun u ⟨hu,hkeep⟩=>?_
  have fr : Frame base work s u := (AllocatedFrame.of_keeps hkeep).widenRegs (by decide)
  have iu : Inv M base 8192 C.p Sl V (tmv C 4 base u) u := by
    have hh:=hi.of_keeps hkeep (by decide)
    have he : tmv C 4 base u=tmv C 4 base s := by funext x; unfold tmv; rw [hkeep.mem]
    rw [he]; exact hh
  refine WP.mono (signedEntry_ok hV hro iu (hf.keep (frame_build fr)) (ht.keep fr) hj
    ((hkeep.gpr _ (by decide)).trans h19) (by
      change u.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 (k+offset) j)) at hu
      simpa only [Window5.combWin_five] using hu)) fun t hp=>?_
  refine ⟨fr.trans hp.frame,hp.counter.trans (hkeep.gpr _ (by decide)),hp.field,hp.zero,hp.cache2,hp.cache3,?_,hp.point⟩
  intro x hx
  rw [hp.same x hx,hkeep.mem]

end VG.Proof.P256.EcdhJac

end

/-! ## `First` -/

section

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

end
