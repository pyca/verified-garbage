import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT

/-! ## AdxTri8RowCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure CtLayout where
  B : Addr
  Z : Nat
  w : Nat
  I : Nat
  e : Nat
  hZ : slot w 8≤Z
  hi : I+8≤w
  he : e+64≤Z

def HeadState (L : CtLayout) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I

/-- The rows' state before `clearEnds` sets the output base. -/
def Pre (n : Nat) (rs : List Reg) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ s.gpr .rbp=off L.B L.e ∧ value s rs<2^(64*n)

/-- The block's output base, in `rcx` through the rows. -/
def Based (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I)

def Stage (n : Nat) (rs : List Reg) (L : CtLayout) (s : State) : Prop :=
  Pre n rs L s ∧ s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I)

theorem head_pins : Pins HeadState [.rdi] := by
  rintro L s t ⟨mi,hs,_⟩ ⟨mj,ht,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem storeHead_ct (i : Nat) (lo hi : Reg)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead i lo hi) hint).isSome=true) :
    RelCT isa (Two Based) (AdxTri8.storeHead i lo hi) (fun _ _ => True) := by
  refine two_taint [.rcx] ?_ hT
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.2.trans ht.2.symm

theorem rowCore_head {i n : Nat} {rs : List Reg} (hr : Regs rs) (hlen : rs.length=n+1)
    (hi : i+n+1≤8) (L : CtLayout) (s : State) (h : Stage n rs L s) :
    WP isa (.block (AdxTri8.rowCore i rs)) s (Based L) := by
  obtain ⟨⟨⟨mi,hg,hI⟩,hp,hv⟩,hc⟩ := h
  have he := L.he
  refine WP.mono (rowCore_ok rs hg.scr hp (by rw [hlen]; omega) (by intro eq; rw [eq] at hlen; simp at hlen)
    hr.1 (fun r h => let q := hr.2 r h; ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩)
    (by rw [hlen,Nat.add_sub_cancel]; exact hv)) fun t ⟨_,kt⟩ => ?_
  have dr : t.gpr .rdi=s.gpr .rdi := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,fun h => (hr.2 .rdi h).2.2.2.2 rfl⟩)
  have cr : t.gpr .rcx=s.gpr .rcx := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,fun h => (hr.2 .rcx h).2.2.2.1 rfl⟩)
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2.2,dr.trans hg.rdi,kt.2.1 ▸ hg.hdr⟩,kt.2.1 ▸ hI⟩,cr.trans hc⟩

theorem rowStep_ct {i n : Nat} {lo hi : Reg} {tail : List Reg}
    (hr : Regs (lo::hi::tail)) (hlen : (lo::hi::tail).length=n+2) (hi8 : i+n+2≤8)
    {hint htail hmov : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead i lo hi) htail).isSome=true)
    (hM : (taint.check (Taint.ofRegs []) (.block [.mov32 lo (.imm 0)]) hmov).isSome=true)
    (hC : (taint.check (Taint.ofRegs [.rbp]) (.block (AdxTri8.rowCore i (lo::hi::tail))) hint).isSome=true) :
    RelCT isa (Two (Stage (n+1) (lo::hi::tail))) (AdxTri8.rowStep i lo hi tail) (fun _ _ => True) := by
  unfold AdxTri8.rowStep
  refine RelCT.seq (two_piece [.rbp] ?_ hC (rowCore_head hr hlen hi8)) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.1.2.1.trans ht.1.2.1.symm
  refine RelCT.seq (storeHead_ct i lo hi hT) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) hM

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8RowsCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem rowStep_stage {i n : Nat} {lo hi : Reg} {tail : List Reg}
    (hr : Regs (lo::hi::tail)) (hlen : (lo::hi::tail).length=n+2) (hi8 : i+n+2≤8)
    (L : CtLayout) (s : State) (h : Stage (n+1) (lo::hi::tail) L s) :
    WP isa (AdxTri8.rowStep i lo hi tail) s (Stage n (tail++[lo]) L) := by
  obtain ⟨⟨⟨mi,hg,hI⟩,hp,hv⟩,hc⟩ := h
  have he := L.he; have hiL := L.hi; have hZ := L.hZ
  have bound : slot L.w aAcc+16*L.I+(16+8*(2*i+2))+8≤L.Z := by
    unfold slot aAcc at *; omega
  refine WP.mono (rowStep_ok hg.scr hc hp (by rw [hlen]; omega)
    bound hr.1 hr.2 (by rw [hlen,show n+2-1=n+1 by omega]; exact hv))
    fun t ⟨_,zt,ot,kt⟩ => ?_
  have dr : t.gpr .rdi=L.B := (kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.2.symm,(hr.2 hi (by simp)).2.2.2.2.symm,
      fun h => (hr.2 .rdi (by simp [h])).2.2.2.2 rfl⟩⟩)).trans hg.rdi
  have pr : t.gpr .rbp=off L.B L.e := (kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).1.2.1.symm,(hr.2 hi (by simp)).1.2.1.symm,
      fun h => (hr.2 .rbp (by simp [h])).1.2.1 rfl⟩⟩)).trans hp
  have ht := hg.hdr.of_outside ot (by unfold slot; omega)
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I := by
    rw [ot.word (by unfold slot hdrBytes sFn; omega) (by decide)]; exact hI
  have len : tail.length=n := by simp only [List.length_cons] at hlen; omega
  have cr : t.gpr .rcx=s.gpr .rcx := kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.1.symm,(hr.2 hi (by simp)).2.2.2.1.symm,
      fun h => (hr.2 .rcx (by simp [h])).2.2.2.1 rfl⟩⟩)
  refine ⟨⟨⟨mi,⟨hg.scr.congr kt.2.2,dr,ht⟩,it⟩,pr,?_⟩,cr.trans hc⟩
  have h := value_zero_top (rs := tail) zt
  simpa only [List.length_append,List.length_cons,List.length_nil,len,Nat.zero_add,Nat.add_sub_cancel] using h

/-- Closed hints for each unrolled row; the loop itself is proved relationally. -/
def RowChecks (i : Nat) (lo hi : Reg) (tail : List Reg) : Prop :=
  ∃ ht hm hc : VG.Taint.Hint VG.X86_64.Taint.T,
    (taint.check (Taint.ofRegs [.rcx]) (AdxTri8.storeHead i lo hi) ht).isSome=true ∧
    (taint.check (Taint.ofRegs []) (.block [.mov32 lo (.imm 0)]) hm).isSome=true ∧
    (taint.check (Taint.ofRegs [.rbp]) (.block (AdxTri8.rowCore i (lo::hi::tail))) hc).isSome=true

def Checks : Nat → Nat → List Reg → Prop
  | 0, _, _ => True
  | n+1, i, rs => RowChecks i rs[0]! rs[1]! (rs.drop 2) ∧ Checks n (i+1) (AdxTri8.rotate rs)

theorem rows_ct (n i : Nat) (rs : List Reg) (hr : Regs rs) (hlen : rs.length=n+1)
    (hi : i+n+1≤8) (hc : Checks n i rs) :
    RelCT isa (Two (Stage n rs)) (AdxTri8.rows n i rs) (fun _ _ => True) := by
  induction n generalizing i rs with
  | zero => exact RelCT.block_nil fun _ _ _ => trivial
  | succ n ih =>
    cases rs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons lo rs =>
      cases rs with
      | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
      | cons h tail =>
        obtain ⟨⟨ht,hm,hcore,htc,hmc,hcc⟩,next⟩ := hc
        change RelCT isa (Two (Stage (n+1) (lo::h::tail)))
          (.seq (AdxTri8.rowStep i lo h tail) (AdxTri8.rows n (i+1) (tail++[lo]))) _
        refine RelCT.seq (two_post (rowStep_ct hr hlen hi htc hmc hcc) (rowStep_stage hr hlen hi)) ?_
        apply ih (i+1) (tail++[lo]) (rotate_regs hr) _ (by omega) next
        simp only [List.length_cons] at hlen
        simp only [List.length_append,List.length_cons,List.length_nil]; omega

theorem checks_seven : Checks 7 0 AdxTri8.columns := by
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  exact ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,True.intro⟩

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlockCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def BlockState (ps : List (Nat × Nat)) (a : Nat) (L : CtLayout) (s : State) : Prop :=
  HeadState L s ∧ Ops s.mem L.B L.w ps ∧ L.e=slot L.w a+8*L.I

def CoreReady (L : CtLayout) (s : State) : Prop := HeadState L s ∧ s.gpr .rbp=off L.B L.e

theorem setup_ct_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : CtLayout) (s : State)
    (h : BlockState ps a L s) : WP isa (.block (AdxTri8.setup ca)) s (CoreReady L) := by
  obtain ⟨⟨mi,hg,hI⟩,hv,he⟩ := h
  refine WP.mono (setup_ok hg.scr hg.rdi L.hZ hv pa hI) fun t ⟨pt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,he ▸ pt⟩

theorem clear_ct_fw (L : CtLayout) (s : State) (h : CoreReady L s) :
    WP isa (.block AdxTri8.clearColumns) s (Pre 7 AdxTri8.columns L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp⟩ := h
  refine WP.mono (clear_ok AdxTri8.columns s) fun t ⟨zt,mt,kt⟩ => ?_
  exact ⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hI⟩,
    (kt.gpr (by decide)).trans hp,value_zero_lt zt 7⟩

theorem pre_pins (n : Nat) (rs : List Reg) : Pins (Pre n rs) [.rdi] :=
  fun L s t hs ht => head_pins L s t hs.1 ht.1

/-- The two stores of `clearEnds`, at addresses from `rcx`. -/
def EndStores : Prog isa :=
  .seq (.block [.store (AdxRotate8.at_ .rcx 16) .r8]) (.block [.store (AdxRotate8.at_ .rcx 136) .r8])

theorem clearEnds_fw (L : CtLayout) (s : State) (h : Pre 7 AdxTri8.columns L s) :
    WP isa AdxTri8.clearEnds s (Stage 7 AdxTri8.columns L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp,hv⟩ := h
  have hi := L.hi
  have hZ := L.hZ
  refine WP.mono (clearEnds_ok hg.scr hg.rdi hg.hdr L.hZ hI (by have := slot_le (w := L.w) (show aTmp < 8 by decide); unfold slot aAcc aTmp at *; omega)) fun t ⟨_,_,_,ot,ct,kt⟩ => ?_
  have cols : value t AdxTri8.columns=value s AdxTri8.columns :=
    value_congr fun r hr => kt.gpr (by
      simp only [AdxTri8.columns,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  refine ⟨⟨⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ot (by unfold slot; omega)⟩,?_⟩,(kt.gpr (by decide)).trans hp,cols ▸ hv⟩,ct⟩
  rw [ot.word (by unfold slot hdrBytes sFn; omega) (by decide)]; exact hI

theorem clearEnds_ct
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rcx]) EndStores hint).isSome=true) :
    RelCT isa (Two (Pre 7 AdxTri8.columns)) AdxTri8.clearEnds (Two (Stage 7 AdxTri8.columns)) := by
  refine two_post ?_ clearEnds_fw
  unfold AdxTri8.clearEnds
  refine RelCT.seq (two_piece (Ψ := fun L s => s.gpr .rcx=off L.B (slot L.w aAcc+16*L.I))
    [.rdi] (pre_pins 7 _) (by taint_decide) ?_) (two_taint [.rcx] ?_ hT)
  · rintro L s ⟨⟨mi,hg,hI⟩,_⟩
    exact WP.mono (headBases_ok hg.scr hg.rdi hg.hdr L.hZ hI) fun _ h => h.1
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

theorem block_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (BlockState ps a)) (AdxTri8.block ca) (fun _ _ => True) := by
  unfold AdxTri8.block
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup_ct_fw pa)) ?_
  · intro L s t hs ht
    exact head_pins L s t hs.1 ht.1
  exact RelCT.seq (two_piece [] (by simp [Pins]) (by taint_decide) clear_ct_fw)
    (RelCT.seq (clearEnds_ct (by taint_decide))
      (rows_ct 7 0 AdxTri8.columns columns_regs (by decide) (by decide) checks_seven))

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTri8BlocksCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout LoopState GoodV)

def AtBlock (ps : List (Nat × Nat)) (p : Layout × Nat) (s : State) : Prop := p.2<p.1.n ∧ LoopState ps p.1 p.2 s

theorem block_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (p : Layout × Nat) (s : State) (h : AtBlock ps p s) :
    WP isa (AdxTri8.block ca) s (AtBlock ps p) := by
  obtain ⟨hk,mi,hg,hv,hI⟩ := h
  have wn := p.1.hwN
  refine WP.mono (block_ok hg.scr hg.rdi hg.hdr p.1.hZ hv pa ha ha1 ha2 (by omega) hI)
    fun t ⟨_,ot,kt⟩ => ?_
  refine ⟨hk,mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ot (by unfold slot; omega)⟩,
    hv.of_outside ot (by unfold slot sFn hdrBytes; omega),?_⟩
  rw [ot.word (by unfold slot hdrBytes sFn; omega) (by decide)]; exact hI

theorem block_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (AtBlock ps)) (AdxTri8.block ca) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  have sa := slot_le (w := L.w) ha
  have hi : 8*k+8≤L.w := by omega
  have hZ := L.hZ
  let C : CtLayout := ⟨L.B,L.Z,L.w,8*k,slot L.w a+8*(8*k),L.hZ,hi,by omega⟩
  exact block_ct pa hS s t ts tt s' t' ⟨C,⟨⟨mi,gs,is⟩,vs,rfl⟩,⟨⟨mj,gt,it⟩,vt,rfl⟩⟩ es et

theorem step_loop_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (AtBlock ps)) (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (block_loop_ct pa ha hS) (block_loop_fw pa ha ha1 ha2))
    (two_taint [.rdi] ?_ (by taint_decide))
  rintro p s t ⟨_,mi,hs,_⟩ ⟨_,mj,ht,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem step_loop_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (k : Nat) (s : State) (hk : k<L.n) (h : LoopState ps L k s) :
    WP isa (.seq (AdxTri8.block ca) (.block AdxTri8.nextBlock)) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n)) ∧
      (k+1<L.n → LoopState ps L (k+1) t) ∧ (k+1=L.n → GoodV ps L t) := by
  refine WP.seq (WP.mono (block_loop_fw pa ha ha1 ha2 (L,k) s ⟨hk,h⟩) fun u ⟨_,mi,hg,hv,hI⟩ => ?_)
  dsimp only at hg hI
  have wn := L.hwN
  have hw := L.hw
  have nowrap := hg.scr.nowrap
  refine WP.mono (AdxTiledProduct.nextRow_ok hg.scr hg.rdi hg.hdr L.hZ (by omega) (by omega) hI)
    fun t ⟨mt,zt,kt⟩ => ?_
  have ot : Outside L.B (8*sFn 12) 8 u.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm L.B (AdxTiledProduct.ranges L.w) u.mem t.mem := by
    intro x hx
    apply ot x
    have := hx (8*sFn 12,32) (by simp [AdxTiledProduct.ranges]); omega
  have gt : Good t L.B L.Z L.w mi :=
    ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,AdxTiledProduct.frame_hdr hg.hdr ft⟩
  have vt := AdxTiledProduct.frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,gt,vt,?_⟩,fun _ => ⟨⟨mi,gt⟩,vt⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n
    · simp only [show 8*k+8=L.w by omega,decide_true,Bool.not_true,show ¬(k+1<L.n) by omega,decide_false]
    · simp only [show ¬(8*k+8=L.w) by omega,decide_false,Bool.not_false,show k+1<L.n by omega,decide_true]
  · rw [mt,word_writeW_self,show 8*(k+1)=8*k+8 by omega]

theorem blocks_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTri8.blocks ca) (Two (GoodV ps)) := by
  unfold AdxTri8.blocks
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) AdxTiledProduct.rows_init_fw)
    (two_loop (fun L : Layout => L.n) (step_loop_ct pa ha ha1 ha2 hS) (step_loop_fw pa ha ha1 ha2))
  rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTri8

end

/-! ## AdxTiledSquareRawCrossCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV setup_fw save_fw)

theorem rawCross_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawCross ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawCross
  refine RelCT.seq (two_piece (Ψ := GoodV ps) [.rdi] (pins_goodV ps) hS
    fun L s h => WP.mono (setup_fw pa L s h) fun _ ht => ht.1) ?_
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  refine RelCT.seq (two_post (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.save_ct) save_fw) ?_
  exact RelCT.seq (RelCT.seq (AdxTri8.blocks_ct pa ha ha1 ha2 hT) (rowsChoice_ct pa ha ha1 ha2 hR))
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.restore_ct)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
