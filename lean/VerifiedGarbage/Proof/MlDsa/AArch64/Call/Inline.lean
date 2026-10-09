import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call

namespace VG.Proof.MlDsa.AArch64
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Arg glue)

/-- Inline the real verified body after its argument moves. Unlike a call,
this does not introduce unknown link registers or flags. -/
theorem inlineAt_ok {S : Nat} (hS : S<2^64) {c : Prog isa} {k : Contract isa}
    (C : CalleeOk S c k) {as : List (Reg × Arg)}
    (hok : ∀a∈as,a.2.Ok ∧ a.1∈argRegs) (hnd : (as.map (·.1)).Nodup)
    {s : State} {rd wr : List Region}
    (hpre : ∀s1,Args as s s1 → k.pre (s1.withRegions rd wr))
    (hc : Covers (rd++wr) (s.rd++s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block (glue as)) c) s fun t=>Post S s t wr ∧
      ∃s1,Args as s s1 ∧ k.post (s1.withRegions rd wr) (t.withRegions rd wr) := by
  refine WP.seq (WP.mono (glue_ok hok hnd s) fun s1 h1=>?_)
  have k1:=h1.2
  refine WP.narrowF (C.correct _ (hpre s1 h1))
    (by rw [k1.rd,k1.wr];exact hc) (by rw [k1.wr];exact hw)
    (fun t hrd hwr hsp hf hp=>?_) (by have := C.fd;omega)
  refine ⟨⟨hrd.trans k1.rd,hwr.trans k1.wr,hsp.trans k1.sp,
    fun r hr _=>?_,?_,fun r hr=>(hp.1.2.2 r hr).trans (k1.vcs r hr)⟩,s1,h1,hp.2⟩
  · exact (hp.1.1 r hr).trans (k1.gpr r (argRegs_pres r hr))
  · rw [h1.1.2,k1.sp] at hf
    exact Frame.below_mono hf C.fd hS

/-- Timing of an actual inline body under its ordinary contract. -/
theorem inlineBody_tr {S : Nat} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀x y,P x y → k.pre (x.withRegions rd wr) ∧ k.pre (y.withRegions rd wr) ∧
      k.pub (x.withRegions rd wr) (y.withRegions rd wr) ∧
      Covers (rd++wr) (x.rd++x.wr) ∧ Covers wr x.wr ∧
      Covers (rd++wr) (y.rd++y.wr) ∧ Covers wr y.wr) :
    RelCT isa P c fun _ _=>True := by
  intro x y tx ty u v hp ex ey
  obtain ⟨px,py,pub,cx,wx,cy,wy⟩:=hP x y hp
  obtain ⟨u',ex'⟩:=VG.AArch64.trace_narrow C.correct px cx wx ex
  obtain ⟨v',ey'⟩:=VG.AArch64.trace_narrow C.correct py cy wy ey
  exact ⟨C.ct _ _ _ _ _ _ px py pub ex' ey',trivial⟩

theorem inlineAt_tr {S : Nat} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {as : List (Reg × Arg)} (hok : ∀a∈as,a.2.Ok ∧ a.1∈argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀x y x1 y1,P x y → Args as x x1 → Args as y y1 → ∃rd wr : List Region,
      k.pre (x1.withRegions rd wr) ∧ k.pre (y1.withRegions rd wr) ∧
      k.pub (x1.withRegions rd wr) (y1.withRegions rd wr) ∧
      Covers (rd++wr) (x.rd++x.wr) ∧ Covers wr x.wr ∧
      Covers (rd++wr) (y.rd++y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (.seq (.block (glue as)) c) fun _ _=>True :=
  RelCT.seq (RelCT.postDep (Q:=fun x1 y1=>∃x y,P x y ∧ Args as x x1 ∧ Args as y y1)
    (block_nomem_tr (glue_nomem as)) (fun x y _=>⟨glue_ok hok hnd x,glue_ok hok hnd y⟩)
    fun x y _ _ hp h1 h2=>⟨x,y,hp,h1,h2⟩)
    (RelCT.mono (RelCT.exists_ (P:=fun (a : List Region × List Region) (x1 y1 : State)=>
      k.pre (x1.withRegions a.1 a.2) ∧ k.pre (y1.withRegions a.1 a.2) ∧
      k.pub (x1.withRegions a.1 a.2) (y1.withRegions a.1 a.2) ∧
      Covers (a.1++a.2) (x1.rd++x1.wr) ∧ Covers a.2 x1.wr ∧
      Covers (a.1++a.2) (y1.rd++y1.wr) ∧ Covers a.2 y1.wr)
      fun a=>inlineBody_tr C a.1 a.2 fun _ _ h=>h)
      (fun x1 y1 ⟨x,y,hp,h1,h2⟩=>by
        obtain ⟨rd,wr,p1,p2,pub,c1,w1,c2,w2⟩:=hP x y x1 y1 hp h1 h2
        exact ⟨(rd,wr),p1,p2,pub,by rw [h1.2.rd,h1.2.wr];exact c1,
          by rw [h1.2.wr];exact w1,by rw [h2.2.rd,h2.2.wr];exact c2,
          by rw [h2.2.wr];exact w2⟩)
      fun _ _ h=>h)
end VG.Proof.MlDsa.AArch64
