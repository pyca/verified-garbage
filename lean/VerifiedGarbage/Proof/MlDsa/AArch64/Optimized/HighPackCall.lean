import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Pack
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVerified

namespace VG.Proof.MlDsa.AArch64
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Spec.Sha3 (bytesAt)

abbrev hpLen (g : Nat) : Nat := 32*bitlen ((q-1)/(2*g)-1)
abbrev hpArgs (f out : Ptr) : List (Reg × Arg) := [(.x0,.ptr f),(.x1,.ptr out)]

theorem hp_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs)
    {f out : Ptr} {len : Nat} (c2 : inB bs f 1024=true) (c3 : inB bs out len=true) :
    ∀ x∈hpArgs f out, x.2.Ok ∧ x.1∈argRegs := by
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c2),by decide⟩,⟨ptr_ok (ptr_kept L c3),by decide⟩⟩

theorem hp_pre {S g : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {f out : Ptr}
    (hc : rwChk rbs wbs f 1024 out (hpLen g)=true)
    (hf : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (hpArgs f out) s s1) :
    (highPackContract g AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s f,1024⟩] [⟨pa s out,hpLen g⟩]) := by
  obtain ⟨c1,c2,c3⟩ := rw_parts hc
  sig_pre [highPackContract,highPackSig,AArch64.abi,VG.AArch64.argRegs]
  rw [Args.r0 h1,Args.r1 h1,Args.sp h1,Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hf

/-- Fused packing call preserves the caller's live layout while producing
the same bytes as separate HighBits and SimpleBitPack operations. -/
theorem highPackAt_ok {S g : Nat} (hS : S<2^64) {nm : String} {cd : Prog isa}
    (C : CalleeOk S cd (highPackContract g AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {f out : Ptr}
    (hc : rwChk rbs wbs f 1024 out (hpLen g)=true) (hf : Reduced s.mem (pa s f)) :
    WP isa (callAt nm cd (hpArgs f out)) s fun t =>
      PPostB S s t [(out,hpLen g)] ∧ t.gpr .x24=s.gpr .x24 ∧
      bytesAt t.mem (pa s out) (hpLen g)=simpleBitPack
        ((polyAt s.mem (pa s f)).map fun c => (highBits g c).toNat) ((q-1)/(2*g)-1) := by
  obtain ⟨_,c2,c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (hp_args L.ok c2 c3)
    (by simp only [List.map_cons,List.map_nil]; decide)
    (fun s1 h1 => hp_pre L hc hf h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP.b,hP.cs .x24 (by decide) (by decide),?_⟩
  sig_post [highPackContract,highPackSig,AArch64.abi,VG.AArch64.argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  exact hq


/-- Calling the fused helper reveals no coefficient values through timing. -/
theorem highPackAt_tr {S g : Nat} {nm : String} {cd : Prog isa}
    (C : CalleeOk S cd (highPackContract g AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : LayIn B (rbs++wbs)) {f out : Ptr}
    (hc : rwChk rbs wbs f 1024 out (hpLen g)=true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧ SameIn B x y) :
    RelCT isa Q (callAt nm cd (hpArgs f out)) fun _ _ => True := by
  obtain ⟨_,c2,c3⟩ := rw_parts hc
  have hbs : f.1∈B ∧ out.1∈B := ⟨ptr_bs hB c2,ptr_bs hB c3⟩
  refine callAt_tr C (hp_args hB c2 c3) (by simp only [List.map_cons,List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx,Ly,rx,ry,e⟩ := hQ x y hp
  refine ⟨_,_,hp_pre Lx hc rx h1,?_,?_,(rw_cov Lx hc).1,(rw_cov Lx hc).2,?_,?_⟩
  · rw [e.pa hbs.1,e.pa hbs.2]; exact hp_pre Ly hc ry h2
  · sig_pub [highPackContract,highPackSig,AArch64.abi,VG.AArch64.argRegs]
    rw [Args.r0 h1,Args.r1 h1,Args.r0 h2,Args.r1 h2,Args.sp h1,Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2,e.pa hbs.1,e.pa hbs.2⟩
  · rw [e.pa hbs.1,e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

end VG.Proof.MlDsa.AArch64
