import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample

namespace VG.Proof.MlDsa.AArch64
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Spec.Sha3 (bytesAt)

def maskPairChk (rbs wbs : List (Reg × Nat)) (seed a b ss : Ptr) : Bool :=
  sepB rbs wbs seed 132 a 1024 && sepB rbs wbs seed 132 b 1024 &&
  sepB rbs wbs seed 132 ss 8192 && sepB rbs wbs a 1024 b 1024 &&
  sepB rbs wbs a 1024 ss 8192 && sepB rbs wbs b 1024 ss 8192 &&
  inB (rbs++wbs) seed 132 && inB (rbs++wbs) a 1024 && inB (rbs++wbs) b 1024 &&
  inB (rbs++wbs) ss 8192 && inB wbs a 1024 && inB wbs b 1024 && inB wbs ss 8192

abbrev maskPairArgs (seed : Ptr) (g : Nat) (a b ss : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr seed),(.x1,.imm g),(.x2,.ptr a),(.x3,.ptr b),(.x4,.ptr ss)]

theorem maskPair_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs)
    {seed a b ss : Ptr} (g : Nat) (cs : inB bs seed 132=true)
    (ca : inB bs a 1024=true) (cb : inB bs b 1024=true) (ct : inB bs ss 8192=true) :
    ∀ x∈maskPairArgs seed g a b ss, x.2.Ok ∧ x.1∈argRegs := by
  simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  exact ⟨⟨ptr_ok (ptr_kept L cs),by decide⟩,⟨trivial,by decide⟩,
    ⟨ptr_ok (ptr_kept L ca),by decide⟩,⟨ptr_ok (ptr_kept L cb),by decide⟩,
    ⟨ptr_ok (ptr_kept L ct),by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
  {seed a b ss : Ptr} (hc : maskPairChk rbs wbs seed a b ss=true)
include L hc

theorem maskPair_cov :
    Covers ([⟨pa s seed,132⟩]++[⟨pa s a,1024⟩,⟨pa s b,1024⟩,⟨pa s ss,8192⟩]) (s.rd++s.wr) ∧
    Covers [⟨pa s a,1024⟩,⟨pa s b,1024⟩,⟨pa s ss,8192⟩] s.wr := by
  simp only [maskPairChk,Bool.and_eq_true,and_assoc] at hc
  obtain ⟨_,_,_,_,_,_,cs,_,_,_,ca,cb,ct⟩ := hc
  have hW := Covers.cons (L.cW ca) (Covers.cons (L.cW cb) (L.cW ct))
  exact ⟨Covers.append_left (L.cR cs) (Covers.right hW),hW⟩

theorem maskPair_pre {g : Nat} (hg : g=2^17 ∨ g=2^19) {s1 : State}
    (h1 : Args (maskPairArgs seed g a b ss) s s1) :
    (expandMaskPairContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed,132⟩] [⟨pa s a,1024⟩,⟨pa s b,1024⟩,⟨pa s ss,8192⟩]) := by
  simp only [maskPairChk,Bool.and_eq_true,and_assoc] at hc
  obtain ⟨c1,c2,c3,c4,c5,c6,cs,ca,cb,ct,_,_,_⟩ := hc
  sig_pre [expandMaskPairContract,expandMaskPairSig,AArch64.abi,VG.AArch64.argRegs]
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega)]
  cpre L
  exact hg
end

/-- Both independent masks, with the caller's layout and flag preserved. -/
theorem maskPairAt_ok {S : Nat} (hS : S<2^64) {nm : String} {cd : Prog isa}
    (C : CalleeOk S cd (expandMaskPairContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a b ss : Ptr}
    (hc : maskPairChk rbs wbs seed a b ss=true) {g : Nat} (hg : g=2^17 ∨ g=2^19) :
    WP isa (callAt nm cd (maskPairArgs seed g a b ss)) s fun t =>
      PPostB S s t [(a,1024),(b,1024),(ss,8192)] ∧ t.gpr .x24=s.gpr .x24 ∧
      PolyIs t.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s seed) 66)
        (32*(1+bitlen (g-1)))) (g-1) g)) ∧
      PolyIs t.mem (pa s b) (toRq (bitUnpack (H (bytesAt s.mem (pa s seed+66) 66)
        (32*(1+bitlen (g-1)))) (g-1) g)) := by
  have hc' := hc
  simp only [maskPairChk,Bool.and_eq_true,and_assoc] at hc'
  obtain ⟨_,_,_,_,_,_,cs,ca,cb,ct,_,_,_⟩ := hc'
  refine WP.mono (callAt_ok hS C (maskPair_args L.ok g cs ca cb ct)
    (by simp only [List.map_cons,List.map_nil]; decide)
    (fun s1 h1 => maskPair_pre L hc hg h1) (maskPair_cov L hc).1 (maskPair_cov L hc).2)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP.b,hP.cs .x24 (by decide) (by decide),?_⟩
  sig_post [expandMaskPairContract,expandMaskPairSig,AArch64.abi,VG.AArch64.argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega)] at hq
  exact hq

/-- Public pointers suffice for the paired call; neither seed is declassified. -/
theorem maskPairAt_tr {S : Nat} {nm : String} {cd : Prog isa}
    (C : CalleeOk S cd (expandMaskPairContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {B : List Reg} (hB : LayIn B (rbs++wbs))
    {seed a b ss : Ptr} (hc : maskPairChk rbs wbs seed a b ss=true)
    {g : Nat} (hg : g=2^17 ∨ g=2^19) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameIn B x y) :
    RelCT isa Q (callAt nm cd (maskPairArgs seed g a b ss)) fun _ _ => True := by
  have hc' := hc
  simp only [maskPairChk,Bool.and_eq_true,and_assoc] at hc'
  obtain ⟨_,_,_,_,_,_,cs,ca,cb,ct,_,_,_⟩ := hc'
  have hs := ptr_bs hB cs
  have ha := ptr_bs hB ca
  have hb := ptr_bs hB cb
  have ht := ptr_bs hB ct
  refine callAt_tr C (maskPair_args hB g cs ca cb ct)
    (by simp only [List.map_cons,List.map_nil]; decide) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx,Ly,e⟩ := hQ x y hp
  refine ⟨_,_,maskPair_pre Lx hc hg h1,?_,?_,(maskPair_cov Lx hc).1,(maskPair_cov Lx hc).2,?_,?_⟩
  · rw [e.pa hs,e.pa ha,e.pa hb,e.pa ht]; exact maskPair_pre Ly hc hg h2
  · sig_pub [expandMaskPairContract,expandMaskPairSig,AArch64.abi,VG.AArch64.argRegs]
    rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.sp h1,
      Args.r0 h2,Args.r1 h2,Args.r2 h2,Args.r3 h2,Args.r4 h2,Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2,e.pa hs,trivial,e.pa ha,e.pa hb,e.pa ht⟩
  · rw [e.pa hs,e.pa ha,e.pa hb,e.pa ht]; exact (maskPair_cov Ly hc).1
  · rw [e.pa ha,e.pa hb,e.pa ht]; exact (maskPair_cov Ly hc).2

end VG.Proof.MlDsa.AArch64
