module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBoth
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
public import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Bounded fourth/fifth-block continuation and exact failure cleanup -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.Sha3
open VG.Proof.Sha3.AArch64.Neon

def resumeWrites (p a b : Addr) : List Region := [⟨p,1712⟩,polyRegion a,polyRegion b]

def resumeRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x20,.x21,.x22,.x23]

structure ProgressW (w16 : Bool) (A B : Spec.Sha3.State) (n : Nat) (p a b c : Addr) (s : State) : Prop where
  context : Context p a b c s
  ptr : s.gpr .x19=p
  pair : PairAt s.mem p (iterF n A) (iterF n B)
  left : Rej8.Scalar.CoeffsW w16 s.mem a (accepted A n)
  right : Rej8.Scalar.CoeffsW w16 s.mem b (accepted B n)
  saveLeft : checkpointW w16 (p+1680) a (accepted A n) s.mem
  saveRight : checkpointW w16 (p+1696) b (accepted B n) s.mem

structure AdvancedW (w16 : Bool) (A B : Spec.Sha3.State) (n : Nat) (p a b c : Addr) (s u : State) : Prop where
  keep : Keep resumeRegs s u
  frame : Frame (resumeWrites p a b) s.mem u.mem
  progress : ProgressW w16 A B n p a b c u
  flag : (u.gpr .x6).toNat=if (accepted A n).length=256 ∧ (accepted B n).length=256 then 1 else 0

structure BoundedW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) (s u : State) : Prop where
  keep : Keep resumeRegs s u
  frame : Frame (resumeWrites p a b) s.mem u.mem
  context : Context p a b c u
  ptr : u.gpr .x19=p
  left : Rej8.Scalar.CoeffsW w16 u.mem a (accepted A 5)
  right : Rej8.Scalar.CoeffsW w16 u.mem b (accepted B 5)
  saveLeft : checkpointW w16 (p+1680) a (accepted A 5) u.mem
  saveRight : checkpointW w16 (p+1696) b (accepted B 5) u.mem
  flag : (u.gpr .x6).toNat=if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0

abbrev Bounded := BoundedW false

theorem bounded_of_five {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (h : AdvancedW w16 A B 5 p a b c s u) : BoundedW w16 A B p a b c s u :=
  ⟨h.keep,h.frame,h.progress.context,h.progress.ptr,h.progress.left,h.progress.right,
   h.progress.saveLeft,h.progress.saveRight,h.flag⟩

theorem bounded_of_full_four {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (h : AdvancedW w16 A B 4 p a b c s u) (hf : u.gpr .x6≠0) : BoundedW w16 A B p a b c s u := by
  have full : (accepted A 4).length=256 ∧ (accepted B 4).length=256 := by
    by_contra hh
    have he : (u.gpr .x6).toNat=0 := by rw [h.flag,ite_eq_right hh]
    exact hf (BitVec.eq_of_toNat_eq he)
  have ha := accepted_full full.1 (by decide : 4≤5)
  have hb := accepted_full full.2 (by decide : 4≤5)
  refine ⟨h.keep,h.frame,h.progress.context,h.progress.ptr,?_,?_,?_,?_,?_⟩
  · rw [ha]; exact h.progress.left
  · rw [hb]; exact h.progress.right
  · rw [ha]; exact h.progress.saveLeft
  · rw [hb]; exact h.progress.saveRight
  · rw [ha,hb]; exact h.flag

theorem bounded_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa (Impl.MlKem.AArch64.Paired.extraStep w16) t (AdvancedW w16 A B (n+1) p a b c t))
    (h : ProgressW w16 A B 3 p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa (.seq (Impl.MlKem.AArch64.Paired.extraStep w16)
      (.ite (.zero .x .x6) (Impl.MlKem.AArch64.Paired.extraStep w16) (.block []))) s
      (BoundedW w16 A B p a b c s) := by
  refine WP.seq (WP.mono_syms (step (Or.inl rfl) h hs) fun t ht st => ?_)
  refine WP.ite (t.gpr .x6 == 0) (eval_zero _ _) (fun _=>?_) (fun hz=>?_) 
  · refine WP.mono (step (Or.inr rfl) ht.progress (by rw [st]; exact hs)) fun u hu => ?_
    exact ⟨(ht.keep.trans hu.keep).mono (by decide),ht.frame.trans hu.frame,hu.progress.context,
      hu.progress.ptr,hu.progress.left,hu.progress.right,hu.progress.saveLeft,hu.progress.saveRight,hu.flag⟩
  · apply wp_nil
    exact bounded_of_full_four ht (by intro he; rw [he] at hz; contradiction)

structure ResumePostW (w16 : Bool) (A B : Spec.Sha3.State) (p a b : Addr) (s u : State) : Prop where
  keep : Keep (.x24::resumeRegs) s u
  frame : Frame (resumeWrites p a b) s.mem u.mem
  left : CoeffsUpToW w16 u.mem a (accepted A 5).length (Sample.cvW w16 (accepted A 5)) (fun _=>0)
  reducedLeft : ReducedW (cw w16) u.mem a
  right : CoeffsUpToW w16 u.mem b (accepted B 5).length (Sample.cvW w16 (accepted B 5)) (fun _=>0)
  reducedRight : ReducedW (cw w16) u.mem b
  status : u.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0)

theorem resume_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa (Impl.MlKem.AArch64.Paired.extraStep w16) t (AdvancedW w16 A B (n+1) p a b c t))
    (h : ProgressW w16 A B 3 p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa (Impl.MlKem.AArch64.Paired.extraPair w16) s (ResumePostW w16 A B p a b s) := by
  change WP isa (.seq (Impl.MlKem.AArch64.Paired.extraStep w16) (.seq (.ite _ _ _) _)) s _
  apply WP.assoc
  refine WP.seq (WP.mono (bounded_ok step h hs) fun t ht => ?_)
  have hand : WP isa (.block [.logic .and .x .x24 .x24 .x6]) t fun v=>
      Only [.x24] t v ∧ v.gpr .x24=t.gpr .x24 &&& t.gpr .x6 :=
    wp_and fun v kv ev=>wp_nil ⟨kv,ev⟩
  refine WP.seq (WP.mono hand fun v ⟨kv,ev⟩ => ?_)
  have cv : Context p a b c v := ht.context.frame kv.rd kv.wr (by rw [kv.mem]; exact Frame.refl _ _)
  refine WP.mono (zeroBoth_ok cv (by rw [kv.get .x19]; exact ht.ptr)
    (accepted_length A 5) (accepted_length B 5)
    (by rw [kv.mem]; exact ht.left) (by rw [kv.mem]; exact ht.right)
    (by rw [kv.mem]; exact ht.saveLeft) (by rw [kv.mem]; exact ht.saveRight)) fun u ⟨ku,fu,ca,ra,cb,rb⟩ => ?_
  refine ⟨((ht.keep.trans kv.keep).trans ku).mono (by decide),?_,ca,ra,cb,rb,?_⟩
  · have ff : Frame (resumeWrites p a b) t.mem u.mem := by
      rw [←kv.mem]
      exact fu.mono (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl <;> simp [resumeWrites])
    exact ht.frame.trans ff
  · rw [ku.get .x24,ev,ht.keep.get .x24]
    apply congrArg (fun x : BitVec 64 => s.gpr .x24 &&& x)
    apply BitVec.eq_of_toNat_eq
    rw [ht.flag]
    split_ifs <;> rfl

theorem ResumePostW.saved {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s₀ s u : State}
    (h : ResumePostW w16 A B p a b s u) (ctx : Context p a b c s)
    (hs : Noise.Saved p s₀ s.mem) : Noise.Saved p s₀ u.mem := by
  apply hs.frame h.frame
  intro r hr
  simp only [resumeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Offset.disjoint_base p (by decide) (by decide)
  · exact ctx.farA.sub_left (Offset.sub_base p (by decide))
  · exact ctx.farB.sub_left (Offset.sub_base p (by decide))

end VG.Proof.MlKem.AArch64.Paired
