module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context

import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.MlKem.AArch64.Paired
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
/-! # Bounded fourth/fifth-block continuation and exact failure cleanup -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ZeroBoth.lean`, which only this module imported.
section

/-! # Finalize both bounded matrix samples, retaining zero-filled failure outputs -/
section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem zeroBoth_ok {w16 : Bool} {s : State} {p a b c : Addr} {L M : List Zq}
    (hctx : Context p a b c s) (hp : s.gpr .x19=p)
    (hl : L.length≤256) (hm : M.length≤256)
    (ca : Rej8.Scalar.CoeffsW w16 s.mem a L) (cb : Rej8.Scalar.CoeffsW w16 s.mem b M)
    (sa : checkpointW w16 (p+1680) a L s.mem) (sb : checkpointW w16 (p+1696) b M s.mem) :
    WP isa (.seq (Impl.MlKem.AArch64.Paired.zeroExtra 1680 w16)
      (Impl.MlKem.AArch64.Paired.zeroExtra 1696 w16)) s fun u =>
      Keep [.x3,.x4,.x13] s u ∧ Frame [polyRegion a,polyRegion b] s.mem u.mem ∧
      CoeffsUpToW w16 u.mem a L.length (Sample.cvW w16 L) (fun _=>0) ∧ ReducedW (cw w16) u.mem a ∧
      CoeffsUpToW w16 u.mem b M.length (Sample.cvW w16 M) (fun _=>0) ∧ ReducedW (cw w16) u.mem b := by
  have iw {o l : Nat} (h : o+l≤2048) := in_rd_wr (rd := s.rd) (Noise.inScratch hctx.scratch h (by decide))
  refine WP.seq (WP.mono (zeroExtra_ok s (slot:=1680) (by decide) (by decide) hl ca
    (by rw [hp]; exact sa) (by rw [hp]; exact iw (by decide)) (by rw [hp]; exact iw (by decide))
    (fun i hi=>Noise.inScratch hctx.outA (cs_store_le w16 hi) (by decide))) fun t ⟨kt,ft,ct,rt⟩ => ?_)
  have t19 : t.gpr .x19=p := (kt.get .x19).trans hp
  have cb' : Rej8.Scalar.CoeffsW w16 t.mem b M := coeffs_frame cb hm ft (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact hctx.apart.symm)
  have sb' : checkpointW w16 (t.gpr .x19+1696) b M t.mem := by
    rw [t19]
    exact checkpoint_frame sb ft (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact hctx.farA.sub_left (Offset.sub_base p (by decide)))
  refine WP.mono (zeroExtra_ok t (slot:=1696) (by decide) (by decide) hm cb' sb'
    (by rw [kt.rd,kt.wr,t19]; exact iw (by decide))
    (by rw [kt.rd,kt.wr,t19]; exact iw (by decide))
    (fun i hi=>by rw [kt.wr]; exact Noise.inScratch hctx.outB (cs_store_le w16 hi) (by decide))) fun u ⟨ku,fu,cu,ru⟩ => ?_
  have ca' : CoeffsUpToW w16 u.mem a L.length (Sample.cvW w16 L) (fun _=>0) := by
    intro i hi
    rw [coeffAtW_frame fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact hctx.apart) hi]
    exact ct i hi
  exact ⟨(kt.trans ku).mono (by decide),
    (ft.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans
      (fu.mono (by intro r hr; rw [List.mem_singleton.mp hr]; simp)),
    ca',Sample.reduced_of_coeffs ca',cu,ru⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.Sha3
open VG.Proof.Sha3.AArch64.Neon

def resumeWrites (p a b : Addr) : List Region := [⟨p,1712⟩,polyRegion a,polyRegion b]

def resumeRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x20,.x21,.x22,.x23]

/-- The registers of `Paired.retry`: those of its blocks and its counter `x30`. -/
def retryRegs : List Reg := resumeRegs ++ [.x30]

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
  keep : Keep retryRegs s u
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
    (k : Keep retryRegs s u) (f : Frame (resumeWrites p a b) s.mem u.mem) (h : ProgressW w16 A B 5 p a b c u)
    (hf : (u.gpr .x6).toNat=if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0) :
    BoundedW w16 A B p a b c s u :=
  ⟨k,f,h.context,h.ptr,h.left,h.right,h.saveLeft,h.saveRight,hf⟩

theorem bounded_of_full_four {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (k : Keep retryRegs s u) (f : Frame (resumeWrites p a b) s.mem u.mem) (h : ProgressW w16 A B 4 p a b c u)
    (hf : (u.gpr .x6).toNat=if (accepted A 4).length=256 ∧ (accepted B 4).length=256 then 1 else 0)
    (full : (accepted A 4).length=256 ∧ (accepted B 4).length=256) : BoundedW w16 A B p a b c s u := by
  have ha := accepted_full full.1 (by decide : 4≤5)
  have hb := accepted_full full.2 (by decide : 4≤5)
  refine ⟨k,f,h.context,h.ptr,?_,?_,?_,?_,?_⟩
  · rw [ha]; exact h.left
  · rw [hb]; exact h.right
  · rw [ha]; exact h.saveLeft
  · rw [hb]; exact h.saveRight
  · rw [ha,hb]; exact hf

/-- Before an iteration of `Paired.retry` with `n` blocks left after it
(`n = 1`, or `n = 0` after a fourth block), `x30 = n`. -/
structure RetryInv (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) (s : State) (n : Nat) (v : State) :
    Prop where
  le : n ≤ 1
  keep : Keep retryRegs s v
  frame : Frame (resumeWrites p a b) s.mem v.mem
  progress : ProgressW w16 A B (4-n) p a b c v
  count : v.gpr .x30 = BitVec.ofNat 64 n
  syms : v.syms "VG_MLKEM_REJ_SHUFFLE"=c

/-- Whether `Paired.retry` takes another block after the one leaving `n`: only
after the fourth, when a stream still lacks candidates. -/
def retryAgain (A B : Spec.Sha3.State) (n : Nat) : Bool :=
  decide (n=1 ∧ ¬((accepted A 4).length=256 ∧ (accepted B 4).length=256))

theorem ProgressW.only {w16 : Bool} {A B : Spec.Sha3.State} {n : Nat} {p a b c : Addr} {s u : State}
    (h : ProgressW w16 A B n p a b c s) {rs : List Reg} (k : Only rs s u) (hr : .x19 ∉ rs := by decide) :
    ProgressW w16 A B n p a b c u := by
  refine ⟨h.context.frame k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _),?_,?_,?_,?_,?_,?_⟩
  · rw [k.get .x19 hr]; exact h.ptr
  all_goals rw [k.mem]
  · exact h.pair
  · exact h.left
  · exact h.right
  · exact h.saveLeft
  · exact h.saveRight

/-- `(x6 - x30) >>> 63`, for `x6` and `x30` at most one: whether `x6 < x30`. -/
theorem retry_cond {x y : BitVec 64} {n : Nat} (hx : x.toNat ≤ 1) (hy : y=BitVec.ofNat 64 n) (hn : n ≤ 1) :
    (x - y) >>> 63 = if x.toNat < n then 1 else 0 := by
  have hx' : x=0 ∨ x=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h|h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  subst hy
  rcases hx' with rfl|rfl <;> rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl|rfl <;> decide

/-- An iteration of `Paired.retry`: a block, then `x7` says whether to take another. -/
theorem retryStep_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s v : State} {n : Nat}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa (Impl.MlKem.AArch64.Paired.extraStep w16) t (AdvancedW w16 A B (n+1) p a b c t))
    (h : RetryInv w16 A B p a b c s n v) :
    WP isa (.seq (Impl.MlKem.AArch64.Paired.extraStep w16)
      (.block [.sub .x .x7 .x6 .x30,.lsr .x .x7 .x7 63,.movz .x .x30 0 0])) v fun u =>
      isa.eval (.nonzero .x .x7) u=some (retryAgain A B n) ∧
      (retryAgain A B n=false → BoundedW w16 A B p a b c s u) ∧
      (retryAgain A B n=true → RetryInv w16 A B p a b c s 0 u) := by
  have hn := h.le
  refine WP.seq (WP.mono_syms (step (by omega) h.progress h.syms) fun t ht ts => ?_)
  have t30 : t.gpr .x30=BitVec.ofNat 64 n := (ht.keep.get .x30).trans h.count
  have t6 : (t.gpr .x6).toNat ≤ 1 := by rw [ht.flag]; split <;> omega
  refine WP.of_syms (wp_sub fun t₁ k₁ e₁ => wp_lsr (by decide) fun t₂ k₂ e₂ =>
    wp_movz fun u k₃ e₃ => wp_nil fun us => ?_)
  have ku : Only ([.x7]++[.x7]++[.x30]) t u := (k₁.trans k₂).trans k₃
  have u7 : u.gpr .x7=if (t.gpr .x6).toNat<n then 1 else 0 := by
    rw [k₃.get .x7, e₂, e₁]; exact retry_cond t6 t30 hn
  have u6 : u.gpr .x6=t.gpr .x6 := ku.get .x6
  have keep : Keep retryRegs s u := ((h.keep.trans ht.keep).trans ku.keep).mono
  have frame : Frame (resumeWrites p a b) s.mem u.mem := by rw [ku.mem]; exact h.frame.trans ht.frame
  have pu := ht.progress.only ku
  have syms : u.syms "VG_MLKEM_REJ_SHUFFLE"=c := by rw [us, ts]; exact h.syms
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl|rfl
  · have hf : (u.gpr .x6).toNat=if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0 := by
      rw [u6]; exact ht.flag
    have ra : retryAgain A B 0=false := by simp [retryAgain]
    refine ⟨?_,fun _ => bounded_of_five keep frame pu hf,fun h => (by rw [ra] at h; cases h)⟩
    rw [eval_nonzero,u7,ra]; simp
  · have hf : (t.gpr .x6).toNat=if (accepted A 4).length=256 ∧ (accepted B 4).length=256 then 1 else 0 :=
      ht.flag
    by_cases full : (accepted A 4).length=256 ∧ (accepted B 4).length=256
    · have ra : retryAgain A B 1=false := by simp [retryAgain,full]
      refine ⟨?_,fun _ => bounded_of_full_four keep frame pu (by rw [u6]; exact ht.flag) full,
        fun h => (by rw [ra] at h; cases h)⟩
      rw [eval_nonzero,u7,ra,hf]; simp [full]
    · have ra : retryAgain A B 1=true := by simp [retryAgain,full]
      refine ⟨?_,fun h => (by rw [ra] at h; cases h),fun _ => ⟨by decide,keep,frame,pu,?_,syms⟩⟩
      · rw [eval_nonzero,u7,ra,hf]; simp [full]
      · rw [e₃]; decide

/-- `x30 = 1` before the first iteration of `Paired.retry`. -/
theorem retryInit_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : ProgressW w16 A B 3 p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa (.block [.movz .x .x30 1 0]) s (RetryInv w16 A B p a b c s 1) :=
  WP.of_syms (wp_movz fun v k e => wp_nil fun vs =>
    ⟨Nat.le_refl _,k.keep.mono,by rw [k.mem]; exact Frame.refl _ _,h.only k,by rw [e]; decide,
      by rw [vs]; exact hs⟩)

/-- The fourth block, and the fifth when a stream still lacks candidates after it. -/
theorem bounded_ok {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa (Impl.MlKem.AArch64.Paired.extraStep w16) t (AdvancedW w16 A B (n+1) p a b c t))
    (h : ProgressW w16 A B 3 p a b c s) (hs : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) :
    WP isa (Impl.MlKem.AArch64.Paired.retry w16) s (BoundedW w16 A B p a b c s) := by
  refine WP.seq (WP.mono (retryInit_ok h hs) fun v inv => ?_)
  refine WP.loop (M := isa) (fun n u => RetryInv w16 A B p a b c s n u) (fun n u hu => ?_) 1 v inv
  refine WP.mono (retryStep_ok step hu) fun u' ⟨ev,hb,hi⟩ => ?_
  cases hr : retryAgain A B n
  · exact .inl ⟨by rw [ev,hr],hb hr⟩
  · have hn : n=1 := by simp only [retryAgain,decide_eq_true_eq] at hr; exact hr.1
    exact .inr ⟨by rw [ev,hr],0,by omega,hi hr⟩

structure ResumePostW (w16 : Bool) (A B : Spec.Sha3.State) (p a b : Addr) (s u : State) : Prop where
  keep : Keep (.x24::retryRegs) s u
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
  change WP isa (.seq (Impl.MlKem.AArch64.Paired.retry w16) (.seq (.block _) _)) s _
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
    (repeat' split) <;> rfl

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
