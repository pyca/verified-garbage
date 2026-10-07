import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (read_x)

def nafPrepPublic : List Reg := [.x0,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x19,.x20]

structure NafPrepChecks (K : WinCfg) (src : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block (Naf.prepInit K src))
  step : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs nafPrepPublic)) Naf.prepStep

structure NafPrepPair (base : Addr) (size bits k j : Nat) (s t : State) : Prop where
  left : NafPrepState base size bits k j s
  right : NafPrepState base size bits k j t
  sp : s.sp=t.sp

theorem NafPrepPair.public {base : Addr} {size bits k j : Nat} {s t : State}
    (h : NafPrepPair base size bits k j s t) : AArch64.Taint.Agree (Taint.ofRegs nafPrepPublic) s t := by
  have hv := nafVal5_inj (h.left.value.trans h.right.value.symm)
  refine ⟨h.sp,?_⟩
  intro r hr
  simp only [Taint.mem_ofRegs,nafPrepPublic,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.left.scr.x0.trans h.right.scr.x0.symm
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2.1
  · exact hv.2.2.2.2
  · exact h.left.mask.trans h.right.mask.symm
  · exact h.left.sign.trans h.right.sign.symm
  · exact h.left.zero.trans h.right.zero.symm
  · exact h.left.one.trans h.right.one.symm
  · exact h.left.count.trans h.right.count.symm
  · exact h.left.ptr.trans h.right.ptr.symm

theorem nafPrepStep_relCT {K : WinCfg} {src : Nat} (hc : NafPrepChecks K src)
    {base : Addr} {size k j : Nat} (hb : K.bits+257≤size) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    RelCT isa (NafPrepPair base size K.bits k j) Naf.prepStep (NafPrepPair base size K.bits k (j+1)) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,ks,_⟩ := nafPrepStep_ok hp.left hb hj hv
  obtain ⟨_,_,xt,it,kt,_⟩ := nafPrepStep_ok hp.right hb hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial hp.public es et,is,it,ks.sp.trans (hp.sp.trans kt.sp.symm)⟩

theorem nafPrepLoop_relCT {K : WinCfg} {src : Nat} (hc : NafPrepChecks K src)
    {base : Addr} {size k : Nat} (hb : K.bits+257≤size) (hk : k<2^256) :
    RelCT isa (NafPrepPair base size K.bits k 0) (.loop Naf.prepStep (.nonzero .x .x19)) (fun _ _ => True) := by
  let I := fun m s t => 1≤m ∧ m≤257 ∧ NafPrepPair base size K.bits k (257-m) s t
  have step : ∀ m,RelCT isa (I m) Naf.prepStep (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → True) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<m,I n s t)) := by
    intro m
    by_cases hm : 1≤m ∧ m≤257
    · have hv := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hv' : Naf5.residual k (257-m)≤2^256 := Nat.le_trans hv
        (Nat.pow_le_pow_right (by decide) (by omega))
      refine (nafPrepStep_relCT hc hb (j:=257-m) (by omega) hv').mono
        (P':=I m) (fun _ _ h => h.2.2) ?_
      intro s t hp
      have s19 : s.gpr .x19=BitVec.ofNat 64 (m-1) := by rw [hp.left.count]; congr 1; omega
      have t19 : t.gpr .x19=BitVec.ofNat 64 (m-1) := by rw [hp.right.count]; congr 1; omega
      refine ⟨by simp only [eval,read_x,s19,t19],fun _ => trivial,fun he => ?_⟩
      have hn : m-1≠0 := by
        intro hz; simp only [eval,read_x,s19,hz] at he; cases he
      refine ⟨m-1,by omega,by omega,by omega,?_⟩
      have hj : 257-(m-1)=257-m+1 := by omega
      rw [hj]; exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)
  exact (RelCT.loop I step 257).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem nafPrep_relCT (K : WinCfg) {base : Addr} {size src : Nat}
    (hsrc : src+32≤size) (hsrc8 : src%8=0) (hbits : K.bits<4096)
    (hb : K.bits+257≤size) (hc : NafPrepChecks K src) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      wordsVal s.mem base src 4=wordsVal t.mem base src 4)
      (Naf.prep K src) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧ a.sp=b.sp ∧
      wordsVal a.mem base src 4=wordsVal s.mem base src 4 ∧ wordsVal b.mem base src 4=wordsVal s.mem base src 4)
      (.block (Naf.prepInit K src)) (NafPrepPair base size K.bits (wordsVal s.mem base src 4) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_,_,xa,ia,ka,_⟩ := nafPrepInit_ok K hab.1 hsrc hsrc8 hbits
    obtain ⟨_,_,xb,ib,kb,_⟩ := nafPrepInit_ok K hab.2.1 hsrc hsrc8 hbits
    obtain ⟨_,rfl⟩ := Exec.det ea xa
    obtain ⟨_,rfl⟩ := Exec.det eb xb
    rw [hab.2.2.2.1] at ia
    rw [hab.2.2.2.2] at ib
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0]) a b := by
      refine ⟨hab.2.2.1,?_⟩
      intro r hr; simp only [Taint.mem_ofRegs,List.mem_singleton] at hr; subst r
      exact hab.1.x0.trans hab.2.1.x0.symm
    exact ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb,ia,ib,ka.sp.trans (hab.2.2.1.trans kb.sp.symm)⟩
  exact (RelCT.seq hi (nafPrepLoop_relCT hc hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,hp.2.2.1,rfl,hp.2.2.2.symm⟩ es et

end VG.Proof.Weierstrass.AArch64
