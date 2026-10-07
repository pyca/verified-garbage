import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrepTiming

/-! Sparse recoding branches depend on the public scalar and its public digit index. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

structure FastPrepChecks (src bits w : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
    (.block (Naf.init src++setConst 33 bits 0))
  step : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs nafPrepPublic))
    (Impl.Weierstrass.X86_64.FastNaf.step bits w)

abbrev FastPrepPair (base : Addr) (size bits w k j : Nat) (s t : State) : Prop :=
  FastPrepState base size bits w k j s ∧ FastPrepState base size bits w k j t

theorem FastPrepPair.public {base : Addr} {size bits w k j : Nat} {s t : State}
    (h : FastPrepPair base size bits w k j s t) : X86_64.Taint.Agree (Taint.ofRegs nafPrepPublic) s t := by
  have hv := nafVal5_inj (h.1.value.trans h.2.value.symm)
  apply Taint.agree_ofRegs
  intro r hr
  simp only [nafPrepPublic,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  · exact h.1.count.trans h.2.count.symm
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2.1
  · exact hv.2.2.2.2

theorem fastPrepStep_relCT {src bits w : Nat} (hw : FastNaf.Width w) (hc : FastPrepChecks src bits w)
    {base : Addr} {size k j : Nat} (hb : bits+264≤size) (hj : j<257)
    (hv : FastNaf.residual w k j≤2^256) :
    RelCT isa (FastPrepPair base size bits w k j) (Impl.Weierstrass.X86_64.FastNaf.step bits w) (fun s t =>
      FastPrepPair base size bits w k (j+fastDelta w k j) s t ∧
      s.cf=some (decide (j+fastDelta w k j<257)) ∧ t.cf=some (decide (j+fastDelta w k j<257))) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,fs,_,_⟩ := fastPrepStep_ok hw hp.1 hb hj hv
  obtain ⟨_,_,xt,it,ft,_,_⟩ := fastPrepStep_ok hw hp.2 hb hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial hp.public es et,⟨is,it⟩,fs,ft⟩

theorem fastPrepLoop_relCT {src bits w : Nat} (hw : FastNaf.Width w) (hc : FastPrepChecks src bits w)
    {base : Addr} {size k : Nat} (hb : bits+264≤size) (hk : k<2^256) :
    RelCT isa (FastPrepPair base size bits w k 0)
      (.loop (Impl.Weierstrass.X86_64.FastNaf.step bits w) .b) (fun _ _ => True) := by
  let I := fun m s t => 1≤m ∧ m≤257 ∧ FastPrepPair base size bits w k (257-m) s t
  have step : ∀ m,RelCT isa (I m) (Impl.Weierstrass.X86_64.FastNaf.step bits w) (fun s t =>
      eval .b s=eval .b t ∧ (eval .b s=some false → True) ∧
      (eval .b s=some true → ∃ n<m,I n s t)) := by
    intro m
    by_cases hm : 1≤m ∧ m≤257
    · have hv := FastNaf.residual_bound w (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hv' : FastNaf.residual w k (257-m)≤2^256 := Nat.le_trans hv
        (Nat.pow_le_pow_right (by decide) (by omega))
      refine (fastPrepStep_relCT hw hc hb (j:=257-m) (by omega) hv').mono
        (P':=I m) (fun _ _ h => h.2.2) ?_
      intro s t ⟨hp,fs,ft⟩
      refine ⟨fs.trans ft.symm,fun _ => trivial,fun he => ?_⟩
      have hn : 257-m+fastDelta w k (257-m)<257 := by
        change s.cf=some true at he
        rw [fs] at he
        exact of_decide_eq_true (Option.some.inj he)
      have hd := fastDelta_bounds hw k (257-m)
      refine ⟨m-fastDelta w k (257-m),by omega,by omega,by omega,?_⟩
      rw [show 257-(m-fastDelta w k (257-m))=257-m+fastDelta w k (257-m) from by omega]
      exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)
  exact (RelCT.loop I step 257).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem fastPrep_relCT {src bits w : Nat} {base : Addr} {size : Nat}
    (hw : FastNaf.Width w) (hsrc : src+32≤size) (hb : bits+264≤size) (hc : FastPrepChecks src bits w) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base src 4=wordsVal t.mem base src 4)
      (Impl.Weierstrass.X86_64.FastNaf.prep src bits w) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧
      wordsVal a.mem base src 4=wordsVal s.mem base src 4 ∧ wordsVal b.mem base src 4=wordsVal s.mem base src 4)
      (.block (Naf.init src++setConst 33 bits 0)) (FastPrepPair base size bits w (wordsVal s.mem base src 4) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_,_,xa,ia,_,_⟩ := fastPrepInit_ok (w:=w) hab.1 hsrc hb
    obtain ⟨_,_,xb,ib,_,_⟩ := fastPrepInit_ok (w:=w) hab.2.1 hsrc hb
    obtain ⟨_,rfl⟩ := Exec.det ea xa
    obtain ⟨_,rfl⟩ := Exec.det eb xb
    rw [hab.2.2.1] at ia
    rw [hab.2.2.2] at ib
    have pub : X86_64.Taint.Agree (Taint.ofRegs [.rdi]) a b := by
      apply Taint.agree_ofRegs
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hab.1.rdi.trans hab.2.1.rdi.symm
    exact ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb,ia,ib⟩
  exact (RelCT.seq hi (fastPrepLoop_relCT hw hc hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,rfl,hp.2.2.symm⟩ es et

end VG.Proof.Weierstrass.X86_64
