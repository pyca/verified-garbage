import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! Recoding branches depend only on the public scalar, never on stale scratch. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont

def nafPrepPublic : List Reg := [.rdi,.rbx,.r8,.r9,.r10,.r11,.r12]

structure NafPrepChecks (bits src : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi])) (.block (Naf.init src))
  step : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs nafPrepPublic)) (Naf.step bits)

structure NafPrepPair (base : Addr) (size bits k j : Nat) (s t : State) : Prop where
  left : NafPrepState base size bits k j s
  right : NafPrepState base size bits k j t

theorem NafPrepPair.public {base : Addr} {size bits k j : Nat} {s t : State}
    (h : NafPrepPair base size bits k j s t) : X86_64.Taint.Agree (Taint.ofRegs nafPrepPublic) s t := by
  have hv := nafVal5_inj (h.left.value.trans h.right.value.symm)
  apply Taint.agree_ofRegs
  intro r hr
  simp only [nafPrepPublic,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.left.scr.rdi.trans h.right.scr.rdi.symm
  · exact h.left.count.trans h.right.count.symm
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2.1
  · exact hv.2.2.2.2

theorem nafPrepStep_relCT {bits src : Nat} (hc : NafPrepChecks bits src)
    {base : Addr} {size k j : Nat} (hb : bits+257≤size) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    RelCT isa (NafPrepPair base size bits k j) (Naf.step bits) (fun s t =>
      NafPrepPair base size bits k (j+1) s t ∧
      s.cf=some (decide (j+1<257)) ∧ t.cf=some (decide (j+1<257))) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,fs,_,_⟩ := nafPrepStep_ok hp.left hb hj hv
  obtain ⟨_,_,xt,it,ft,_,_⟩ := nafPrepStep_ok hp.right hb hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial hp.public es et,⟨is,it⟩,fs,ft⟩

theorem nafPrepLoop_relCT {bits src : Nat} (hc : NafPrepChecks bits src)
    {base : Addr} {size k : Nat} (hb : bits+257≤size) (hk : k<2^256) :
    RelCT isa (NafPrepPair base size bits k 0) (.loop (Naf.step bits) .b) (fun _ _ => True) := by
  let I := fun m s t => 1≤m ∧ m≤257 ∧ NafPrepPair base size bits k (257-m) s t
  have step : ∀ m,RelCT isa (I m) (Naf.step bits) (fun s t =>
      eval .b s=eval .b t ∧ (eval .b s=some false → True) ∧
      (eval .b s=some true → ∃ n<m,I n s t)) := by
    intro m
    by_cases hm : 1≤m ∧ m≤257
    · have hv := Naf5.residual_bound (Nat.le_of_lt hk) (j:=257-m) (by omega)
      have hv' : Naf5.residual k (257-m)≤2^256 := Nat.le_trans hv
        (Nat.pow_le_pow_right (by decide) (by omega))
      refine (nafPrepStep_relCT hc hb (j:=257-m) (by omega) hv').mono
        (P':=I m) (fun _ _ h => h.2.2) ?_
      intro s t ⟨hp,fs,ft⟩
      refine ⟨fs.trans ft.symm,fun _ => trivial,fun he => ?_⟩
      have hn : 257-m+1<257 := by
        change s.cf=some true at he
        rw [fs] at he
        exact of_decide_eq_true (Option.some.inj he)
      refine ⟨m-1,by omega,by omega,by omega,?_⟩
      rw [show 257-(m-1)=257-m+1 from by omega]
      exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)
  exact (RelCT.loop I step 257).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem nafPrep_relCT {bits : Nat} {base : Addr} {size src : Nat}
    (hsrc : src+32≤size) (hb : bits+257≤size) (hc : NafPrepChecks bits src) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base src 4=wordsVal t.mem base src 4)
      (Naf.prep bits src) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧
      wordsVal a.mem base src 4=wordsVal s.mem base src 4 ∧ wordsVal b.mem base src 4=wordsVal s.mem base src 4)
      (.block (Naf.init src)) (NafPrepPair base size bits (wordsVal s.mem base src 4) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_,_,xa,ia,_,_⟩ := nafPrepInit_ok (bits:=bits) hab.1 hsrc
    obtain ⟨_,_,xb,ib,_,_⟩ := nafPrepInit_ok (bits:=bits) hab.2.1 hsrc
    obtain ⟨_,rfl⟩ := Exec.det ea xa
    obtain ⟨_,rfl⟩ := Exec.det eb xb
    rw [hab.2.2.1] at ia
    rw [hab.2.2.2] at ib
    have pub : X86_64.Taint.Agree (Taint.ofRegs [.rdi]) a b := by
      apply Taint.agree_ofRegs
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hab.1.rdi.trans hab.2.1.rdi.symm
    exact ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb,ia,ib⟩
  exact (RelCT.seq hi (nafPrepLoop_relCT hc hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,rfl,hp.2.2.symm⟩ es et

end VG.Proof.Weierstrass.X86_64
