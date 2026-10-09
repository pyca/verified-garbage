import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt seqR)
open VG.Proof.MlDsa.AArch64.Optimized

/-- Static artifact addresses are public; secret polynomial contents are not. -/
def RootSymbolsEq (x y : State) : Prop :=
  x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED" ∧
  x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED"

def RootRS (p : Params) (S : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  RS p S E I x y ∧ RootSymbolsEq x y

theorem positiveDecode_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x,y)∈bitPackParams) (hl : len=32*bitlen (x+y))
    (hc : decChk p a b c src len j=true) :
    RelCT isa (fun s t => LRel S (sgR p) (sgW p) s t ∧ StaticRoots S s ∧ StaticRoots S t ∧ RootSymbolsEq s t)
      (positiveDecode P src len x y j) fun _ _ => True := by
  simp only [decChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hu,hn⟩,_⟩,_⟩ := hc
  simp only [ipChkS,ipChk,Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨_,hin⟩,_⟩,hw⟩,_⟩ := hn
  have hws : ∀ w∈[(pS j,1024)],inB (sgW p) w.1 w.2=true := by simpa using hw
  let I := fun tab (s : State) => StaticRoots S s ∧ s.syms "VG_MLDSA_NTT_EXPANDED"=tab
  let J := fun tab (s : State) => I tab s ∧ Reduced s.mem (pa s (pS j))
  have ht (tab : Addr) : RelCT isa
      (fun s t => LRel S (sgR p) (sgW p) s t ∧ I tab s ∧ I tab t)
      (positiveDecode P src len x y j) fun _ _ => True := by
    apply seqL (I := I tab) (J := J tab)
    · exact RelCT.mono (bupAt_tr hP hp hl hu) (fun _ _ h => h.1) (fun _ _ h => h)
    · intro s L h
      exact WP.mono_syms (bupAt_ok hP L hp hl hu) fun t ht hy =>
        ⟨⟨_,ht.1⟩,⟨h.1.step_layout L ht.1 hy hws,by rw [hy]; exact h.2⟩,
          by rw [ht.1.pa (pS_bases j)]; exact ht.2.2.1⟩
    · apply positiveNttAt_tr (S := S) (ptr_ok (pS_bases j))
      intro s t h
      have ready (z : State) (L : Lay S (sgR p) (sgW p) z) (hz : J tab z) : NttCallReady (pS j) z :=
        ⟨L.nwp hin,hz.1.1.nttTableAt (L.inW hw),hz.2,
          Covers.cons hz.1.1.forward.readable (L.cR hin),L.cW hw⟩
      exact ⟨ready s h.1.lx h.2.1,ready t h.1.ly h.2.2,h.1.pa (by change Reg.x28∈bases; decide),h.1.sp,
        h.2.1.1.2.trans h.2.2.1.2.symm⟩
  exact RelCT.mono (RelCT.exists_ ht)
    (fun s t h => ⟨s.syms "VG_MLDSA_NTT_EXPANDED",h.1,⟨h.2.1,rfl⟩,⟨h.2.2.1,h.2.2.2.1.symm⟩⟩)
    (fun _ _ h => h)

/-- Functional phase proofs supply the next semantic invariant; the symbol
map is preserved by execution itself, independently of the register frame. -/
theorem liftRootT {p : Params} {S : Nat} {E I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s,I σ s → St p S σ s ∧ StaticRoots S s)
    (hw : ∀ σ s,(signK p S).pre σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (fun x y => LRel S (sgR p) (sgW p) x y ∧ StaticRoots S x ∧ StaticRoots S y ∧ RootSymbolsEq x y)
      code fun _ _ => True) : RelCT isa (RootRS p S E I) code (RootRS p S E J) := by
  intro x y tx ty x' y' h ex ey
  obtain ⟨σ,τ,hσ,hτ,hpub,he,hx,hy⟩ := h.1
  have htrace := (ht _ _ _ _ _ _ ⟨lrel_of hpub (hi _ _ hx).1 (hi _ _ hy).1,
    (hi _ _ hx).2,(hi _ _ hy).2,h.2⟩ ex ey).1
  obtain ⟨_,u,eu,hu⟩ := hw σ x hσ hx
  obtain ⟨_,v,ev,hv⟩ := hw τ y hτ hy
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨htrace,⟨σ,τ,hσ,hτ,hpub,he,hu,hv⟩,by simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using h.2⟩

/-- Decoding all three secret vectors leaks only the established public
layout and artifact addresses. The transformed coefficients remain secret. -/
theorem positiveDecodeSecrets_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hc : dChk p=true) {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveID p S · 0 0 0))
      (.seq
        (seqR (fun r => positiveDecode P (.x25,skS1 p r) (sLen p) p.η p.η (s1Base p+r)) 0 p.ℓ)
        (.seq (seqR (fun i => positiveDecode P (.x25,skS2 p i) (sLen p) p.η p.η (s2Base p+i)) 0 p.k)
          (seqR (fun i => positiveDecode P (.x25,skT0 p i) 416 4095 4096 (t0Base p+i)) 0 p.k)))
      (RootRS p S E (PositiveID p S · p.ℓ p.k p.k)) := by
  have hs := dChk_spec hc
  refine RelCT.seq (R := RootRS p S E (PositiveID p S · p.ℓ 0 0)) ?_
    (RelCT.seq (R := RootRS p S E (PositiveID p S · p.ℓ p.k 0)) ?_ ?_)
  · simpa only [Nat.zero_add] using
      seqR_tr (Q := fun r => RootRS p S E (PositiveID p S · r 0 0)) p.ℓ 0
        (fun r _ hr => liftRootT (fun _ _ h => ⟨h.im.st,h.roots⟩)
          (fun _ _ _ h => positiveDecodeS1_ok hP hc (by omega) h)
          (positiveDecode_tr hP hs.2.2.2.2.2.2.1 (sLen_eq p) (hs.1 r (by omega)).1))
  · simpa only [Nat.zero_add] using
      seqR_tr (Q := fun i => RootRS p S E (PositiveID p S · p.ℓ i 0)) p.k 0
        (fun i _ hi => liftRootT (fun _ _ h => ⟨h.im.st,h.roots⟩)
          (fun _ _ _ h => positiveDecodeS2_ok hP hc (by omega) h)
          (positiveDecode_tr hP hs.2.2.2.2.2.2.1 (sLen_eq p) (hs.2.1 i (by omega)).1))
  · simpa only [Nat.zero_add] using
      seqR_tr (Q := fun i => RootRS p S E (PositiveID p S · p.ℓ p.k i)) p.k 0
        (fun i _ hi => liftRootT (fun _ _ h => ⟨h.im.st,h.roots⟩)
          (fun _ _ _ h => positiveDecodeT0_ok hP hc (by omega) h)
          (positiveDecode_tr hP (by decide) (by decide) (hs.2.2.1 i (by omega)).1))

end VG.Proof.MlDsa.AArch64.Sign
