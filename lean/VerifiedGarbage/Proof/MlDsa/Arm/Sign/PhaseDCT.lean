module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Rel
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsD
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.CopyTr

/-!
# ML-DSA signing on ARMv7: decoding leaks only the pointers

Each call while decoding leaks only its pointers, given that its input
polynomial is reduced (`dec_tr`); so two runs agree on what decoding leaks
(`decode_tr`); and copying prepared polynomials leaks only the pointers too
(`decodeC_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A piece that leaks only its pointers, from runs in the layout. -/
theorem liftT {p : Params} {D : Nat} {E I J : State → State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → St p D σ s) (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (LRel D (sgR p) (sgW p)) c fun _ _ => True) : RelCT isa (RS p D E I) c (RS p D E J) :=
  liftL (T := fun _ => True) (fun σ s h => ⟨hI σ s h, trivial⟩) hw (RelCT.mono ht (fun _ _ h => h.1) fun _ _ h => h)

theorem dec_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y)) (hc : decChk p a b c src len j = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) fun _ _ => True := by
  simp only [decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hc
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun s => Reduced s.mem (pa s (pS j)))
    (RelCT.mono (bupAt_tr hP hp hl h1) (fun _ _ h => h.1) fun _ _ h => h)
    (fun s L _ => WP.mono (bupAt_ok hP L hp hl h1) fun s' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩)
    (ipAt_tr (t := ntt) hP.ntt h2)) (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem decode_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : dChk p = true) {E : State → State → Prop} :
    RelCT isa (RS p D E (IM p D)) (decode P p) (RS p D E (IK p D)) := by
  have hs := dChk_spec hc
  unfold decode
  refine RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ 0 0 s) ?_ (RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ p.k 0 s)
    ?_ (RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ p.k p.k s) ?_ ?_))
  · refine RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ID p D σ r 0 0 s) p.ℓ 0 fun r _ hr =>
      liftT (fun _ _ h => h.im.st) (fun _ _ _ h => decS1_ok hP hc (by omega) h)
        (dec_tr hP hs.2.2.2.2.2.2.1 (sLen_eq p) (hs.1 r (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ID p D σ p.ℓ i 0 s) p.k 0 fun i _ hi =>
      liftT (fun _ _ h => h.im.st) (fun _ _ _ h => decS2_ok hP hc (by omega) h)
        (dec_tr hP hs.2.2.2.2.2.2.1 (sLen_eq p) (hs.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ID p D σ p.ℓ p.k i s) p.k 0 fun i _ hi =>
      liftT (fun _ _ h => h.im.st) (fun _ _ _ h => decT0_ok hP hc (by omega) h)
        (dec_tr hP (by decide) (by decide) (hs.2.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, h.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.im.st) (fun _ _ _ h => rpp_ok hP hc h)
      (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs.2.2.2.1) (fun _ _ h => h) fun _ _ _ => trivial)

/-- Two runs keep the same pointers in `bases`. -/
theorem rs_reg {p : Params} {D : Nat} {E I : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {x y : State}
    (h : RS p D E I x y) {r : Reg} (hr : r ∈ bases) : x.gpr r = y.gpr r := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, -, -, h9⟩ := hpub
  rw [(hI _ _ i₁).top.regs r hr, (hI _ _ i₂).top.regs r hr]
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ptrOf] <;> with_reducible assumption

theorem decodeC_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hd : dChk p = true)
    (hc : dcChk p = true) {E : State → State → Prop} :
    RelCT isa (RS p D E (IM p D)) (decodeC P p) (RS p D E (IK p D)) := by
  have hs := dChk_spec hd
  have him0 : imChk p [] = true := by
    simp only [dcChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h0⟩, -⟩, -⟩, -⟩, -⟩ := hc
    exact h0
  unfold decodeC
  refine RelCT.seq (R := RS p D E fun σ s => IM p D σ s ∧ s.z = (stackArg σ 1 == 0)) ?_ (RelCT.ite ?_ ?_ ?_)
  · refine liftR (fun σ s _ h => WP.mono (cmp9_ok s D) fun s₁ ⟨hP₁, _, _, hz⟩ => ⟨h.step hP₁ him0, ?_⟩)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
    have e := h.st.top.regs .r9 (by decide)
    simp only [ptrOf] at e
    rw [hz, e]
  · rintro x y ⟨σ₁, σ₂, -, -, hpub, -, ⟨-, hx⟩, ⟨-, hy⟩⟩
    show some (!x.z) = some (!y.z)
    rw [hx, hy, hpub.2.2.2.2.2.2.2]
  · unfold cached
    refine RelCT.mono (P := RS p D E fun σ s => IM p D σ s ∧ stackArg σ 1 ≠ 0)
      (RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ p.k p.k s) ?_ ?_) ?_ fun _ _ h => h
    · exact liftR (fun σ s hpre ⟨h, hne⟩ => cachedCopy_ok hc hpre hne h)
        (copy_tr (by decide) (pS_bases _) fun x y h =>
          ⟨rs_reg (fun _ _ h => h.1.st) h (pS_bases _), rs_reg (fun _ _ h => h.1.st) h (by decide)⟩)
    · exact liftT (fun _ _ h => h.im.st) (fun _ _ _ h => rpp_ok hP hd h)
        (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs.2.2.2.1) (fun _ _ h => h) fun _ _ _ => trivial)
    · rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, hx⟩, ⟨i₂, hy⟩⟩, hcx⟩
      have hcx' : some (!x.z) = some true := hcx
      rw [hx] at hcx'
      have hne : stackArg σ₁ 1 ≠ 0 := by simpa using hcx'
      exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, hne⟩, ⟨i₂, hpub.2.2.2.2.2.2.2 ▸ hne⟩⟩
  · exact RelCT.mono (decode_tr hP hd) (fun x y ⟨h, _⟩ => h.mono (fun _ _ h => h) fun _ _ h => h.1)
      fun _ _ h => h

end VG.Proof.MlDsa.Arm.Sign
