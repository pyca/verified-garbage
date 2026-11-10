module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBase
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.PrivCall
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTBlocks
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two

/-!
# RSASSA-PSS signing on PPC64LE: the private operation, twice

Untrusted: everything here is checked by Lean. `priv_ct`: two runs of the
private operation from states with `Base` for entry states with the same
public data leak alike: its frame's arguments by the taint analysis, and the
call of `vg_rsa_private_checked` by its constant time (`RelCT.callEx`),
whose public data at the call (`priv_pub`) are the entry's: the pointers and
lengths, the modulus and the public exponent.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE (B B.sp pins_of two_seq allocated_sp fb)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two two_alloc)

theorem psa_pub {a s : State} (p : PubS pc a s) {i : Nat} (hi : i < nP pc) : psa s i = psa a i := by
  by_cases h12 : i < 12
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [psa, Ss, p.g .r9 (by decide), p.g .r10 (by decide), p.args _ (by decide : (0 : Nat) < 16),
        p.args _ (by decide : (1 : Nat) < 16), p.args _ (by decide : (2 : Nat) < 16),
        p.args _ (by decide : (3 : Nat) < 16), p.args _ (by decide : (4 : Nat) < 16),
        p.args _ (by decide : (5 : Nat) < 16), p.args _ (by decide : (6 : Nat) < 16),
        p.args _ (by decide : (7 : Nat) < 16), p.args _ (by decide : (12 : Nat) < 16),
        p.args _ (by decide : (13 : Nat) < 16)]
  · cases pc with
    | false => exact absurd hi (by simp only [nP, Bool.false_eq_true, ↓reduceIte]; omega)
    | true =>
      rcases (by simp only [nP, ↓reduceIte] at hi; omega : i = 12 ∨ i = 13) with rfl | rfl
      · exact (p.pre rfl).1
      · exact (p.pre rfl).2.1

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (D : Nat) (a u : State) : Prop :=
  ∃ s em, PreS pc D s ∧ (pc = true → PreXS s) ∧ PubK pc a s ∧ AtPriv pc s em u

/-- What two runs share at the call. -/
theorem priv_pub {D : Nat} {a u₁ u₂ : State} (h₁ : APriv pc D a u₁) (h₂ : APriv pc D a u₂) :
    ∃ s₁ s₂ em₁ em₂, PreS pc D s₁ ∧ (pc = true → PreXS s₁) ∧ AtPriv pc s₁ em₁ u₁ ∧ PreS pc D s₂ ∧
      (pc = true → PreXS s₂) ∧ AtPriv pc s₂ em₂ u₂ ∧
      (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < nP pc, stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r5) ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r5) ((callE pc s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r7) ((callE pc s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r7) ((callE pc s₂ u₂).gpr .r8).toNat ∧
      (pc = true → Spec.Rsa.privatePrecomputedLeak (callE pc s₁ u₁).mem (stackArg (callE pc s₁ u₁) 12)
          ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.privatePrecomputedLeak (callE pc s₂ u₂).mem (stackArg (callE pc s₂ u₂) 12)
          ((callE pc s₂ u₂).gpr .r6).toNat) := by
  obtain ⟨s₁, em₁, P₁, X₁, ⟨p₁, _⟩, A₁⟩ := h₁
  obtain ⟨s₂, em₂, P₂, X₂, ⟨p₂, _⟩, A₂⟩ := h₂
  refine ⟨s₁, s₂, em₁, em₂, P₁, X₁, A₁, P₂, X₂, A₂, ?_, fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pub p₁ hi, psa_pub p₂ hi], ?_, ?_, ?_⟩
  · rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp]
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, Ss, Ss, p₁.args 12 (by decide), p₂.args 12 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
    have hb := fun {s u : State} {em : List Byte} (P : PreS pc D s) (A : AtPriv pc s em u) {p : Addr} {len : Nat}
      (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaOaep.PPC64LE.SC Ss s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hs hl
    rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6,
      hb P₁ A₁ P₁.kn ((P₁.ns.symm).sub_left (sc_sub P₁)) (by have := P₁.wn; omega),
      hb P₂ A₂ P₂.kn ((P₂.ns.symm).sub_left (sc_sub P₂)) (by have := P₂.wn; omega), p₁.n, p₂.n]
  · have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
    have hb := fun {s u : State} {em : List Byte} (P : PreS pc D s) (A : AtPriv pc s em u) {p : Addr} {len : Nat}
      (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaOaep.PPC64LE.SC Ss s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hs hl
    rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8,
      hb P₁ A₁ P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      hb P₂ A₂ P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]
  · intro hpc
    subst hpc
    have hw : ∀ {s u : State} {em : List Byte} (P : PreS true D s) (X : PreXS s) (A : AtPriv true s em u),
        Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
            ((callE true s u).gpr .r6).toNat =
          (Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).map (·.toNat) := by
      intro s u em P X A
      have pwl : Spec.Rsa.precomputedWords (s.gpr .r6).toNat ≤ (stackArg s 17).toNat := by
        rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega
      simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
        callE_gpr s u (r := .r6), A.r6]
      congr 1
      have subPre : Region.Sub ⟨stackArg s 16, 8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat⟩ (preR s) :=
        fun _ hx => by simp only [Region.Contains] at hx ⊢; omega
      exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact X.kP.symm.sub_left subPre
        · exact (X.sP.symm.sub_right (sc_sub P)).sub_left subPre)
        (by have := X.wP; omega)
    rw [hw P₁ (X₁ rfl) A₁, hw P₂ (X₂ rfl) A₂, (p₁.pre rfl).2.2, (p₂.pre rfl).2.2]

theorem call_ct {D : Nat} : RelCT isa (Two (APriv pc D)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, s₂, em₁, em₂, P₁, _, A₁, P₂, _, A₂, hsp, hr, ha, hn, he, _⟩ := priv_pub h₁ h₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, s₂, em₁, em₂, P₁, X₁, A₁, P₂, X₂, A₂, hsp, hr, ha, hn, he, hp⟩ := priv_pub h₁ h₂
    exact ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ (X₁ rfl) A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ (X₂ rfl) A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr ha hn he (hp rfl),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩

/-- The private operation, in both runs, from states with `Base` for entry
states with `PreS` and `PubK`. -/
theorem priv_ct {D : Nat} {Pre : State → Prop} {Pub : State → State → Prop} (hP : ∀ {s}, Pre s → PreS pc D s)
    (hX : ∀ {s}, Pre s → pc = true → PreXS s)
    (hQ : ∀ {a s}, Pub a s → PubK pc a s) : RelCT isa (Two (B Ss vS Pre Pub)) (priv pc) fun _ _ => True := by
  have X := signOk D hP hQ
  unfold priv
  refine two_alloc (R := fun _ _ => True) (pins_of X (an := id) (fun _ _ h => h) []) ?_
  refine two_seq (Ψ := APriv pc D) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.sp X, h₂.sp X], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, b⟩, e⟩ => by
      subst e; exact WP.mono (privArgs_ok (hP P) b rfl) fun u' A => ⟨s, _, hP P, hX P, hQ p, A⟩)
    call_ct

end VG.Proof.RsaPss.PPC64LE.Sg
