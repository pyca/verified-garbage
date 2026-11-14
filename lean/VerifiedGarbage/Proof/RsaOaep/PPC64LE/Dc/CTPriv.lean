module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBase
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivArgs
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation, twice

Untrusted: everything here is checked by Lean. `priv_ct`: two runs of the
private operation from entry states with the same public data leak alike:
its frame's arguments by the taint analysis, and the call of
`vg_rsa_private_checked` by its constant time (`RelCT.callEx`), whose public
data at the call (`priv_pub`) are the entry's: the pointers and lengths, the
modulus and the public exponent. Its result then differs between the runs,
in `r20` (`DX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_alloc)

theorem psa_pub {a s : State} (p : PubD a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Sd, p.g .r10 (by decide), p.args _ (by decide : (0 : Nat) < 17),
      p.args _ (by decide : (1 : Nat) < 17), p.args _ (by decide : (2 : Nat) < 17),
      p.args _ (by decide : (3 : Nat) < 17), p.args _ (by decide : (4 : Nat) < 17),
      p.args _ (by decide : (5 : Nat) < 17), p.args _ (by decide : (6 : Nat) < 17),
      p.args _ (by decide : (7 : Nat) < 17), p.args _ (by decide : (8 : Nat) < 17),
      p.args _ (by decide : (13 : Nat) < 17), p.args _ (by decide : (14 : Nat) < 17)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (a u : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ AtPriv pc s u ∧ XP pc a s

/-- The public data at the call, but `pre`'s leak. -/
theorem priv_facts {pc : Bool} {a s₁ s₂ u₁ u₂ : State} (P₁ : PreD pc s₁) (p₁ : PubD a s₁) (A₁ : AtPriv pc s₁ u₁)
    (P₂ : PreD pc s₂) (p₂ : PubD a s₂) (A₂ : AtPriv pc s₂ u₂) :
    (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < 12, stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r5) ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r5) ((callE pc s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r7) ((callE pc s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r7) ((callE pc s₂ u₂).gpr .r8).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} (A : AtPriv pc s u) {p : Addr} {len : Nat}
    (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hl
  refine ⟨by rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp], fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ (lt_nCall hi), callE_stackArg A₂ (lt_nCall hi), psa_pub p₁ hi,
      psa_pub p₂ hi], ?_, ?_⟩
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, Sd, Sd, p₁.args 13 (by decide), p₂.args 13 (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6, hb A₁ P₁.kn (by have := P₁.wn; omega_using []),
      hb A₂ P₂.kn (by have := P₂.wn; omega_using []), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8, hb A₁ P₁.ke (by have := P₁.we; omega_using []),
      hb A₂ P₂.ke (by have := P₂.we; omega_using []), p₁.e, p₂.e]

/-- With `pc`, the call's two more stack arguments, `pre` and `pre_len`, are
the anchor's. -/
theorem psa_pubP {a s : State} (x : PubP a s) {i : Nat} (hi : 12 ≤ i) (hi' : i < 14) : psa s i = psa a i := by
  rcases (by omega_using [hi, hi'] : i = 12 ∨ i = 13) with rfl | rfl
  · exact x.1
  · exact x.2.1

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s u : State} (X : PreXD s) (A : AtPriv true s u) :
    Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
        ((callE true s u).gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r7).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .r7).toNat ≤ (stackArg s 18).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
    callE_gpr (pc := true) s u (r := .r6), A.r6]
  congr 1
  have subPre : Region.Sub ⟨stackArg s 17, 8 * Spec.Rsa.precomputedWords (s.gpr .r7).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem call_ct (pc : Bool) : RelCT isa (Two (APriv pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, -⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, -⟩ := h₂
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, x₁⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, x₂⟩ := h₂
    obtain ⟨X₁, q₁⟩ := x₁ rfl
    obtain ⟨X₂, q₂⟩ := x₂ rfl
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    refine ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ X₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ X₂ A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr (fun i hi => ?_) hn he
        (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂, q₁.2.2, q₂.2.2]),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
    by_cases h12 : i < 12
    · exact ha i h12
    · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pubP q₁ (by omega_using [h12]) hi, psa_pubP q₂ (by omega_using [h12]) hi]

/-- After the entry, from an entry state with `a`'s public data. -/
def AEnt (pc : Bool) (a t : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ Entered s t ∧ XP pc a s

theorem aEnt_sp {pc : Bool} {a t : State} (h : AEnt pc a t) : t.sp = fb a :=
  let ⟨_, _, p, E, _⟩ := h; by rw [E.sv.sp, fb, fb, p.sp]

/-- The private operation, from the entry to `DX`. -/
theorem priv_ct (pc : Bool) : RelCT isa (Two (AEnt pc)) (priv pc) fun _ _ => True := by
  unfold priv
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, PreD pc s ∧ PubD a s ∧ w.sp = fb s ∧
      WP isa (.block [.lsr .w .r20 .r3 0]) w (AfterPriv s))
    (two_alloc (R := fun _ _ => True) (fun a t₁ t₂ h₁ h₂ => ⟨(aEnt_sp h₁).trans (aEnt_sp h₂).symm, fun _ h => nomatch h⟩) ?_)
    fun a t ⟨s, P, p, E, x⟩ => WP.mono (privF_ok P (fun h => (x h).1) E) fun w h => ⟨s, P, p, h⟩)
    (lsr_taint fun a w₁ w₂ ⟨s₁, _, p₁, e₁, _⟩ ⟨s₂, _, p₂, e₂, _⟩ =>
      ⟨by rw [e₁, e₂, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_seq (Ψ := APriv pc) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, aEnt_sp h₁, aEnt_sp h₂], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, E, x⟩, e⟩ => by
      subst e; exact WP.mono (privArgsG_ok P E) fun u' A => ⟨s, P, p, A, x⟩)
    (call_ct pc)

end VG.Proof.RsaOaep.PPC64LE.Dec
