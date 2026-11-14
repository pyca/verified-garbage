module

-- separate module: it builds in parallel with `CTLabel` and the proofs of correctness, which `Verified` also needs.

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBase
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTBlocks
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two

/-!
# RSAES-OAEP decryption on RISC-V: the private operation, twice

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/CTPriv.lean`): `priv_ct`, two runs of the
private operation from entry states with the same public data leak alike:
its frame's arguments by the taint analysis, and the call of
`vg_rsa_private_checked` by its constant time (`RelCT.callEx`), whose public
data at the call (`priv_pub`) are the entry's: the pointers and lengths, the
modulus and the public exponent. Its result then differs between the runs,
in `s4` (`DX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_alloc)
open VG.Proof.RsaOaep.RISCV64 (two_seq)

theorem psa_pub {pc : Bool} {a s : State} (p : PubD pc a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Sd, p.g .a7 (by decide), p.args _ (by decide : (0 : Nat) < 17),
      p.args _ (by decide : (1 : Nat) < 17), p.args _ (by decide : (2 : Nat) < 17),
      p.args _ (by decide : (3 : Nat) < 17), p.args _ (by decide : (4 : Nat) < 17),
      p.args _ (by decide : (5 : Nat) < 17), p.args _ (by decide : (6 : Nat) < 17),
      p.args _ (by decide : (7 : Nat) < 17), p.args _ (by decide : (8 : Nat) < 17),
      p.args _ (by decide : (13 : Nat) < 17), p.args _ (by decide : (14 : Nat) < 17)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (a u : State) : Prop := ∃ s, PreD pc s ∧ PubD pc a s ∧ AtPriv pc s u

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s t : State} (P : PreD true s) (A : AtPriv true s t) :
    Spec.Rsa.privatePrecomputedLeak (callE true s t).mem (stackArg (callE true s t) 12)
        ((callE true s t).gpr .a3).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .a4).toNat := by
  have X := P.px rfl
  have pwl : Spec.Rsa.precomputedWords (s.gpr .a4).toNat ≤ (stackArg s 18).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
    callE_gpr true s t (r := .a3), A.a3]
  congr 1
  have subPre : Region.Sub ⟨stackArg s 17, 8 * Spec.Rsa.precomputedWords (s.gpr .a4).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

/-- What the two calls' public data share, from entry states with `a`'s. -/
theorem priv_facts {pc : Bool} {a s₁ s₂ u₁ u₂ : State}
    (P₁ : PreD pc s₁) (p₁ : PubD pc a s₁) (A₁ : AtPriv pc s₁ u₁)
    (P₂ : PreD pc s₂) (p₂ : PubD pc a s₂) (A₂ : AtPriv pc s₂ u₂) :
    (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < (if pc then 14 else 12), stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .a2) ((callE pc s₁ u₁).gpr .a3).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .a2) ((callE pc s₂ u₂).gpr .a3).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .a4) ((callE pc s₁ u₁).gpr .a5).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .a4) ((callE pc s₂ u₂).gpr .a5).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} (A : AtPriv pc s u) {p : Addr} {len : Nat}
    (hd : (kD pc s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hl
  refine ⟨by rw [show (callE pc s₁ u₁).sp = pb pc s₁ from A₁.sp,
      show (callE pc s₂ u₂).sp = pb pc s₂ from A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp],
    fun r hr => ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [callE_gpr _ _ _ (fun h => by revert r; decide), callE_gpr _ _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, Sd, Sd, p₁.args 13 (by decide), p₂.args 13 (by decide)]
    · rw [A₁.a1, A₂.a1, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a2, A₂.a2, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a3, A₂.a3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a4, A₂.a4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a5, A₂.a5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a6, A₂.a6, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.a7, A₂.a7, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi]
    by_cases h : i < 12
    · rw [psa_pub p₁ h, psa_pub p₂ h]
    · cases pc with
      | false => exact absurd hi (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [h])
      | true =>
        obtain ⟨x₁, y₁⟩ := p₁.args2 rfl
        obtain ⟨x₂, y₂⟩ := p₂.args2 rfl
        rcases (by simp only [↓reduceIte] at hi; omega_using [h, hi] : i = 12 ∨ i = 13) with rfl | rfl
        · simp only [psa]; rw [x₁, x₂]
        · simp only [psa]; rw [y₁, y₂]
  · rw [m, m, callE_gpr _ _ _ (r := .a2), callE_gpr _ _ _ (r := .a3), callE_gpr _ _ _ (r := .a2),
      callE_gpr _ _ _ (r := .a3), A₁.a2, A₁.a3, A₂.a2, A₂.a3, hb A₁ P₁.kn (by have := P₁.wn; omega_using []),
      hb A₂ P₂.kn (by have := P₂.wn; omega_using []), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ _ (r := .a4), callE_gpr _ _ _ (r := .a5), callE_gpr _ _ _ (r := .a4),
      callE_gpr _ _ _ (r := .a5), A₁.a4, A₁.a5, A₂.a4, A₂.a5, hb A₁ P₁.ke (by have := P₁.we; omega_using []),
      hb A₂ P₂.ke (by have := P₂.we; omega_using []), p₁.e, p₂.e]

theorem call_ct {pc : Bool} : RelCT isa (Two (APriv pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
      Rsa.RISCV64.Priv.code_ct fun u₁ u₂ ⟨a, ⟨s₁, P₁, p₁, A₁⟩, ⟨s₂, P₂, p₂, A₂⟩⟩ => ?_
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.RISCV64.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.RISCV64.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.RISCV64.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContractP) Rsa.RISCV64.Priv.codeP_correct
      Rsa.RISCV64.Priv.codeP_ct fun u₁ u₂ ⟨a, ⟨s₁, P₁, p₁, A₁⟩, ⟨s₂, P₂, p₂, A₂⟩⟩ => ?_
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    exact ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.RISCV64.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ (P₁.px rfl) A₁),
      Rsa.RISCV64.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ (P₂.px rfl) A₂),
      Rsa.RISCV64.Priv.pub_ofP hsp hr ha hn he
        (by rw [pre_leak P₁ A₁, pre_leak P₂ A₂, p₁.leak rfl, p₂.leak rfl]),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩

/-- After the entry, from an entry state with `a`'s public data. -/
def AEnt (pc : Bool) (a t : State) : Prop := ∃ s, PreD pc s ∧ PubD pc a s ∧ Entered s t

theorem aEnt_sp {pc : Bool} {a t : State} (h : AEnt pc a t) : t.sp = fb a :=
  let ⟨_, _, p, E⟩ := h; by rw [E.sv.sp, fb, fb, p.sp]

/-- The private operation, from the entry to `DX`. -/
theorem priv_ct {pc : Bool} : RelCT isa (Two (AEnt pc)) (priv pc) fun _ _ => True := by
  unfold priv
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, PreD pc s ∧ PubD pc a s ∧ w.sp = fb s ∧
      WP isa (.block [.shift .sll .d .s4 .a0 32, .shift .srl .d .s4 .s4 32]) w (AfterPriv pc s))
    (two_alloc (R := fun _ _ => True) ?_) fun a t ⟨s, P, p, E⟩ => WP.mono (privF_ok P E) fun w h => ⟨s, P, p, h⟩)
    (zext_taint fun a w₁ w₂ ⟨s₁, _, p₁, e₁, _⟩ ⟨s₂, _, p₂, e₂, _⟩ =>
      ⟨by rw [e₁, e₂, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_seq (Ψ := APriv pc) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show t₁.sp - _ = t₂.sp - _; rw [aEnt_sp h₁, aEnt_sp h₂], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, E⟩, e⟩ => by subst e; exact WP.mono (privArgs_ok P E) fun u' A => ⟨s, P, p, A⟩)
    call_ct

end VG.Proof.RsaOaep.RISCV64.Dec
