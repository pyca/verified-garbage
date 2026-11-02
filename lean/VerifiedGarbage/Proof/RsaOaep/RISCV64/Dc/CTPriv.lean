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

theorem psa_pub {a s : State} (p : PubD a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Sd, p.g .a7 (by decide), p.args _ (by decide : (0 : Nat) < 15),
      p.args _ (by decide : (1 : Nat) < 15), p.args _ (by decide : (2 : Nat) < 15),
      p.args _ (by decide : (3 : Nat) < 15), p.args _ (by decide : (4 : Nat) < 15),
      p.args _ (by decide : (5 : Nat) < 15), p.args _ (by decide : (6 : Nat) < 15),
      p.args _ (by decide : (7 : Nat) < 15), p.args _ (by decide : (8 : Nat) < 15),
      p.args _ (by decide : (13 : Nat) < 15), p.args _ (by decide : (14 : Nat) < 15)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (a u : State) : Prop := ∃ s, PreD s ∧ PubD a s ∧ AtPriv s u

theorem priv_pub {a u₁ u₂ : State} (h₁ : APriv a u₁) (h₂ : APriv a u₂) :
    ∃ s₁ s₂, PreD s₁ ∧ AtPriv s₁ u₁ ∧ PreD s₂ ∧ AtPriv s₂ u₂ ∧
      Rsa.RISCV64.Priv.fnContract.pub (callE s₁ u₁) (callE s₂ u₂) := by
  obtain ⟨s₁, P₁, p₁, A₁⟩ := h₁
  obtain ⟨s₂, P₂, p₂, A₂⟩ := h₂
  refine ⟨s₁, s₂, P₁, A₁, P₂, A₂, ?_⟩
  have m : ∀ {s u : State}, (callE s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} (A : AtPriv s u) {p : Addr} {len : Nat}
    (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hl
  refine Rsa.RISCV64.Priv.pub_of (by rw [show (callE s₁ u₁).sp = pb s₁ from A₁.sp,
      show (callE s₂ u₂).sp = pb s₂ from A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp])
    (fun r hr => ?_) (fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pub p₁ hi, psa_pub p₂ hi])
    ?_ ?_
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
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
  · rw [m, m, callE_gpr _ _ (r := .a2), callE_gpr _ _ (r := .a3), callE_gpr _ _ (r := .a2),
      callE_gpr _ _ (r := .a3), A₁.a2, A₁.a3, A₂.a2, A₂.a3, hb A₁ P₁.kn (by have := P₁.wn; omega),
      hb A₂ P₂.kn (by have := P₂.wn; omega), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .a4), callE_gpr _ _ (r := .a5), callE_gpr _ _ (r := .a4),
      callE_gpr _ _ (r := .a5), A₁.a4, A₁.a5, A₂.a4, A₂.a5, hb A₁ P₁.ke (by have := P₁.we; omega),
      hb A₂ P₂.ke (by have := P₂.we; omega), p₁.e, p₂.e]

theorem call_ct : RelCT isa (Two APriv) privCall fun _ _ => True := by
  unfold privCall
  refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
    Rsa.RISCV64.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨s₁, s₂, P₁, A₁, P₂, A₂, hp⟩ := priv_pub h₁ h₂
  exact ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, Rsa.RISCV64.Priv.pre_of_preP (preP_at P₁ A₁),
    Rsa.RISCV64.Priv.pre_of_preP (preP_at P₂ A₂), hp, (call_covers P₁ A₁).1, (call_covers P₁ A₁).2,
    (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩

/-- After the entry, from an entry state with `a`'s public data. -/
def AEnt (a t : State) : Prop := ∃ s, PreD s ∧ PubD a s ∧ Entered s t

theorem aEnt_sp {a t : State} (h : AEnt a t) : t.sp = fb a :=
  let ⟨_, _, p, E⟩ := h; by rw [E.sv.sp, fb, fb, p.sp]

/-- The private operation, from the entry to `DX`. -/
theorem priv_ct : RelCT isa (Two AEnt) priv fun _ _ => True := by
  unfold priv
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, PreD s ∧ PubD a s ∧ w.sp = fb s ∧
      WP isa (.block [.shift .sll .d .s4 .a0 32, .shift .srl .d .s4 .s4 32]) w (AfterPriv s))
    (two_alloc (R := fun _ _ => True) ?_) fun a t ⟨s, P, p, E⟩ => WP.mono (privF_ok P E) fun w h => ⟨s, P, p, h⟩)
    (zext_taint fun a w₁ w₂ ⟨s₁, _, p₁, e₁, _⟩ ⟨s₂, _, p₂, e₂, _⟩ =>
      ⟨by rw [e₁, e₂, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_seq (Ψ := APriv) (privArgs_taint fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show t₁.sp - _ = t₂.sp - _; rw [aEnt_sp h₁, aEnt_sp h₂], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, E⟩, e⟩ => by subst e; exact WP.mono (privArgs_ok P E) fun u' A => ⟨s, P, p, A⟩)
    call_ct

/-- After the private operation's result. -/
theorem priv_dx {a t : State} (h : AEnt a t) : WP isa priv t fun v => ∃ s, PreD s ∧ PubD a s ∧ AfterPriv s v :=
  let ⟨s, P, p, E⟩ := h
  WP.mono (priv_ok P E) fun _ A => ⟨s, P, p, A⟩

end VG.Proof.RsaOaep.RISCV64.Dec
