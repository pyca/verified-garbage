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

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE (B.sp pins_of two_seq allocated_sp fb)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two two_alloc)

theorem psa_pub {a s : State} (p : PubS a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Ss, p.g .r9 (by decide), p.g .r10 (by decide), p.args _ (by decide : (0 : Nat) < 13),
      p.args _ (by decide : (1 : Nat) < 13), p.args _ (by decide : (2 : Nat) < 13),
      p.args _ (by decide : (3 : Nat) < 13), p.args _ (by decide : (4 : Nat) < 13),
      p.args _ (by decide : (5 : Nat) < 13), p.args _ (by decide : (6 : Nat) < 13),
      p.args _ (by decide : (7 : Nat) < 13), p.args _ (by decide : (11 : Nat) < 13),
      p.args _ (by decide : (12 : Nat) < 13)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (D : Nat) (a u : State) : Prop := ∃ s em, PreS D s ∧ PubK a s ∧ AtPriv s em u

theorem priv_pub {D : Nat} {a u₁ u₂ : State} (h₁ : APriv D a u₁) (h₂ : APriv D a u₂) :
    ∃ s₁ s₂ em₁ em₂, PreS D s₁ ∧ AtPriv s₁ em₁ u₁ ∧ PreS D s₂ ∧ AtPriv s₂ em₂ u₂ ∧
      Rsa.PPC64LE.Priv.fnContract.pub (callE s₁ u₁) (callE s₂ u₂) := by
  obtain ⟨s₁, em₁, P₁, ⟨p₁, _⟩, A₁⟩ := h₁
  obtain ⟨s₂, em₂, P₂, ⟨p₂, _⟩, A₂⟩ := h₂
  refine ⟨s₁, s₂, em₁, em₂, P₁, A₁, P₂, A₂, ?_⟩
  have m : ∀ {s u : State}, (callE s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} {em : List Byte} (P : PreS D s) (A : AtPriv s em u) {p : Addr} {len : Nat}
    (hd : (kS s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaOaep.PPC64LE.SC Ss s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hs hl
  refine Rsa.PPC64LE.Priv.pub_of (by rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp])
    (fun r hr => ?_) (fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pub p₁ hi, psa_pub p₂ hi])
    ?_ ?_
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, Ss, Ss, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6,
      hb P₁ A₁ P₁.kn ((P₁.ns.symm).sub_left (sc_sub P₁)) (by have := P₁.wn; omega),
      hb P₂ A₂ P₂.kn ((P₂.ns.symm).sub_left (sc_sub P₂)) (by have := P₂.wn; omega), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8,
      hb P₁ A₁ P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      hb P₂ A₂ P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]

theorem call_ct {D : Nat} : RelCT isa (Two (APriv D)) privCall fun _ _ => True := by
  unfold privCall
  refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
    Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨s₁, s₂, em₁, em₂, P₁, A₁, P₂, A₂, hp⟩ := priv_pub h₁ h₂
  exact ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
    Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), hp, (call_covers P₁ A₁).1, (call_covers P₁ A₁).2,
    (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩

/-- The private operation, in both runs. -/
theorem priv_ct {D : Nat} : RelCT isa (Two (BS D)) priv fun _ _ => True := by
  unfold priv
  refine two_alloc (R := fun _ _ => True) (pins_of (signOk D) (an := id) (fun _ _ h => h) []) ?_
  refine two_seq (Ψ := APriv D) (privArgs_taint fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.sp (signOk D), h₂.sp (signOk D)], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, b⟩, e⟩ => by
      subst e; exact WP.mono (privArgs_ok P b rfl) fun u' A => ⟨s, _, P, p, A⟩)
    call_ct

end VG.Proof.RsaPss.PPC64LE.Sg
