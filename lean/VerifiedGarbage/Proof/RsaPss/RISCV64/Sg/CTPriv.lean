module

-- separate module: it builds in parallel with the encoding's proofs (`Em`, `Enc`) and `CTBlocks`, which
-- `CTMain` also needs.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Priv
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.CTBlocks
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS signing on RISC-V: the public data, and the private operation twice

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/CTBase.lean`, `Sg/CTPriv.lean`): the shared
contract's public data (`PubS`, `pubS_of`): the stack pointer, the pointers
and lengths (all the arguments), the modulus and `e`. An entry state with
the anchor's public data has its modulus' first byte (`PubS.byte`), so its
`lo`, and agrees with it on what `Base` fixes (`signOk`). `priv_ct`: two
runs of the private operation from states with `Base` and the saved
arguments (`BP`) leak alike: its frame's arguments by the taint analysis, and
the call of `vg_rsa_private_checked` by its constant time (`RelCT.callEx`),
whose public data at the call (`priv_pub`) are the entry's: the pointers and
lengths, the modulus and the public exponent.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign
open VG.Impl.RsaOaep.RISCV64 (frameBytes)
open VG.Proof.RsaOaep.RISCV64 (Base Agree Ok B fx fb two_seq)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two two_alloc)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The shared contract's public data, by name. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s.gpr r = a.gpr r
  args : ∀ i < 13, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a4) (a.gpr .a5).toNat

theorem pubS_of {G : Spec.Mgf1.Hash} {s₁ s₂ : State}
    (h : (Spec.RsaPss.signContract G G abi stackBytes).pub s₁ s₂) : PubS s₁ s₂ := by
  have e : stackBytes = 3471 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  rw [List.map_append, List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, g3])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm]

theorem pubS_refl (s : State) : PubS s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

section
variable {a s : State} (p : PubS a s)
include p

theorem PubS.pKk : kk s = kk a := by rw [kk, kk, p.g .a3 (by decide)]

theorem PubS.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .a2) = a.mem (a.gpr .a2) := by
  have e1 : kk s = kk a := p.pKk
  have := congrArg (·.getD 0 0) p.n
  rwa [VG.Proof.RsaPkcs1Sig.bytesAt_getD hk, VG.Proof.RsaPkcs1Sig.bytesAt_getD (by unfold kk at e1 hk; omega),
    BitVec.add_zero, BitVec.add_zero] at this

theorem PubS.pLo (hk : 1 ≤ kk s) : loS s = loS a := by simp only [loS, p.byte hk]

theorem PubS.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubS.agree (hk : 1 ≤ kk s) : Agree Ss vS a s := ⟨p.sp, p.args 11 (by decide), fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [vS]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk
  · exact p.args 10 (by decide)⟩

end

/-- `PubS`, for a nonempty modulus. -/
def PubK (a s : State) : Prop := PubS a s ∧ 1 ≤ kk s

/-- `PubK` gives what the shared code needs. -/
theorem signOk (D : Nat) : Ok Ss vS (PreS D) PubK where
  fits P := fits P
  agree p := p.1.agree p.2

/-- `Base` from an entry state with the anchor's public data. -/
abbrev BS (D : Nat) : State → State → Prop := B Ss vS (PreS D) PubK

/-- `Base` and the saved arguments, from an entry state with the anchor's
public data. -/
def BP (D : Nat) (a t : State) : Prop := ∃ s, PreS D s ∧ PubK a s ∧ Base Ss vS s t ∧ Spilled s t.mem

theorem BP.bs {D : Nat} {a t : State} (h : BP D a t) : BS D a t := let ⟨s, P, p, b, _⟩ := h; ⟨s, P, p, b⟩

/-! ## The private operation -/

theorem psa_pub {a s : State} (p : PubS a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Ss, p.g .a6 (by decide), p.g .a7 (by decide), p.args _ (by decide : (0 : Nat) < 13),
      p.args _ (by decide : (1 : Nat) < 13), p.args _ (by decide : (2 : Nat) < 13),
      p.args _ (by decide : (3 : Nat) < 13), p.args _ (by decide : (4 : Nat) < 13),
      p.args _ (by decide : (5 : Nat) < 13), p.args _ (by decide : (6 : Nat) < 13),
      p.args _ (by decide : (7 : Nat) < 13), p.args _ (by decide : (11 : Nat) < 13),
      p.args _ (by decide : (12 : Nat) < 13)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (D : Nat) (a u : State) : Prop := ∃ s em, PreS D s ∧ PubK a s ∧ AtPriv s em u

theorem priv_pub {D : Nat} {a u₁ u₂ : State} (h₁ : APriv D a u₁) (h₂ : APriv D a u₂) :
    ∃ s₁ s₂ em₁ em₂, PreS D s₁ ∧ AtPriv s₁ em₁ u₁ ∧ PreS D s₂ ∧ AtPriv s₂ em₂ u₂ ∧
      Rsa.RISCV64.Priv.fnContract.pub (callE s₁ u₁) (callE s₂ u₂) := by
  obtain ⟨s₁, em₁, P₁, ⟨p₁, _⟩, A₁⟩ := h₁
  obtain ⟨s₂, em₂, P₂, ⟨p₂, _⟩, A₂⟩ := h₂
  refine ⟨s₁, s₂, em₁, em₂, P₁, A₁, P₂, A₂, ?_⟩
  have m : ∀ {s u : State}, (callE s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} {em : List Byte} (P : PreS D s) (A : AtPriv s em u) {p : Addr} {len : Nat}
    (hd : (kS s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaOaep.RISCV64.SC Ss s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hs hl
  refine Rsa.RISCV64.Priv.pub_of (by rw [show (callE s₁ u₁).sp = pb s₁ from A₁.sp,
      show (callE s₂ u₂).sp = pb s₂ from A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp])
    (fun r hr => ?_) (fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pub p₁ hi, psa_pub p₂ hi])
    ?_ ?_
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a1, A₂.a1, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a2, A₂.a2, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a3, A₂.a3, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a4, A₂.a4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a5, A₂.a5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.a6, A₂.a6, Ss, Ss, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.a7, A₂.a7, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [m, m, callE_gpr _ _ (r := .a2), callE_gpr _ _ (r := .a3), callE_gpr _ _ (r := .a2),
      callE_gpr _ _ (r := .a3), A₁.a2, A₁.a3, A₂.a2, A₂.a3,
      hb P₁ A₁ P₁.kn ((P₁.ns.symm).sub_left (sc_sub P₁)) (by have := P₁.wn; omega),
      hb P₂ A₂ P₂.kn ((P₂.ns.symm).sub_left (sc_sub P₂)) (by have := P₂.wn; omega), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .a4), callE_gpr _ _ (r := .a5), callE_gpr _ _ (r := .a4),
      callE_gpr _ _ (r := .a5), A₁.a4, A₁.a5, A₂.a4, A₂.a5,
      hb P₁ A₁ P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      hb P₂ A₂ P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.e, p₂.e]

theorem call_ct {D : Nat} : RelCT isa (Two (APriv D)) privCall fun _ _ => True := by
  unfold privCall
  refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
    Rsa.RISCV64.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
  obtain ⟨s₁, s₂, em₁, em₂, P₁, A₁, P₂, A₂, hp⟩ := priv_pub h₁ h₂
  exact ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, Rsa.RISCV64.Priv.pre_of_preP (preP_at P₁ A₁),
    Rsa.RISCV64.Priv.pre_of_preP (preP_at P₂ A₂), hp, (call_covers P₁ A₁).1, (call_covers P₁ A₁).2,
    (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩

theorem BP.sp {D : Nat} {a t : State} (h : BP D a t) : t.sp = fb a :=
  let ⟨_, _, p, b, _⟩ := h; by rw [b.sp, fb, fb, p.1.sp]

theorem BP.s0 {D : Nat} {a t : State} (h : BP D a t) : t.gpr .s0 = Ss a :=
  let ⟨_, _, p, b, _⟩ := h; b.s0.trans (p.1.args 11 (by decide))

/-- The private operation, in both runs. -/
theorem priv_ct {D : Nat} : RelCT isa (Two (BP D)) priv fun _ _ => True := by
  unfold priv
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := APriv D) (privArgs_taint fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show t₁.sp - _ = t₂.sp - _; rw [h₁.sp, h₂.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]; exact h₁.s0.trans h₂.s0.symm⟩)
    (fun a u ⟨t, ⟨s, P, p, b, sp⟩, e⟩ => by
      subst e; exact WP.mono (privArgs_ok P b sp rfl) fun u' A => ⟨s, _, P, p, A⟩)
    call_ct

end VG.Proof.RsaPss.RISCV64.Sg
