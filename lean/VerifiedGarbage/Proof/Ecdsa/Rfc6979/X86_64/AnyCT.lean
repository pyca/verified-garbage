module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Any
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Any
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Deterministic ECDSA on x86-64, for any hash function: constant time

Two runs from entries whose public data agree (`Pair`): the entry blocks
address memory at `rsp` and at the table's address, which agree
(`prefix_ct`); the dispatch branches on `hash`, which is public; and `sign`
of the hash function's configuration is constant time (`sign_ct`), from the
states the entry blocks leave (`case_pair`): `any_ct`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

theorem entry_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block entry) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem entryFns_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp, .r10]) (.block entryFns) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The state `entry` leaves. -/
abbrev afterEntry (e : State) : State :=
  ((e.setReg .rcx (e.gpr .r8)).setReg .r10 (stackArg e 0)).setReg .rax (e.gpr .r9)

namespace RfcAny

variable (A : RfcAny)

/-- Two entries whose public data agree. -/
def Pair (s₁ s₂ : State) : Prop :=
  (A.I.signAnyContract (abi.withConsts A.cs) 408).pre s₁ ∧ (A.I.signAnyContract (abi.withConsts A.cs) 408).pre s₂ ∧
    (A.I.signAnyContract (abi.withConsts A.cs) 408).pub s₁ s₂

/-- The states the entry blocks leave, from two such entries. -/
def After2 (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, A.Pair σ₁ σ₂ ∧ Ent σ₁ s₁ ∧ Ent σ₂ s₂

theorem prefix_ct :
    RelCT isa A.Pair (.seq (.block entry) (.block entryFns)) fun s₁ s₂ => True ∧ A.After2 s₁ s₂ := by
  have h₁ := RelCT.wpDep (F := fun σ s => s = afterEntry σ)
    (RelCT.taint (A := taint) (P := A.Pair) (c := .block entry) (Taint.ofRegs [.rsp]) (fun s₁ s₂ ⟨_, _, hpub⟩ => Taint.agree_ofRegs fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (apub_of hpub).rsp) entry_taint.choose_spec)
    fun s₁ s₂ (⟨p₁, p₂, _⟩ : A.Pair s₁ s₂) => ⟨entry_ok (apre_of p₁), entry_ok (apre_of p₂)⟩
  have h₂ := RelCT.taint (A := taint) (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, A.Pair σ₁ σ₂ ∧ s₁ = afterEntry σ₁ ∧
      s₂ = afterEntry σ₂) (c := .block entryFns) (Taint.ofRegs [.rsp, .r10])
    (fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨_, _, hpub⟩, e₁, e₂⟩ => Taint.agree_ofRegs fun r hr => by
      subst e₁ e₂
      have hb := apub_of hpub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [RegUpd.gpr_setReg, hb.rsp, hb.arg]) entryFns_taint.choose_spec
  refine (RelCT.wpDep (F := fun σ s => Ent σ s) (RelCT.seq h₁ h₂) fun s₁ s₂ (⟨p₁, p₂, _⟩ : A.Pair s₁ s₂) =>
    ⟨WP.seq (WP.mono (entry_ok (apre_of p₁)) fun s hs => by subst hs; exact entryFns_ok (apre_of p₁)),
      WP.seq (WP.mono (entry_ok (apre_of p₂)) fun s hs => by subst hs; exact entryFns_ok (apre_of p₂))⟩).mono
    (fun _ _ h => h) fun _ _ ⟨_, σ₁, σ₂, hp, e₁, e₂⟩ => ⟨trivial, σ₁, σ₂, hp, e₁, e₂⟩

theorem constRegions_congr {f g : String → BitVec 64} {cs : List (String × List (BitVec 64))}
    (h : ∀ x ∈ cs, f x.1 = g x.1) : Abi.constRegions f cs = Abi.constRegions g cs :=
  List.map_congr_left fun x hx => by rw [h x hx]

/-- The states the dispatch enters `sign` of the hash function `T` with, as
`sign_ct` has them, with the first entry as the anchor. -/
theorem case_pair {k : Nat} {T : Spec.HashFns.Streaming} (hT : Spec.HashFns.streaming k = some T)
    (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) {σ₁ σ₂ s₁ s₂ : State} (hp : A.Pair σ₁ σ₂) (e₁ : Ent σ₁ s₁)
    (e₂ : Ent σ₂ s₂) (hk₁ : (σ₁.gpr .r9).toNat = k) :
    BodyPair (A.hashOf hT hk) σ₁ [tabR σ₁, argR σ₁] s₁ s₂ := by
  obtain ⟨p₁, p₂, hpub⟩ := hp
  have a₁ := apre_of p₁
  have a₂ := apre_of p₂
  have hb := apub_of hpub
  have hk₂ : (σ₂.gpr .r9).toNat = k := by rw [← hb.r9]; exact hk₁
  obtain ⟨T', hT', hm, -⟩ := hash_facts hk
  rw [hT] at hT'
  cases hT'
  have hX : [tabR σ₂, argR σ₂] = [tabR σ₁, argR σ₁] := by
    simp only [tabR, argR, stackArgAddr, hb.arg, hb.rsp]
  have hl₁ := A.len_eq a₁ hT hk₁
  have hl₂ := A.len_eq a₂ hT hk₂
  have hlike : Like σ₁ σ₂ := by
    refine ⟨⟨hb.same.1.symm, hb.same.2.1.symm, by
      have := hb.same.2.2; simp only [abi, Option.elim] at this ⊢; exact this.symm⟩, ?_, ?_, hb.rsp.symm⟩
    · rw [a₁.rd, a₂.rd, constRegions_congr (cs := A.cs) (fun x hx => (hb.syms x hx).symm)]
      simp only [dR, dgR, tabR, argR, stackArgAddr, hb.rsi, hb.rdx, hb.rcx, hb.arg, hb.rsp]
    · rw [a₁.wr, a₂.wr]
      simp only [outR, scrR, hb.rdi, hb.r8]
  have hw₁ := hb.leak
  rw [hk₁, hk₂, A.anyResult_eq hm _ _ _ hl₁, A.anyResult_eq hm _ _ _ hl₂] at hw₁
  simp only [Option.map_some, Option.getD_some, Spec.HashFns.tableWords, List.cons.injEq] at hw₁
  obtain ⟨hr, w₀, w₁, w₂, -⟩ := hw₁
  refine ⟨A.body_pre a₁ e₁ hT hk₁, hX ▸ A.body_pre a₂ e₂ hT hk₂, ?_, A.body_in a₁ e₁ hT hk₁ ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩,
    A.body_in a₂ e₂ hT hk₂ hlike, ?_, ?_, ?_⟩
  · refine ⟨by rw [e₁.cs .rsp (by decide), e₂.cs .rsp (by decide), hb.rsp], by rw [e₁.rdi, e₂.rdi, hb.rdi],
      by rw [e₁.rsi, e₂.rsi, hb.rsi], by rw [e₁.rdx, e₂.rdx, hb.rdx], by rw [e₁.rcx, e₂.rcx, hb.r8], ?_,
      fun x hx => by rw [e₁.syms, e₂.syms]; exact hb.syms x hx⟩
    show (result (A.instOf T) s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result (A.instOf T) s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)).2
    rw [e₁.mem, e₂.mem, e₁.rsi, e₂.rsi, e₁.rdx, e₂.rdx]
    exact hr
  · rw [e₁.r9, e₂.r9]; exact BitVec.eq_of_toNat_eq w₀
  · rw [e₁.r10, e₂.r10]; exact BitVec.eq_of_toNat_eq w₁
  · rw [e₁.r11, e₂.r11]; exact BitVec.eq_of_toNat_eq w₂

/-- `vg_ecdsa_<curve>_rfc6979_sign` is constant time but for what the shared
contract makes public: the hash function, the table and the number of
candidates tried. -/
theorem any_ct : ConstantTime isa (A.I.signAnyContract (abi.withConsts A.cs) 408).pre
    (A.I.signAnyContract (abi.withConsts A.cs) 408).pub A.code := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.assoc (RelCT.seq A.prefix_ct ?_))
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests (by rw [keys_any]; decide)
    (by rw [keys_any]; decide) (fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨p₁, _, hpub⟩, e₁, e₂⟩ => ?_) fun k c hc => ?_
  · rw [keys_any]
    refine ⟨show (s₁.gpr .rax).toNat = (s₂.gpr .rax).toNat by rw [e₁.rax, e₂.rax, (apub_of hpub).r9], ?_⟩
    show (s₁.gpr .rax).toNat ∈ hashIds
    rw [e₁.rax]
    exact (apre_of p₁).hk
  · obtain ⟨k', hk', hkc⟩ := List.mem_map.mp hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkc
    obtain ⟨T, hT, -⟩ := hash_facts hk'
    rw [← A.hashOf_sign hT hk']
    refine (RelCT.exists_ (P := fun σ s₁ s₂ => BodyPair (A.hashOf hT hk') σ [tabR σ, argR σ] s₁ s₂)
      fun σ => sign_ct (P := A.hashOf hT hk') σ _).mono
      (fun s₁ s₂ ⟨a₁, a₂, ⟨_, σ₁, σ₂, hp, e₁, e₂⟩, hsel, r₁, r₂, _, _⟩ => ⟨σ₁, A.case_pair hT hk' hp (e₁.flags r₁)
        (e₂.flags r₂) (by rw [← e₁.rax]; exact hsel)⟩) fun _ _ h => h

end RfcAny

end VG.Proof.Ecdsa.Rfc6979.X86_64
