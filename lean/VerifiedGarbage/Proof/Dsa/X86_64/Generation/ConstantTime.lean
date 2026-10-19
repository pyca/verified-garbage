module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInnerCT

/-! # The complete parameter-generation ABI satisfies its declared public leak -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation

private theorem generation_post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem generation_constantTime (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel) :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 472).pre
      (Spec.Dsa.generateParametersContract abi 472).pub
      (code H.sha1 H.sha256 Sq.mm M.mm K.run) := by
  intro s t tsa tsb u v hs ht hpub ea eb
  have hsa := generationABI_of hs
  have hta := generationABI_of ht
  have hp := generation_public_related hpub
  unfold code at ea eb
  cases ea with
  | frame pa ba _ =>
    cases eb with
    | frame pb bb _ =>
      rw [generation_alloc (by decide) (by omega_using [hsa.stackLower] : 48 ≤ (s.gpr .rsp).toNat), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (by omega_using [hta.stackLower] : 48 ≤ (t.gpr .rsp).toNat), Option.some.injEq] at pb
      subst pa; subst pb
      cases ba with | seq sa restA => cases restA with | seq ia ra =>
      cases bb with | seq sb restB => cases restB with | seq ib rb =>
      have saveTrace := (entrySave_ct _ _ _ _ _ _ (by
        change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
        rw [hp.sp]) sa sb).1
      obtain ⟨ga, rda, wra, _, fa⟩ := generation_post_of_exec (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) sa
      obtain ⟨gb, rdb, wrb, _, fb⟩ := generation_post_of_exec (entrySave_ok (s := allocState 48 t) (List.mem_cons_self ..)) sb
      have inner := entryInner_ct H M Sq K hsa hta hp ga rda wra fa gb rdb wrb fb ia ib
      have restoreTrace := (entryRestore_ct _ _ _ _ _ _ inner.2 ra rb).1
      simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
      rw [saveTrace, inner.1, restoreTrace]

end VG.Proof.Dsa.X86_64.Generation
