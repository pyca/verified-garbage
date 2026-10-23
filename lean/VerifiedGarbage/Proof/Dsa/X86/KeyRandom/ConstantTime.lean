module
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.State
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.BodyCT




/-!
# The key generator is constant time (x86)

The contract's public data (the arguments, the public domain bytes, the status,
the consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

/-- Two entries with the same public data: the same arguments, q, public
key bytes, status and trace. -/
theorem random_public {s t : State} (H : (Spec.Dsa.generateKeyContract abi 232).pub s t) :
    pubOf s = pubOf t ∧ keyLeak s = keyLeak t ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨hsp, hleak, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := H
  change keyLeak s ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    keyLeak t ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : (keyLeak s).length = (keyLeak t).length := by
    simp only [keyLeak, rInput, List.length_map, rBytes_length,
      a4]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  refine ⟨?_, hk, hst, htr⟩
  have hargs : ∀ i < 11, X86.arg s i = X86.arg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
  have hkey : (rInput s).key = (rInput t).key :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a5
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a6
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [hkey, hp, hq]

theorem alloc_push {s₀ : State} (A : KeyABI s₀) :
    isa.push (.alloc KeyRandom.frameBytes) s₀ = some (allocated KeyRandom.frameBytes s₀) := by
  have hsp : KeyRandom.frameBytes ≤ (s₀.gpr .esp).toNat := by have := A.stackLow; unfold KeyRandom.frameBytes; omega
  have hn : 0 < KeyRandom.frameBytes ∧ KeyRandom.frameBytes < 4096 ∧ KeyRandom.frameBytes % 4 = 0 := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_generate_key` leaks only what its contract makes public. -/
theorem generateKeyWith_constantTime {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I)
    (stable : StableScratch I) (ctC : CheckInvokeCT C) (ctD : DeriveInvokeCT D) :
    ConstantTime isa (Spec.Dsa.generateKeyContract abi 232).pre (Spec.Dsa.generateKeyContract abi 232).pub
      (codeWith C.code D.code) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have As := keyABI_of hs
  have At' := keyABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := random_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := bodyWith_ct C D stable ctC ctD As At' e hk hst htr hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

theorem generateKey_constantTime (C : CheckCall.CheckFn) (D : DeriveFn) :
    ConstantTime isa (Spec.Dsa.generateKeyContract abi 232).pre (Spec.Dsa.generateKeyContract abi 232).pub
      (code C.name D.name C.code D.code) :=
  generateKeyWith_constantTime C.invoke D.invoke (fun _ _ _ => trivial) C.invoke_ct D.invoke_ct

end VG.Proof.Dsa.X86.KeyRandom
