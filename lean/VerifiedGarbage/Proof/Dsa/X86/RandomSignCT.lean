module
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.RandomAttemptState
public import VerifiedGarbage.Proof.Dsa.X86.RandomCallCT

import VerifiedGarbage.Proof.Dsa.X86.RandomBodyCT
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The randomized signer is constant time (x86)

The contract's public data (the arguments, the public key bytes, the status,
the consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

theorem drop_take_prefix {α : Type} (xs : List α) {p q n : Nat} (h : p + q ≤ n) :
    (xs.drop p).take q = ((xs.take n).drop p).take q := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Two entries with the same public data: the same arguments, q, public
key bytes, status and trace. -/
theorem random_public {s t : State} (H : (Spec.Dsa.randomSignContract abi 156).pub s t) :
    pubOf s = pubOf t ∧ keyLeak s = keyLeak t ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨hsp, hleak, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := H
  change keyLeak s ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    keyLeak t ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : (keyLeak s).length = (keyLeak t).length := by
    simp only [keyLeak, Spec.Dsa.publicBytesLeak, rInput, List.length_map, List.length_take, rBytes_length,
      a4, a5, a6]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  refine ⟨?_, hk, hst, htr⟩
  have hargs : ∀ i < 13, X86.arg s i = X86.arg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 := by omega
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  have hkey : (rInput s).key.take (3 * (rInput s).pLen + (rInput s).qLen) =
      (rInput t).key.take (3 * (rInput t).pLen + (rInput t).qLen) :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a5
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a6
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [drop_take_prefix _ (n := 3 * (rInput s).pLen + (rInput s).qLen) (by omega), hkey,
    drop_take_prefix (rInput t).key (n := 3 * (rInput t).pLen + (rInput t).qLen) (by omega), hp, hq]

theorem alloc_push {s₀ : State} (A : RandomSignABI s₀) :
    isa.push (.alloc Random.frameBytes) s₀ = some (allocated Random.frameBytes s₀) := by
  have hsp : Random.frameBytes ≤ (s₀.gpr .esp).toNat := by have := A.stackLow; unfold Random.frameBytes; omega
  have hn : 0 < Random.frameBytes ∧ Random.frameBytes < 4096 ∧ Random.frameBytes % 4 = 0 := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_sign_random` leaks only what its contract makes public. -/
theorem randomSign_constantTime (F : SignFn) :
    ConstantTime isa (Spec.Dsa.randomSignContract abi 156).pre (Spec.Dsa.randomSignContract abi 156).pub
      (code F.name F.code) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have As := randomSignABI_of hs
  have At' := randomSignABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := random_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct F _ _ _ _ _ _ ⟨⟨pubOf s, keyLeak s, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.X86
