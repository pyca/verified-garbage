module
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Dsa.Arm.RandomTwo
public import VerifiedGarbage.Proof.Framework.Arm.Call

import VerifiedGarbage.Proof.Dsa.Arm.RandomBodyCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# The randomized signer is constant time (32-bit ARM)

The contract's public data (the arguments, the public key bytes, the status,
the consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign

theorem drop_take_prefix {α : Type} (xs : List α) {p q n : Nat} (h : p + q ≤ n) :
    (xs.drop p).take q = ((xs.take n).drop p).take q := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Two entries with the same public data: the same arguments, q, public
key bytes, status and trace. -/
theorem random_public {s t : State} (H : (Spec.Dsa.randomSignContract Arm.abi 144).pub s t) :
    pubOf s = pubOf t ∧ keyLeak s = keyLeak t ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at H
  obtain ⟨hsp, hleak, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  change keyLeak s ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    keyLeak t ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : (keyLeak s).length = (keyLeak t).length := by
    simp only [keyLeak, Spec.Dsa.publicBytesLeak, rInput, List.length_map, List.length_take, rBytes_length,
      a0, a1, a2]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  refine ⟨?_, hk, hst, htr⟩
  have hargs : ∀ i < 9, stackArg s i = stackArg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8]
  have hkey : (rInput s).key.take (3 * (rInput s).pLen + (rInput s).qLen) =
      (rInput t).key.take (3 * (rInput t).pLen + (rInput t).qLen) :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a1
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a2
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, by rw [r0, r1, r2, r3], List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [drop_take_prefix _ (n := 3 * (rInput s).pLen + (rInput s).qLen) (by omega), hkey,
    drop_take_prefix (rInput t).key (n := 3 * (rInput t).pLen + (rInput t).qLen) (by omega), hp, hq]

theorem alloc_push {s₀ : State} (A : RandomABI s₀) :
    isa.push (.alloc frameBytes) s₀ = some (allocated frameBytes s₀) := by
  have hsp : frameBytes ≤ s₀.sp.toNat := by have := A.stackLow; unfold frameBytes; omega
  have hn : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧
      encodable (BitVec.ofNat 32 frameBytes) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_sign_random` leaks only what its contract makes public. -/
theorem randomSign_constantTime (name : String) :
    ConstantTime isa (Spec.Dsa.randomSignContract Arm.abi 144).pre
      (Spec.Dsa.randomSignContract Arm.abi 144).pub (code name (Entry.operation true)) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have As := randomABI_of hs
  have At' := randomABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := random_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct name _ _ _ _ _ _ ⟨⟨pubOf s, keyLeak s, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.Arm
