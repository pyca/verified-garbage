module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.ABI
public import VerifiedGarbage.Impl.Dsa.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Impl.Dsa.Arm.Generate

import VerifiedGarbage.Proof.Dsa.Arm.Key.BodyCT
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key generation is constant time (32-bit ARM)

The contract's public data (the arguments, the domain, the status, the
consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey

/-- Two entries with the same public data: the same arguments, domain,
status and trace. -/
theorem key_public {s t : State} (H : (Spec.Dsa.generateKeyContract Arm.abi 144).pub s t) :
    pubOf s = pubOf t ∧ (rInput s).key = (rInput t).key ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at H
  obtain ⟨hsp, hleak, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6⟩ := H
  change (rInput s).key.map (·.toNat) ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    (rInput t).key.map (·.toNat) ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : ((rInput s).key.map (·.toNat)).length = ((rInput t).key.map (·.toNat)).length := by
    simp only [rInput, List.length_map, rBytes_length, a0]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  have hkey : (rInput s).key = (rInput t).key := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  refine ⟨?_, hkey, hst, htr⟩
  have hargs : ∀ i < 7, stackArg s i = stackArg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6]
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a1
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a2
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, by rw [r0, r1, r2, r3], List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [hkey, hp, hq]

theorem alloc_push {s₀ : State} (A : KeyABI s₀) :
    isa.push (.alloc frameBytes) s₀ = some (allocated frameBytes s₀) := by
  have hsp : frameBytes ≤ s₀.sp.toNat := by have := A.stackLow; unfold frameBytes; omega
  have hn : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧
      encodable (BitVec.ofNat 32 frameBytes) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_generate_key` leaks only what its contract makes public. -/
theorem generateKey_constantTime (check derive : String) :
    ConstantTime isa (Spec.Dsa.generateKeyContract Arm.abi 144).pre
      (Spec.Dsa.generateKeyContract Arm.abi 144).pub
      (code check derive Generate.checkParameters Generate.deriveKey) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have As := keyABI_of hs
  have At' := keyABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := key_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct check derive _ _ _ _ _ _
        ⟨⟨pubOf s, (rInput s).key, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.Arm.Key
