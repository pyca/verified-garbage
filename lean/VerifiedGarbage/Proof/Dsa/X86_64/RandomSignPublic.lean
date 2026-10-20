module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-! Public argument and key-prefix agreement for randomized signing. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

structure RandomSignPublicAgree (s t : State) : Prop where
  sp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ argRegs, s.gpr r = t.gpr r
  args : ∀ i < 7, stackArg s i = stackArg t i
  key : (randomInput s).key.take (3 * (randomInput s).pLen + (randomInput s).qLen) =
    (randomInput t).key.take (3 * (randomInput t).pLen + (randomInput t).qLen)

theorem RandomSignPublicAgree.base {s t : State} (h : RandomSignPublicAgree s t) : randomBase s = randomBase t := by
  unfold randomBase
  rw [h.sp]

theorem RandomSignPublicAgree.qbytes {s t : State} (h : RandomSignPublicAgree s t) : randomQBytes s = randomQBytes t := by
  have hp : (randomInput s).pLen = (randomInput t).pLen := congrArg BitVec.toNat (h.regs .r9 (by decide))
  have hq : (randomInput s).qLen = (randomInput t).qLen := congrArg BitVec.toNat (h.args 0 (by decide))
  have hk := h.key
  rw [← hp, ← hq] at hk
  have he := prefix_component_eq (offset := (randomInput s).pLen) (len := (randomInput s).qLen) hk (by omega)
  unfold randomQBytes
  rw [← hp, ← hq]
  exact he

theorem RandomSignPublicAgree.keyLeak {s t : State} (h : RandomSignPublicAgree s t) :
    Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key =
      Spec.Dsa.publicBytesLeak (randomInput t).pLen (randomInput t).qLen (randomInput t).key := by
  unfold Spec.Dsa.publicBytesLeak
  rw [h.key]

theorem random_sign_public_related {extra : Nat} {s t : State}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t)
    (h : (Spec.Dsa.randomSignContract abi (extra + 256)).pub s t) :
    RandomSignPublicAgree s t ∧
      (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status ∧
      (randomSignRemaining (randomInput s) 0 8).used = (randomSignRemaining (randomInput t) 0 8).used ∧
      (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace := by
  sig_pub [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
  have hregs : ∀ r ∈ argRegs, s.gpr r = t.gpr r := by
    intro r hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hdi, hsi, hdx, hcx, h8, h9]
  have hargs : ∀ i < 7, stackArg s i = stackArg t i := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6]
  change (Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key ++
      [_, _] ++ _) = (Spec.Dsa.publicBytesLeak (randomInput t).pLen (randomInput t).qLen (randomInput t).key ++
      [_, _] ++ _) at hleak
  have hes := random_remaining_bytes hs
  have het := random_remaining_bytes ht
  dsimp only [randomInput] at hes het
  rw [← hes, ← het, List.append_assoc, List.append_assoc] at hleak
  have hlen : (Spec.Dsa.publicBytesLeak (randomInput s).pLen (randomInput s).qLen (randomInput s).key).length =
      (Spec.Dsa.publicBytesLeak (randomInput t).pLen (randomInput t).qLen (randomInput t).key).length := by
    simp only [Spec.Dsa.publicBytesLeak, randomInput, List.length_map, List.length_take, bytesAt_length, h8, h9, a0]
  obtain ⟨hkey, hrest⟩ := List.append_inj hleak hlen
  have hk := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hkey
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  exact ⟨⟨hsp, hregs, hargs, hk⟩, hrest⟩

end VG.Proof.Dsa.X86_64
