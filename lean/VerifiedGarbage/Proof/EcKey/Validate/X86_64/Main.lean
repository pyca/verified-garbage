module

import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Finish
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front

/-!
# The standalone validator's correctness

Compose the existing decoder, point check, flag conversion, and register
restore. The bridge to the encoded-key specification is ECDH's existing
`decode_eq`; no new curve-arithmetic argument is needed.
-/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.Ecdsa.Verify.X86_64 (KeyOk keyX keyY)
open VG.Spec.Weierstrass

/-- The check's existing validity predicate is precisely successful decoding. -/
theorem decode_key (c : Cfg) (s : State) :
    (Spec.EcKey.decodePublicKey c.C
      (Spec.EcKey.bytesAt s.mem (s.gpr .rdi) (2 * c.C.len + 1))).isSome = decide (KeyOk c s) := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).head? =
      some (s.mem (s.gpr .rdi)) := by rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hiff : Proof.Ecdh.Valid c.C (s.mem (s.gpr .rdi)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, hcv⟩; exact ⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩; exact ⟨h4, hx, hy, hcv⟩
  have hlen' : 2 * c.C.len + 1 = 1 + 2 * c.C.len := Nat.add_comm _ _
  change (Spec.EcKey.decodePublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (2 * c.C.len + 1))).isSome = _
  rw [hlen', Proof.Ecdh.decode_eq hlen hb0 hxv hyv]
  by_cases hk : KeyOk c s
  · rw [dite_eq_left (hiff.mpr hk)]
    exact (decide_eq_true_iff.mpr hk).symm
  · rw [dite_eq_right (mt hiff.mp hk)]
    exact (decide_eq_false_iff_not.mpr hk).symm

/-- Correctness of the inlined code, with the ABI's register restores. -/
theorem correct (c : Cfg) (hc : BaseCfgOk c)
    (hi : (Impl.EcKey.Validate.X86_64.validate c).InlineOk = true)
    (hmx : (Impl.EcKey.Validate.X86_64.validate c).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (keyContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Validate.X86_64.validate c).inline s t s' ∧
      abiPreserved s s' ∧ (keyContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hd, hret, hfit⟩ := hs
  have hp : Pre c s :=
    ⟨by rw [hrd, show 1 + 2 * c.C.len = 2 * c.C.len + 1 from Nat.add_comm _ _]; simp,
      by rw [hwr]; simp, by simpa only [Nat.add_comm] using hd, hfit⟩
  obtain ⟨t, s', he, hpost, saved⟩ := front_ok hc hp (fun g t F => finish_ok hc F)
  have he' : Exec isa (Impl.EcKey.Validate.X86_64.validate c).inline s t s' := he
  have hsp := Code.clobbers_rsp_of_inlineOk hi
  have F := (Exec.regions he' (Code.noCalls_inline hi)).2.2
  refine ⟨t, s', he', abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he'
    ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact saved _ (by decide)
    · exact saved _ (by decide)
    · exact Exec.gpr hsp he'
    · exact saved _ (by decide)
    · exact saved _ (by decide)
    · exact saved _ (by decide)
    · exact saved _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hret) (by decide)
  · change (s'.gpr .rax).setWidth 32 = _
    rw [decode_key]
    simpa only [decide_eq_true_eq] using hpost

end VG.Proof.EcKey.Validate.X86_64
