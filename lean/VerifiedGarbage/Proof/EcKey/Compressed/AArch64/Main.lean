module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Front
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Finish
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! # Compression meets the merged API contract -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdh.AArch64 Spec.Weierstrass

theorem compress_key (c : Cfg) (s : State) :
    Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (s.gpr .x1) (2 * c.C.len + 1)) =
    if KeyOk c s then some (BitVec.ofNat 8 (2 + keyY c s % 2) :: toBytes c.C.len (keyX c s)) else none := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]
    omega
  have hhead : (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (1 + 2 * c.C.len)).head? =
      some (s.mem (s.gpr .x1)) := by rw [peer_bytes]; rfl
  have hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    rfl
  have hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hv : Proof.Ecdh.Valid c.C (s.mem (s.gpr .x1)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, he⟩
      exact ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
      exact ⟨h4, hx, hy, he⟩
  change Spec.EcKey.compressPublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega, compress_eq hlen hhead hx hy]
  simp only [hv]

theorem compress_correct (c : Cfg) (hc : BaseCfgOk c)
    (hn : CallsKeep (Impl.EcKey.Compressed.AArch64.compress c))
    (hu : KeepsUntouched (Impl.EcKey.Compressed.AArch64.compress c))
    (hv : (Impl.EcKey.Compressed.AArch64.compress c).allInstrs keepsV = true)
    (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.AArch64.compress c) s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hwfit⟩ := hs
  have hp : Pre c s :=
    ⟨by rw [hrd, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega]; simp,
      by rw [hwr]; simp, by simpa only [Nat.add_comm] using hpw, hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.AArch64.compress c) s fun s' =>
      (compressContract c.C).post s s' ∧ ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
    apply front_ok hc hp
    intro g t F
    refine WP.mono (finish_ok hc F.scr F.out (by rw [F.wr, hwr]; simp) how hfit F.saved
      (decide (KeyOk c s)) (by simp only [F.flag, mask, decide_eq_true_eq])) fun s' ⟨hout, hret, hsave⟩ => ?_
    refine ⟨?_, fun r hr => (hsave r hr).trans (F.original r hr)⟩
    change (match Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (s.gpr .x1) (2 * c.C.len + 1)) with
      | some bs => _
      | none => _)
    rw [compress_key]
    rw [F.x, F.y] at hout
    change Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (c.C.len + 1) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    by_cases hk : KeyOk c s
    · rw [ite_eq_left hk] at hret hout ⊢
      exact ⟨hret, hout⟩
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, hout⟩
  obtain ⟨t, s', he, hpost, hsave⟩ := hrun
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsave, hpost⟩

end VG.Proof.EcKey.Compressed.AArch64
