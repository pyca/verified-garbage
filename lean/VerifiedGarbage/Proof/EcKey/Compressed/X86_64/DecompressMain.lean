module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMiddle
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressFinish
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.EcKey.Compressed.Decode

/-! # Decompression meets the merged API contract -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (c.C.len + 1) =
      s.mem (s.gpr .rsi) :: Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : BaseCfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (hi : (Impl.EcKey.Compressed.X86_64.decompress c).InlineOk = true)
    (hmx : (Impl.EcKey.Compressed.X86_64.decompress c).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86_64.decompress c).inline s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hro, hrw, hfit, hwfit⟩ := hs
  have hp : DecompressPre c s :=
    ⟨by rw [hrd]; simp, by rw [hwr]; simp, hpw, hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.X86_64.decompress c).inline s fun s' =>
      (decompressContract c.C root).post s s' ∧ ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
    apply decompressFront_ok hc hp
    intro g t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega]; simp)
      (by simpa only [Nat.add_comm] using how)
      (by omega) U.saved
      (decide (CompressedAccept c root s)) (by simp only [U.flag, mask, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, _⟩ => ?_
    refine ⟨?_, fun r hr => (hsave r hr).trans (U.original r hr)⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave⟩ := hrun
  have F := (Exec.regions he (Code.noCalls_inline hi)).2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact Exec.gpr (Code.clobbers_rsp_of_inlineOk hi) he
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrw) (by decide)

end VG.Proof.EcKey.Compressed.X86_64
