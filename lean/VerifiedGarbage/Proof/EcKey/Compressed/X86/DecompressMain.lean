module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMiddle
import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressFinish
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Pre

/-! # Decompression meets the merged API contract -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (ptr s 1) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (ptr s 1) (c.C.len + 1) =
      s.mem (ptr s 1) :: Spec.Ecdsa.bytesAt s.mem (ptr s 1 + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

def decompressFront (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.seq (.block (Impl.EcKey.Compressed.X86.decompressPeer c))
      (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)))

theorem decompressFront_prefix_ok {c : Cfg} (hc : CfgOk c) {s : State}
    (hp : InputPre c (1 + c.C.len) s) : WP isa (decompressFront c) s (DecompressFront c s) := by
  have h := decompressFront_ok hc hp (rest := .block []) (fun _ F => WP.block_nil F)
  simpa only [decompressFront, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using h

def decompressBody (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.seq (.block (Impl.EcKey.Compressed.X86.decompressPeer c))
      (.seq (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c))
        (Impl.EcKey.Compressed.X86.recoverCoordinate c)))

theorem decompressBody_ok {c : Cfg} (hc : CfgOk c)
    {root : Fe c.C → Fe c.C} (hroot : CandidateCorrect c root) {s : State}
    (hp : InputPre c (1 + c.C.len) s) :
    WP isa (decompressBody c) s (DecompressChecked c root s) :=
  decompressFront_ok hc hp (fun _ F => decompressMiddle_ok hc hroot F)

theorem decompress_correct (c : Cfg) (hc : CfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.decompress c) 28)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  have hp := codec_input (c := c) hs
  obtain ⟨hrd, hwr, how, hpo, hpw, hao, haw, hro, hrw, hfit, hpk, hws, hsf, hlo, hso, hsw⟩ := hs
  simp only [Bool.false_eq_true, ite_false] at hrd hwr
  have hbody : SpOk (decompressBody c) 28 :=
    hsp.left.seq (hsp.right.left.seq (hsp.right.right.left.seq hsp.right.right.right.left))
  have hrun : WP isa (Impl.EcKey.Compressed.X86.decompress c) s fun u =>
      (decompressContract c.C root).post s u ∧
      (∀ rd ∈ Cfg.saved, u.gpr rd.1 = s.gpr rd.1) ∧ u.gpr .esp = s.gpr .esp := by
    change WP isa ([.block (c.setupWith Impl.EcKey.Compressed.X86.args),
      .block (Impl.EcKey.Compressed.X86.decompressPeer c),
      Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)].foldr .seq
      (.seq (Impl.EcKey.Compressed.X86.recoverCoordinate c)
        (.block (Impl.EcKey.Compressed.X86.decompressFinish c)))) s _
    rw [WP.split]
    refine WP.seq (WP.mono (WP.spFrame hbody hlo (decompressBody_ok hc hroot
      (by simpa only [Nat.add_comm] using hp))) fun t ⟨F, W⟩ => ?_)
    have hin : InRegions (s.rd ++ s.wr) (argAddr s 0) 4 :=
      ⟨_, by rw [hrd, hwr]; simp, arg_containsN (k := 3) (by omega) (by decide)⟩
    have hdarg : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 28], Region.Disjoint ⟨argAddr s 0, 4⟩ r := by
      intro r hr
      rw [hwr] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hao.sub_left (arg_subN (k := 3) (by omega) (by decide))
      · exact haw.sub_left (arg_subN (k := 3) (by omega) (by decide))
      · exact (below_disjoint_args hlo (by omega) (by decide)).symm
    have hout := argLoad_frame hin hdarg F.esp (by rw [F.rd, F.wr]) W
    refine WP.mono (decompressFinish_ok hc F.scr hout (by omega)
      (by rw [F.wr, hwr]; simp [Nat.add_comm]) (by simpa only [Nat.add_comm] using how)
      F.saved (decide (CompressedAccept c root s)) (by simp only [F.flag, decide_eq_true_eq]))
      fun u ⟨bytes, ret, saved, esp, _⟩ => ?_
    refine ⟨?_, saved, (esp _ (by decide)).trans F.esp⟩
    dsimp only [decompressContract]
    rw [decompress_key, BitVec.setWidth_append_eq_right]
    rw [F.x, F.y] at bytes
    change Spec.EcKey.bytesAt u.mem ((arg s 0).setWidth 64) (1 + 2 * c.C.len) = _ at bytes
    simp only [decide_eq_true_eq] at ret bytes
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at ret bytes ⊢
      refine ⟨ret, ?_⟩
      change Spec.EcKey.bytesAt u.mem (ptr s 0) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using bytes
    · rw [ite_eq_right hk] at ret bytes ⊢
      exact ⟨ret, by simpa only [Nat.add_comm] using bytes⟩
  obtain ⟨t, u, he, ⟨hpost, saved, esp⟩, W⟩ := WP.spFrame hsp hlo hrun
  refine ⟨t, u, he, ⟨?_, ?_⟩, hpost⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact saved (.ebx, 0) (by decide)
    · exact saved (.esi, 4) (by decide)
    · exact saved (.edi, 8) (by decide)
    · exact saved (.ebp, 12) (by decide)
    · exact esp
  · refine W.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [hwr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hro
    · exact hrw
    · exact (below_disjoint_ret hlo).symm

end VG.Proof.EcKey.Compressed.X86
