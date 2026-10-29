module

public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP

import VerifiedGarbage.Proof.EcKey.Compressed.X86.Pre
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Finish
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.X86.Main
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/Main.lean`, which only this module imported.
section

section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Ecdh.X86 Spec.Weierstrass

theorem compress_key (c : Cfg) (s : State) :
    Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (ptr s 1) (2 * c.C.len + 1)) =
    if KeyOk c s then some (BitVec.ofNat 8 (2 + keyY c s % 2) :: toBytes c.C.len (keyX c s)) else none := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]
    omega
  have hhead : (Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).head? =
      some (s.mem (ptr s 1)) := by rw [peer_bytes]; rfl
  have hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    rfl
  have hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (ptr s 1) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hv : Proof.Ecdh.Valid c.C (s.mem (ptr s 1)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, he⟩
      exact ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
      exact ⟨h4, hx, hy, he⟩
  change Spec.EcKey.compressPublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (ptr s 1) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega, compress_eq hlen hhead hx hy]
  simp only [hv]


def compressFront (c : Cfg) : Prog isa :=
  .seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 1)) (Impl.Ecdh.X86.Cfg.validate c))

theorem compressFront_ok {c : Cfg} (hc : CfgOk c) {s : State}
    (hp : InputPre c (1 + 2 * c.C.len) s) : WP isa (compressFront c) s (Front c s) := by
  have h := front_ok hc hp (rest := .block []) (fun _ F => WP.block_nil F)
  simpa only [compressFront, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using h

theorem compress_correct (c : Cfg) (hc : CfgOk c)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.compress c) 28)
    (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86.compress c) s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  have hp := codec_input (c := c) hs
  obtain ⟨hrd, hwr, how, hpo, hpw, hao, haw, hro, hrw, hfit, hpk, hws, hsf, hlo, hso, hsw⟩ := hs
  simp only [Bool.false_eq_true, ite_false] at hrd hwr
  have hfront : SpOk (compressFront c) 28 := hsp.left.seq (hsp.right.left.seq hsp.right.right.left)
  have hrun : WP isa (Impl.EcKey.Compressed.X86.compress c) s fun u =>
      (compressContract c.C).post s u ∧
      (∀ rd ∈ Cfg.saved, u.gpr rd.1 = s.gpr rd.1) ∧ u.gpr .esp = s.gpr .esp := by
    change WP isa ([.block (c.setupWith Impl.EcKey.Compressed.X86.args),
      .block (Impl.Ecdh.X86.Cfg.peerAt c 1)].foldr .seq
      (.seq (Impl.Ecdh.X86.Cfg.validate c) (.block (Impl.EcKey.Compressed.X86.compressFinish c)))) s _
    rw [WP.split]
    refine WP.seq (WP.mono (WP.spFrame hfront hlo (compressFront_ok hc
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
    refine WP.mono (finish_ok hc F.scr hout (by omega)
      (by rw [F.wr, hwr]; simp [Nat.add_comm]) (by simpa only [Nat.add_comm] using how)
      F.saved (decide (KeyOk c s)) (by simp only [F.flag, decide_eq_true_eq]))
      fun u ⟨bytes, ret, saved, esp, _⟩ => ?_
    refine ⟨?_, saved, esp.trans F.esp⟩
    dsimp only [compressContract]
    rw [compress_key, BitVec.setWidth_append_eq_right]
    rw [F.x, F.y] at bytes
    change Spec.EcKey.bytesAt u.mem ((arg s 0).setWidth 64) (1 + c.C.len) = _ at bytes
    simp only [decide_eq_true_eq] at ret bytes
    by_cases hk : KeyOk c s
    · rw [ite_eq_left hk] at ret bytes ⊢
      exact ⟨ret, by simpa only [Nat.add_comm] using bytes⟩
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
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86

theorem compress_verified {c : Cfg} (hc : CfgOk c) (I : Spec.EcKey.Instance) (hC : c.C = I.curve)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.compress c) 28)
    (hct : ConstantTime isa (compressContract c.C).pre (compressContract c.C).pub
      (Impl.EcKey.Compressed.X86.compress c))
    (hsig : ∃ s, (I.compressPublicKeyContract abi 28).pre s) :
    Verified target (Impl.EcKey.Compressed.X86.compress c) (I.compressPublicKeyContract abi 28) := by
  have himp := compress_implies I hsig
  have hsat := himp.sat_left
  have localSat : ∃ s, (compressContract c.C).pre s := by
    obtain ⟨s, hs⟩ := hsat
    refine ⟨s.withRegions (codecRd (2 * I.curve.len + 1) s) (codecWr (I.curve.len + 1) s), ?_⟩
    rw [hC]
    exact codecWide_pre hs
  have localVerified : Verified target (Impl.EcKey.Compressed.X86.compress c) (compressContract I.curve) := by
    rw [← hC]
    exact Verified.of_correct (compress_correct c hc hsp) hct (.refl localSat)
  apply Verified.of_implies (Verified.narrowTo localVerified
    (codecRd (2 * I.curve.len + 1)) (codecWr (I.curve.len + 1))
    (fun _ h => codecWide_pre h) ?_ ?_ ?_ ?_ hsat) himp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecRd, codecWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [compressContract, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [compressContract, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.EcKey.Compressed.X86
