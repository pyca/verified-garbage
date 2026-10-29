module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
/-! # Complete generator range checks from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Rsa VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorFromFrame_ok {s : State} {B F S : Addr} {Z len : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} {pb xb : List Byte} (result : Bool)
    (L : Lay s F S) (R : Rep s.mem F S V W) (hs : Scr s B Z)
    (hB : W 5 + BitVec.ofNat 64 arithmetic = B)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (hZ : slot (len / 8) 16 ≤ Z)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (hframe : ∀ k < 37, ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i))
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨B, Z⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨B, Z⟩)
    (sp : Src s B Z (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sx : Src s B Z (if result then off (W 5) Impl.Dsa.Generation.Layout.g else W 21) xb)
    (hp : pb.length = len) (hx : xb.length = len)
    (hodd : result = false → Spec.Rsa.os2ip pb % 2 = 1)
    (hresult : result = true → Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame len result) s fun t =>
      t.gpr .rax = mask (decide (if result then 1 < Spec.Rsa.os2ip xb
        else 1 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb - 1)) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧ Ws t B Z (len / 8) ∧
      Frame [⟨B, Z⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hb : 2 ≤ len / 8 ∧ len / 8 < 2 ^ 24 ∧ 1 ≤ len ∧ len < 2 ^ 31 ∧ len ≤ 8 * (len / 8) := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  unfold Impl.Dsa.X86_64.Generation.generatorRangeFromFrame
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceBase_ok L R hB) fun u ⟨hdi, hm, ku⟩ => ?_)
  have spu := sp.congrK (fun a _ => by rw [hm]) ku
  have sxu := sx.congrK (fun a _ => by rw [hm]) ku
  refine WP.seq (WP.mono (workspace_ok (hs.congr ku.2.2) hdi hZ hb.1 hb.2.1)
    fun v ⟨hv, _, fv, kv⟩ => ?_)
  have bounds : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  refine WP.mono (generatorCheck_ok result hv hb.2.2.2.1
    ((kv.gpr (by decide)).trans ((ku.gpr (by decide)).trans L.rsp))
    (fun k hk => by rw [kv.2.1, kv.2.2, ku.2.1, ku.2.2]; exact L.ld (by unfold frameBytes; omega))
    (fun k hk => by rw [frame_word_of_workspace fv bounds (hframe k hk), hm]; exact R.fr k hk)
    hsep (spu.congrK (InScr.of_frm fv bounds) kv) (sxu.congrK (InScr.of_frm fv bounds) kv)
    hp hx hb.2.2.1 hb.2.2.2.2 hodd hresult) fun t ⟨hr, ht, ft, kt⟩ => ?_
  have allk := (ku.trans kv).trans kt
  have ff : Frame [⟨B, Z⟩] s.mem t.mem := by
    intro a ha
    have hn := ha ⟨B, Z⟩ (by simp)
    change ¬ ofs B a < Z at hn
    rw [ft a (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> right
      · exact Nat.le_trans hz (by omega)
      · exact Nat.le_trans (hZ.trans' (slot_lt (by decide : 0 < 16))) (by omega)
      · exact Nat.le_trans (hZ.trans' (slot_lt (by decide : 1 < 16))) (by omega)),
      fv a (fun r hr => Or.inr (Nat.le_trans (bounds r hr) (by omega))), hm]
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  exact ⟨hr, lay_of_rep L R Rt rfl (allk.gpr (by decide)) allk.2.2, Rt, ht, ff, allk.mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
