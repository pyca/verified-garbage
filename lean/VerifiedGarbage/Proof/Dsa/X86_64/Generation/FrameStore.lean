module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.Scan
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-! # Initialize frame words before the search scratch pointer has been stored -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameWord_write {F : Addr} {k : Nat} (hk : k < nW) (m : Mem) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m.writeW (off F (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega))

theorem frameStore_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < nW) (r : Reg) :
    WP isa (.block [.store (sp (8 * k)) r]) s fun t =>
      Rep t.mem F S V (upd W k (s.gpr r)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (s.gpr r))
    (by xrun [ea_sp, hsp, hw]) rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem initialRep (m : Mem) (F S : Addr) :
    Rep m F S (fun i => m (off S i)) (fun k => word m F (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Dsa.X86_64.Generation
