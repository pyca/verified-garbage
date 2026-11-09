module

import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Schedule
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64
open VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Spec.ChaCha20 (innerBlock)

theorem parallelRound_ok {sve : Bool} {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hc : VG.Proof.ChaCha20.AArch64.Holds v s) :
    WP isa (parallelRound sve) s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => innerBlock (vs j)) u ∧ VG.Proof.ChaCha20.AArch64.Holds (innerBlock v) u ∧
      VG.Proof.ChaCha20.AArch64.RI (innerBlock v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  refine (Scheduled.ops_ok roundOps Scheduled.roundOps_valid hn ht hc).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  simp only [roundOps, VG.Proof.ChaCha20.AArch64.Neon4.innerBlock_eq] at hu hr
  exact ⟨hu,hr.holds,hr,hsp,hut⟩

theorem rounds_ok {sve : Bool} {vs : Nat → CState} {v : CState} {s : State}
    (hn : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hc : VG.Proof.ChaCha20.AArch64.Holds v s) :
    ∀ n, WP isa (rounds sve n) s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (vs j)) u ∧
      VG.Proof.ChaCha20.AArch64.RI (Nat.repeat innerBlock n v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  | 0 => WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | n + 1 => by
    apply WP.seq
    refine (rounds_ok hn ht hc n).mono fun a ⟨ha,hca,hsp,hat⟩ => ?_
    refine (parallelRound_ok ha hat hca.holds).mono fun b ⟨hb,_,hab,hsp',hbt⟩ =>
      ⟨hb,⟨hab.holds,hab.mem.trans hca.mem,hab.rd.trans hca.rd,hab.wr.trans hca.wr,
        fun r hr => (hab.keep r hr).trans (hca.keep r hr)⟩,hsp'.trans hsp,hbt⟩

end VG.Proof.ChaCha20.AArch64.Mixed5
