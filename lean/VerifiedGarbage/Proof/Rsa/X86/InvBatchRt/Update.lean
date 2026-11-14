module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.State
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # Sequences of a batch, regrouped -/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff, WP.seq_iff] at h
  exact WP.seq_iff.mpr (WP.mono h fun _ hu => WP.seq_iff.mpr hu)

end VG.Proof.Rsa.X86.InvBatchRt
