module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-! # Public child width and workspace selection -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev childCount (offset : Nat) : List Instr :=
  ([.mov .rsi (.reg .rdi), .mov .r12 (.mem (hdr argLen)),
    .alu .add .r12 (.imm 7), .shift .shr .r12 3] : List Instr) ++ Core.enter offset

theorem childCount_ok {s : State} {B : Addr} {Z offset len : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (ho : offset < 2 ^ 31) (hlen : len < 2 ^ 32)
    (hl : word s.mem B (8 * argLen) = BitVec.ofNat 64 len) :
    WP isa (.block (childCount offset)) s fun t =>
      t.gpr .rsi = B ∧ t.gpr .rdi = off B offset ∧ t.gpr .r12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .r12] s t := by
  refine WP.mono (WP.keep [.rsi, .rdi, .r12] (Q := fun t =>
      t.gpr .rsi = B ∧ t.gpr .rdi = off B offset ∧ t.gpr .r12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨⟨hsi, hd, h12, hm⟩, hk⟩ => ⟨hsi, hd, h12, hm, hk⟩
  unfold childCount Core.enter
  simp only [List.cons_append, List.nil_append]
  xrun [State.ea, hdr, hdrOff, hdi, hl, hs.ld (Nat.le_trans (show 8 * argLen + 8 ≤ pWorkspace by decide) hZ),
    shr3_w len hlen, sx_ofNat ho]

end VG.Proof.Dsa.X86_64
