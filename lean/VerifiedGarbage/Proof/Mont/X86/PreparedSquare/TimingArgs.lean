module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingBase
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
import VerifiedGarbage.Proof.Framework.X86.ArgTaint

/-! # Recover public cdecl argument bytes after a symmetric square -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem prepared_arg_word {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : VG.Proof.Mont.X86.Compact.Args s W L A) {i : Nat} (index : i < 5) :
    s.mem.readW (s.ea (VG.Impl.Mont.X86.Compact.arg i)) 32 = A i := by
  have H := h.read i index
  change s.load32 (s.ea (VG.Impl.Mont.X86.Compact.arg i)) = some (A i) at H
  unfold State.load32 at H
  split at H
  · exact Option.some.inj H
  · cases H

theorem timing_wf_transport {s t : State} (h : VG.X86.Taint.Wf (Compact.timingTaint []) s)
    (sp : t.gpr .esp = s.gpr .esp) (wr : t.wr = s.wr) :
    VG.X86.Taint.Wf (Compact.timingTaint []) t := by
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun _ h => (List.not_mem_nil h).elim,
    ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
  · intro positive
    have H := h.args positive
    simpa only [VG.X86.Taint.argByte, sp, wr] using H
  · simpa only [sp] using h.stk
  · intro p member
    have H := h.frames p member
    simpa only [sp, wr] using H

theorem timing_argument_byte {s : State} (wf : VG.X86.Taint.Wf (Compact.timingTaint []) s)
    {k : Nat} (low : 4 ≤ k) (high : k < 24) :
    VG.X86.Taint.argByte s (16 + k) = s.ea (VG.Impl.Mont.X86.Compact.arg ((k - 4) / 4)) +
      BitVec.ofNat 64 ((k - 4) % 4) := by
  have fit := (wf.args (by change 0 < 24; decide)).1
  change (s.gpr .esp).toNat + 16 + 24 ≤ 2 ^ 32 at fit
  change (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (16 + k) =
    addr (s.gpr .esp) (20 + 4 * ((k - 4) / 4)) + BitVec.ofNat 64 ((k - 4) % 4)
  rw [addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem timing_args_agree {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (S : VG.Proof.Mont.X86.Compact.Args s W L A) (T : VG.Proof.Mont.X86.Compact.Args t W L A)
    (swf : VG.X86.Taint.Wf (Compact.timingTaint []) s)
    (twf : VG.X86.Taint.Wf (Compact.timingTaint []) t) (sp : s.gpr .esp = t.gpr .esp) :
    VG.X86.Taint.Agree (Compact.timingTaint []) s t := by
  refine ⟨⟨?_, fun h => nomatch h⟩, fun h => absurd rfl h, swf, twf,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, ?_⟩
  · intro r hr
    simp only [Compact.timingTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r
    exact sp
  · intro k low high
    change s.mem (VG.X86.Taint.argByte s (16 + k)) = t.mem (VG.X86.Taint.argByte t (16 + k))
    change k < 24 at high
    rw [timing_argument_byte swf low high, timing_argument_byte twf low high,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide)),
      prepared_arg_word S (by omega), prepared_arg_word T (by omega)]

end VG.Proof.Mont.X86.PreparedSquare
