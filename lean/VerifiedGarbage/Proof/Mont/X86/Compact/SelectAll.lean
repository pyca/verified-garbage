module

import VerifiedGarbage.Proof.Mont.X86.Compact.Length
import VerifiedGarbage.Proof.Mont.X86.Compact.Select
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
import VerifiedGarbage.Proof.Mont.X86.Rt.Csub

/-! # Final conditional subtraction in the compact prepared result -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem selectAll_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws t W L) (ha : Args t W L A) (base : (A 0).toNat = W.toNat)
    {N S o : Nat} (width : w32 t.mem W 48 * 8 = 4 * N)
    (headerFit : 128 ≤ L) (outIndex : (A 2).toNat < 8)
    (outPtr : w32 t.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32)
    (scratchFit : S + Compact.accOff + 8 * N + 4 ≤ L)
    (outFit : o + 4 * N ≤ L)
    (outScratch : o + 4 * N ≤ S ∨ S + Compact.accOff + 8 * N + 4 ≤ o)
    (hebp : PtrAt t W .ebp (S + Compact.accOff + 8 * N)) {c : Bool}
    (borrow : t.gpr .ecx = cmask c) :
    WP isa (.seq (.block Rt.mask) Compact.select) t fun u =>
      Outside W o (4 * N) t.mem u.mem ∧
      val32 u.mem W o N = val32 t.mem W
        (if !(decide (w32 t.mem W (S + Compact.accOff + 8 * N) < c.toNat))
        then o else S + Compact.accOff + 4 * N) N ∧ Keeps clob7 t u := by
  have nowrap := hw.nowrap
  refine WP.seq (WP.mono (mask_ok hw hebp scratchFit borrow) fun a ⟨mask, M, K⟩ => ?_)
  have args := ha.of_keeps K (by decide) (by rw [M]; exact Outs.refl _ _ _)
  unfold Compact.select
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (WP.block_append (WP.mono (lenTimes_ok (hw.of_keeps K) args base (by omega_arith) 0)
    fun b ⟨len, Mb, Kb⟩ => ?_))
  refine wp_subS rfl fun d D _ => ?_
  have Kd : Keeps [.eax, .edx, .ebp] a d := (Kb.mono (by decide)).widen D.keeps
  have Md : d.mem = t.mem := D.mem.trans (Mb.trans M)
  have argsD := args.of_keeps Kd (by decide)
    (by rw [D.mem, Mb]; exact Outs.refl _ _ _)
  refine WP.block_append (WP.mono (operandPtr_ok ((hw.of_keeps K).of_keeps Kd) argsD base
    (r := .esi) (t := .edx) (i := 2) (by decide) (by decide) (by decide) (by omega_arith))
    fun e ⟨P, Me, Ke⟩ => ?_)
  have argsE := argsD.of_keeps Ke (by decide) (by rw [Me]; exact Outs.refl _ _ _)
  refine WP.mono (lenTimes_ok (((hw.of_keeps K).of_keeps Kd).of_keeps Ke) argsE base (by omega_arith) 0)
    fun f ⟨Lf, Mf, Kf⟩ => ?_
  have Kaf : Keeps [.eax, .edx, .ebp, .esi, .edi] a f :=
    ((Kd.mono (by decide)).widen Ke).widen Kf
  have Mft : f.mem = t.mem := Mf.trans (Me.trans Md)
  have lenB : (b.gpr .eax).toNat = 4 * N := by
    rw [len, M, show 2 ^ (3 + 0) = 8 from rfl, width, Nat.mod_eq_of_lt hN32]
  have bpB : PtrAt b W .ebp (S + Compact.accOff + 8 * N) := by
    rw [PtrAt, Kb.1 .ebp (by decide), K.1 .ebp (by decide)]; exact hebp
  have bpD : PtrAt d W .ebp (S + Compact.accOff + 4 * N) := by
    rw [PtrAt, D.gpr, ptr_sub bpB _ (by rw [lenB]; omega_arith), lenB]
    congr 2 <;> omega_arith
  have bpF : PtrAt f W .ebp (S + Compact.accOff + 4 * N) := by
    rw [PtrAt, Kf.1 .ebp (by decide), Ke.1 .ebp (by decide)]; exact bpD
  have siF : PtrAt f W .esi o := by
    rw [PtrAt, Kf.1 .esi (by decide), P, Md]; exact outPtr
  have diF : (f.gpr .edi).toNat = 4 * N := by
    rw [Lf, Me, Md, show 2 ^ (3 + 0) = 8 from rfl, width, Nat.mod_eq_of_lt hN32]
  have maskF : f.gpr .ecx = if !(decide (w32 t.mem W (S + Compact.accOff + 8 * N) < c.toNat))
      then BitVec.allOnes 32 else 0 := by
    rw [Kaf.1 .ecx (by decide)]; exact mask
  refine WP.mono (selLoop_ok (hw.of_keeps ((K.mono (rs' := clob7) (by decide)).trans (Kaf.mono (by decide))))
    _ hN (by omega_arith) outFit (by omega_arith) bpF siF diF maskF) ?_
  rintro u ⟨O, V, Ku⟩
  refine ⟨?_, ?_, ((K.mono (rs' := clob7) (by decide)).trans (Kaf.mono (by decide))).trans (Ku.mono (by decide))⟩
  · rw [Mft] at O; exact O
  · rw [V, Mft]

end VG.Proof.Mont.X86.Compact
