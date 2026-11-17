module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Bignum.X86.PrecomputeFailure`, which this module and modules that import it used -/

section

/-! # Invalid moduli clear every precomputation word -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputeFailure_ok {s : State} {out : BitVec 32} {n : Nat}
    (positive : 0 < n) (bound : 8 * n < 2 ^ 32) (fit : out.toNat + 8 * n ≤ 2 ^ 32)
    (P : readSrc s (.mem (PublicFn.argument 0)) = some out)
    (C : readSrc s (.mem (PublicFn.argument 1)) = some (BitVec.ofNat 32 n))
    (write : InRegions s.wr (byteAddr out) (8 * n)) :
    WP isa PrecomputeFn.failure s fun t =>
      t.gpr .eax = 0 ∧ Spec.Rsa.wordsAt t.mem (byteAddr out) n = List.replicate n 0 ∧
      Outside (byteAddr out) 0 (8 * n) s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  unfold PrecomputeFn.failure
  refine WP.seq (wp_movS P fun u A _ => ?_)
  refine wp_movS (by rw [argument_keep A.keeps (by decide) A.mem 1]; exact C) fun v B _ => ?_
  refine wp_addS rfl fun w D _ => ?_
  refine wp_addS rfl fun x E _ => ?_
  refine wp_addS rfl fun y F _ => ?_
  refine wp_movS rfl fun z G _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx, .eax] s z :=
    (((((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen G.keeps
  have M : z.mem = s.mem := G.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (B.mem.trans A.mem))))
  have count : z.gpr .ecx = BitVec.ofNat 32 (8 * n) := by
    rw [G.other .ecx (by decide), F.gpr, E.gpr, D.gpr, B.gpr]
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega_using []
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok (by omega_using [positive]) bound fit
    (by rw [G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), B.other .esi (by decide), A.gpr]) count G.gpr ?_)
    fun t ⟨V, Z, O, T⟩ => ?_
  · intro i hi
    rw [K.2.2]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by unfold byteAddr; rw [Mem.sub_ofNat_toNat _ (by omega_using [bound, hi])]; omega_using [hi])⟩
  · refine ⟨Z, ?_, M ▸ O, K.trans (T.mono (by decide))⟩
    apply wordsAt_zero_read
    apply read_zero_bytes
    intro j hj
    have h := congrArg (fun bs : List Byte => bs[j]?) V
    simpa only [byteAddr, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hj,
      Option.map_some, List.getElem?_replicate, ite_eq_left hj, Option.some.injEq] using h

end VG.Proof.Bignum.X86

end

end

/-! # Public precomputation succeeds exactly for valid moduli -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputeFailure_post {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s)
    (invalid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = false) :
    WP isa PrecomputeFn.failure s fun t => PrecomputePost base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have twice : 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len := by omega_using []
  refine WP.mono (precomputeFailure_ok (n := 2 * Spec.Rsa.modulusWords len) (by omega_using [dims]) (by omega_using [dims])
    (by simpa only [twice] using h.outFit) ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.preLen]; exact (h.stack 1 (by decide)).readSrc)
    (by simpa only [twice] using h.outWrite)) fun t ⟨B, Y, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · simp only [Spec.Rsa.publicPrecompute, bytesAt_length, invalid, Bool.false_eq_true, ite_false]
    exact ⟨B, Y⟩
  · have F := outside_frame O (by omega_using [dims])
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [twice])

theorem precomputeBody_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PrecomputeInputs base bytes len args s) :
    WP isa PrecomputeFn.body s fun t => PrecomputePost base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PrecomputeFn.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower h.upper (by rw [P]; exact h.nFit)
    (by rw [P, K.2.1, K.2.2]; exact h.nRead) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Ms : v.mem = s.mem := Mv.trans M
  have Ks : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
  have sp : v.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len) Z ?_ ?_
  · intro valid
    refine WP.mono (precomputeValid_ok hv (by rw [Ms]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Ms, sp] using R, Ks.trans T⟩
  · intro invalid
    refine WP.mono (precomputeFailure_post hv (by rw [Ms]; exact invalid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Ms, sp] using R, Ks.trans T⟩

end VG.Proof.Bignum.X86.PublicContext
