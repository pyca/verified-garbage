module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

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
    omega
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok (by omega) bound fit
    (by rw [G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), B.other .esi (by decide), A.gpr]) count G.gpr ?_)
    fun t ⟨V, Z, O, T⟩ => ?_
  · intro i hi
    rw [K.2.2]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by unfold byteAddr; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · refine ⟨Z, ?_, M ▸ O, K.trans (T.mono (by decide))⟩
    apply wordsAt_zero_read
    apply read_zero_bytes
    intro j hj
    have h := congrArg (fun bs : List Byte => bs[j]?) V
    simpa only [byteAddr, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hj,
      Option.map_some, List.getElem?_replicate, ite_eq_left hj, Option.some.injEq] using h

end VG.Proof.Bignum.X86
