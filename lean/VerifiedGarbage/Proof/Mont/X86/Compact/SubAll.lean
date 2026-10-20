module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
import VerifiedGarbage.Proof.Mont.X86.Compact.Length
import VerifiedGarbage.Proof.Mont.X86.Compact.Sub
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

/-! # Subtract the modulus directly into the prepared result -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem subAll_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws t W L) (ha : Args t W L A) (base : (A 0).toNat = W.toNat)
    {N S mo a b o : Nat} (V : Metadata t.mem W A N S mo a b)
    (headerFit : 128 ≤ L) (outIndex : (A 2).toNat < 8)
    (outPtr : w32 t.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32)
    (scratchFit : S + Compact.accOff + 8 * N + 4 ≤ L)
    (modFit : mo + 4 * N ≤ L) (outFit : o + 4 * N ≤ L)
    (outHeader : 128 ≤ o)
    (outScratch : o + 4 * N ≤ S ∨ S + Compact.accOff + 8 * N + 4 ≤ o)
    (outMod : o = mo ∨ o + 4 * N ≤ mo ∨ mo + 4 * N ≤ o)
    (hebp : PtrAt t W .ebp (S + Compact.accOff + 4 * N)) :
    WP isa Compact.subM t fun u =>
      Outside W o (4 * N) t.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem W o N + val32 t.mem W mo N =
          val32 t.mem W (S + Compact.accOff + 4 * N) N + 2 ^ (32 * N) * c.toNat) ∧
      PtrAt u W .ebp (S + Compact.accOff + 8 * N) ∧
      PtrAt u W .edi S ∧ Keeps clob7 t u := by
  have nowrap := hw.nowrap
  unfold Compact.subM
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (arrayPtr_ok hw ha base (r := .esi) (j := 0) (by omega))
    fun s₁ ⟨p₁, m₁, K₁⟩ => ?_))
  have ha₁ := ha.of_keeps K₁ (by decide) (by rw [m₁]; exact Outs.refl _ _ _)
  refine WP.block_append (WP.mono (operandPtr_ok (hw.of_keeps K₁) ha₁ base
    (r := .ebx) (t := .edx) (i := 2) (by decide) (by decide) (by decide) (by omega))
    fun s₂ ⟨p₂, m₂, K₂⟩ => ?_)
  have ha₂ := ha₁.of_keeps K₂ (by decide) (by rw [m₂]; exact Outs.refl _ _ _)
  refine WP.block_append (WP.mono (lenTimes_ok ((hw.of_keeps K₁).of_keeps K₂) ha₂ base (by omega) 0)
    fun s₃ ⟨l₃, m₃, K₃⟩ => ?_)
  refine wp_movS rfl fun s₄ B _ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi] t s₄ :=
    (((K₁.mono (by decide)).widen K₂).widen K₃).widen B.keeps
  have M : s₄.mem = t.mem := B.mem.trans (m₃.trans (m₂.trans m₁))
  have bp : PtrAt s₄ W .ebp (S + Compact.accOff + 4 * N) := by
    rw [PtrAt, K.1 .ebp (by decide)]; exact hebp
  have si : PtrAt s₄ W .esi mo := by
    rw [PtrAt, B.other .esi (by decide), K₃.1 .esi (by decide), K₂.1 .esi (by decide), p₁]
    exact V.modulus
  have bx : PtrAt s₄ W .ebx o := by
    rw [PtrAt, B.other .ebx (by decide), K₃.1 .ebx (by decide), p₂, m₁]
    exact outPtr
  have di : (s₄.gpr .edi).toNat = 4 * N := by
    rw [B.other .edi (by decide), l₃, m₂, m₁, show 2 ^ (3 + 0) = 8 from rfl,
      V.width, Nat.mod_eq_of_lt hN32]
  refine WP.seq (WP.mono (subLoop_ok (hw.of_keeps K) hN (by omega) modFit outFit
    (by omega) outMod bp si bx di B.gpr) fun u₁ ⟨O, Q, P, K'⟩ => ?_)
  have Kt : Keeps clob7 t u₁ := (K.mono (by decide)).trans K'
  have Ot : Outside W o (4 * N) t.mem u₁.mem := by rw [← M]; exact O
  have args := ha.of_keeps Kt (by decide)
    (Outs.of_outside (Ot.mono (by omega) (by omega)) (List.mem_singleton_self _))
  unfold Compact.scratchPtr
  refine WP.mono (arrayPtr_ok (hw.of_keeps Kt) args base (r := .edi) (j := 2) (by omega)) ?_
  rintro u ⟨ptr, mem, keep⟩
  refine ⟨?_, ?_, ?_, ?_, Kt.trans (keep.mono (by decide))⟩
  · rw [mem]; exact Ot
  · obtain ⟨c, C, q⟩ := Q
    refine ⟨c, by rw [keep.1 .ecx (by decide)]; exact C, ?_⟩
    rw [mem]; rw [M] at q; exact q
  · rw [PtrAt, keep.1 .ebp (by decide)]
    rw [show S + Compact.accOff + 8 * N = S + Compact.accOff + 4 * N + 4 * N by omega]
    exact P
  · rw [PtrAt, ptr]
    exact (V.keep Ot outHeader).scratch

end VG.Proof.Mont.X86.Compact
