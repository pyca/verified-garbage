module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Q
import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCT
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Two runs of q from the same seed leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Before a copy from the tape at the state word `w`: its value. -/
def CopyIn (E : Env) (w : Nat) (x : BitVec 32) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base w) 32 = x

/-- A copy from a pointer in a state word: the pointer is the same in both
runs. -/
theorem copyIn_ct {E : Env} (v : E.Valid) {w : Nat} (hw : w + 4 ≤ 73728) (dst n : Nat) :
    RelCT isa (Both (CopyIn E w)) (copyTo [.mov .esi (.mem (sc w))] dst n) fun _ _ => True := by
  have sz := v.size_ge
  unfold copyTo
  refine RelCT.seq (both_post (Ψ := fun x t => ∀ r ∈ [Reg.esp, .edi, .esi, .ebx, .ecx],
      t.gpr r = if r = .esi then x else if r = .ebx then E.base.setWidth 32 + BitVec.ofNat 32 dst
        else if r = .ecx then BitVec.ofNat 32 n else baseVal E r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1)
      (tcheckE _ _ (.block ([.mov .esi (.mem (sc 0))] ++ scr .ebx 0 ++ [.mov .ecx (.imm (BitVec.ofNat 32 0))]))
        (by kernel_rfl) (by decide +kernel) (by decide +kernel))) fun x s h => ?_)
    (both_agree [.esp, .edi, .esi, .ebx, .ecx] _ (fun _ _ h => h)
      (tcheck _ _ (by decide +kernel)))
  simp only [List.cons_append, List.nil_append, scr]
  refine ld_ok h.1.scr (d := w) (by omega) fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_addi fun t₃ u₃ =>
    wp_movi fun t₄ u₄ => WP.block_nil ?_
  have pins := base_pins h.1
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact pins _ (by simp)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact pins _ (by simp)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.2]; rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.1.edi]; rfl
  · rw [u₄.gpr]; rfl

theorem copyS_erase (a b n : Nat) : Code.erase (copyS a b n) = Code.erase (copyS 0 0 1) := rfl

/-- Before q of seed `a.1`, with the witness cursor at `a.2`. -/
def QIn (E : Env) (a : Nat × Nat) (s : State) : Prop :=
  Base E s ∧ (a.1 + 1) * E.qLen ≤ E.seedsLen ∧
    s.mem.readW (off E.base fSeed) 32 = (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32 ∧
    s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 a.2 ∧ a.2 ≤ E.witLen

theorem qAt_pins {E : Env} {g : Geo} {s t : State} (Q : QAt E g s t) : ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r :=
  base_pins Q.base

theorem qPart_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (QIn E)) g.qPart fun _ _ => True := by
  have sz := v.size_ge
  have q20 : 20 ≤ g.qLen := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have q32 : g.qLen ≤ 32 := by rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  unfold Geo.qPart
  simp only [seqs]
  -- The seed in the block.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sState + g.H.N)) g.qLen = chunk E a.1)
    (both_map (fun a => (E.seeds + BitVec.ofNat 64 (a.1 * E.qLen)).setWidth 32) (fun a s h => ⟨h.1, h.2.2.1⟩)
      (copyIn_ct v (w := fSeed) (by decide) _ _))
    fun a s h => WP.mono (q1_ok G v hq h.1 h.2.1 h.2.2.1) fun t h' => ⟨s, h, h'⟩) ?_
  -- Its hash.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N = Spec.Dsa.seedHash (8 * g.qLen) (chunk E a.1))
    (both_map (fun _ => ()) (fun a t h => by obtain ⟨s, _, Q, _⟩ := h; exact Q.base) (hash_ct G v _))
    fun a t h => by
      obtain ⟨s, hs, Q, S⟩ := h
      exact WP.mono (q2_ok G v Q S) fun u h' => ⟨s, hs, h'⟩) ?_
  -- q's top and low bits.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen)) g.H.N =
        VG.Proof.Ffdh.ParameterCandidate.shapedOctets (Spec.Dsa.seedHash (8 * g.qLen) (chunk E a.1)) 7)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨s, _, Q, _⟩ := h; exact qAt_pins Q)
      (tcheckE _ _ (.block (orByte 0 0x80 ++ orByte 0 1)) (by kernel_rfl) (by decide +kernel) (by decide +kernel)))
    fun a t h => by
      obtain ⟨s, hs, Q, H⟩ := h
      exact WP.mono (q3_ok G v Q H) fun u h' => ⟨s, hs, h'⟩) ?_
  -- Into the test's working space.
  refine RelCT.seq (both_post (Ψ := fun a t => ∃ s, QIn E a s ∧ QAt E g s t ∧
      Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)) t.mem
        (off E.base sPP) = Spec.Dsa.qCandidate (8 * g.qLen) (chunk E a.1))
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun a t h => by obtain ⟨s, _, Q, _⟩ := h; exact qAt_pins Q)
      (tcheckE _ _ (copyS 0 0 1) (copyS_erase _ _ _) (by decide +kernel) (by decide +kernel)))
    fun a t h => by
      obtain ⟨s, hs, Q, H⟩ := h
      exact WP.mono (q4_ok G v Q H) fun u h' => ⟨s, hs, h'.1, h'.2.1⟩) ?_
  -- The test.
  have lay : (VG.Impl.Dsa.X86.ProbablePrime.layout (8 * g.qLen)).size ≤ 8 * ppWords := by
    rcases G.lengths with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> decide
  refine both_map (fun a => (a.2, Spec.Dsa.qCandidate (8 * g.qLen) (chunk E a.1))) (fun a t h => ?_)
    (test_ct G.qv G.qNoSp G.qStack v lay)
  obtain ⟨s, hs, Q, cval⟩ := h
  have Ap := qPre_apart G v
  have qsh := VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * g.qLen) (by omega) (chunk E a.1)
  refine ⟨Q.base, ?_, hs.2.2.2.2, cval, qsh.1, VG.Proof.Dsa.Generation.qCandidate_bitLength (by omega) _⟩
  rw [Env.Chg.word v Q.chg (by simp only [fUsed, hdr]; omega) (fun o ho => ⟨(Ap o ho).1, by
    simp only [qPre, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> simp only [sState, sHScr, sPk, sPP, fUsed, hdr] <;> omega⟩),
    hs.2.2.2.1]

end VG.Proof.Dsa.X86.Generation
