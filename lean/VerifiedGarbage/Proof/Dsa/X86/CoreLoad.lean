module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Verified component loading for DSA arithmetic calls -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- Reassociating a sequence, for a lemma about its first two parts. -/
theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with
  | seq h₁ h₂ => cases h₁ with
    | seq h₁₁ h₁₂ => exact ⟨_, _, .seq h₁₁ (.seq h₁₂ h₂), hq⟩

/-- Every register but `edi` and `esp`: the shape checks' loops use them all. -/
def shapeClob : List Reg := [.esi, .eax, .ebx, .ecx, .edx, .ebp]

/-- What loading a component writes: its pointer and the loop's registers. -/
def loadClob : List Reg := [.esi, .eax, .ebx, .edx, .ebp]

structure ReadableComponent (s : State) (base : Addr) (p : Pointer) (len : Nat) : Prop where
  fits : (pointerValue base s p).toNat + len ≤ 2 ^ 32
  reads : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr)
    ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 d) 4

theorem coreLoad_ok {s : State} {base : Addr} {size len n out : Nat} {p : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (ho : out + 8 * n ≤ size) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base p len)
    (hd : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (Core.load n len out p) s fun t =>
      wordsVal t.mem base out n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len) ∧
      Keeps loadClob s t ∧ Outside base out (8 * n) s.mem t.mem := by
  unfold Core.load
  refine WP.seq (WP.mono (pointer_ok hs hz p) fun u ⟨Pu, Ku, Mu⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine WP.mono (loadComponent_ok hu ho (by rw [Pu]; exact hr.fits) h4 hlen hw4
    (by intro d h; rw [Pu, Ku.2.1, Ku.2.2]; exact hr.reads d h)
    (by rw [Pu]; exact hd)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Ku.mono (by decide)).widen Kt, ?_⟩
  · rw [Vt, Mu, Pu]
  · rw [Mu] at Ot
    exact Ot

theorem coreLoadSlot_ok {s : State} {base : Addr} {size len n m i : Nat} {p : Pointer}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hi : i < 9) (hi0 : i ≠ 0) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base p len)
    (hd : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base (slot n i), 8 * n⟩) :
    WP isa (Core.load n len (slot n i) p) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n i) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len) ∧
      Keeps loadClob s t ∧ Outside base (slot n i) (8 * n) s.mem t.mem := by
  have bound := slot_bound (n := n) hi
  have sep := slot_sep (n := n) hi0
  simp only [stride] at bound sep
  refine WP.mono (coreLoad_ok h.scr hz (by have := h.size_le; omega) h4 hlen hw4 hr hd)
    fun t ⟨V, K, O⟩ => ⟨?_, V, K, O⟩
  apply h.outside_keep K (by decide) (by decide) O
  · omega
  · have := slot_header n i
    omega

end VG.Proof.Dsa.X86
