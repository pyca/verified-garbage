module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Dsa.X86.LoadSlot

/-! # Verified component loading for DSA arithmetic calls -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure ReadableComponent (s : State) (base : Addr) (p : Pointer) (len : Nat) : Prop where
  fits : (pointerValue base s p).toNat + len ≤ 2 ^ 32
  reads : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr)
    ((pointerValue base s p).setWidth 64 + BitVec.ofNat 64 d) 4

theorem coreLoad_ok {s : State} {base : Addr} {size len n out : Nat} {p : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (ho : out + 8 * n ≤ size) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ReadableComponent s base p len)
    (hd : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (.block (Core.load n len out p)) s fun t =>
      wordsVal t.mem base out n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len) ∧
      Keeps [.esi, .eax] s t ∧ Outside base out (8 * n) s.mem t.mem := by
  unfold Core.load
  refine WP.block_append (WP.mono (pointer_ok hs hz p) fun u ⟨Pu, Ku, Mu⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine WP.mono (loadComponent_ok hu ho (by rw [Pu]; exact hr.fits) h4 hlen
    (by intro d h; rw [Pu, Ku.2.1, Ku.2.2]; exact hr.reads d h)
    (by rw [Pu]; exact hd)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Ku.mono (by decide)).widen Kt, ?_⟩
  · rw [Vt, Mu, Pu]
  · rw [Mu] at Ot
    exact Ot

theorem coreLoadSlot_ok {s : State} {base : Addr} {size len n m i : Nat} {p : Pointer}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hi : i < 9) (hi0 : i ≠ 0) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ReadableComponent s base p len)
    (hd : Region.Disjoint ⟨(pointerValue base s p).setWidth 64, len⟩ ⟨off base (slot n i), 8 * n⟩) :
    WP isa (.block (Core.load n len (slot n i) p)) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n i) n = Spec.Dsa.decodeBE
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s p).setWidth 64) len) ∧
      Keeps [.esi, .eax] s t ∧ Outside base (slot n i) (8 * n) s.mem t.mem := by
  have bound := slot_bound (n := n) hi
  have sep := slot_sep (n := n) hi0
  simp only [stride] at bound sep
  refine WP.mono (coreLoad_ok h.scr hz (by have := h.size_le; omega) h4 hlen hr hd)
    fun t ⟨V, K, O⟩ => ⟨?_, V, K, O⟩
  apply h.outside_keep K (by decide) (by decide) O
  · omega
  · have := slot_header n i
    omega

end VG.Proof.Dsa.X86
