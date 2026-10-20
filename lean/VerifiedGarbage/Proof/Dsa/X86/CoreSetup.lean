module

public import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Reinitializing the shared context from a DSA modulus -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem setupRanges_whole {n : Nat} {base : Addr} {s t : State}
    (O : Outs base (setupRanges n) s.mem t.mem) : Outside base 0 (contextBytes n) s.mem t.mem := by
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have b3 := slot_bound (n := n) (i := 3) (by decide)
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  simp only [stride] at b1 b2 b3 b4
  intro x hx
  apply O x
  intro r hr
  simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega

theorem coreSetup_ok {s : State} {base : Addr} {size len n m : Nat} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (hr : ReadableComponent s base (.input modulus) len)
    (hd : Region.Disjoint ⟨(pointerValue base s (.input modulus)).setWidth 64, len⟩ ⟨off base (slot n 0), 8 * n⟩)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Core.setup len modulus) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps powerClob s t := by
  have hn0 : 0 < n := by omega
  have hn48 : n ≤ 48 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsaved : 8256 ≤ size := hz
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  unfold Core.setup
  rw [← hn]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (by omega) h4 (by omega) hw4 hr hd)
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  refine WP.mono (contextSetup_ok (hs.of_keeps Ku (by decide)) hn0 (by omega) (by omega)
    (Vu.trans hm) hm1 hodd) fun t ⟨Ct, One, R2, Ot, Kt⟩ => ?_
  refine ⟨Ct, One, R2, ?_, (Ku.mono (by decide)).trans Kt⟩
  exact (Ou.mono (o' := 0) (n' := contextBytes n) (by omega) (by omega)).trans (setupRanges_whole Ot)

end VG.Proof.Dsa.X86
