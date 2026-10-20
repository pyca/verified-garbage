module

public import VerifiedGarbage.Proof.MillerRabin.X86.ScanFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Mask
import VerifiedGarbage.Proof.MillerRabin.X86.Select
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.MillerRabin.X86.Context

/-! # One fixed-address scan step only replaces the matching digit -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem scanEntry_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 16) :
    WP isa (.seq (.block (maskIndex j)) (selectEntry j)) s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j
          then aTable + j else aX)) g.words ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  refine WP.seq (WP.mono (maskIndex_ok v C j index) fun a ⟨Mask, O, K, Ca⟩ => ?_)
  refine WP.mono (selectEntry_ok v Ca j index
    (decide ((s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j)) (by simpa using Mask)) ?_
  rintro t ⟨V, Ot, Kt, Ct⟩
  have header := v.arrayHeader aX
  have tableHeader := v.arrayHeader (aTable + j)
  have fitX := v.arrayFit (j := aX) (by decide)
  have fitT := v.arrayFit (j := aTable + j) (by unfold aTable; omega)
  refine ⟨?_, (Outs.of_outside O (by simp [scanWrites])).trans
    (Outs.of_outside Ot (by simp [scanWrites])), (K.mono (by decide)).trans Kt, Ct⟩
  by_cases eq : (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j
  · simp only [eq, decide_true, ↓reduceIte] at V ⊢
    rw [V, O.val32 (by unfold sEq1; omega) (by have := C.ws.nowrap; omega)]
  · simp only [eq, decide_false, Bool.false_eq_true, ↓reduceIte] at V ⊢
    rw [V, O.val32 (by unfold sEq1; omega) (by have := C.ws.nowrap; omega)]

end VG.Proof.MillerRabin.X86
