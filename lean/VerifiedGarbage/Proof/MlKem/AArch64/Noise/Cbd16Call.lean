module

import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Loop
public import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

/-! # Calling `vg_mlkem16_cbd2` -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem16_cbd2(b, f)`: `SamplePolyCBD₂` of the 128 bytes at `b`, with 16-bit
coefficients at `f`. -/
theorem cbd16_call {s : State} {b f : Addr} (h0 : s.gpr .x0 = b) (h1 : s.gpr .x1 = f)
    (hd : Region.Disjoint ⟨b, 128⟩ ⟨f, 512⟩) (hc : Covers [⟨b, 128⟩, ⟨f, 512⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨f, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) → Q s') :
    WP isa (.call "vg_mlkem16_cbd2" Cbd16.code16) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (entry s).trans h1
  refine WP.callV (k := cbd2_16AArch64) Cbd16W.correct (rd := [⟨b, 128⟩]) (wr := [⟨f, 512⟩]) ?_ hc hw ?_
  · simp only [cbd2_16AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hd⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [cbd2_16AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

/-- A region's prefix is covered where the region is. -/
theorem covers_prefix {b : Addr} {l l' : Nat} {X : List Region} (hl : l ≤ l') (h : Covers [⟨b, l'⟩] X) :
    Covers [⟨b, l⟩] X := fun a n ⟨r, hr, hc⟩ => by
  rw [List.mem_singleton.mp hr] at hc
  exact h a n ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- `cbdCall w16`: `SamplePolyCBD₂` of the 128 bytes at `b` into the polynomial at `f`, with
16-bit coefficients (`w16`) or 32-bit ones. -/
theorem cbdW_call {w16 : Bool} {s : State} {b f : Addr} (h0 : s.gpr .x0 = b) (h1 : s.gpr .x1 = f)
    (hd : Region.Disjoint ⟨b, 128⟩ ⟨f, 1024⟩) (hc : Covers [⟨b, 128⟩, ⟨f, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨f, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' →
      PolyIsW (cw w16) s'.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) → Q s') :
    WP isa (Noise.cbdCall w16) s Q := by
  cases w16
  · exact cbd2_call h0 h1 hd hc hw hQ
  · refine cbd16_call h0 h1 (hd.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
      (Covers.cons (Covers.head hc) (covers_prefix (by decide : 512 ≤ 1024) (Covers.tail hc)))
      (covers_prefix (by decide : 512 ≤ 1024) hw)
      fun s' k p => hQ s' (Kept.sub k fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide : 512 ≤ 1024)⟩) p

end VG.Proof.MlKem.AArch64
