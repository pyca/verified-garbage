module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on AArch64: the table of `vg_mlkem16_ntt`, as its callers hold it

`FastTable`: the table at its symbol, readable and apart from what the
caller writes; `FastReady`: what a call on the polynomial at `f` needs of
it.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Proof.MlKem
open VG.Impl.MlKem.AArch64.Ntt16.Fast (name tab tabWords)
open VG.Proof.MlKem.AArch64.Ntt16 (hw4)

theorem tabWords_length : tabWords.length = 116 := by
  rw [tabWords, tab.lit_eq]; decide +kernel

theorem tabWords_get : ∀ i < 116, tabWords.getD i 0 = hw4 tab i := by
  rw [tabWords, tab.lit_eq]; decide +kernel

/-- The region of the table. -/
abbrev fastRegion (s : State) : Region := ⟨s.syms name, 928⟩

def FastTable (s : State) : Prop :=
  (∀ i < 116, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = hw4 tab i) ∧
    Covers [fastRegion s] (s.rd ++ s.wr) ∧ ∀ r ∈ s.wr, (fastRegion s).Disjoint r

structure FastReady (s : State) (f w : Addr) : Prop where
  table : ∀ i < 116, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = hw4 tab i
  readable : Covers [fastRegion s] (s.rd ++ s.wr)
  output : (polyRegion f).Disjoint (fastRegion s)
  scratch : (polyRegion w).Disjoint (fastRegion s)

theorem FastTable.apart {s : State} (h : FastTable s) {r : Region} (hc : Covers [r] s.wr) :
    (fastRegion s).Disjoint r := by
  intro addr ha hb
  obtain ⟨q, hq, hh⟩ := hc addr 1 ⟨r, by simp, hb⟩
  exact h.2.2 q hq addr ha hh

theorem FastTable.ready {s : State} (h : FastTable s) {f w : Addr}
    (hc : Covers [polyRegion f, polyRegion w] s.wr) : FastReady s f w := by
  refine ⟨h.1, h.2.1, (h.apart fun a n hh => hc a n ?_).symm, (h.apart fun a n hh => hc a n ?_).symm⟩
  · obtain ⟨r, hr, ha⟩ := hh
    rw [List.mem_singleton.mp hr] at ha
    exact ⟨polyRegion f, by simp, ha⟩
  · obtain ⟨r, hr, ha⟩ := hh
    rw [List.mem_singleton.mp hr] at ha
    exact ⟨polyRegion w, by simp, ha⟩

theorem FastTable.frameFar {s t : State} {rs : List Region} (h : FastTable s) (hs : t.syms = s.syms)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (fastRegion s).Disjoint r) : FastTable t := by
  refine ⟨?_, by simpa only [fastRegion, hs, hr, hw] using h.2.1, by simpa only [fastRegion, hs, hw] using h.2.2⟩
  intro i hi
  rw [hs, hf.readW (r := fastRegion s) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
  exact h.1 i hi

theorem FastTable.frame {s t : State} {rs : List Region} (h : FastTable s) (hs : t.syms = s.syms)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame rs s.mem t.mem) (hc : Covers rs s.wr) :
    FastTable t :=
  h.frameFar hs hr hw hf fun r hh =>
    h.apart fun a n ⟨q, hq, ha⟩ => hc a n ⟨q, by rw [List.mem_singleton.mp hq]; exact hh, ha⟩

theorem FastReady.frame {s t : State} {f w : Addr} {rs : List Region} (h : FastReady s f w)
    (hs : t.syms = s.syms) (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (fastRegion s).Disjoint r) : FastReady t f w := by
  refine ⟨?_, by simpa only [fastRegion, hs, hr, hw] using h.readable, by simpa only [fastRegion, hs] using h.output,
    by simpa only [fastRegion, hs] using h.scratch⟩
  intro i hi
  rw [hs, hf.readW (r := fastRegion s) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
  exact h.table i hi

end VG.Proof.MlKem.AArch64.NttR
