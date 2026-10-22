module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.FastInv
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitFI
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on AArch64: the tables of `vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt`, as their callers hold them

`STable sym H`: the table of halfwords `H` (116 words) at the symbol `sym`,
readable and apart from what the caller writes; `SReady sym H`: what a call
on the polynomial at `f` needs of it. `FastTable` and `FastReady` are those
of `vg_mlkem16_ntt`'s table, `FastInvTable` and `FastInvReady` those of
`vg_mlkem16_inv_ntt`'s.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (hw4)

theorem tabWords_length : Impl.MlKem.AArch64.Ntt16.Fast.tabWords.length = 116 := by
  rw [Impl.MlKem.AArch64.Ntt16.Fast.tabWords, Impl.MlKem.AArch64.Ntt16.Fast.tab.lit_eq]; decide +kernel

theorem tabWords_get : ∀ i < 116,
    Impl.MlKem.AArch64.Ntt16.Fast.tabWords.getD i 0 = hw4 Impl.MlKem.AArch64.Ntt16.Fast.tab i := by
  rw [Impl.MlKem.AArch64.Ntt16.Fast.tabWords, Impl.MlKem.AArch64.Ntt16.Fast.tab.lit_eq]; decide +kernel

theorem tabWordsI_length : Impl.MlKem.AArch64.Ntt16.FastInv.tabWords.length = 116 := by
  rw [Impl.MlKem.AArch64.Ntt16.FastInv.tabWords, Impl.MlKem.AArch64.Ntt16.FastInv.tab.lit_eq]; decide +kernel

theorem tabWordsI_get : ∀ i < 116,
    Impl.MlKem.AArch64.Ntt16.FastInv.tabWords.getD i 0 = hw4 Impl.MlKem.AArch64.Ntt16.FastInv.tab i := by
  rw [Impl.MlKem.AArch64.Ntt16.FastInv.tabWords, Impl.MlKem.AArch64.Ntt16.FastInv.tab.lit_eq]; decide +kernel

/-- The region of the table at `sym`. -/
abbrev sRegion (sym : String) (s : State) : Region := ⟨s.syms sym, 928⟩

/-- The table of halfwords `H` at `sym`, readable and apart from what the caller writes. -/
def STable (sym : String) (H : List Nat) (s : State) : Prop :=
  (∀ i < 116, s.mem.readW (s.syms sym + BitVec.ofNat 64 (8 * i)) 64 = hw4 H i) ∧
    Covers [sRegion sym s] (s.rd ++ s.wr) ∧ ∀ r ∈ s.wr, (sRegion sym s).Disjoint r

/-- What a call on the polynomial at `f`, with working space at `w`, needs of the table. -/
structure SReady (sym : String) (H : List Nat) (s : State) (f w : Addr) : Prop where
  table : ∀ i < 116, s.mem.readW (s.syms sym + BitVec.ofNat 64 (8 * i)) 64 = hw4 H i
  readable : Covers [sRegion sym s] (s.rd ++ s.wr)
  output : (polyRegion f).Disjoint (sRegion sym s)
  scratch : (polyRegion w).Disjoint (sRegion sym s)

/-- The region of `vg_mlkem16_ntt`'s table. -/
abbrev fastRegion (s : State) : Region := sRegion Impl.MlKem.AArch64.Ntt16.Fast.name s

/-- The region of `vg_mlkem16_inv_ntt`'s table. -/
abbrev fastInvRegion (s : State) : Region := sRegion Impl.MlKem.AArch64.Ntt16.FastInv.name s

abbrev FastTable (s : State) : Prop :=
  STable Impl.MlKem.AArch64.Ntt16.Fast.name Impl.MlKem.AArch64.Ntt16.Fast.tab s

abbrev FastReady (s : State) (f w : Addr) : Prop :=
  SReady Impl.MlKem.AArch64.Ntt16.Fast.name Impl.MlKem.AArch64.Ntt16.Fast.tab s f w

abbrev FastInvTable (s : State) : Prop :=
  STable Impl.MlKem.AArch64.Ntt16.FastInv.name Impl.MlKem.AArch64.Ntt16.FastInv.tab s

abbrev FastInvReady (s : State) (f w : Addr) : Prop :=
  SReady Impl.MlKem.AArch64.Ntt16.FastInv.name Impl.MlKem.AArch64.Ntt16.FastInv.tab s f w

section
variable {sym : String} {H : List Nat}

theorem STable.apart {s : State} (h : STable sym H s) {r : Region} (hc : Covers [r] s.wr) :
    (sRegion sym s).Disjoint r := by
  intro addr ha hb
  obtain ⟨q, hq, hh⟩ := hc addr 1 ⟨r, by simp, hb⟩
  exact h.2.2 q hq addr ha hh

theorem STable.ready {s : State} (h : STable sym H s) {f w : Addr}
    (hc : Covers [polyRegion f, polyRegion w] s.wr) : SReady sym H s f w := by
  refine ⟨h.1, h.2.1, (h.apart fun a n hh => hc a n ?_).symm, (h.apart fun a n hh => hc a n ?_).symm⟩
  · obtain ⟨r, hr, ha⟩ := hh
    rw [List.mem_singleton.mp hr] at ha
    exact ⟨polyRegion f, by simp, ha⟩
  · obtain ⟨r, hr, ha⟩ := hh
    rw [List.mem_singleton.mp hr] at ha
    exact ⟨polyRegion w, by simp, ha⟩

theorem STable.frameFar {s t : State} {rs : List Region} (h : STable sym H s) (hs : t.syms = s.syms)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (sRegion sym s).Disjoint r) : STable sym H t := by
  refine ⟨?_, by simpa only [sRegion, hs, hr, hw] using h.2.1, by simpa only [sRegion, hs, hw] using h.2.2⟩
  intro i hi
  rw [hs, hf.readW (r := sRegion sym s) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
  exact h.1 i hi

theorem STable.frame {s t : State} {rs : List Region} (h : STable sym H s) (hs : t.syms = s.syms)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame rs s.mem t.mem) (hc : Covers rs s.wr) :
    STable sym H t :=
  h.frameFar hs hr hw hf fun r hh =>
    h.apart fun a n ⟨q, hq, ha⟩ => hc a n ⟨q, by rw [List.mem_singleton.mp hq]; exact hh, ha⟩

theorem SReady.frame {s t : State} {f w : Addr} {rs : List Region} (h : SReady sym H s f w)
    (hs : t.syms = s.syms) (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (sRegion sym s).Disjoint r) : SReady sym H t f w := by
  refine ⟨?_, by simpa only [sRegion, hs, hr, hw] using h.readable, by simpa only [sRegion, hs] using h.output,
    by simpa only [sRegion, hs] using h.scratch⟩
  intro i hi
  rw [hs, hf.readW (r := sRegion sym s) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
  exact h.table i hi

end

end VG.Proof.MlKem.AArch64.NttR
