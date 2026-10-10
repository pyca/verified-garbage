import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

/-! ## From `PairedTableConstants.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

private theorem mapped_prefix_get {α β : Type} [Inhabited α] [Inhabited β]
    (xs : List α) (f : α → β) (ys : List β) {n i : Nat} (hi : i<n) (hn : n≤xs.length) :
    ((xs.take n).map f ++ ys)[i]! = f xs[i]! := by
  have hlen : ((xs.take n).map f).length=n := by simp [Nat.min_eq_left hn]
  rw [getElem!_pos _ _ (by simp only [List.length_append,hlen]; omega),
    List.getElem_append_left (by rw [hlen]; exact hi),List.getElem_map,List.getElem_take,
    getElem!_pos xs i (by omega)]

private theorem mapped_suffix_get {α β : Type} [Inhabited α] [Inhabited β]
    (xs : List β) (ys : List α) (f : α → β) {i : Nat} (hi : i<ys.length) :
    (xs ++ ys.map f)[xs.length+i]! = f ys[i]! := by
  rw [getElem!_pos _ _ (by simp only [List.length_append,List.length_map]; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,List.getElem_map]
  rw [getElem!_pos ys i hi]

theorem expanded_first {i : Nat} (hi : i<960) :
    expandedVals[i]! = VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedVals[i]! := by
  rw [expandedVals_layout,mapped_prefix_get _ _ _ hi (by rw [InverseTable.layout_length]; decide),
    InverseTable.expanded_get (by omega)]

theorem expanded_tail {i : Nat} (hi : i<64) :
    expandedVals[960+i]! = tailValue tailLayout[i]! := by
  rw [expandedVals_layout]
  have hn : ((InverseTable.layout.take 960).map InverseTable.value).length=960 := by
    simp only [List.length_map,List.length_take,InverseTable.layout_length]; decide
  have h := mapped_suffix_get ((InverseTable.layout.take 960).map InverseTable.value)
    tailLayout tailValue (i := i) (by rw [tailLayout_length]; exact hi)
  simpa only [hn] using h

theorem tail_values {j e : Nat} (hj : j<8) (he : e<4) :
    expandedVals[960+8*j+e]! = tailRoot j ∧
    expandedVals[960+8*j+e+4]! = bar (tailRoot j) := by
  have hh := tail_layout ⟨j,hj⟩ ⟨e,he⟩
  have h0 := (expanded_tail (i := 8*j+e) (by omega)).trans (congrArg tailValue hh.1)
  have h1 := (expanded_tail (i := 8*j+e+4) (by omega)).trans (congrArg tailValue hh.2)
  constructor
  · simpa only [Nat.add_assoc,tailValue,Bool.false_eq_true,ite_false] using h0
  · simpa only [Nat.add_assoc,tailValue,ite_true] using h1


theorem layer1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+8*g+e]! = z (255-16*u-4*g-e) ∧
    expandedVals[120*u+8*g+e+4]! = bar (z (255-16*u-4*g-e)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer1_values hu hg he

theorem layer2_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+32+8*g+e]! = z (127-8*u-2*g-e/2) ∧
    expandedVals[120*u+32+8*g+e+4]! = bar (z (127-8*u-2*g-e/2)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer2_values hu hg he

theorem layer4_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+64+8*g+e]! = z (63-4*u-g) ∧
    expandedVals[120*u+64+8*g+e+4]! = bar (z (63-4*u-g)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer4_values hu hg he

theorem layer8_values {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    expandedVals[120*u+96+8*g+e]! = z (31-2*u-g) ∧
    expandedVals[120*u+96+8*g+e+4]! = bar (z (31-2*u-g)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer8_values hu hg he

theorem layer16_values {u e : Nat} (hu : u<8) (he : e<4) :
    expandedVals[120*u+112+e]! = z (15-u) ∧
    expandedVals[120*u+112+e+4]! = bar (z (15-u)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer16_values hu he

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable

end

/-! ## From `PairedTableWords.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

 theorem tailRoot_lt (j : Nat) : tailRoot j < 8380417 := by
  unfold tailRoot
  split
  · decide
  · split
    · exact Nat.mod_lt _ (by decide)
    · exact Nat.mod_lt _ (by decide)

theorem tailValue_lt (p : Nat × Bool) : tailValue p < 2^32 := by
  have hz := tailRoot_lt p.1
  have hb : tailRoot p.1*2^31/8380417 < 2^31 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hz (show 0<2^31 by decide)
  cases h : p.2 <;> simp only [tailValue,bar,h,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem expandedVals_lt {i : Nat} (hi : i<1024) : expandedVals[i]! < 2^32 := by
  by_cases h : i<960
  · rw [expanded_first h]; exact InverseTable.expandedVals_lt (by omega)
  · rw [show i=960+(i-960) by omega,expanded_tail (by omega)]
    exact tailValue_lt _

theorem expandedWords_length : expandedWords.length = 512 := by
  simp only [expandedWords,List.length_map,List.length_range,expandedVals_length]

private theorem range_map_get {α : Type} [Inhabited α] (f : Nat → α) {n i : Nat}
    (hi : i<n) : ((List.range n).map f)[i]! = f i := by
  rw [getElem!_pos ((List.range n).map f) i (by simpa only [List.length_map,List.length_range] using hi),
    List.getElem_map,List.getElem_range]

theorem expandedWords_get {i : Nat} (hi : i<512) :
    expandedWords[i]! = BitVec.ofNat 64 (expandedVals[2*i]!+2^32*expandedVals[2*i+1]!) := by
  exact range_map_get _ (by simpa only [expandedVals_length] using hi)

theorem expandedWords_low {i : Nat} (hi : i<512) :
    (expandedWords[i]!).extractLsb' 0 32 = BitVec.ofNat 32 expandedVals[2*i]! := by
  rw [expandedWords_get hi]
  exact TableConstants.pack_low _ _ (expandedVals_lt (by omega)) (expandedVals_lt (by omega))

theorem expandedWords_high {i : Nat} (hi : i<512) :
    (expandedWords[i]!).extractLsb' 32 32 = BitVec.ofNat 32 expandedVals[2*i+1]! := by
  rw [expandedWords_get hi]
  exact TableConstants.pack_high _ _ (expandedVals_lt (by omega)) (expandedVals_lt (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable

end

/-! ## From `PairedTableMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

/-- The immutable inverse table's actual packed artifact data. -/
def Artifact (m : Mem) (p : Addr) : Prop :=
  ∀ i<512, m.readW (p+BitVec.ofNat 64 (8*i)) 64=expandedWords[i]!

def Words (m : Mem) (p : Addr) : Prop :=
  ∀ k<1024, m.readW (p+BitVec.ofNat 64 (4*k)) 32=BitVec.ofNat 32 expandedVals[k]!

theorem Artifact.words {m : Mem} {p : Addr} (h : Artifact m p) : Words m p := by
  intro k hk
  have hi : k/2<512 := by omega
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,expandedWords_low hi] at hx
    simpa only [show 8*(k/2)=4*k by omega,← he] using hx
  · have he : k=2*(k/2)+1 := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,expandedWords_high hi,BitVec.add_assoc,
      ← BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega,← he] using hx

theorem Words.vector {m : Mem} {p : Addr} (h : Words m p)
    {k e : Nat} (hk : k+4≤1024) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (4*k)) 16) e=BitVec.ofNat 32 expandedVals[k+e]! := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,
    BitVec.add_assoc,← BitVec.ofNat_add,← Nat.mul_add]
  exact h _ (by omega)

/-- A pair of SIMD loads selects a root and its reciprocal from one row. -/
theorem Words.row {m : Mem} {p : Addr} (h : Words m p)
    {u off g e root : Nat} (ho : off%4=0) (he : e<4)
    (hb : 480*u+off+32*g+32≤4096)
    (hv : expandedVals[120*u+off/4+8*g+e]! = z root ∧
      expandedVals[120*u+off/4+8*g+e+4]! = bar (z root)) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+off+32*g)) 16) e=BitVec.ofNat 32 (z root) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+off+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z root)) := by
  have h0 : 480*u+off+32*g=4*(120*u+off/4+8*g) := by omega
  have h1 : 480*u+off+32*g+16=4*(120*u+off/4+8*g+4) := by omega
  constructor
  · rw [h0,h.vector (by omega) he,hv.1]
  · rw [h1,h.vector (by omega) he]
    rw [show 120*u+off/4+8*g+4+e=120*u+off/4+8*g+e+4 by omega,hv.2]

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable

end
