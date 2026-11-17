module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.Layout

/-! ### `Dsa.X86_64.BufferFrame`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.LocalCallFrame`, which this module and modules that import it used -/

section

/-! # Framing arithmetic calls whose result is a local scratch buffer -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def localCallRanges (o wx d k : Nat) : List (Nat × Nat) :=
  [(128, 48), (o + 136, slot wx 8 + tabBytes wx - 136), (d, k)]

theorem callFrame_local {B : Addr} {o wx d k : Nat} {mem mem' : Mem}
    (hf : CallFrame B o wx (off B d) k mem mem')
    (ho : o + slot wx 8 + tabBytes wx ≤ 2 ^ 64) (hd : d + k ≤ 2 ^ 64) :
    Frm B (localCallRanges o wx d k) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  intro x hx
  apply hf x (hx (128, 48) (by simp [localCallRanges]))
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have h := hx (o + 136, slot wx 8 + tabBytes wx - 136) (by simp [localCallRanges])
    rcases ofs_rebase B x (o := o) (by omega_using [ho, hslot]) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at * <;> omega_arith
  · intro j hj he
    have h := hx (d, k) (by simp [localCallRanges])
    rw [he, ofs_off B (by omega_using [hd, hj])] at h
    simp only at h
    omega_using [hj, h]

/-- A local result cannot change a disjoint initialized child. -/
theorem localCall_ready {B : Addr} {o wx d k other ow m : Nat} {mi : BitVec 64} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx d k) mem mem') (hready : ChildReady mem B other ow m mi)
    (hlo : 176 ≤ other) (hhi : other + slot ow 8 ≤ 2 ^ 64)
    (hsep : other + slot ow 8 ≤ o ∨ o + slot wx 8 + tabBytes wx ≤ other)
    (hout : other + slot ow 8 ≤ d ∨ d + k ≤ other) : ChildReady mem' B other ow m mi := by
  have hslot : 256 ≤ slot ow 8 := by unfold slot hdrBytes; omega_using []
  have hwork : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have he : ∀ e, e + 8 ≤ slot ow 8 → word mem' (off B other) e = word mem (off B other) e := by
    intro e he
    rw [word_off, word_off]
    apply hf.word_eq _ (by omega_using [hhi, he])
    intro r hr
    simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · right; omega_using [hlo]
    · rcases hsep with hsep | hsep
      · left; omega_using [he, hsep]
      · right; omega_using [hwork, hsep]
    · rcases hout with hout | hout
      · left; omega_using [he, hout]
      · right; omega_using [hout]
  have hn := slot_le (w := ow) (show VG.Impl.Bignum.X86_64.Public.aN < 8 by decide)
  refine ⟨hready.header.of_words (fun i hi => he _ (by omega_using [hslot, hi])), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega_using [hn, hi]))]
    exact hready.modulus
  · rw [he _ (by omega_using [hn])]
    exact hready.inverse

end VG.Proof.Dsa.X86_64

end

end

/-! # Preserving operands and recovering result bytes between DSA calls -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem localCall_field {B : Addr} {o wx d k : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx d k) mem mem') (ho : pWorkspace ≤ o) (hd : pWorkspace ≤ d)
    (f : Field) : word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro r hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right; omega_using [hb]
  · left; omega_using [ho, hb]
  · left; omega_using [hd, hb]

theorem callFrame_source {s t : State} {B src out : Addr} {Z o wx k : Nat} {bs : List Byte} {rs : List Reg}
    (hf : CallFrame B o wx out k s.mem t.mem) (hk : Keep rs s t)
    (hZ : 176 ≤ Z) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hbound : Z ≤ 2 ^ 64)
    (hs : Src s B Z src bs)
    (hsep : ∀ i < bs.length, ∀ j < k, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) : Src t B Z src bs := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  refine ⟨fun i hi => by rw [hk.2.1, hk.2.2]; exact hs.rd i hi, ?_, hs.out⟩
  intro i hi
  rw [hf _ (Or.inr (Nat.le_trans hZ (hs.out i hi))) ?_ (hsep i hi)]
  · exact hs.val i hi
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have hp := hs.out i hi
    rcases ofs_rebase B (src + BitVec.ofNat 64 i) (o := o) (by omega_using [hhi, hbound, hslot]) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only <;> right <;> omega_arith

theorem source_bytesAt {s : State} {B p : Addr} {Z n : Nat} {bs : List Byte}
    (hb : Spec.Rsa.bytesAt s.mem p n = bs)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (ho : ∀ i < n, Z ≤ ofs B (p + BitVec.ofNat 64 i)) : Src s B Z p bs := by
  have hlen : bs.length = n := by rw [← hb]; simp [Spec.Rsa.bytesAt]
  refine ⟨fun i hi => hr i (by omega_using [hlen, hi]), ?_, fun i hi => ho i (by omega_using [hlen, hi])⟩
  intro i hi
  subst bs
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

/-- Read back a computed local scalar or element as an operand. -/
theorem output_operand {s : State} {B : Addr} {Z d k : Nat} {f : Field} {bs : List Byte}
    (hl : word s.mem B f.offset = BitVec.ofNat 64 k)
    (hb : Spec.Rsa.bytesAt s.mem (off B d) k = bs)
    (hr : ∀ i < k, InRegions (s.rd ++ s.wr) (off B d + BitVec.ofNat 64 i) 1)
    (ho : ∀ i < k, Z ≤ ofs B (off B d + BitVec.ofNat 64 i)) :
    OperandBytes s B Z ⟨.local d, f⟩ bs := by
  have hlen : bs.length = k := by rw [← hb]; simp [Spec.Rsa.bytesAt]
  exact ⟨by rw [hlen]; exact hl, source_bytesAt hb hr ho⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Persistent state across DSA arithmetic and validation schedules -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ExecutionLayout where
  base : Addr
  pLen : Nat
  qLen : Nat
  modulus : Nat
  subgroup : Nat
  pInverse : BitVec 64
  qInverse : BitVec 64
  fields : Field → BitVec 64
  lengths : Spec.Dsa.lengthsValid pLen qLen
  pLength : fields .pLen = BitVec.ofNat 64 pLen
  qLength : fields .qLen = BitVec.ofNat 64 qLen

abbrev ExecutionLayout.pWords (L : ExecutionLayout) : Nat := (L.pLen + 7) / 8
abbrev ExecutionLayout.qWords (L : ExecutionLayout) : Nat := (L.qLen + 7) / 8

structure Ready (L : ExecutionLayout) (s : State) : Prop where
  parent : Good s L.base activeBytes outerWords 0
  scratch : Scr s L.base usedBytes
  fields : ∀ f : Field, f ≠ .mask → word s.mem L.base f.offset = L.fields f
  pChild : ChildReady s.mem L.base pWorkspace L.pWords L.modulus L.pInverse
  qChild : ChildReady s.mem L.base qWorkspace L.qWords L.subgroup L.qInverse

theorem Ready.afterP {L : ExecutionLayout} {s t : State} {d k : Nat}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base pWorkspace L.pWords L.modulus L.pInverse)
    (hf : CallFrame L.base pWorkspace L.pWords (off L.base d) k s.mem t.mem)
    (hk : Keep coreRegs s t) (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hlf := callFrame_local hf (by omega_using [hd, hend, hpHi, hqHi, hn]) (by omega_using [hend, hn])
  refine ⟨hp, h.scratch.congr hk.2.2, ?_, hc, ?_⟩
  · intro f hm
    exact (localCall_field hlf (Nat.le_refl _) (Nat.le_trans (by decide) hd) f).trans (h.fields f hm)
  · exact localCall_ready hlf h.qChild (by decide) (by omega_using [hd, hend, hqHi, hn]) (Or.inr hpHi) (Or.inl (by omega_using [hd, hqHi]))

theorem Ready.afterQ {L : ExecutionLayout} {s t : State} {d k : Nat}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base qWorkspace L.qWords L.subgroup L.qInverse)
    (hf : CallFrame L.base qWorkspace L.qWords (off L.base d) k s.mem t.mem)
    (hk : Keep coreRegs s t) (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hlf := callFrame_local hf (by omega_using [hd, hend, hqHi, hn]) (by omega_using [hend, hn])
  refine ⟨hp, h.scratch.congr hk.2.2, ?_, ?_, hc⟩
  · intro f hm
    exact (localCall_field hlf (by decide) (Nat.le_trans (by decide) hd) f).trans (h.fields f hm)
  · exact localCall_ready hlf h.pChild (by decide) (by omega_using [hd, hend, hpHi, hqHi, hn]) (Or.inl (by omega_using [hpHi])) (Or.inl (by omega_using [hd, hpHi, hqHi]))

theorem Ready.local_write {L : ExecutionLayout} {s : State} {d k : Nat} (h : Ready L s)
    (hend : d + k ≤ usedBytes) : ∀ i < k, InRegions s.wr (off L.base d + BitVec.ofNat 64 i) 1 := by
  intro i hi
  rw [show off L.base d + BitVec.ofNat 64 i = off L.base (d + i) by simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact h.scratch.st8 (by omega_using [hend, hi])

theorem Ready.local_out {L : ExecutionLayout} {s : State} {d k : Nat} (h : Ready L s)
    (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) :
    ∀ i < k, activeBytes ≤ ofs L.base (off L.base d + BitVec.ofNat 64 i) := by
  intro i hi
  rw [ofs_off L.base (by have := h.scratch.nowrap; omega_using [hend, hi, this])]
  omega_using [hd]

end VG.Proof.Dsa.X86_64
