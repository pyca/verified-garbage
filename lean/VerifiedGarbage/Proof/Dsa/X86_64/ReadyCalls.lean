module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-! ### `Dsa.X86_64.Execution`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.X86_64.Modulus`, which this module and modules that import it used -/

section

/-! # Selecting one of the two reusable DSA arithmetic moduli -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

inductive ModulusSide where | p | q

def ModulusSide.offset : ModulusSide → Nat | .p => pWorkspace | .q => qWorkspace
def ModulusSide.lengthField : ModulusSide → Field | .p => .pLen | .q => .qLen
def ModulusSide.length (side : ModulusSide) (L : ExecutionLayout) : Nat := match side with | .p => L.pLen | .q => L.qLen
def ModulusSide.words (side : ModulusSide) (L : ExecutionLayout) : Nat := (side.length L + 7) / 8
def ModulusSide.value (side : ModulusSide) (L : ExecutionLayout) : Nat := match side with | .p => L.modulus | .q => L.subgroup
def ModulusSide.inverse (side : ModulusSide) (L : ExecutionLayout) : BitVec 64 := match side with | .p => L.pInverse | .q => L.qInverse

theorem ModulusSide.bounds (side : ModulusSide) (L : ExecutionLayout) :
    2 ≤ side.words L ∧ side.words L ≤ outerWords ∧
    slot outerWords 8 ≤ side.offset ∧ side.offset < 2 ^ 31 ∧
    side.offset + slot (side.words L) 8 + tabBytes (side.words L) ≤ activeBytes ∧
    1 ≤ side.length L ∧ side.length L < 2 ^ 31 := by
  obtain ⟨hp2, hp48, hq2, hq48, hpLo, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hl : 1 ≤ L.pLen ∧ L.pLen < 2 ^ 31 ∧ 1 ≤ L.qLen ∧ L.qLen < 2 ^ 31 := by
    rcases L.lengths with ⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  cases side
  · exact ⟨hp2, hp48, hpLo, by decide, Nat.le_trans hpHi hqa, hl.1, hl.2.1⟩
  · exact ⟨hq2, hq48, by decide, by decide, hqHi, hl.2.2.1, hl.2.2.2⟩

theorem Ready.child {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide) :
    ChildReady s.mem L.base side.offset (side.words L) (side.value L) (side.inverse L) := by
  cases side
  · exact h.pChild
  · exact h.qChild

theorem Ready.length {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide) :
    word s.mem L.base side.lengthField.offset = BitVec.ofNat 64 (side.length L) := by
  cases side
  · exact (h.fields .pLen (by decide)).trans L.pLength
  · exact (h.fields .qLen (by decide)).trans L.qLength

theorem Ready.afterCall {L : ExecutionLayout} {s t : State} {d k : Nat} (side : ModulusSide)
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base side.offset (side.words L) (side.value L) (side.inverse L))
    (hf : CallFrame L.base side.offset (side.words L) (off L.base d) k s.mem t.mem)
    (hk : Keep coreRegs s t) (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) : Ready L t := by
  cases side
  · exact h.afterP hp hc hf hk hd hend
  · exact h.afterQ hp hc hf hk hd hend

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Arguments2`, which this module and modules that import it used -/

section

/-! # Input and output bindings for streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def Arguments2 (mem original : Mem) (B : Addr) (a output : Operand) : Prop :=
  word mem B (8 * arg) = pointerValue original B a.pointer ∧
  word mem B (8 * argLen) = word original B a.length.offset ∧
  word mem B (8 * result) = pointerValue original B output.pointer ∧
  word mem B (8 * resultLen) = word original B output.length.offset

/-- Bind the reduction input and result while preserving saved fields and
both structural and modulus words of the selected child. -/
theorem arguments2_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 256 ≤ o) (hhi : o + slot wx 8 ≤ Z)
    (a output : Operand) (ha : pointerFits a.pointer) (hout : pointerFits output.pointer) :
    WP isa (.block (Core.operand arg argLen a ++ Core.operand result resultLen output)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Arguments2 t.mem s.mem B a output ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B argumentRanges s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hg.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hual, hfieldsu, hfu, hku⟩ => ?_
  have hchildu := call_ready child hfu (by decide) (by decide) ho (by omega_using [hhi, hn])
  refine WP.mono (operand_context hgu hZ output hout (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨hgt, hto, htol, hfieldst, hft, hkt⟩ => ?_
  rw [pointerValue_congr hfieldsu] at hto
  rw [hfieldsu output.length] at htol
  refine ⟨hgt, call_ready hchildu hft (by decide) (by decide) ho (by omega_using [hhi, hn]), ?_,
    fun f => (hfieldst f).trans (hfieldsu f), ?_, (hku.trans hkt).mono (by decide)⟩
  · exact ⟨(call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hua,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hual, hto, htol⟩
  · exact (call_argument_frame hfu (by decide) (by decide)).trans
      (call_argument_frame hft (by decide) (by decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreCalls`, which only this module used -/

section

/-! # Exponentiation and multiplication in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete parent-to-child exponentiation, with a reusable modulus and
an ordinary big-endian result. No primality assumption is required. -/
theorem corePow_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.pow Sq.mm M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  refine WP.mono (power_ok M Sq hc hw2 hw48 hwx hw30 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hb2)
    fun v ⟨hcv, hv, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩

/-- Complete parent-to-child multiplication. Both input buffers may contain
unreduced values, and the destination may alias either input. -/
theorem coreProduct_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.product M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  refine WP.mono (product_ok M hc hw2 hw48 hwx hw30 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hbw)
    fun v ⟨hcv, hv, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreReduce`, which only this module used -/

section

/-! ### `Dsa.X86_64.Call2`, which only this module used -/

section

/-! # Complete DSA arithmetic calls, from operand binding through return -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The common two-operand calling convention. The arithmetic body is
proved separately for the selected Montgomery backend. -/
theorem call2_ok {s : State} {B : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (a output : Operand) (ha : pointerFits a.pointer)
    (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j))
    (run : ∀ u, SubCtx u B Z o w wx minv → ChildReady u.mem B o wx m minv →
      Arguments2 u.mem s.mem B a output → Frm B argumentRanges s.mem u.mem → Keep coreRegs s u →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧
        ModCtx v (off B o) (slot wx 8) wx minv m ∧
        wv v.mem (off B o) (slot wx aY) wx = value ∧
        Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (seqs (([.block (Core.operand arg argLen a ++
      Core.operand result resultLen output ++ Core.enter o), body] : List (Prog isa)) ++ Core.finish)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k value ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  change WP isa (.seq (.block _) (.seq body (seqs Core.finish))) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (arguments2_ok hg child hZ (by omega_using [hlo, hslot]) (by omega_using [hhi]) a output ha houtp)
    fun u ⟨hgu, hchild, hargs, _, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hfv : Frm B argumentRanges s.mem v.mem := by rw [hmem]; exact hf
  have hav : Arguments2 v.mem s.mem B a output := by rw [hmem]; exact hargs
  have hchv : ChildReady v.mem B o wx m minv := by rw [hmem]; exact hchild
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.mono (returnAfter_ok (parentMinv := parentMinv) hcv (run v hcv hchv hav hfv hks)
    (by rw [hmem]; exact hgu.hdr.hminv) hav.2.2.1 (hav.2.2.2.trans hl)
    hk1 hk' hkw (fun j hj => by rw [hks.2.2]; exact hout j hj) hprefix)
    fun t ⟨hgt, hct, htout, _, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htout, ?_, (hks.trans hkt).mono (by decide)⟩
  intro x hx hc hxout
  exact (hft x hc hxout).trans (hfv x (by
    intro r hr
    simp only [argumentRanges, List.mem_singleton] at hr
    subst r
    exact hx))

end VG.Proof.Dsa.X86_64

end

end

/-! # Streaming reduction in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete streaming reduction call, including empty digest inputs. -/
theorem coreReduce_ok (M : Mont) {s : State} {B : Addr} {Z w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B qWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ qWorkspace)
    (hhi : qWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 255 < m) (hodd : m % 2 = 1)
    (a output : Operand) (ha : pointerFits a.pointer)
    (houtp : pointerFits output.pointer) {ba : List Byte}
    (has : OperandBytes s B Z a ba) (hal : ba.length < 2 ^ 64)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.reduce M.mm a output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B qWorkspace wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ba % m) ∧
      CallFrame B qWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call2_ok hg child hZ hlo hhi (by decide) a output ha houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  exact reduce_ok M hc hw2 hw48 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) hargs.1 (hargs.2.1.trans has.length)
    (arguments_source hf hk (Nat.le_trans (by decide) hZ) has.source) hal

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreAdd`, which only this module used -/

section

/-! # Exponentiation and multiplication in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete modular addition call for two already reduced scalars. -/
theorem coreAdd_ok {s : State} {B : Addr} {Z w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B qWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ qWorkspace)
    (hhi : qWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (haReduced : Spec.Dsa.decodeBE ba < m) (hbReduced : Spec.Dsa.decodeBE bb < m)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.add a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B qWorkspace wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k ((Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m) ∧
      CallFrame B qWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have h := call3_ok (body := seqs [Arithmetic.load aX arg argLen,
    Arithmetic.load aXm arg2 arg2Len, Crt.addMod aY aX aXm])
    hg child hZ hlo hhi (by decide) a b output ha hb houtp hl hk1 hk' hkw hout hprefix
    (value := (Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m) ?_
  · change WP isa (.seq (.block _) (.seq (Arithmetic.load aX arg argLen)
      (.seq (Arithmetic.load aXm arg2 arg2Len) (.seq (Crt.addMod aY aX aXm) (seqs Core.finish))))) s _
    refine WP.seq (WP.mono (WP.seq_iff.mp h) fun u hu => ?_)
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv =>
      WP.seq (WP.mono (WP.seq_iff.mp hv) fun z hz => WP.seq hz))
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  exact add_ok hc ⟨hc.good, hchild.modulus, hchild.inverse⟩ hw2 hw48 hwx hw30
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hbw
    haReduced hbReduced

end VG.Proof.Dsa.X86_64

end

end


/-! # Arithmetic calls preserving the complete DSA execution context -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CallResult (L : ExecutionLayout) (side : ModulusSide) (d value : Nat) (s t : State) : Prop where
  ready : Ready L t
  bytes : Spec.Rsa.bytesAt t.mem (off L.base d) (side.length L) = Spec.Dsa.encodeBE (side.length L) value
  frame : CallFrame L.base side.offset (side.words L) (off L.base d) (side.length L) s.mem t.mem
  keep : Keep coreRegs s t

theorem readyPow_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.pow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) (side.value L)) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (corePow_ok M Sq h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hb2 (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyProduct_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ side.words L)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.product M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % side.value L) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreProduct_ok M h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyReduce_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 255 < L.subgroup) (hodd : L.subgroup % 2 = 1)
    (a : Operand) {ba : List Byte} (ha : pointerFits a.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hal : ba.length < 2 ^ 64)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.qLen ≤ usedBytes) :
    WP isa (Core.reduce M.mm a (Core.scalar d)) s
      (CallResult L .q d (Spec.Dsa.decodeBE ba % L.subgroup) s) := by
  obtain ⟨hw2, hw48, hlo, _, hhi, hk1, hk31⟩ := ModulusSide.q.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreReduce_ok M h.parent h.qChild (by decide) hlo hhi hw2 hw48 hm hodd
    a (Core.scalar d) ha hdp has hal (h.length .q) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterQ hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyAdd_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ L.qWords)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ L.qWords)
    (har : Spec.Dsa.decodeBE ba < L.subgroup) (hbr : Spec.Dsa.decodeBE bb < L.subgroup)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.qLen ≤ usedBytes) :
    WP isa (Core.add a b (Core.scalar d)) s
      (CallResult L .q d ((Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % L.subgroup) s) := by
  obtain ⟨hw2, hw48, hlo, _, hhi, hk1, hk31⟩ := ModulusSide.q.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreAdd_ok h.parent h.qChild (by decide) hlo hhi hw2 hw48 hw48 (by decide)
    a b (Core.scalar d) ha hb hdp has hbs ha1 haw hb1 hbw har hbr
    (h.length .q) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterQ hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
