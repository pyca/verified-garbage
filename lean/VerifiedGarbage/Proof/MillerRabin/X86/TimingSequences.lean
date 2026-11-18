module

public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.MillerRabin.X86.Data
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryValues
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MillerRabin.X86.EntryArgs`, which the modules that import this one used -/

section

/-! # The saved round frame retains the two public cdecl arguments -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem argument_offset {s : State} (E : Entry s) {i : Nat} (index : i < 2) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have bound := E.stackBound
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [index, bound]

theorem Entry.pushed_arg {s : State} (E : Entry s) {i : Nat} (index : i < 2) :
    (entered s).mem.readW (argAddr s i) 32 = arg s i := by
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide)
    (by change 16 ≤ (s.gpr .esp).toNat; have := E.stackFit; omega_using [this])
  have separate : (⟨argAddr s 0, 8⟩ : Region).Disjoint (below (s.gpr .esp) 16) :=
    E.stackArgsSeparate'.symm.sub_right (below_sub (by decide) E.stackFit)
  have contains : (⟨argAddr s 0, 8⟩ : Region).Contains (argAddr s i) 4 := by
    rw [argument_offset E index]
    exact Offset.contains_base _ (by omega_using [index]) (by omega_using [index])
  exact saved.readW contains (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)

theorem Entry.read_arg {s : State} (E : Entry s) {i : Nat} (index : i < 2) :
    readSrc (entered s) (.mem (VG.Impl.Mont.X86.Compact.arg i)) = some (arg s i) := by
  change (entered s).load32 ((entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((entered s).rd ++ (entered s).wr) (argAddr s i) 4 := by
    rw [entered, Compact.entered, pushed_rd, E.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    rw [argument_offset E index]
    exact Offset.contains_base _ (by omega_using [index]) (by omega_using [index])
  rw [State.load32, ite_eq_left access, E.pushed_arg index]

theorem lengthRegion_entered (s : State) :
    lengthRegion ((entered s).gpr .esp) = ⟨argAddr s 1, 4⟩ := by
  change (⟨(((entered s).gpr .esp) + 24#32).setWidth 64, 4⟩ : Region) = _
  rw [entered, Compact.entered, pushed_esp]
  change (⟨(s.gpr .esp - 16#32 + (16#32 + 8#32)).setWidth 64, 4⟩ : Region) = _
  rw [← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem Entry.length_sub {s : State} (E : Entry s) :
    Region.Sub (lengthRegion ((entered s).gpr .esp)) ⟨argAddr s 0, 8⟩ := by
  rw [lengthRegion_entered, argument_offset E (by decide : 1 < 2)]
  intro x hx
  apply Region.Contains.byte (Offset.contains_base (argAddr s 0) (by decide : 4 + 4 ≤ 8) (by decide))
  change (x - (argAddr s 0 + BitVec.ofNat 64 4)).toNat + 1 ≤ 4 at hx
  omega_using [hx]

theorem Entry.caller {s : State} (E : Entry s) :
    Caller (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (entered s) := by
  have sub : Region.Sub (below ((entered s).gpr .esp) 80) (below (s.gpr .esp) 96) := by
    rw [entered, Compact.entered, pushed_esp]
    exact below_inner (by decide : 80 + 16 ≤ 96) E.stackFit
  refine ⟨rfl, ?_, E.stackSeparate'.symm.sub_right sub,
    E.argSeparate.symm.sub_left E.length_sub, E.stackArgsSeparate'.symm.sub_left E.length_sub |>.sub_right sub, ?_⟩
  · rw [entered, Compact.entered, pushed_esp]
    change 80 ≤ (s.gpr .esp - 16#32).toNat
    rw [sub_toNat (by have := E.stackFit; omega_using [this])]
    have := E.stackFit
    omega_using [this]
  · change readSrc (entered s) (.mem (VG.Impl.Mont.X86.Compact.arg 1)) = some (BitVec.ofNat 32 (arg s 1).toNat)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact E.read_arg (by decide : 1 < 2)

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.EntryMarker`, which the modules that import this one used -/

section

/-! ### `MillerRabin.X86.EntryValues`, which this module and modules that import it used -/

section

/-! # The prepared contract supplies the round's native-word initial values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont

def initialValues (s : State) (j : Nat) : Nat := numAt s.mem (wsOf s) (geometry s).w j

theorem Entry.context {s t : State} (E : Entry s)
    (mem : t.mem = (entered s).mem) (workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr)
    (base : PtrAt t (wsOf s) .edi 0) : Context (geometry s) t := by
  have v := E.valid
  have header : 256 ≤ lenOf s := v.headerFit
  have layout := E.layout.2.1
  have widthBound := v.maxWidth
  refine ⟨⟨?_, ?_⟩, base, ?_, ?_, ?_⟩
  · exact workspace
  · change (wsOf s).toNat + lenOf s ≤ 2 ^ 32
    rw [E.ws_toNat]; exact E.bound
  · change w32 t.mem (wsOf s) 48 = (geometry s).w
    rw [mem, E.pushed_w32 (by omega_using [header]), show 48 = 8 * 6 from rfl, Compact.header_low]
    change (geometry s).w % 2 ^ 32 = (geometry s).w
    exact Nat.mod_eq_of_lt (by omega_using [widthBound])
  · change w32 t.mem (wsOf s) 224 = 8 * ((geometry s).w + 2)
    rw [mem, E.pushed_w32 (by omega_using [header]), show 224 = 8 * 28 from rfl, Compact.header_low]
    have stride : wordAt s.mem (wsOf s) 28 = BitVec.ofNat 64 (8 * ((geometry s).w + 2)) := E.layout.2.2.2.2.2
    rw [stride, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [widthBound]), Nat.mod_eq_of_lt (by omega_using [widthBound])]
  · intro j index
    change w32 t.mem (wsOf s) (64 + 8 * j) = _
    rw [mem, E.pushed_w32 (by omega_using [header, index])]
    exact Compact.layout_pointer_low layout index

theorem Entry.modulus {s t : State} (E : Entry s) (mem : t.mem = (entered s).mem) :
    Modulus (geometry s) (initialValues s 0) t.mem := by
  have v := E.valid
  have header : 256 ≤ lenOf s := v.headerFit
  have candidateFit := v.arrayFit (j := 0) (by decide)
  change (geometry s).array 0 + 4 * (geometry s).words ≤ lenOf s at candidateFit
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (t.mem.readW (off (wsOf s) 48) 64).toNat = _
    rw [mem, E.pushed_read (by omega_using [header])]
    rfl
  · intro j index
    change t.mem.readW (off (wsOf s) (8 * arrWord j)) 64 = _
    rw [mem, E.pushed_read (by unfold arrWord; omega_using [header, index])]
    exact E.layout.2.1.2.2.2 j index
  · change val32 t.mem (wsOf s) ((geometry s).array 0) (geometry s).words = _
    rw [mem, E.pushed_val32 candidateFit]
    exact (Compact.numAt_val32 _ _ _ _).symm
  · change ((t.mem.readW (off (wsOf s) ((geometry s).array 0)) 64).toNat *
      (t.mem.readW (off (wsOf s) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [mem, E.pushed_read (by have := v.minWidth; unfold Geometry.words at candidateFit; omega_using [candidateFit, this]),
      E.pushed_read (by omega_using [header])]
    exact E.prepared.2.2.1

theorem Entry.data {s t : State} (E : Entry s)
    (mem : t.mem = (entered s).mem) (workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr)
    (base : PtrAt t (wsOf s) .edi 0) :
    Data (geometry s) (initialValues s) initialArrays (fun _ => 0) [] t := by
  refine ⟨E.context mem workspace base, ?_, by simp⟩
  intro j known
  have bound : j < 28 := by
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨bound, ?_⟩
  change val32 t.mem (wsOf s) ((geometry s).array j) (geometry s).words = _
  rw [mem, E.pushed_val32 (E.valid.arrayFit bound)]
  exact (Compact.numAt_val32 _ _ _ _).symm

end VG.Proof.MillerRabin.X86

end

end

/-! # Split the prepared exponent marker into the two native i686 words -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

theorem marker_halves {m : Mem} {W : Addr} {d k : Nat} (bound : k < 64)
    (marker : m.readW (off W d) 64 = BitVec.twoPow 64 k) :
    m.readW (off W d) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32) ∧
    m.readW (off W (d + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32) := by
  have value : (m.readW (off W d) 64).toNat = 2 ^ k := by
    rw [marker, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) bound)]
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, value,
      BitVec.toNat_ofNat, Nat.mod_mod]
  · have address : off W (d + 4) = off W d + BitVec.ofNat 64 4 := by
      unfold off
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address]
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_hi, BitVec.extractLsb'_toNat, value, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat]

theorem Entry.marker {s : State} (E : Entry s) :
    (entered s).mem.readW (off (wsOf s) ((geometry s).array 27 + 4 * (geometry s).words)) 32 =
      BitVec.ofNat 32 (2 ^ (mrA (initialValues s 0) % 64) % 2 ^ 32) ∧
    (entered s).mem.readW (off (wsOf s) ((geometry s).array 27 + 4 * (geometry s).words + 4)) 32 =
      BitVec.ofNat 32 (2 ^ (mrA (initialValues s 0) % 64) / 2 ^ 32) := by
  apply marker_halves (Nat.mod_lt _ (by decide))
  have fit : (geometry s).array 27 + 4 * (geometry s).words + 8 ≤ lenOf s := by
    have arrays := E.valid.arraysFit
    change Proof.Rsa.Mont.arrAt (geometry s).w 28 ≤ lenOf s at arrays
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
    unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at arrays
    omega_using [arrays]
  rw [E.pushed_read fit]
  rw [show 4 * (geometry s).words = 8 * (geometry s).w by unfold Geometry.words; omega_using []]
  exact E.prepared.2.2.2.2.2.2.2

end VG.Proof.MillerRabin.X86

end

end

/-! # Regrouping the round's statically unrolled instruction sequences -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem seqs_append_exec (cs ds : List (Prog isa)) {s t : State} {tr : List Leak}
    (E : Exec isa (seqs (cs ++ ds)) s tr t) :
    Exec isa (.seq (seqs cs) (seqs ds)) s tr t := by
  induction cs generalizing s tr with
  | nil => exact .seq (show Exec isa (.block []) s [] s from .block rfl) E
  | cons c cs ih =>
    cases cs with
    | nil =>
      cases ds with
      | nil => simpa only [seqs, List.append_nil] using (Exec.seq E (show Exec isa (.block []) t [] t from .block rfl))
      | cons d ds => exact E
    | cons d cs =>
      cases E with
      | seq Ec Er =>
        have split := ih Er
        cases split with
        | seq Es Ed => simpa only [seqs, List.append_assoc] using Exec.seq (Exec.seq Ec Es) Ed

theorem seqs_append_relCT {P R Q : State → State → Prop} (cs ds : List (Prog isa))
    (left : RelCT isa P (seqs cs) R) (right : RelCT isa R (seqs ds) Q) :
    RelCT isa P (seqs (cs ++ ds)) Q := by
  intro s t tr ur u z H E G
  exact RelCT.seq left right _ _ _ _ _ _ H (seqs_append_exec cs ds E) (seqs_append_exec cs ds G)

theorem seqs_range_relCT (n : Nat) (code : Nat → Prog isa) (P : Nat → State → State → Prop)
    (step : ∀ j < n, RelCT isa (P j) (code j) (P (j + 1))) :
    RelCT isa (P 0) (seqs ((List.range n).map code)) (P n) := by
  induction n with
  | zero => exact RelCT.block_nil (fun _ _ H => H)
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    exact seqs_append_relCT _ _ (ih (fun j hj => step j (by omega_using [hj]))) (step n (by omega_using []))

end VG.Proof.MillerRabin.X86
