module

public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSequences
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCoreState
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquares
public import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `MillerRabin.X86.Verified`, which only this module used -/

section

/-! ### `MillerRabin.X86.ConstantTime`, which only this module used -/

section

/-! ### `MillerRabin.X86.TimingEntry`, which only this module used -/

section

/-! # The reviewed input contract initializes each run's private timing invariant -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.RsaKeyGen VG.Impl.MillerRabin.X86

def entrySecret (s : State) : CoreSecret :=
  ⟨initialValues s 0, initialValues s, (fun _ => 0), mrA (initialValues s 0) % 64, (entered s).mem⟩

theorem Entry.coreMath {s : State} (E : Entry s) : CoreMath (geometry s) (entrySecret s) := by
  have minimum : 3 ≤ initialValues s 0 := E.prepared.1
  have odd : initialValues s 0 % 2 = 1 := E.prepared.2.1
  have lt : initialValues s aX < initialValues s 0 := E.prepared.2.2.2.1
  have one : initialValues s aOne = 2 ^ (64 * (geometry s).w) % initialValues s 0 := E.prepared.2.2.2.2.1
  refine ⟨odd, lt, ?_, Nat.mod_lt _ (by decide), E.marker⟩
  change initialValues s aOne < initialValues s 0
  rw [one]
  exact Nat.mod_lt _ (by omega_using [minimum])

theorem Entry.base {s : State} (E : Entry s) :
    WP isa (.block [.mov .edi (.mem (at_ .esp 20))]) (entered s) fun t =>
      CoreStart (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (entrySecret s) t ∧
      Keeps [.edi] (entered s) t := by
  have read := E.read_arg (i := 0) (by decide : 0 < 2)
  change readSrc (entered s) (.mem (at_ .esp 20)) = some (arg s 0) at read
  refine wp_movS read fun t T _ => WP.block_nil ?_
  have mem : t.mem = (entered s).mem := T.mem
  have workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr := by
    rw [T.wr, entered, Compact.entered, pushed_wr, E.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have base : PtrAt t (wsOf s) .edi 0 := by
    rw [PtrAt, T.gpr, Nat.add_zero, E.ws_toNat]
    exact (Nat.mod_eq_of_lt (arg s 0).isLt).symm
  refine ⟨⟨⟨E.data mem workspace base, E.modulus mem, ?_, ?_⟩, E.coreMath, mem⟩, T.keeps⟩
  · apply E.caller.keepFrame T.keeps (by decide)
    rw [T.mem]
    exact Frame.refl _ _
  · intro j known
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide

theorem geometry_eq {s t : State} (a0 : arg s 0 = arg t 0) (a1 : arg s 1 = arg t 1)
    (width : Proof.Rsa.Mont.wOf s.mem (wsOf s) = Proof.Rsa.Mont.wOf t.mem (wsOf t)) : geometry s = geometry t := by
  unfold geometry
  rw [width, wsOf, wsOf, lenOf, lenOf, a0, a1]

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingCore`, which only this module used -/

section

/-! ### `MillerRabin.X86.TimingTable`, which only this module used -/

section

/-! # Power-table construction reuses the prepared modulus at every product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

structure TableSecret where
  c : Nat
  A : Nat → Nat
  V : Nat → BitVec 32
  slots : List Nat

def TableStart (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : TableSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A initialArrays σ.V σ.slots s ∧ σ.c % 2 = 1 ∧ σ.A aX < σ.c

def TableStage (g : Geometry) (capacity : Nat) (p : BitVec 32) (k : Nat) (σ : TableSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (tableValues σ.A σ.c g.w k) (tableArrays k) σ.V σ.slots s ∧
    σ.c % 2 = 1 ∧ σ.A aX < σ.c

theorem tableInit_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (TableStart g capacity p))
      (seqs [copy aTable aOne, copy (aTable + 1) aX, copy aY aX]) (Two g (TableStage g capacity p 0)) := by
  refine private_lift (RelCT.seq (copy_relCT v aTable aOne (by decide) (by decide))
    (RelCT.seq (copy_relCT v (aTable + 1) aX (by decide) (by decide))
      (copy_relCT v aY aX (by decide) (by decide)))) ?_
  intro σ s ⟨S, odd, lt⟩
  exact WP.mono (tableInit_ok v S) fun _ R => ⟨R.1, odd, lt⟩

theorem tableStep_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity k : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (index : k < 14) :
    RelCT isa (Two g (TableStage g capacity p k))
      (.seq (mulY name code aX) (copy (aTable + k + 2) aY)) (Two g (TableStage g capacity p (k + 1))) := by
  refine private_attach ?_ ?_ (fun _ _ H => H.1.data.context)
  · apply RelCT.seq (Q := VG.X86.Taint.Agree (roundTaint [.edi]))
      ((mulY_relCT (p := p) verified noSp stack v length (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide)).mono ?_ (fun _ _ H => H))
    · exact (copy_relCT v (aTable + k + 2) aY (by unfold aTable; omega_using [index]) (by decide)).mono
        (fun _ _ H => H) (fun _ _ H => H.2.2)
    · intro s t ⟨P, ⟨σ, S, oddS, ltS⟩, ⟨ρ, T, oddT, ltT⟩⟩
      refine ⟨P, S.mulInput oddS (by simp [tableArrays, initialArrays]) ?_,
        T.mulInput oddT (by simp [tableArrays, initialArrays]) ?_⟩
      · rw [tableValues_x]; exact ltS
      · rw [tableValues_x]; exact ltT
  · intro σ s ⟨S, odd, lt⟩
    exact WP.mono (tableStep_ok verified noSp stack v S length odd lt index) fun _ R => ⟨R.1, odd, lt⟩

theorem table_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (TableStart g capacity p)) (table name code) (Two g (TableStage g capacity p 14)) := by
  unfold table
  exact seqs_append_relCT _ _ (tableInit_relCT v)
    (seqs_range_relCT 14 _ (fun k => Two g (TableStage g capacity p k))
      (fun _ index => tableStep_relCT verified noSp stack v length index))

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingMarker`, which only this module used -/

section

/-! # The secret exponent marker is read at its fixed public-width address -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem markerPointer_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block markerPointer) (VG.X86.Taint.Agree (roundTaint [.edi, .ebp])) := by
  unfold markerPointer
  rw [List.append_assoc]
  refine RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp aExponent (by decide) (by decide) [.edi] (by decide))
    (RelCT.block_append (RelCT.seq (words_pair_relCT v [.ebp, .edi] (by decide)) ?_)))
  exact (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp, .esi, .eax] true) (by kernel_rfl) (by kernel_rfl)).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem markerCalc_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .ebp]))
    (.block markerCalc) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp]) (by kernel_rfl) (by kernel_rfl)

theorem lastSquares_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block lastSquares) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold lastSquares
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (markerPointer_trace v)
    (RelCT.block_append (RelCT.seq markerCalc_trace (checkedBlockInvariant rfl rfl))))

theorem initWindows_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block initWindows) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant (τ' := roundTaint [.edi, .eax]) rfl rfl

end VG.Proof.MillerRabin.X86

end

end


/-! # The complete prepared round has a trace determined by public geometry -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem prepareRun_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (CoreStart g capacity p))
      (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) (Two g (CoreRun g capacity p)) := by
  refine private_attach ?_ (fun _ _ H => H.prepare verified noSp stack v length) (fun _ _ H => H.1.data.context)
  refine RelCT.seq ((table_relCT (p := p) verified noSp stack v length).mono ?_ (fun _ _ H => H.1))
    (RelCT.seq (copy_relCT v aY aOne (by decide) (by decide))
      (initWindows_trace.mono (fun _ _ H => H.2.2) (fun _ _ H => H)))
  intro s t ⟨P, ⟨σ, S, mathS, _⟩, ⟨ρ, T, mathT, _⟩⟩
  exact ⟨P, ⟨⟨σ.c, σ.A, σ.V, []⟩, S, mathS.1, mathS.2.1⟩,
    ⟨⟨ρ.c, ρ.A, ρ.V, []⟩, T, mathT.1, mathT.2.1⟩⟩

theorem coreWords_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (CoreRun g capacity p)) (.loop (wordStep name code) .ne) (Two g (CoreWords g capacity p)) := by
  refine private_attach ((wordLoop_relCT (p := p) verified noSp stack v length
    (by have := v.minWidth; unfold Geometry.words; omega_using [this] : 0 < g.words)).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.wordInput, H.2.2.choose_spec.wordInput⟩) (fun _ _ H => H.2.2))
    (fun _ _ H => H.words verified noSp stack v length) (fun _ _ H => H.1.data.context)

theorem coreMarker_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (CoreWords g capacity p)) (.block lastSquares) (Two g (CoreFinal g capacity p)) :=
  private_attach ((lastSquares_trace v).mono (fun _ _ H => H.1) (fun _ _ H => H))
    (fun _ _ H => H.marker v) (fun _ _ H => H.1.data.context)

theorem core_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (CoreStart g capacity p)) (core name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (seqs ([table name code, copy aY aOne, .block initWindows] ++
    [.loop (wordStep name code) .ne, .block lastSquares, squareLoop name code,
      .block [.mov .eax (.mem (slot sFlag))]])) _
  refine seqs_append_relCT _ _ (prepareRun_relCT verified noSp stack v length)
    (RelCT.seq (coreWords_relCT verified noSp stack v length) (RelCT.seq (coreMarker_relCT v) ?_))
  exact RelCT.seq ((squareLoop_relCT (p := p) verified noSp stack v length (by decide : 0 < 3)).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.squareInput, H.2.2.choose_spec.squareInput⟩) (fun _ _ H => H))
    ((checkedBlockInvariant rfl rfl).mono (fun _ _ H => H.2.2) (fun _ _ H => H))

end VG.Proof.MillerRabin.X86

end

end


/-! # Callable i686 Miller–Rabin is constant time under the reviewed contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem publicInputs {s t : State}
    (H : (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
      Proof.Rsa.Mont.wOf s.mem (wsOf s) = Proof.Rsa.Mont.wOf t.mem (wsOf t) := by
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, by with_reducible assumption, by with_reducible assumption, ?_⟩
  apply List.singleton_inj.mp
  with_reducible assumption

theorem baseLoad_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint []))
    (.block [.mov .edi (.mem (at_ .esp 20))]) (VG.X86.Taint.Agree (roundTaint [])) :=
  checkedBlockInvariant rfl rfl

theorem restore_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block VG.Impl.Mont.X86.Compact.restoreRegs) (VG.X86.Taint.Agree (roundTaint [])) :=
  checkedProgramChange (hint := .block []) (τ' := roundTaint []) rfl rfl

private theorem pair_of_context {g : Geometry} {s t : State}
    (S : Context g s) (T : Context g t) (sp : s.gpr .esp = t.gpr .esp) : Pair g [.edi] s t := by
  refine ⟨S, T, agree_regs ?_⟩
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact sp
  · exact ptr_agree S.base T.base

theorem constantTime : ConstantTime isa
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub (code montName montCode) := by
  apply RelCT.constantTime
  unfold code
  refine VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := fun _ _ => True)
    (fun _ _ H => (publicInputs H.2.2).1) ?_
  rintro a b tr ur u z ⟨s, t, H, rfl, rfl⟩ E G
  have S := entry_of H.1
  have T := entry_of H.2.1
  obtain ⟨sp, a0, a1, width⟩ := publicInputs H.2.2
  have geo := geometry_eq a0 a1 width
  have enteredSp : (entered s).gpr .esp = (entered t).gpr .esp := by
    rw [entered, entered, Compact.entered, Compact.entered, pushed_esp, pushed_esp, sp]
  cases E with
  | seq bodyS restoreS =>
    cases G with
    | seq bodyT restoreT =>
      cases bodyS with
      | seq loadS coreS =>
        cases bodyT with
        | seq loadT coreT =>
          have baseAgree : VG.X86.Taint.Agree (roundTaint []) (entered s) (entered t) := agree_regs (by
            intro r mem
            change r ∈ [.esp] at mem
            obtain rfl := List.mem_singleton.mp mem
            exact enteredSp)
          have baseTrace := (baseLoad_trace _ _ _ _ _ _ baseAgree loadS loadT).1
          obtain ⟨startS, keepS⟩ := wp_result S.base loadS
          obtain ⟨startT, keepT⟩ := wp_result T.base loadT
          have startT' := startT
          rw [← geo, ← a1, ← enteredSp] at startT'
          have pair := pair_of_context startS.1.data.context startT'.1.data.context (by
            rw [keepS.1 .esp (by decide), keepT.1 .esp (by decide)]
            exact enteredSp)
          obtain ⟨coreTrace, after⟩ := core_trace VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack S.valid
            (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega_using []) _ _ _ _ _ _
            ⟨pair, ⟨entrySecret s, startS⟩, ⟨entrySecret t, startT'⟩⟩ coreS coreT
          have restoreTrace := (restore_trace _ _ _ _ _ _ after restoreS restoreT).1
          exact ⟨by rw [baseTrace, coreTrace, restoreTrace], trivial⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.Satisfiable`, which only this module used -/

section

/-! # A concrete prepared four-limb candidate meets the i686 round contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 4 else if k = 7 then 0x5555555555555555
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 48)
  else if k = 28 then 48 else if k = 32 then 3
  else if k = 86 then 1 else if k = 92 then 2
  else if k = 194 then 1 else if k = 198 then 2 else 0

def satArg (i : Nat) : BitVec 32 := if i = 0 then 0x1000 else 200

def satMem : Mem := fun x =>
  if (x - 0x1000).toNat < 1600 then
    (satWord ((x - 0x1000).toNat / 8)).extractLsb' (8 * ((x - 0x1000).toNat % 8)) 8
  else if (x - 0x8004).toNat < 8 then
    (satArg ((x - 0x8004).toNat / 4)).extractLsb' (8 * ((x - 0x8004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x8004, 8⟩]
  wr := [⟨0x1000, 1600⟩]

theorem sat_arg0 : arg satState 0 = 0x1000#32 := by decide +kernel
theorem sat_arg1 : arg satState 1 = 200#32 := by decide +kernel

theorem sat_layout : Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact satMem 0x1000 200 := by
  refine ⟨Or.inr rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  case refine_4 =>
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega_using [hj]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  all_goals first
    | decide +kernel
    | change Proof.Rsa.Mont.wordAt satMem 0x1000 28 = BitVec.ofNat 64 (8 * (Proof.Rsa.Mont.wOf satMem 0x1000 + 2)); decide +kernel

theorem sat_prepared : Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact satMem 0x1000 := by
  unfold Proof.MillerRabin.Round.Prepared
  decide +kernel

theorem satisfiable : ∃ s, (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sat_arg0, sat_arg1]
  sig_and_intros
  all_goals first
    | exact sat_layout
    | exact sat_prepared
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.Frame`, which only this module used -/

section

/-! ### `MillerRabin.X86.EntryCore`, which only this module used -/

section

/-! ### `MillerRabin.X86.Core`, which only this module used -/

section

/-! # The complete prepared round computes the native fixed-window test -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def finishedState (A : Nat → Nat) (c w N k : Nat) : Nat × Bool :=
  squareState (exponentValues (runValues A c w) c w N false N) c w
    (4 - VG.Proof.RsaKeyGen.sigOf k) 3 (exponentState (runValues A c w) c w N false N).2 3

theorem core_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c k : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A initialArrays V [] s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Xlt : A aX < c) (Olt : A aOne < c) (marker : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (core name code) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (finishedState A c g.w g.words k).2.toNat ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  change WP isa (seqs ([table name code, copy aY aOne, .block initWindows] ++
    [.loop (wordStep name code) .ne, .block lastSquares, squareLoop name code,
      .block [.mov .eax (.mem (slot sFlag))]])) s _
  rw [seqs_append_iff]
  refine WP.mono (prepareRun_ok verified noSp stack v S length odd Xlt) fun a ⟨Sa, Oa, Ka⟩ => ?_
  change WP isa (.seq (.loop (wordStep name code) .ne) (.seq (.block lastSquares)
    (.seq (squareLoop name code) (.block [.mov .eax (.mem (slot sFlag))])))) a _
  have startLt : runValues A c g.w aY < c := by rw [runValues_y]; exact Olt
  have powersLt : ∀ j < 16, runValues A c g.w (aTable + j) < c := by
    intro j digit
    rw [runValues_power A c g.w digit]
    exact Word32.tp_lt (by omega_using [odd] : 0 < c) Xlt Olt j
  have tableOne : runValues A c g.w aTable = runValues A c g.w aOne := by
    rw [← runValues_identity, runValues_y, runValues_one]
  refine WP.seq (WP.mono (wordLoop_ok verified noSp stack v Sa length odd startLt runArrays_y runArrays_one
    runArrays_minus runArrays_exp runArrays_notX (fun _ digit => runArrays_power digit)
    tableOne powersLt false rfl rfl) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  have loB : b.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32) := by
    have R := roundFrame_marker32 v (Oa.trans Ob) (extra := 0) (Or.inl rfl)
    rw [Nat.add_zero] at R
    exact R.trans lo
  have hiB : b.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32) :=
    (roundFrame_marker32 v (Oa.trans Ob) (extra := 4) (Or.inr rfl)).trans hi
  refine WP.seq (WP.mono (Sb.lastSquares v marker loB hiB) fun d ⟨Sd, Od, Kd⟩ => ?_)
  have yBound : exponentValues (runValues A c g.w) c g.w g.words false g.words aY < c := by
    rw [exponentValues, setAt_self]
    exact exponentState_lt (runValues A c g.w) (by omega_using [odd] : 0 < c) g.w g.words false startLt g.words
  refine WP.seq (WP.mono (squareLoop_ok verified noSp stack v Sd length odd yBound runArrays_y runArrays_minus
    (by decide : 0 < 3) (by decide : 3 < 2 ^ 31) (by omega_using [] : 4 - VG.Proof.RsaKeyGen.sigOf k < 2 ^ 31)
    (exponentState (runValues A c g.w) c g.w g.words false g.words).2
    (by intro e mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl <;> decide) (by decide) rfl rfl rfl)
    fun e ⟨Se, Oe, Ke⟩ => ?_)
  refine wp_movS (Se.data.context.readScalar sFlag (by have := v.headerFit; unfold sFlag; omega_using [this]))
    fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, (((Ka.trans Kb).trans Kd).trans Ke).widen T.keeps⟩
  · rw [T.gpr, (Se.data.slotValues sFlag (by decide)).2]
    rfl
  · rw [T.mem]
    exact ((Oa.trans Ob).trans Od).trans Oe

end VG.Proof.MillerRabin.X86

end

end

/-! # The complete round body satisfies the reviewed mathematical result -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/EntryStage.lean`, which only this module imported.
section

/-! # ABI setup establishes the complete round stage with workspace-only writes -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86

def narrowed (s : State) : State := (entered s).withRegions (entered s).rd [⟨wsOf s, lenOf s⟩]

theorem Entry.narrowed_caller {s : State} (E : Entry s) :
    Caller (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (narrowed s) := by
  have C := E.caller
  refine ⟨C.sp, C.low, C.stackFar, C.lengthFar, C.lengthStackFar, ?_⟩
  change (narrowed s).load32 ((narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 1)) = _
  have ea : (narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 1) = argAddr s 1 := Compact.argument_address s 1
  rw [ea]
  have access : InRegions ((narrowed s).rd ++ (narrowed s).wr) (argAddr s 1) 4 := by
    change InRegions ((entered s).rd ++ _) _ _
    rw [entered, Compact.entered, pushed_rd, E.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    rw [argument_offset E (by decide : 1 < 2)]
    exact Offset.contains_base _ (by decide : 4 * 1 + 4 ≤ 8) (by decide)
  rw [State.load32, ite_eq_left access]
  change some ((entered s).mem.readW (argAddr s 1) 32) = _
  rw [E.pushed_arg (by decide : 1 < 2), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Entry.narrowed_base {s : State} (E : Entry s) :
    WP isa (.block [.mov .edi (.mem (at_ .esp 20))]) (narrowed s) fun t =>
      Stage (geometry s) (arg s 1).toNat (initialValues s 0) ((entered s).gpr .esp)
        (initialValues s) initialArrays (fun _ => 0) [] t ∧
      t.mem = (entered s).mem ∧ Keeps [.edi] (narrowed s) t := by
  have access : readSrc (narrowed s) (.mem (at_ .esp 20)) = some (arg s 0) := by
    change (narrowed s).load32 ((narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 0)) = _
    have ea : (narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 0) = argAddr s 0 := Compact.argument_address s 0
    rw [ea, State.load32]
    have region : InRegions ((narrowed s).rd ++ (narrowed s).wr) (argAddr s 0) 4 := by
      change InRegions ((entered s).rd ++ _) _ _
      rw [entered, Compact.entered, pushed_rd, E.rd]
      refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      simpa only [BitVec.add_zero] using
        (Offset.contains_base (argAddr s 0) (by decide : 0 + 4 ≤ 8) (by decide))
    rw [ite_eq_left region]
    exact congrArg some (E.pushed_arg (by decide : 0 < 2))
  refine wp_movS access fun t T _ => WP.block_nil ?_
  have mem : t.mem = (entered s).mem := T.mem
  have workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr := by
    rw [T.wr]
    exact List.mem_singleton_self _
  have base : PtrAt t (wsOf s) .edi 0 := by
    rw [PtrAt, T.gpr, Nat.add_zero, E.ws_toNat]
    exact (Nat.mod_eq_of_lt (arg s 0).isLt).symm
  refine ⟨⟨E.data mem workspace base, E.modulus mem, ?_, ?_⟩, mem, T.keeps⟩
  · apply E.narrowed_caller.keepFrame T.keeps (by decide)
    rw [T.mem]
    exact Frame.refl _ _
  · intro j known
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/NativeDigits32.lean`, which only this module imported.
section

/-! # A high-to-low native-word window is the corresponding exponent digit -/

section
namespace VG.Proof.MillerRabin

theorem exponentWindow_digit (E N j i : Nat) (word : j < N) (window : i < 8) :
    ((exponentWord E (N - 1 - j) <<< (4 * i)) >>> 28).toNat =
      E / 16 ^ (8 * N - 1 - (8 * j + i)) % 16 := by
  rw [Word32.shl_shr28 _ window, exponentWord, BitVec.toNat_ofNat,
    show 28 - 4 * i = 4 * (7 - i) by omega_using [],
    Word32.digit_word E (N - 1 - j) (7 - i) (by omega_using [])]
  rw [show 8 * (N - 1 - j) + (7 - i) = 8 * N - 1 - (8 * j + i) by omega_using [word, window]]

end VG.Proof.MillerRabin
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ExponentMath.lean`, which only this module imported.
section

/-! # The native-word execution order is the shared mathematical window run -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

theorem wordState_mrun (A : Nat → Nat) (c w E N j : Nat) (F : Bool)
    (word : j < N)
    (initial : (A aY, F) = Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) E (8 * N) (8 * j)) :
    ∀ i, i ≤ 8 → wordState A c w (exponentWord E (N - 1 - j)) F i =
      Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) E (8 * N) (8 * j + i)
  | 0, _ => by simpa only [wordState, Nat.add_zero] using initial
  | i + 1, bound => by
    rw [wordState, wordState_mrun A c w E N j F word initial i (by omega_using [bound]),
      show 8 * j + (i + 1) = (8 * j + i) + 1 by omega_using [], Word32.mrun,
      exponentWindow_digit E N j i word (by omega_using [bound])]

theorem powerView_setY (A : Nat → Nat) (y : Nat) :
    (fun d => setAt A aY y (aTable + d)) = (fun d => A (aTable + d)) := by
  funext d
  exact setAt_other _ _ (by unfold aTable aY; omega_using [])

theorem exponentState_mrun (A : Nat → Nat) (c w N : Nat) (one : A aY = A aTable) :
    ∀ j, j ≤ N → exponentState A c w N false j =
      Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) (A aExponent) (8 * N) (8 * j)
  | 0, _ => by
    change (A aY, false) = (A (aTable + 0), false)
    rw [Nat.add_zero, one]
  | j + 1, bound => by
    have ih := exponentState_mrun A c w N one j (by omega_using [bound])
    let st := exponentState A c w N false j
    let nextA := setAt A aY st.1
    have start : (nextA aY, st.2) =
        Word32.mrun c w (nextA aMinusOne) (fun d => nextA (aTable + d)) (A aExponent) (8 * N) (8 * j) := by
      change (setAt A aY st.1 aY, st.2) = _
      rw [setAt_self]
      change st = Word32.mrun c w (setAt A aY st.1 aMinusOne)
        (fun d => setAt A aY st.1 (aTable + d)) (A aExponent) (8 * N) (8 * j)
      rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), powerView_setY]
      exact ih
    have result := wordState_mrun nextA c w (A aExponent) N j st.2 (by omega_using [bound]) start 8 (by decide)
    change wordState nextA c w (exponentWord (A aExponent) (N - 1 - j)) st.2 8 = _
    rw [result]
    change Word32.mrun c w (setAt A aY st.1 aMinusOne) (fun d => setAt A aY st.1 (aTable + d))
      (A aExponent) (8 * N) (8 * j + 8) = _
    rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), powerView_setY,
      show 8 * j + 8 = 8 * (j + 1) by omega_using []]

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/TableCongr32.lean`, which only this module imported.
section

/-! # A window run reads only the sixteen represented table powers -/

section
namespace VG.Proof.MillerRabin.Word32

theorem mwin_table_congr {T U : Nat → Nat} (table : ∀ d < 16, T d = U d)
    (c w M d : Nat) (digit : d < 16) (s : Nat × Bool) : mwin c w M T d s = mwin c w M U d s := by
  unfold mwin
  rw [table d digit, table 0 (by decide)]

theorem mrun_table_congr {T U : Nat → Nat} (table : ∀ d < 16, T d = U d)
    (c w M E W j : Nat) : mrun c w M T E W j = mrun c w M U E W j := by
  induction j with
  | zero => rw [mrun, mrun, table 0 (by decide)]
  | succ j ih =>
    rw [mrun, mrun, ih]
    exact mwin_table_congr table c w M _ (Nat.mod_lt _ (by decide)) _

end VG.Proof.MillerRabin.Word32
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ResultMath.lean`, which only this module imported.
section

/-! # The complete native-window result is the reviewed Miller–Rabin test -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem finishedState_eq {A : Nat → Nat} {c w b : Nat}
    (odd : c % 2 = 1) (minimum : 3 ≤ c) (fits : c < 2 ^ (64 * w))
    (witness : A aX = b % c * 2 ^ (64 * w) % c)
    (one : A aOne = 2 ^ (64 * w) % c) (minus : A aMinusOne = c - 2 ^ (64 * w) % c)
    (exponent : A aExponent = mrE c) :
    (finishedState A c w (2 * w) (mrA c % 64)).2 = Proof.MillerRabin.Round.round c b := by
  change (Word32.msqs c w (runValues A c w aMinusOne) (4 - sigOf (mrA c % 64)) 3
    (exponentState (runValues A c w) c w (2 * w) false (2 * w)) 3).2 = _
  rw [runValues_minus, sigOf_mod, exponentState_mrun (runValues A c w) c w (2 * w)
    (runValues_identity A c w) (2 * w) (Nat.le_refl _), runValues_minus, runValues_exp]
  have table : ∀ j < 16, runValues A c w (aTable + j) = Word32.tp c w (A aX) (A aOne) j :=
    fun j digit => runValues_power A c w digit
  rw [Word32.mrun_table_congr table c w (A aMinusOne) (A aExponent) (8 * (2 * w)) (8 * (2 * w)),
    show 8 * (2 * w) = 16 * w by omega_using [], exponent]
  exact Word32.final_eq odd minimum fits witness one minus

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.RsaKeyGen
open VG.Impl.MillerRabin.X86

def Result (s : State) (t : State) : Prop :=
  (∀ b, initialValues s aX = b % initialValues s 0 * 2 ^ (64 * (geometry s).w) % initialValues s 0 →
    (t.gpr .eax).toNat = if Proof.MillerRabin.Round.round (initialValues s 0) b then 1 else 0) ∧
  WorkspaceFrame (geometry s) (roundWrites (geometry s)) (entered s).mem t.mem

theorem Entry.narrowed_body {s : State} (E : Entry s) :
    WP isa (body montName montCode) (narrowed s) fun t =>
      Result s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (narrowed s) t := by
  unfold body
  refine WP.seq (WP.mono E.narrowed_base fun t ⟨S, mem, K⟩ => ?_)
  obtain ⟨minimum, odd, _, Xlt, one, minus, exponent, _⟩ := E.prepared
  change 3 ≤ initialValues s 0 at minimum
  change initialValues s 0 % 2 = 1 at odd
  change initialValues s aX < initialValues s 0 at Xlt
  change initialValues s aOne = 2 ^ (64 * (geometry s).w) % initialValues s 0 at one
  change initialValues s aMinusOne = initialValues s 0 - 2 ^ (64 * (geometry s).w) % initialValues s 0 at minus
  change initialValues s aExponent = mrE (initialValues s 0) at exponent
  have marker := E.marker
  rw [← mem] at marker
  have Olt : initialValues s aOne < initialValues s 0 := by
    rw [one]
    exact Nat.mod_lt _ (by omega_using [minimum])
  refine WP.mono (core_ok VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack E.valid S
    (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega_using []) odd Xlt Olt (Nat.mod_lt _ (by decide)) marker.1 marker.2)
    fun u ⟨value, frame, keep⟩ => ?_
  refine ⟨⟨?_, ?_⟩, (K.mono (by decide)).widen keep⟩
  · intro b witness
    have fits : initialValues s 0 < 2 ^ (64 * (geometry s).w) := by
      rw [initialValues, Compact.numAt_val32]
      have := val32_lt s.mem (wsOf s) (Proof.Rsa.Mont.arrAt (geometry s).w 0) (2 * (geometry s).w)
      simpa only [show 32 * (2 * (geometry s).w) = 64 * (geometry s).w by omega_using []] using this
    have final := finishedState_eq odd minimum fits witness one minus exponent
    change u.gpr .eax = BitVec.ofNat 32
      (finishedState (initialValues s) (initialValues s 0) (geometry s).w (2 * (geometry s).w)
        (mrA (initialValues s 0) % 64)).2.toNat at value
    rw [value, final]
    cases Proof.MillerRabin.Round.round (initialValues s 0) b <;> rfl
  · rw [mem] at frame
    exact frame

end VG.Proof.MillerRabin.X86

end

end

/-! # The prepared round restores the i686 ABI after its nested calls -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/BodyFrame.lean`, which only this module imported.
section

/-! # Nested calls write below the saved i686 register frame -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem Entry.body {s : State} (E : Entry s) :
    WP isa (body montName montCode) (entered s) fun t =>
      Result s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t ∧
      Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem := by
  have writable : Covers [⟨wsOf s, lenOf s⟩] (entered s).wr := by
    apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    rw [entered, Compact.entered, pushed_wr, E.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  refine WP.narrowSp E.narrowed_body ?_ writable body_noSp ?_ ?_
  · exact Covers.append (Covers.refl _) writable
  · have := E.caller.low
    exact Nat.le_trans body_stack this
  · intro t rd wr F R
    refine ⟨R.1, ⟨R.2.1, rd, wr⟩, ?_⟩
    apply F.sub
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · exact ⟨r, List.mem_append_left _ mem, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub body_stack E.caller.low⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/SavedFrame.lean`, which only this module imported.
section

/-! # Nested-call stack writes leave the round's saved registers intact -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def savedRegion (s : State) : Region := ⟨((entered s).gpr .esp).setWidth 64, 16⟩

theorem savedRegion_eq (s : State) : savedRegion s = below (s.gpr .esp) 16 := by
  unfold savedRegion entered Compact.entered
  rw [pushed_esp]
  rfl

theorem Entry.saved_stack_far {s : State} (E : Entry s) :
    (savedRegion s).Disjoint (below ((entered s).gpr .esp) 80) := by
  have low := E.stackFit
  have innerLow : 80 ≤ ((entered s).gpr .esp).toNat := by
    rw [entered, Compact.entered, pushed_esp]
    change 80 ≤ (s.gpr .esp - 16#32).toNat
    rw [sub_toNat (by omega)]
    omega
  unfold savedRegion below
  rw [Taint.sub_setWidth innerLow]
  exact Offset.base_disjoint_below _ (by decide : 16 + 80 ≤ 2 ^ 64)

theorem Entry.saved_read {s t : State} (E : Entry s)
    (F : Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem)
    {i : Nat} (index : i < 4) :
    t.mem.readW (addr ((entered s).gpr .esp) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have low := E.stackFit
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by omega)]
    have := (s.gpr .esp).isLt
    omega
  have contained : (savedRegion s).Contains (addr ((entered s).gpr .esp) (4 * i)) 4 := by
    rw [addr_eq (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  have same := F.readW (r := savedRegion s) (w := 32) contained (by
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · rw [savedRegion_eq]; exact E.savedSeparate
    · exact E.saved_stack_far) (by decide : 32 / 8 < 2 ^ 64)
  exact same.trans (pushed_word (rs := Compact.savedRegisters) (by decide) (by change 16 ≤ _; omega) index)

theorem Entry.return_read {s t : State} (E : Entry s)
    (F : Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have sub : Region.Sub (below ((entered s).gpr .esp) 80) (below (s.gpr .esp) 96) := by
    rw [entered, Compact.entered, pushed_esp]
    exact below_inner (by decide : 80 + 16 ≤ 96) E.stackFit
  have outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 96) := by
    unfold below
    rw [Taint.sub_setWidth E.stackFit]
    exact Offset.base_disjoint_below _ (by decide : 4 + 96 ≤ 2 ^ 64)
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact E.returnSeparate
    · exact outside.sub_right sub) (by decide : 32 / 8 < 2 ^ 64)
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega)
  refine same.trans (saved.readW (Region.contains_self _ _) ?_ (by decide))
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact outside.sub_right (below_sub (by decide) E.stackFit)

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem inner_noSp : NoSp (.seq (body montName montCode) (.block VG.Impl.Mont.X86.Compact.restoreRegs)) :=
  .of_all (by decide +kernel)

theorem Result.keep {s t u : State} (R : Result s t)
    (eax : u.gpr .eax = t.gpr .eax) (mem : u.mem = t.mem) : Result s u := by
  unfold Result at *
  rw [eax, mem]
  exact R

/-- The result, whatever the bytes of the push are and the unknowns. -/
theorem Result.frame {s t : State} (E : Entry s) (R : Result s t) {m : Mem} {u : Nat → BitVec 32}
    (fl : Frame [below (s.gpr .esp) 16] t.mem m) : Result s { t with mem := m, unknowns := u } := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := E.stackFit; omega_using [this]
  have far : (below (s.gpr .esp) 16).Disjoint ⟨wsOf s, lenOf s⟩ := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact E.stackSeparate.sub_left (Offset.sub_below _ (by decide) (by decide))
  have wk : WorkspaceFrame (geometry s) [] t.mem m := fun i index _ =>
    fl.bytes (R := ⟨wsOf s, lenOf s⟩) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact far.symm)
      (by change lenOf s ≤ 2 ^ 64; have := E.bound; omega_using [this]) index
  exact ⟨R.1, R.2.trans (wk.mono fun _ mem => nomatch mem)⟩

theorem Entry.framed {s : State} (E : Entry s) :
    WP isa (code montName montCode) s fun t => abiPreserved s t ∧ Result s t := by
  unfold code
  have fit16 : 16 ≤ (s.gpr .esp).toNat := by have := E.stackFit; omega_using [this]
  refine WP.frameLocal (rs := Compact.savedRegisters) (by decide) (by decide) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega_using [this]) inner_noSp
    (fun t m _ ⟨abi, R⟩ fl => ⟨Compact.abi_frame fit16 abi fl, R.frame E fl⟩) ?_
  refine WP.seq (WP.mono E.body fun t ⟨R, K, F⟩ => ?_)
  have sp : t.gpr .esp = (entered s).gpr .esp := K.1 .esp (by decide)
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by have := E.stackFit; omega_using [this])]
    have := (s.gpr .esp).isLt
    omega_using []
  have read (i : Nat) (index : i < 4) :
      readSrc t (.mem (at_ .esp (4 * i))) = some
        (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega_using []))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp, entered, Compact.entered, pushed_wr]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      rw [← savedRegion_eq]
      change (savedRegion s).Contains (addr ((entered s).gpr .esp) (4 * i)) 4
      rw [addr_eq (by omega_using [fit, index])]
      exact Offset.contains_base _ (by omega_using [index]) (by omega_using [index])
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, E.saved_read F index]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = (entered s).gpr .esp := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, sp', mem]
      exact E.saved_read F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', entered, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact E.return_read F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]

end VG.Proof.MillerRabin.X86

end

end

/-! # Verified prepared fixed-window Miller–Rabin on baseline i686 -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/Correct.lean`, which only this module imported.
section

/-! # The callable i686 round meets the existing Miller–Rabin contract -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem Entry.pushed_byte {s : State} (E : Entry s) {i : Nat} (index : i < lenOf s) :
    (entered s).mem (off (wsOf s) i) = s.mem (off (wsOf s) i) := by
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega)
  apply saved
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  intro inside
  apply E.savedSeparate _ inside
  exact Offset.contains_base _ (by omega) (by have := E.bound; omega)

theorem correct (s : State)
    (h : (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre s) :
    ∃ tr t, Exec isa (code montName montCode) s tr t ∧ abiPreserved s t ∧
      (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).post s t := by
  have E := entry_of h
  obtain ⟨tr, t, exec, abi, result, frame⟩ := E.framed
  refine ⟨tr, t, exec, abi, ?_⟩
  sig_post [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes]
  refine ⟨?_, ?_⟩
  · intro b witness
    rw [BitVec.setWidth_append_eq_right]
    exact result b witness
  · apply roundFrame_keeps (g := geometry s) (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega)
    intro i index outside
    exact (frame i index outside).trans (E.pushed_byte index)

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem verified : Verified target (VG.Impl.MillerRabin.X86.code montName montCode)
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.MillerRabin.X86

end

end


/-! # The verified baseline prepared round on i686 -/

@[expose] public section
namespace VG.Proof.Variants.MillerRabin.X86.Base
open VG VG.Proof.MillerRabin.X86

def variant : RoundImpl where
  code := Impl.MillerRabin.X86.code montName montCode
  verified := VG.Proof.MillerRabin.X86.verified
  noSp := code_noSp
  spSafe := by decide +kernel
  stack := code_stack
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.X86.Base
