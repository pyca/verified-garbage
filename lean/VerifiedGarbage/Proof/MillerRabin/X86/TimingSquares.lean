module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
import VerifiedGarbage.Proof.MillerRabin.X86.SquareStep
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPrivate
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
public import VerifiedGarbage.Proof.MillerRabin.X86.Equal
import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `MillerRabin.X86.TimingSquareStep`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.TimingEqual`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.TimingReadonly`, which this module and modules that import it used -/

section

/-! # Retain the prepared geometry across read-only timing blocks -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

theorem readonly_relCT {g : Geometry} {code : Prog isa} {before after : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (roundTaint before)) code (VG.X86.Taint.Agree (roundTaint after)))
    (correct : ∀ s, Context g s → WP isa code s fun t => t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t) :
    RelCT isa (Pair g before) code (Pair g after) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := raw _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, Ku⟩ := wp_result (correct s H.1) E
  obtain ⟨Mz, Kz⟩ := wp_result (correct t H.2.1) G
  exact ⟨trace, H.1.keepMem Ku (by decide) Mu, H.2.1.keepMem Kz (by decide) Mz, A⟩

end VG.Proof.MillerRabin.X86

end

end

/-! # Full-width equality scans use public addresses and counters -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def equalRegisters : List Reg := [.esi, .ecx, .ebp, .edi]

theorem equalZero_relCT {g : Geometry} :
    RelCT isa (Pair g equalRegisters) (.block [.mov .ebx (.imm 0)]) (Pair g equalRegisters) := by
  refine readonly_relCT (checkedProgramChange (hint := .block [])
    (τ' := roundTaint (.ebx :: equalRegisters)) (by kernel_rfl) (by kernel_rfl)) ?_
  intro s _
  exact wp_movS rfl fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem equalLoop_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint equalRegisters))
    (.loop (.block equalBody) .ne) (VG.X86.Taint.Agree (roundTaint equalRegisters)) :=
  checkedProgramChange (τ' := roundTaint equalRegisters true)
    (hint := VG.Taint.hintOf taint (roundTaint equalRegisters) (.loop (.block equalBody) .ne)) (by kernel_rfl) (by kernel_rfl)

theorem equalFinish_raw (result : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
      (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1), .alu .adc .eax (.imm 0), .store (slot result) .eax])
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
    .alu .adc .eax (.imm 0), .store (slot 0) .eax]) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem equal_trace {g : Geometry} (v : g.Valid) (result a b : Nat) (ai : a < 28) (bi : b < 28) :
    RelCT isa (Pair g [.edi]) (equal result a b) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold equal
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp a (by decide) ai [.edi] (by decide))
    (RelCT.block_append (RelCT.seq
      (pointer_pair_relCT v .ecx b (by decide) bi [.ebp, .edi] (by decide))
      (RelCT.block_append (RelCT.seq
        (words_pair_relCT v [.ecx, .ebp, .edi] (by decide)) equalZero_relCT)))))) ?_
  refine RelCT.seq (equalLoop_raw.mono (P' := Pair g equalRegisters) (fun _ _ H => H.2.2) (fun _ _ H => H)) ?_
  exact (equalFinish_raw result).mono (fun _ _ H => round_add_regs (round_forget H) fun r mem =>
    round_regs H (by obtain rfl := List.mem_singleton.mp mem; decide)) (fun _ _ H => H)

theorem equal_relCT {g : Geometry} (v : g.Valid) (result a b : Nat)
    (scratch : scratchWord result) (ai : a < 28) (bi : b < 28) :
    RelCT isa (Pair g [.edi]) (equal result a b) (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := equal_trace v result a b ai bi _ _ _ _ _ _ H E G
  have fit : result + 4 ≤ g.L := Nat.le_trans (scratch_fit scratch) v.headerFit
  obtain ⟨_, Ou, Ku⟩ := wp_result (equal_ok v H.1 result a b fit ai bi) E
  obtain ⟨_, Oz, Kz⟩ := wp_result (equal_ok v H.2.1 result a b fit ai bi) G
  exact ⟨trace, H.1.keepScalar Ku (by decide) Ou scratch, H.2.1.keepScalar Kz (by decide) Oz scratch, A⟩

end VG.Proof.MillerRabin.X86

end

end

/-! # Squaring and masked flag updates have a public-address trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem squareStep_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity aY p s ∧ MulInput g capacity aY p t)
      (squareStep name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (mulY name code aY)
    (.seq (equal sEq2 aY aMinusOne) (.block squareFlag))) _
  refine RelCT.seq (mulY_relCT verified noSp stack v length (by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide)) ?_
  exact RelCT.seq (equal_relCT v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp) (by decide) (by decide))
    (squareFlag_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H))

end VG.Proof.MillerRabin.X86

end

end

/-! # A public square count controls the loop; the threshold remains secret -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def SquareInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ c A V r, ∃ flag : Bool,
    Stage g capacity c p A [aY, aMinusOne] V [sSquares, sThreshold, sFlag] s ∧
    c % 2 = 1 ∧ A aY < c ∧ r < 2 ^ 31 ∧ q < 2 ^ 31 ∧
    V sSquares = BitVec.ofNat 32 q ∧ V sThreshold = BitVec.ofNat 32 r ∧ V sFlag = BitVec.ofNat 32 flag.toNat

theorem SquareInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) : Context g s := by
  obtain ⟨_, _, _, _, _, S, _⟩ := I
  exact S.data.context

theorem SquareInput.mulInput {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) : MulInput g capacity aY p s := by
  obtain ⟨c, A, V, r, F, S, odd, lt, _⟩ := I
  refine ⟨S.data.context, ⟨c, S.modulus, odd, ?_⟩, S.caller⟩
  rw [(S.data.arrayValues aY (by decide)).2]
  exact lt

theorem SquareInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (squareStep name code) s fun t => SquareInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨c, A, V, r, F, S, odd, lt, rBound, qBound, count, threshold, flag⟩ := I
  refine WP.mono (squareStep_ok verified noSp stack v S length odd lt (by decide) (by decide)
    positive qBound rBound F (by intro d mem; exact mem) count threshold flag) fun t ⟨St, Z, _, _⟩ => ?_
  let Y := Word32.mm c g.w (A aY) (A aY)
  let E := decide (Y = A aMinusOne)
  refine ⟨⟨c, setAt A aY Y, squareSlots (setAt V sEq2 (BitVec.ofNat 32 E.toNat)) q r E F,
    r, F || (decide (r < q) && E), ?_, odd, ?_, rBound, by omega_using [qBound], rfl, ?_, ?_⟩, Z⟩
  · exact St.mono (fun j mem => ⟨mem, rfl⟩) (by
      intro d mem
      refine ⟨?_, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl | rfl <;> simp)
  · rw [setAt_self]
    exact Word32.mm_lt (by omega_using [odd] : 0 < c)
  · exact threshold
  · change BitVec.ofNat 32 (F || (E && decide (r < q))).toNat = _
    rw [Bool.and_comm]

end VG.Proof.MillerRabin.X86
