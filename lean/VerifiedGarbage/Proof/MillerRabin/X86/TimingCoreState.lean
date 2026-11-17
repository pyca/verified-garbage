module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquares
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
public import VerifiedGarbage.Proof.MillerRabin.X86.SelectLoop
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MillerRabin.X86.DataSquareControl
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.MillerRabin.X86.ModulusKeep

/-! ### `MillerRabin.X86.MarkerPointer`, which only this module used -/

section

/-! # The exponent marker is addressed using only the prepared public width -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem Geometry.Valid.markerFit {g : Geometry} (v : g.Valid) :
    g.array aExponent + 4 * g.words + 8 ≤ g.L := by
  have fit := v.arraysFit
  unfold Geometry.array Geometry.words aExponent Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at *
  omega_using [fit]

theorem markerPointer_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block markerPointer) s fun t =>
      PtrAt t g.W .ebp (g.array aExponent + 4 * g.words) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp, .esi] s t := by
  unfold markerPointer
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (C.ptr v aExponent (by decide) .ebp (by decide) (by decide))
    fun a ⟨P, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (words_ok v Ca) fun b ⟨Count, Mb, Kb⟩ => ?_)
  refine wp_movS rfl fun c D _ => wp_addS rfl fun d H _ => wp_addS rfl fun e I _ => ?_
  have Ke : Keeps [.eax, .edx, .ebp, .esi] s e :=
    (((((Ka.mono (by decide)).trans (Kb.mono (by decide))).widen D.keeps).widen H.keeps).widen I.keeps)
  have bp : PtrAt e g.W .ebp (g.array aExponent) := by
    rw [PtrAt, I.other .ebp (by decide), H.other .ebp (by decide), D.other .ebp (by decide),
      Kb.1 .ebp (by decide)]; exact P
  have width : (e.gpr .eax).toNat = 4 * g.words := by
    rw [I.gpr, H.gpr, D.gpr]
    simp only [BitVec.toNat_add, Count]
    have bound := v.maxWidth
    unfold Geometry.words
    omega_using [bound]
  refine wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, Ke.widen T.keeps⟩
  · rw [PtrAt, T.gpr, ptr_add bp, width]
  · rw [T.mem, I.mem, H.mem, D.mem, Mb, Ma]

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.StageLiteral`, which only this module used -/

section

/-! # Initialize a public counter without disturbing prepared round data -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem Stage.literal {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d : Nat) (scratch : scratchWord d) (value : BitVec 32) :
    WP isa (.block [.mov .eax (.imm value), .store (slot d) .eax]) s fun t =>
      Stage g capacity c p A Js (setAt V d value) (d :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  have fit : d + 4 ≤ g.L := Nat.le_trans (scratch_fit scratch) v.headerFit
  refine wp_movS rfl fun a A₁ _ => ?_
  have Ca := S.data.context.keepMem A₁.keeps (by decide) A₁.mem
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := d) (by omega_using [fit]))
    (ws_write Ca.ws (y := 0 + d) (n := 4) (by omega_using [fit])) fun t T => WP.block_nil ?_
  have O : Outside g.W d 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add, A₁.mem]
    exact writeW32_outside _ _ _ (by have := S.data.context.ws.nowrap; omega_using [fit, this])
  have K : Keeps [.eax] s t := A₁.keeps.widen (T.keeps [])
  have C := S.data.context.keepScalar K (by decide) O scratch
  have stored : t.mem.readW (off g.W d) 32 = value := by
    rw [T.mem, Nat.zero_add, Mem.readW_writeW_self32, A₁.gpr]
  have D := S.data.afterScalar v C d scratch value O stored
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] (by intro e mem; obtain rfl := List.mem_singleton.mp mem; exact scratch)
    outs K (by decide), scalar_roundFrame S.data.context.ws.nowrap (rs := [d])
      (by intro e mem; obtain rfl := List.mem_singleton.mp mem; exact scratch) outs, K⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.StageCopy`, which only this module used -/

section

/-! # Array copies preserve all invariants needed by the next prepared product -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataCopy.lean`, which only this module imported.
section

/-! # Copying a prepared array as a value-state transition -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.copy {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (dst src : Nat) (dstIndex : dst < 28) (srcKnown : src ∈ Js) :
    WP isa (copy dst src) s fun t =>
      Data g (setAt A dst (A src)) (dst :: Js) V Ds t ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  have source := D.arrayValues src srcKnown
  refine WP.mono (copy_ok v D.context dst src dstIndex source.1) fun t ⟨Value, O, K, C⟩ => ?_
  refine ⟨⟨C, ?_, ?_⟩, O, K⟩
  · intro j known
    by_cases same : j = dst
    · subst j
      exact ⟨dstIndex, by rw [setAt_self, Value, source.2]⟩
    · have old : j ∈ Js := by
        rcases List.mem_cons.mp known with bad | old
        · exact False.elim (same bad)
        · exact old
      obtain ⟨index, read⟩ := D.arrayValues j old
      have sep := (g.arraysApart dst j).resolve_left (g.array_ne (fun eq => same eq.symm))
      refine ⟨index, ?_⟩
      rw [O.val32 (by omega) (by have := v.arrayFit index; have := C.ws.nowrap; omega), read,
        setAt_other A (A src) same]
  · intro d known
    obtain ⟨scratch, read⟩ := D.slotValues d known
    refine ⟨scratch, ?_⟩
    have header := v.arrayHeader dst
    have bound := scratch_fit scratch
    have unchanged := BitVec.eq_of_toNat_eq (O.w32 (d := d) (by omega) (by omega))
    exact unchanged.trans read

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.copy {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (dst src : Nat) (index : dst < 28) (notMod : 0 < dst) (notScratch : dst ≠ 2 ∧ dst ≠ 3)
    (source : src ∈ Js) :
    WP isa (copy dst src) s fun t =>
      Stage g capacity c p (setAt A dst (A src)) (dst :: Js) V Ds t ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.copy v dst src index source) fun t ⟨D, O, K⟩ => ?_
  refine ⟨⟨D, S.modulus.keepArray v S.data.context.ws.nowrap notMod O, ?_, ?_⟩, O, K⟩
  · exact S.caller.keepOuts K (by decide) (Outs.of_outside O (List.mem_singleton_self _)) (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact v.arrayFit index)
  · intro j mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact notScratch
    · exact S.noScratch j mem

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingSquareLoop`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.TimingAttach`, which this module and modules that import it used -/

section

/-! # Attach each run's functional invariant to a checked public-address trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Dsa.X86

theorem private_attach {α : Type} {g : Geometry} {F G : α → State → Prop} {code : Prog isa}
    (trace : RelCT isa (Two g F) code (VG.X86.Taint.Agree (roundTaint [.edi])))
    (step : ∀ σ s, F σ s → WP isa code s (G σ))
    (context : ∀ σ s, G σ s → Context g s) :
    RelCT isa (Two g F) code (Two g G) := by
  intro s t tr ur u z H E B
  obtain ⟨same, A⟩ := trace _ _ _ _ _ _ H E B
  obtain ⟨_, ⟨σ, S⟩, ⟨ρ, T⟩⟩ := H
  have Gu := wp_result (step σ s S) E
  have Gz := wp_result (step ρ t T) B
  exact ⟨same, ⟨context σ u Gu, context ρ z Gz, A⟩, ⟨σ, Gu⟩, ⟨ρ, Gz⟩⟩

theorem ne_of_zf {s : State} {q : Nat} (positive : 0 < q) (Z : s.zf = some (decide (q = 1))) :
    isa.eval .ne s = some (decide (1 < q)) := by
  change Option.map Bool.not s.zf = _
  rw [Z]
  by_cases eq : q = 1
  · simp [eq]
  · have more : 1 < q := by omega_using [positive, eq]
    simp [eq, more]

theorem private_control {α : Type} {g : Geometry} {F G : α → State → Prop} {code : Prog isa} {q : Nat}
    (trace : RelCT isa (Two g F) code (VG.X86.Taint.Agree (roundTaint [.edi])))
    (step : ∀ σ s, F σ s → WP isa code s fun t => G σ t ∧ t.zf = some (decide (q = 1)))
    (context : ∀ σ s, G σ s → Context g s) (positive : 0 < q) :
    RelCT isa (Two g F) code fun s t => Two g G s t ∧
      isa.eval .ne s = some (decide (1 < q)) ∧ isa.eval .ne t = some (decide (1 < q)) := by
  intro s t tr ur u z H E B
  obtain ⟨same, A⟩ := trace _ _ _ _ _ _ H E B
  obtain ⟨_, ⟨σ, S⟩, ⟨ρ, T⟩⟩ := H
  obtain ⟨Gu, Zu⟩ := wp_result (step σ s S) E
  obtain ⟨Gz, Zz⟩ := wp_result (step ρ t T) B
  refine ⟨same, ⟨⟨context σ u Gu, context ρ z Gz, A⟩, ⟨σ, Gu⟩, ⟨ρ, Gz⟩⟩, ?_, ?_⟩
  · exact ne_of_zf positive Zu
  · exact ne_of_zf positive Zz

end VG.Proof.MillerRabin.X86

end

end

/-! # The square loop branches only on its public countdown -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem squareLoop_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ SquareInput g capacity p q s ∧ SquareInput g capacity p q t)
      (squareLoop name code) (Pair g [.edi]) := by
  unfold squareLoop
  refine (private_count_loop (F := fun q (_ : Unit) s => SquareInput g capacity p q s) ?_ q positive).mono
    (fun _ _ H => ⟨H.1, ⟨(), H.2.1⟩, ⟨(), H.2.2⟩⟩) (fun _ _ H => H.1)
  intro n positive
  refine private_control ?_ (fun _ s I => I.step verified noSp stack v length positive)
    (fun _ _ I => I.context) positive
  exact (squareStep_trace verified noSp stack v length).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.mulInput, H.2.2.choose_spec.mulInput⟩) (fun _ _ H => H)

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingStage`, which this module and modules that import it used -/

section

/-! # Functional round stages supply the guards of timing compositions -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86

theorem Stage.mulInput {g : Geometry} {capacity c b : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (odd : c % 2 = 1) (known : b ∈ Js) (lt : A b < c) :
    MulInput g capacity b p s := by
  refine ⟨S.data.context, ⟨c, S.modulus, odd, ?_⟩, S.caller⟩
  rw [(S.data.arrayValues b known).2]
  exact lt

theorem Stage.squareInput {g : Geometry} {capacity c q r : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (odd : c % 2 = 1) (lt : A aY < c)
    (y : aY ∈ Js) (minus : aMinusOne ∈ Js) (rBound : r < 2 ^ 31) (qBound : q < 2 ^ 31)
    (F : Bool) (known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) : SquareInput g capacity p q s := by
  refine ⟨c, A, V, r, F, S.mono ?_ ?_, odd, lt, rBound, qBound, count, threshold, flag⟩
  · intro j mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨y, rfl⟩
    · exact ⟨minus, rfl⟩
  · exact fun d mem => ⟨known d mem, rfl⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.StageLastSquares`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.MarkerCalc`, which only this module used -/

section

/-! # Native instructions fold the secret exponent marker without branching -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/MarkerMath.lean`, which only this module imported.
section

/-! # Folding the exponent marker derives the final secret square threshold -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86

private theorem double_eq_shift (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

def markerFold (lo hi : BitVec 32) : BitVec 32 :=
  let x1 := lo ||| hi
  let x2 := x1 ||| x1 >>> 16
  let x3 := x2 ||| x2 >>> 8
  let x4 := x3 ||| x3 >>> 4
  let b1 := x4 >>> 1 &&& 1
  let b2 := x4 >>> 2 &&& 1
  let b3 := x4 >>> 3 &&& 1
  b3 + b1 + b1 + b1 + b2 + b2

theorem markerFold_eq (lo hi : BitVec 32) : markerFold lo hi = Word32.foldR lo hi := by
  unfold markerFold Word32.foldR
  dsimp only
  rw [← double_eq_shift, ← double_eq_shift]
  simp only [BitVec.add_assoc]
  rfl

theorem markerFold_twoPow {k : Nat} (bound : k < 64) :
    markerFold (BitVec.ofNat 32 (2 ^ k % 2 ^ 32)) (BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) =
      BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k) := by
  rw [markerFold_eq]
  exact Word32.foldR_eq k bound

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem markerCalc_ok {s : State} {W : Addr} {L d : Nat} (hw : Ws s W L)
    (ptr : PtrAt s W .ebp d) (fit : d + 8 ≤ L) :
    WP isa (.block markerCalc) s fun t =>
      t.gpr .eax = markerFold (s.mem.readW (off W d) 32) (s.mem.readW (off W (d + 4)) 32) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold markerCalc
  refine wp_movS (readSrc_ptr hw ptr (d := 0) (by omega_using [fit])) fun s1 u1 _ => ?_
  have bp1 : PtrAt s1 W .ebp d := by rw [PtrAt, u1.other .ebp (by decide)]; exact ptr
  refine wp_orS (readSrc_ptr (hw.of_keeps u1.keeps) bp1 (d := 4) fit) fun s2 u2 => ?_
  refine wp_movS rfl fun s3 u3 _ => ?_
  refine wp_shr (by decide) fun s4 u4 _ => ?_
  refine wp_orS rfl fun s5 u5 => ?_
  refine wp_movS rfl fun s6 u6 _ => ?_
  refine wp_shr (by decide) fun s7 u7 _ => ?_
  refine wp_orS rfl fun s8 u8 => ?_
  refine wp_movS rfl fun s9 u9 _ => ?_
  refine wp_shr (by decide) fun s10 u10 _ => ?_
  refine wp_orS rfl fun s11 u11 => ?_
  refine wp_movS rfl fun s12 u12 _ => ?_
  refine wp_shr (by decide) fun s13 u13 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s14 u14 => ?_
  refine wp_movS rfl fun s15 u15 _ => ?_
  refine wp_shr (by decide) fun s16 u16 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s17 u17 => ?_
  refine wp_shr (by decide) fun s18 u18 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s19 u19 => ?_
  refine wp_addS rfl fun s20 u20 _ => ?_
  refine wp_addS rfl fun s21 u21 _ => ?_
  refine wp_addS rfl fun s22 u22 _ => ?_
  refine wp_addS rfl fun s23 u23 _ => ?_
  refine wp_addS rfl fun s24 u24 _ => ?_
  refine WP.block_nil ⟨?_, ?_, ((((((((((((((((((((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen u9.keeps).widen u10.keeps).widen u11.keeps).widen u12.keeps).widen u13.keeps).widen u14.keeps).widen u15.keeps).widen u16.keeps).widen u17.keeps).widen u18.keeps).widen u19.keeps).widen u20.keeps).widen u21.keeps).widen u22.keeps).widen u23.keeps).widen u24.keeps)⟩
  · let x1 := s.mem.readW (off W d) 32 ||| s.mem.readW (off W (d + 4)) 32
    let x2 := x1 ||| x1 >>> 16
    let x3 := x2 ||| x2 >>> 8
    let x4 := x3 ||| x3 >>> 4
    have v2 : s2.gpr .eax = x1 := by rw [u2.gpr, u1.gpr, u1.mem, Nat.add_zero]
    have v5 : s5.gpr .eax = x2 := by
      rw [u5.gpr, u4.other .eax (by decide), u3.other .eax (by decide), v2, u4.gpr, u3.gpr, v2]
    have v8 : s8.gpr .eax = x3 := by
      rw [u8.gpr, u7.other .eax (by decide), u6.other .eax (by decide), v5, u7.gpr, u6.gpr, v5]
    have v11 : s11.gpr .eax = x4 := by
      rw [u11.gpr, u10.other .eax (by decide), u9.other .eax (by decide), v8, u10.gpr, u9.gpr, v8]
    have v14 : s14.gpr .edx = x4 >>> 1 &&& 1 := by
      rw [u14.gpr, u13.gpr, u12.gpr, v11]
      rfl
    have v17 : s17.gpr .ebx = x4 >>> 2 &&& 1 := by
      rw [u17.gpr, u16.gpr, u15.gpr, u14.other .eax (by decide), u13.other .eax (by decide),
        u12.other .eax (by decide), v11]
      rfl
    have v19 : s19.gpr .eax = x4 >>> 3 &&& 1 := by
      rw [u19.gpr, u18.gpr, u17.other .eax (by decide), u16.other .eax (by decide),
        u15.other .eax (by decide), u14.other .eax (by decide), u13.other .eax (by decide),
        u12.other .eax (by decide), v11]
      rfl
    have d19 : s19.gpr .edx = x4 >>> 1 &&& 1 := by
      rw [u19.other .edx (by decide), u18.other .edx (by decide), u17.other .edx (by decide),
        u16.other .edx (by decide), u15.other .edx (by decide), v14]
    have b19 : s19.gpr .ebx = x4 >>> 2 &&& 1 := by
      rw [u19.other .ebx (by decide), u18.other .ebx (by decide), v17]
    rw [u24.gpr, u23.gpr, u22.gpr, u21.gpr, u20.gpr, v19,
      u23.other .ebx (by decide), u22.other .ebx (by decide), u21.other .ebx (by decide),
      u20.other .ebx (by decide), b19,
      u21.other .edx (by decide), u20.other .edx (by decide), d19]
    rfl
  · rw [u24.mem, u23.mem, u22.mem, u21.mem, u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.MillerRabin.X86

end

end

/-! # The folded marker prepares a fixed three-square finishing stage -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/LastSquares.lean`, which only this module imported.
section

/-! # The final three squares use the threshold encoded by the prepared marker -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem lastSquares_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {k : Nat} (bound : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (.block lastSquares) s fun t =>
      t.mem = (s.mem.writeW (off g.W sThreshold) (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))).writeW
        (off g.W sSquares) 3#32 ∧
      Outs g.W [(sThreshold, 4), (sSquares, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  have header := v.headerFit
  unfold lastSquares
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (markerPointer_ok v C) fun a ⟨P, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (markerCalc_ok Ca.ws P v.markerFit) fun b ⟨AX, Mb, Kb⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (Ka.mono (by decide)).trans (Kb.mono (by decide))
  have M : b.mem = s.mem := Mb.trans Ma
  have Cb := C.keepMem Kall (by decide) M
  have value : b.gpr .eax = BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k) := by
    rw [AX, Ma, lo, hi, markerFold_twoPow bound]
  refine wp_storeS (ea_ptr Cb.ws Cb.base (d := sThreshold) (by unfold sThreshold; omega))
    (ws_write Cb.ws (y := 0 + sThreshold) (n := 4) (by unfold sThreshold; omega)) fun d D => ?_
  have Oth : Outside g.W sThreshold 4 b.mem d.mem := by
    rw [D.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; unfold sThreshold; omega)
  have Cd := Cb.keepScalar (D.keeps []) (by decide) Oth (by unfold scratchWord sThreshold; simp)
  refine wp_movS rfl fun e I _ => ?_
  have Ce := Cd.keepMem I.keeps (by decide) I.mem
  refine wp_storeS (ea_ptr Ce.ws Ce.base (d := sSquares) (by unfold sSquares; omega))
    (ws_write Ce.ws (y := 0 + sSquares) (n := 4) (by unfold sSquares; omega)) fun t T => WP.block_nil ?_
  have Osq : Outside g.W sSquares 4 d.mem t.mem := by
    rw [T.mem, Nat.zero_add, I.mem]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; unfold sSquares; omega)
  refine ⟨?_, ?_, ((Kall.widen (D.keeps [])).widen I.keeps).widen (T.keeps []),
    Ce.keepScalar (T.keeps []) (by decide) (by rw [I.mem]; exact Osq) (by unfold scratchWord sSquares; simp)⟩
  · rw [T.mem, Nat.zero_add, I.gpr, I.mem, D.mem, Nat.zero_add, value, M]
    rfl
  · rw [M] at Oth
    exact (Outs.of_outside Oth (by simp)).trans (Outs.of_outside Osq (by simp))

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.lastSquares {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s)
    {k : Nat} (bound : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (.block lastSquares) s fun t =>
      Stage g capacity c p A Js
        (setAt (setAt V sThreshold (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))) sSquares 3#32)
        ([sThreshold, sSquares] ++ wordFields) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have header := v.headerFit
  have tf : sThreshold + 4 ≤ g.L := by unfold sThreshold; omega_using [header]
  have sf : sSquares + 4 ≤ g.L := by unfold sSquares; omega_using [header]
  have scratch : ∀ d ∈ [sThreshold, sSquares], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sThreshold; simp
    · unfold scratchWord sSquares; simp
  refine WP.mono (lastSquares_ok v S.data.context bound lo hi) fun t ⟨M, O, K, C⟩ => ?_
  have D : Data g A Js
      (setAt (setAt V sThreshold (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))) sSquares 3#32)
      ([sThreshold, sSquares] ++ wordFields) t := by
    refine S.data.afterSlots v C [sThreshold, sSquares] ?_ ?_ O
    · intro d mem
      refine ⟨scratch d mem, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · change t.mem.readW (off g.W sThreshold) 32 = BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k)
        apply BitVec.eq_of_toNat_eq
        change w32 t.mem g.W sThreshold = _
        rw [M, w32_write_ne S.data.context.ws.nowrap sf tf
          (by right; unfold sThreshold sSquares; decide), w32_write_self]
      · change t.mem.readW (off g.W sSquares) 32 = 3#32
        rw [M, Mem.readW_writeW_self32]
    · intro d mem _
      change d ∈ [184, 232] at mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> rfl
  exact ⟨S.afterSlots v D [sThreshold, sSquares] scratch O K (by decide),
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.RoundMarker`, which this module and modules that import it used -/

section

/-! # The prepared exponent marker survives every round write -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.Mont

theorem roundFrame_marker32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (F : WorkspaceFrame g (roundWrites g) m m') {extra : Nat} (half : extra = 0 ∨ extra = 4) :
    m'.readW (off g.W (g.array aExponent + 4 * g.words + extra)) 32 =
      m.readW (off g.W (g.array aExponent + 4 * g.words + extra)) 32 := by
  apply F.read32 (by have := v.markerFit; omega_using [half, this])
  intro r mem
  simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;>
    unfold Geometry.array Geometry.words aExponent Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes <;> omega_using []

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.WordLoop`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.ExponentState`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.WordStep`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.Window`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.StageScan`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.Select`, which this module and modules that import it used -/

section

/-! # Each table selection preserves the prepared header and other arrays -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem selectEntry_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 16) (k : Bool)
    (mask : s.mem.readW (off g.W sEq1) 32 = if k then BitVec.allOnes 32 else 0#32) :
    WP isa (selectEntry j) s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (if k then aTable + j else aX)) g.words ∧
      Outside g.W (g.array aX) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  unfold selectEntry
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v (aTable + j) (by unfold aTable; omega_using [index])
    .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_))
  have Ca := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Ca.ptr v aX (by decide) .ebx (by decide) (by decide))
    fun b ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Ca.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_)
  have Cc := Cb.keepMem Kc (by decide) Mc
  refine wp_movS (readSrc_ptr Cc.ws Cc.base (d := sEq1) (by have := v.headerFit; unfold sEq1; omega_using [this]))
    fun d D _ => WP.block_nil ?_
  have keep : Keeps [.ebx, .ecx, .edx, .ebp, .esi] s d :=
    (((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))).widen D.keeps
  have mem : d.mem = s.mem := D.mem.trans (Mc.trans (Mb.trans M))
  have bp : PtrAt d g.W .ebp (g.array (aTable + j)) := by
    rw [PtrAt, D.other .ebp (by decide), Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have bx : PtrAt d g.W .ebx (g.array aX) := by
    rw [PtrAt, D.other .ebx (by decide), Kc.1 .ebx (by decide)]; exact Pb
  have apart : g.array aX + 4 * g.words ≤ g.array (aTable + j) ∨
      g.array (aTable + j) + 4 * g.words ≤ g.array aX := by
    have sep := g.arraysApart aX (aTable + j)
    have neq : g.array aX ≠ g.array (aTable + j) := by
      have step := Nat.mul_le_mul_right (8 * (g.w + 2)) (show 6 ≤ 11 + j by omega_using [])
      unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes aX aTable
      omega_using [step]
    exact sep.resolve_left neq
  refine WP.mono (selectLoop_ok (C.ws.of_keeps keep)
    (by have := v.minWidth; unfold Geometry.words; omega_using [this]) (v.arrayFit (by decide))
    (v.arrayFit (by unfold aTable; omega_using [index])) apart bx bp
    (by rw [D.other .esi (by decide)]; exact Count) k
    (by rw [D.gpr, Mc, Mb, M, Nat.zero_add]; exact mask)) ?_
  rintro t ⟨O, V, Kt⟩
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    (keep.mono (by decide)).trans (Kt.mono (by decide))
  rw [mem] at O V
  refine ⟨?_, O, Kall, C.keepOutside Kall (by decide) O (v.arrayHeader aX)⟩
  cases k <;> exact V

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.Mask`, which this module and modules that import it used -/

section

/-! # The secret digit chooses a mask without choosing an address -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem maskIndex_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 16) :
    WP isa (.block (maskIndex j)) s fun t =>
      t.mem.readW (off g.W sEq1) 32 =
        (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j then BitVec.allOnes 32 else 0#32) ∧
      Outside g.W sEq1 4 s.mem t.mem ∧ Keeps [.eax, .ecx] s t ∧ Context g t := by
  unfold maskIndex
  refine wp_movS (readSrc_ptr C.ws C.base (d := sValue) (by have := v.headerFit; unfold sValue; omega_using [this]))
    fun a A _ => wp_shr (by decide) fun b B _ => ?_
  refine wp_logicS (.inr rfl) rfl fun c D => wp_subS rfl fun d E _ => ?_
  refine wp_shr (by decide) fun e F _ => wp_movS rfl fun f G _ => wp_subS rfl fun h H _ => ?_
  have K : Keeps [.eax, .ecx] s h :=
    ((((((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen G.keeps).widen H.keeps
  have Ch := C.keepMem K (by decide) (by rw [H.mem, G.mem, F.mem, E.mem, D.mem, B.mem, A.mem])
  refine wp_storeS (ea_ptr Ch.ws Ch.base (d := sEq1) (by have := v.headerFit; unfold sEq1; omega_using [this]))
    (ws_write Ch.ws (y := 0 + sEq1) (n := 4) (by have := v.headerFit; unfold sEq1; omega_using [this]))
    fun t T => WP.block_nil ?_
  have M : h.mem = s.mem := by rw [H.mem, G.mem, F.mem, E.mem, D.mem, B.mem, A.mem]
  have O : Outside g.W sEq1 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add, M]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; have := v.headerFit; unfold sEq1; omega_using [])
  have Kt : Keeps [.eax, .ecx] s t := K.widen (T.keeps [])
  refine ⟨?_, O, Kt, C.keepScalar Kt (by decide) O (by unfold scratchWord sEq1; simp)⟩
  rw [T.mem, Nat.zero_add, Mem.readW_writeW_self32, H.gpr, G.gpr, G.other .eax (by decide),
    F.gpr, E.gpr, D.gpr, B.gpr, A.gpr, Nat.zero_add]
  change 0#32 - ((((s.mem.readW (off g.W sValue) 32 >>> 28) ^^^ BitVec.ofNat 32 j) - 1) >>> 31) = _
  exact digitMask _ index

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.ScanFrame`, which only this module used -/

section

/-! # The precise write footprint of a fixed-window table scan -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.Mont

def scanWrites (g : Geometry) : List (Nat × Nat) := [(sEq1, 4), (g.array aX, 4 * g.words)]

theorem scanFrame_table {g : Geometry} (v : g.Valid) {m m' : Mem}
    (nowrap : g.W.toNat + g.L ≤ 2 ^ 32) (O : Outs g.W (scanWrites g) m m')
    {j : Nat} (index : j < 16) :
    val32 m' g.W (g.array (aTable + j)) g.words = val32 m g.W (g.array (aTable + j)) g.words := by
  have header := v.arrayHeader (aTable + j)
  have sep := g.arrayBefore (show aX < aTable + j by unfold aX aTable; omega_using [])
  have fit := v.arrayFit (j := aTable + j) (by unfold aTable; omega_using [index])
  refine O.val32 ?_ (by omega_using [nowrap, fit])
  intro r hr
  simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · right; unfold sEq1; omega_using [header]
  · exact Or.inr sep

theorem scanFrame_value {g : Geometry} (v : g.Valid) {m m' : Mem}
    (O : Outs g.W (scanWrites g) m m') :
    m'.readW (off g.W sValue) 32 = m.readW (off g.W sValue) 32 := by
  have header := v.arrayHeader aX
  have V := O.val32 (d := sValue) (k := 1) (by
    intro r hr
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; decide
    · left; unfold sValue; omega) (by unfold sValue; decide)
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using V

end VG.Proof.MillerRabin.X86

end

end

/-! # Selecting a secret digit keeps the modulus and caller frame reusable -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ScanEntry.lean`, which only this module imported.
section

/-! # One fixed-address scan step only replaces the matching digit -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/Scan.lean`, which only this module imported.
section

/-! # The complete scan returns exactly the secret digit's table entry -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem scanFrom_ok {g : Geometry} (v : g.Valid) (n : Nat) :
    ∀ j, j + n ≤ 16 → ∀ s, Context g s →
    WP isa (scanFrom j n) s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (if j ≤ (s.mem.readW (off g.W sValue) 32 >>> 28).toNat ∧
            (s.mem.readW (off g.W sValue) 32 >>> 28).toNat < j + n
          then aTable + (s.mem.readW (off g.W sValue) 32 >>> 28).toNat else aX)) g.words ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  induction n with
  | zero =>
    intro j _ s C
    refine WP.block_nil ⟨?_, Outs.refl _ _ _, Keeps.refl _ _, C⟩
    simp only [Nat.add_zero, show ¬ (j ≤ (s.mem.readW (off g.W sValue) 32 >>> 28).toNat ∧
      (s.mem.readW (off g.W sValue) 32 >>> 28).toNat < j) by omega, ↓reduceIte]
  | succ n ih =>
    intro j bound s C
    unfold scanFrom
    refine WP.assoc (WP.seq (WP.mono (scanEntry_ok v C j (by omega)) fun a ⟨Va, Oa, Ka, Ca⟩ => ?_))
    refine WP.mono (ih (j + 1) (by omega) a Ca) fun t ⟨Vt, Ot, Kt, Ct⟩ => ?_
    have value := scanFrame_value v Oa
    simp only [value] at Vt
    refine ⟨?_, Oa.trans Ot, Ka.trans Kt, Ct⟩
    let d := (s.mem.readW (off g.W sValue) 32 >>> 28).toNat
    change val32 t.mem g.W (g.array aX) g.words =
      val32 s.mem g.W (g.array (if j ≤ d ∧ d < j + (n + 1) then aTable + d else aX)) g.words
    change val32 t.mem g.W (g.array aX) g.words =
      val32 a.mem g.W (g.array (if j + 1 ≤ d ∧ d < j + 1 + n then aTable + d else aX)) g.words at Vt
    change val32 a.mem g.W (g.array aX) g.words =
      val32 s.mem g.W (g.array (if d = j then aTable + j else aX)) g.words at Va
    by_cases later : j + 1 ≤ d ∧ d < j + 1 + n
    · rw [ite_eq_left later] at Vt
      rw [Vt, scanFrame_table v C.ws.nowrap Oa (j := d) (digit_lt _),
        ite_eq_left (by omega : j ≤ d ∧ d < j + (n + 1))]
    · rw [ite_eq_right later] at Vt
      rw [Vt, Va]
      by_cases eq : d = j
      · rw [eq, ite_eq_left rfl, ite_eq_left (by omega : j ≤ j ∧ j < j + (n + 1))]
      · rw [ite_eq_right eq, ite_eq_right (by omega : ¬ (j ≤ d ∧ d < j + (n + 1)))]

theorem scan_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa scan s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (aTable + (s.mem.readW (off g.W sValue) 32 >>> 28).toNat)) g.words ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  unfold scan
  refine WP.seq (WP.mono (copy_ok v C aX aTable (by decide) (by decide))
    fun a ⟨Va, Oa, Ka, Ca⟩ => ?_)
  refine WP.mono (scanFrom_ok v 15 1 (by decide) a Ca) fun t ⟨Vt, Ot, Kt, Ct⟩ => ?_
  have frame : Outs g.W (scanWrites g) s.mem a.mem := Outs.of_outside Oa (by simp [scanWrites])
  have value := scanFrame_value v frame
  simp only [value] at Vt
  refine ⟨?_, frame.trans Ot, (Ka.mono (by decide)).trans Kt, Ct⟩
  have digit := digit_lt (s.mem.readW (off g.W sValue) 32)
  by_cases zero : (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = 0
  · simp only [zero, show ¬ (1 ≤ 0 ∧ 0 < 1 + 15) by decide, ↓reduceIte] at Vt
    rw [Vt, Va, zero, Nat.add_zero]
  · rw [ite_eq_left (by omega)] at Vt
    rw [Vt, scanFrame_table v C.ws.nowrap frame digit]

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataScan.lean`, which only this module imported.
section

/-! # A complete fixed-address scan selects the digit's known power -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.scan {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js)
    (digitKnown : sValue ∈ Ds) (maskUnknown : sEq1 ∉ Ds) :
    WP isa scan s fun t =>
      Data g (setAt A aX (A (aTable + (V sValue >>> 28).toNat))) (aX :: Js) V Ds t ∧
      Outs g.W (scanWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have value := (D.slotValues sValue digitKnown).2
  have digit := digit_lt (V sValue)
  have power := D.arrayValues _ (tableKnown _ digit)
  refine WP.mono (scan_ok v D.context) fun t ⟨Value, O, K, C⟩ => ?_
  rw [value, power.2] at Value
  refine ⟨⟨C, ?_, ?_⟩, O, K⟩
  · intro j known
    by_cases same : j = aX
    · subst j
      exact ⟨by decide, by rw [setAt_self]; exact Value⟩
    · have old : j ∈ Js := by
        rcases List.mem_cons.mp known with bad | old
        · exact False.elim (same bad)
        · exact old
      obtain ⟨index, read⟩ := D.arrayValues j old
      refine ⟨index, ?_⟩
      have sep := g.readApart same
      have header := v.arrayHeader j
      rw [O.val32 (by
        intro r mem
        simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl
        · right; unfold sEq1; omega
        · dsimp only
          rcases sep with before | after
          · exact Or.inl before
          · right; unfold Geometry.words at *; omega)
        (by have := v.arrayFit index; have := C.ws.nowrap; omega), read, setAt_other A _ same]
  · intro d known
    obtain ⟨scratch, read⟩ := D.slotValues d known
    have notMask : d ≠ sEq1 := fun eq => maskUnknown (eq ▸ known)
    have apart := scratch_apart scratch (by unfold scratchWord sEq1; simp) notMask
    have bound := scratch_fit scratch
    have header := v.arrayHeader aX
    refine ⟨scratch, ?_⟩
    rw [(WorkspaceFrame.of_outs C.ws.nowrap O).read32 (by have := v.headerFit; omega) (by
      intro r mem
      simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact apart
      · exact Or.inl (Nat.le_trans bound header)), read]

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.scan {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (digitKnown : sValue ∈ Ds) (maskUnknown : sEq1 ∉ Ds) :
    WP isa scan s fun t =>
      Stage g capacity c p (setAt A aX (A (aTable + (V sValue >>> 28).toNat))) (aX :: Js) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.scan v tableKnown digitKnown maskUnknown) fun t ⟨D, O, K⟩ => ?_
  have W := WorkspaceFrame.of_outs S.data.context.ws.nowrap O
  have head := v.arrayHeader aX
  have M : Modulus g c t.mem := S.modulus.keep v W (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · right; decide
    · left; dsimp only; omega_using [head]) (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · right; have := v.arrayHeader 0; unfold sEq1; omega_using [this]
    · exact Or.inl (g.arrayBefore (by decide : 0 < aX)))
  have C := S.caller.keepOuts K (by decide) O (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · have := v.headerFit; unfold sEq1; dsimp only; omega_using [this]
    · exact v.arrayFit (by decide : aX < 28))
  refine ⟨⟨D, M, C, ?_⟩, ?_, K⟩
  · intro j mem
    rcases List.mem_cons.mp mem with rfl | mem
    · decide
    · exact S.noScratch j mem
  · apply W.cover
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact scalar_roundRange g (d := sEq1) (by unfold scratchWord sEq1; simp)
    · exact array_roundRange g (j := aX) (by unfold roundArray aX; simp) (by unfold Geometry.words; omega_using [])

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.SquareLoop`, which this module and modules that import it used -/

section

/-! # A fixed public count of prepared squarings with secret threshold masks -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem squareLoop_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q r : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js) (minusKnown : aMinusOne ∈ Js)
    (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ Ds) (eqUnknown : sEq2 ∉ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (squareLoop name code) s fun t =>
      Stage g capacity c p (squareValues A c g.w r q F q) Js
        (squareCounters V A c g.w r q F q) Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (squareValues A c g.w r q F i) Js
      (squareCounters V A c g.w r q F i) Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [squareValues_initial, squareCounters_initial V A c g.w r q F count flag]
    exact S
  unfold squareLoop
  apply countLoop positive I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : squareValues A c g.w r q F i aY < c := by
    rw [squareValues, setAt_self]
    exact squareState_lt A (by omega_using [odd] : 0 < c) g.w r q F Ylt i
  refine WP.mono (squareStep_ok verified noSp stack v St length odd yBound yKnown minusKnown
    (by omega_using [index] : 0 < q - i) (by omega_using [qBound] : q - i < 2 ^ 31) rBound (squareState A c g.w r q F i).2
    known ?_ ?_ ?_) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  · change setAt (setAt V sSquares (BitVec.ofNat 32 (q - i))) sFlag _ sSquares = _
    rfl
  · change setAt (setAt V sSquares (BitVec.ofNat 32 (q - i))) sFlag _ sThreshold = _
    exact threshold
  · exact setAt_self _ _ _
  · have Snext : Stage g capacity c p (squareValues A c g.w r q F (i + 1)) Js
        (squareCounters V A c g.w r q F (i + 1)) Ds u := Su.mono
      (fun j mem => ⟨mem, congrFun (squareValues_next A c g.w r q F i) j⟩) (by
        intro d mem
        refine ⟨List.mem_append_right _ (List.mem_cons_of_mem _ mem), ?_⟩
        exact squareCounters_next V A c g.w r q F (fun eq => eqUnknown (eq ▸ mem)))
    refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
    rw [Z]
    congr 1
    exact decide_eq_decide.mpr (by omega_using [])

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.FourSquares`, which this module and modules that import it used -/

section

/-! # Every four-bit window starts with four unconditional squarings -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem fourSquares_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) :
    WP isa (.block fourSquares) s fun t =>
      Stage g capacity c p A Js (setAt (setAt V sThreshold 0#32) sSquares 4#32)
        (sSquares :: sThreshold :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.mov .eax (.imm 0), .store (slot sThreshold) .eax] ++
    [.mov .eax (.imm 4), .store (slot sSquares) .eax])) s _
  refine WP.block_append (WP.mono (S.literal v sThreshold
    (by unfold scratchWord sThreshold; simp) 0#32) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.mono (Sa.literal v sSquares (by unfold scratchWord sSquares; simp) 4#32)
    fun t ⟨St, Ot, Kt⟩ => ?_
  exact ⟨St, Oa.trans Ot, Ka.trans Kt⟩

end VG.Proof.MillerRabin.X86

end

end

/-! # One complete prepared fixed-window Miller–Rabin transition -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageWindowControl.lean`, which only this module imported.
section

/-! # A completed window retains all invariants needed by the next window -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.windowEnd {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (known : ∀ d ∈ [sEq1, sEq2, sFlag, sValue, sWindows], d ∈ Ds)
    (eq1 : V sEq1 = BitVec.ofNat 32 E1.toNat) (eq2 : V sEq2 = BitVec.ofNat 32 E2.toNat)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      Stage g capacity c p A Js (windowSlots V q E1 E2 F) ([sFlag, sValue, sWindows] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have scratch : ∀ d ∈ [sFlag, sValue, sWindows], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · unfold scratchWord sFlag; simp
    · unfold scratchWord sValue; simp
    · unfold scratchWord sWindows; simp
  refine WP.mono (S.data.windowEnd v q positive bound E1 E2 F known eq1 eq2 flag count)
    fun t ⟨D, Z, O, K⟩ => ?_
  exact ⟨S.afterSlots v D [sFlag, sValue, sWindows] scratch O K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem window_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V windowFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (positive : 0 < q) (qBound : q < 2 ^ 32) (F : Bool)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (window name code) s fun t =>
      Stage g capacity c p (setAt A aY (windowResult V A c g.w F).1) Js
        (windowCounters V A c g.w q F) windowFields t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  change WP isa (.seq (.block fourSquares) (.seq (squareLoop name code) (.seq scan
    (.seq (mulY name code aX) (.seq (equal sEq1 aY aOne)
      (.seq (equal sEq2 aY aMinusOne) (.block windowEnd))))))) s _
  refine WP.seq (WP.mono (fourSquares_ok v S) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (squareLoop_ok verified noSp stack v Sa length odd Ylt yKnown minusKnown
    (by decide : 0 < 4) (by decide : 4 < 2 ^ 31) (by decide : 0 < 2 ^ 31) F
    (by
      intro d mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> decide)
    (by decide) rfl rfl flag) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  change Stage g capacity c p (squareValues A c g.w 0 4 F 4) Js
    (windowSquaresV V A c g.w F) (sSquares :: sThreshold :: windowFields) b at Sb
  refine WP.seq (WP.mono (Sb.scan v tableKnown (by decide) (by decide)) fun d ⟨Sd, Od, Kd⟩ => ?_)
  change Stage g capacity c p (windowScanA V A c g.w F) (aX :: Js)
    (windowSquaresV V A c g.w F) (sSquares :: sThreshold :: windowFields) d at Sd
  have selectedLt : windowScanA V A c g.w F aX < c := by
    rw [windowScanA, setAt_self, squareValues,
      setAt_other _ _ (by unfold aTable aY; omega_using [] : aTable + windowDigit V ≠ aY)]
    exact tableLt _ (digit_lt _)
  refine WP.seq (WP.mono (Sd.multiply verified noSp stack v length aX
    (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide) odd selectedLt
    (List.mem_cons_self ..) (List.mem_cons_of_mem _ yKnown)) fun e ⟨Se, Oe, Ke⟩ => ?_)
  change Stage g capacity c p (windowProductA V A c g.w F) (aX :: Js)
    (windowSquaresV V A c g.w F) (sSquares :: sThreshold :: windowFields) e at Se
  refine WP.seq (WP.mono (Se.equal v sEq1 aY aOne (by unfold scratchWord sEq1; simp)
    (List.mem_cons_of_mem _ yKnown) (List.mem_cons_of_mem _ oneKnown)) fun f ⟨Sf, Of, Kf⟩ => ?_)
  refine WP.seq (WP.mono (Sf.equal v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp)
    (List.mem_cons_of_mem _ yKnown) (List.mem_cons_of_mem _ minusKnown)) fun h ⟨Sh, Oh, Kh⟩ => ?_)
  change Stage g capacity c p (windowProductA V A c g.w F) (aX :: Js)
    (windowEqV V A c g.w F) (sEq2 :: sEq1 :: sSquares :: sThreshold :: windowFields) h at Sh
  refine WP.mono (Sh.windowEnd v q positive qBound (windowOne V A c g.w F) (windowMinus V A c g.w F)
    (squareState A c g.w 0 4 F 4).2 (by
      intro d mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl <;> decide) rfl rfl rfl count)
    fun t ⟨St, Z, Ot, Kt⟩ => ?_
  refine ⟨St.mono ?_ ?_, Z, ?_, ?_⟩
  · intro j mem
    exact ⟨List.mem_cons_of_mem _ mem, windowProduct_value V A c g.w F (fun eq => xUnknown (eq ▸ mem))⟩
  · intro d mem
    exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))), windowCounters_eq V A c g.w q F one mem⟩
  · have Eq1 := scalar_roundFrame Se.data.context.ws.nowrap (rs := [sEq1])
      (by intro d mem; obtain rfl := List.mem_singleton.mp mem; unfold scratchWord sEq1; simp)
      (Outs.of_outside Of (List.mem_singleton_self _))
    have Eq2 := scalar_roundFrame Sf.data.context.ws.nowrap (rs := [sEq2])
      (by intro d mem; obtain rfl := List.mem_singleton.mp mem; unfold scratchWord sEq2; simp)
      (Outs.of_outside Oh (List.mem_singleton_self _))
    exact ((((((Oa.trans Ob).trans Od).trans (mont_roundFrame Oe)).trans Eq1).trans Eq2).trans Ot)
  · exact (((((((Ka.mono (by decide)).trans Kb).trans Kd).trans (Ke.mono (by decide))).trans Kf).trans Kh).trans
      (Kt.mono (by decide)))

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.WordState`, which this module and modules that import it used -/

section

/-! # Eight windows consume one native exponent word from its top bits -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def wordState (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) : Nat → Nat × Bool
  | 0 => (A aY, F)
  | i + 1 => Word32.mwin c w (A aMinusOne) (fun d => A (aTable + d))
      ((x <<< (4 * i)) >>> 28).toNat (wordState A c w x F i)

def wordValues (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) : Nat → Nat :=
  setAt A aY (wordState A c w x F i).1

def wordCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt (setAt V sFlag (BitVec.ofNat 32 (wordState A c w x F i).2.toNat))
    sValue (x <<< (4 * i))) sWindows (BitVec.ofNat 32 (8 - i))

theorem wordState_lt (A : Nat → Nat) {c : Nat} (positive : 0 < c) (w : Nat) (x : BitVec 32) (F : Bool)
    (initial : A aY < c) : ∀ i, (wordState A c w x F i).1 < c
  | 0 => initial
  | _ + 1 => Word32.mm_lt positive

theorem wordValues_initial (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) :
    wordValues A c w x F 0 = A := setAt_same A aY

theorem wordCounters_initial (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool)
    (value : V sValue = x) (count : V sWindows = 8#32) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    wordCounters V A c w x F 0 = V := by
  change setAt (setAt (setAt V sFlag (BitVec.ofNat 32 F.toNat)) sValue (x <<< 0)) sWindows 8#32 = V
  rw [BitVec.shiftLeft_zero, ← flag, setAt_same, ← value, setAt_same, ← count, setAt_same]

theorem wordWindow_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) :
    windowResult (wordCounters V A c w x F i) (wordValues A c w x F i) c w
      (wordState A c w x F i).2 = wordState A c w x F (i + 1) := by
  unfold windowResult wordValues
  rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), setAt_self]
  have powers : (fun d => setAt A aY (wordState A c w x F i).1 (aTable + d)) =
      (fun d => A (aTable + d)) := by
    funext d
    exact setAt_other _ _ (by unfold aTable aY; omega_using [])
  rw [powers]
  rfl

theorem wordValues_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat) :
    setAt (wordValues A c w x F i) aY
      (windowResult (wordCounters V A c w x F i) (wordValues A c w x F i) c w
        (wordState A c w x F i).2).1 = wordValues A c w x F (i + 1) := by
  rw [wordWindow_next, wordValues, setAt_twice]
  rfl

theorem wordCounters_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (i : Nat)
    {d : Nat} (known : d ∈ windowFields) :
    windowCounters (wordCounters V A c w x F i) (wordValues A c w x F i) c w (8 - i)
      (wordState A c w x F i).2 d = wordCounters V A c w x F (i + 1) d := by
  change d ∈ [184, 208, 232, 240] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl
  · change BitVec.ofNat 32 (windowResult (wordCounters V A c w x F i) (wordValues A c w x F i)
      c w (wordState A c w x F i).2).2.toNat = _
    rw [wordWindow_next]
    rfl
  · exact Word32.shl4_succ32 x i
  · rfl
  · change BitVec.ofNat 32 (8 - i - 1) = BitVec.ofNat 32 (8 - (i + 1))
    congr 1 <;> omega

end VG.Proof.MillerRabin.X86

end

end

/-! # A public word index loads and consumes exactly eight exponent windows -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/WordWindows.lean`, which only this module imported.
section

/-! # Eight fixed windows consume a complete native exponent word -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem wordWindows_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V windowFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (x : BitVec 32) (F : Bool) (value : V sValue = x)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = 8#32) :
    WP isa (.loop (window name code) .ne) s fun t =>
      Stage g capacity c p (wordValues A c g.w x F 8) Js
        (wordCounters V A c g.w x F 8) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (wordValues A c g.w x F i) Js
      (wordCounters V A c g.w x F i) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [wordValues_initial, wordCounters_initial V A c g.w x F value count flag]
    exact S
  apply countLoop (by decide : 0 < 8) I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : wordValues A c g.w x F i aY < c := by
    rw [wordValues, setAt_self]
    exact wordState_lt A (by omega : 0 < c) g.w x F Ylt i
  have sameOne : wordValues A c g.w x F i aTable = wordValues A c g.w x F i aOne := by
    unfold wordValues
    rw [setAt_other _ _ (by decide : aTable ≠ aY), setAt_other _ _ (by decide : aOne ≠ aY)]
    exact one
  have powersLt : ∀ j < 16, wordValues A c g.w x F i (aTable + j) < c := by
    intro j bound
    rw [wordValues, setAt_other _ _ (by unfold aTable aY; omega)]
    exact tableLt j bound
  refine WP.mono (window_ok verified noSp stack v St length odd yBound yKnown oneKnown minusKnown
    xUnknown tableKnown sameOne powersLt (by omega : 0 < 8 - i) (by omega : 8 - i < 2 ^ 32)
    (wordState A c g.w x F i).2 rfl rfl) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  have Snext : Stage g capacity c p (wordValues A c g.w x F (i + 1)) Js
      (wordCounters V A c g.w x F (i + 1)) windowFields u := Su.mono
    (fun j mem => ⟨mem, congrFun (wordValues_next V A c g.w x F i) j⟩)
    (fun d mem => ⟨mem, wordCounters_next V A c g.w x F i mem⟩)
  refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
  rw [Z]
  congr 1
  exact decide_eq_decide.mpr (by omega)

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageCounter.lean`, which only this module imported.
section

/-! # A public countdown is a prepared-stage transition -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.counterDown {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d q : Nat) (scratch : scratchWord d) (known : d ∈ Ds)
    (positive : 0 < q) (bound : q < 2 ^ 32) (count : V d = BitVec.ofNat 32 q) :
    WP isa (.block [.mov .eax (.mem (slot d)), .alu .sub .eax (.imm 1), .store (slot d) .eax]) s fun t =>
      Stage g capacity c p A Js (setAt V d (BitVec.ofNat 32 (q - 1))) (d :: Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  have read := (S.data.slotValues d known).2.trans count
  refine WP.mono (counterDown_ok v S.data.context d q scratch positive bound read)
    fun t ⟨Count, Z, O, K, C⟩ => ?_
  have stored : t.mem.readW (off g.W d) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W d = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have D := S.data.afterScalar v C d scratch _ O stored
  have scratchList : ∀ e ∈ [d], scratchWord e := by
    intro e mem
    obtain rfl := List.mem_singleton.mp mem
    exact scratch
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] scratchList outs K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratchList outs, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def wordEndSlots (V : Nat → BitVec 32) (A : Nat → Nat) (c w : Nat) (x : BitVec 32) (F : Bool) (q : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (wordState A c w x F 8).2.toNat)) sWords (BitVec.ofNat 32 (q - 1))

theorem wordStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (expKnown : aExponent ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (positive : 0 < q) (bound : q ≤ g.words) (F : Bool)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWords = BitVec.ofNat 32 q) :
    let x := exponentWord (A aExponent) (q - 1)
    WP isa (wordStep name code) s fun t =>
      Stage g capacity c p (wordValues A c g.w x F 8) Js (wordEndSlots V A c g.w x F q) wordFields t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  dsimp only
  change WP isa (.seq (.block loadWord) (.seq (.loop (window name code) .ne) (.block wordEnd))) s _
  have readWord := read_exponentWord (S.data.arrayValues aExponent expKnown).2 (by omega_using [positive, bound] : q - 1 < g.words)
  refine WP.seq (WP.mono (S.loadWord v q positive bound count _ readWord) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (wordWindows_ok verified noSp stack v Sa length odd Ylt yKnown oneKnown minusKnown
    xUnknown tableKnown one tableLt _ F rfl flag rfl) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  have qBound : q < 2 ^ 32 := by have := v.maxWidth; unfold Geometry.words at bound; omega_using [bound, this]
  refine WP.mono (Sb.counterDown v sWords q (by unfold scratchWord sWords; simp) (by decide)
    positive qBound count) fun t ⟨St, Z, Ot, Kt⟩ => ?_
  refine ⟨St.mono (fun _ mem => ⟨mem, rfl⟩) ?_, Z, (Oa.trans Ob).trans Ot,
    ((Ka.mono (by decide)).trans Kb).trans (Kt.mono (by decide))⟩
  intro d mem
  have membership : d ∈ sWords :: windowFields := by
    change d ∈ [184, 232] at mem
    change d ∈ [232, 184, 208, 232, 240]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> decide
  refine ⟨membership, ?_⟩
  change d ∈ [184, 232] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> rfl

end VG.Proof.MillerRabin.X86

end

end

/-! # The outer public countdown consumes exponent words from high to low -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def exponentState (A : Nat → Nat) (c w N : Nat) (F : Bool) : Nat → Nat × Bool
  | 0 => (A aY, F)
  | i + 1 =>
    let st := exponentState A c w N F i
    wordState (setAt A aY st.1) c w (exponentWord (A aExponent) (N - 1 - i)) st.2 8

def exponentValues (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) : Nat → Nat :=
  setAt A aY (exponentState A c w N F i).1

def exponentCounters (V : Nat → BitVec 32) (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) :
    Nat → BitVec 32 :=
  setAt (setAt V sFlag (BitVec.ofNat 32 (exponentState A c w N F i).2.toNat)) sWords (BitVec.ofNat 32 (N - i))

theorem exponentState_lt (A : Nat → Nat) {c : Nat} (positive : 0 < c) (w N : Nat) (F : Bool)
    (initial : A aY < c) : ∀ i, (exponentState A c w N F i).1 < c
  | 0 => initial
  | i + 1 => wordState_lt _ positive _ _ _ (by
      rw [setAt_self]
      exact exponentState_lt A positive w N F initial i) 8

theorem exponentValues_initial (A : Nat → Nat) (c w N : Nat) (F : Bool) :
    exponentValues A c w N F 0 = A := setAt_same A aY

theorem exponentCounters_initial (V : Nat → BitVec 32) (A : Nat → Nat) (c w N : Nat) (F : Bool)
    (count : V sWords = BitVec.ofNat 32 N) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    exponentCounters V A c w N F 0 = V := by
  change setAt (setAt V sFlag (BitVec.ofNat 32 F.toNat)) sWords (BitVec.ofNat 32 N) = V
  rw [← flag, setAt_same, ← count, setAt_same]

theorem exponentWord_next (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) :
    wordState (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 8 = exponentState A c w N F (i + 1) := by
  unfold exponentValues
  rw [setAt_other _ _ (by decide : aExponent ≠ aY), Nat.sub_right_comm]
  rfl

theorem exponentValues_next (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat) :
    wordValues (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 8 = exponentValues A c w N F (i + 1) := by
  unfold wordValues
  rw [exponentWord_next, exponentValues, setAt_twice]
  rfl

theorem exponentCounters_next (V : Nat → BitVec 32) (A : Nat → Nat) (c w N : Nat) (F : Bool) (i : Nat)
    {d : Nat} (known : d ∈ wordFields) :
    wordEndSlots (exponentCounters V A c w N F i) (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 (N - i) d = exponentCounters V A c w N F (i + 1) d := by
  change d ∈ [184, 232] at known
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl
  · change BitVec.ofNat 32 (wordState (exponentValues A c w N F i) c w
      (exponentWord (exponentValues A c w N F i aExponent) (N - i - 1))
      (exponentState A c w N F i).2 8).2.toNat = _
    rw [exponentWord_next]
    rfl
  · change BitVec.ofNat 32 (N - i - 1) = BitVec.ofNat 32 (N - (i + 1))
    congr 1 <;> omega

end VG.Proof.MillerRabin.X86

end

end

/-! # The complete exponent loop terminates after the prepared native width -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem wordLoop_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (expKnown : aExponent ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c) (F : Bool)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWords = BitVec.ofNat 32 g.words) :
    WP isa (.loop (wordStep name code) .ne) s fun t =>
      Stage g capacity c p (exponentValues A c g.w g.words F g.words) Js
        (exponentCounters V A c g.w g.words F g.words) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (exponentValues A c g.w g.words F i) Js
      (exponentCounters V A c g.w g.words F i) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [exponentValues_initial, exponentCounters_initial V A c g.w g.words F count flag]
    exact S
  have positive : 0 < g.words := by have := v.minWidth; unfold Geometry.words; omega_using [this]
  apply countLoop positive I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : exponentValues A c g.w g.words F i aY < c := by
    rw [exponentValues, setAt_self]
    exact exponentState_lt A (by omega_using [odd] : 0 < c) g.w g.words F Ylt i
  have sameOne : exponentValues A c g.w g.words F i aTable = exponentValues A c g.w g.words F i aOne := by
    unfold exponentValues
    rw [setAt_other _ _ (by decide : aTable ≠ aY), setAt_other _ _ (by decide : aOne ≠ aY)]
    exact one
  have powersLt : ∀ j < 16, exponentValues A c g.w g.words F i (aTable + j) < c := by
    intro j bound
    rw [exponentValues, setAt_other _ _ (by unfold aTable aY; omega_using [])]
    exact tableLt j bound
  refine WP.mono (wordStep_ok verified noSp stack v St length odd yBound yKnown oneKnown minusKnown expKnown
    xUnknown tableKnown sameOne powersLt (by omega_using [index] : 0 < g.words - i) (by omega_using [] : g.words - i ≤ g.words)
    (exponentState A c g.w g.words F i).2 rfl rfl) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  have Snext : Stage g capacity c p (exponentValues A c g.w g.words F (i + 1)) Js
      (exponentCounters V A c g.w g.words F (i + 1)) wordFields u := Su.mono
    (fun j mem => ⟨mem, congrFun (exponentValues_next A c g.w g.words F i) j⟩)
    (fun d mem => ⟨mem, exponentCounters_next V A c g.w g.words F i mem⟩)
  refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
  rw [Z]
  congr 1
  exact decide_eq_decide.mpr (by omega_using [])

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.PrepareRun`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.Sequences`, which this module and modules that import it used -/

section

/-! # Composing the statically unrolled round operations -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem seqs_cons_iff (c : Prog isa) (cs : List (Prog isa)) (s : State) (Q : State → Prop) :
    WP isa (seqs (c :: cs)) s Q ↔ WP isa c s (fun t => WP isa (seqs cs) t Q) := by
  cases cs with
  | nil => simp only [seqs, WP.block_nil_iff (M := isa)]
  | cons d ds => exact WP.seq_iff

theorem seqs_append_iff (cs ds : List (Prog isa)) (s : State) (Q : State → Prop) :
    WP isa (seqs (cs ++ ds)) s Q ↔ WP isa (seqs cs) s (fun t => WP isa (seqs ds) t Q) := by
  induction cs generalizing s Q with
  | nil => simp only [List.nil_append, seqs, WP.block_nil_iff (M := isa)]
  | cons c cs ih => simp only [List.cons_append, seqs_cons_iff, ih]

theorem seqs_range_ok (n : Nat) (code : Nat → Prog isa) (P : Nat → State → Prop)
    (step : ∀ j < n, ∀ s, P j s → WP isa (code j) s (P (j + 1)))
    (s : State) (initial : P 0 s) : WP isa (seqs ((List.range n).map code)) s (P n) := by
  induction n generalizing s with
  | zero => exact WP.block_nil initial
  | succ n ih =>
    rw [List.range_succ, List.map_append, seqs_append_iff]
    refine WP.mono (ih (fun j hj => step j (by omega_using [hj])) s initial) fun t Pt => ?_
    exact step n (by omega_using []) t Pt

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TableStep`, which this module and modules that import it used -/

section

/-! # Each table product writes its completed power once -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem tableStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c k : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p (tableValues A c g.w k) (tableArrays k) V Ds s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) (index : k < 14) :
    WP isa (.seq (mulY name code aX) (copy (aTable + k + 2) aY)) s fun t =>
      Stage g capacity c p (tableValues A c g.w (k + 1)) (tableArrays (k + 1)) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (S.multiply verified noSp stack v length aX
    (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide) odd (by rw [tableValues_x]; exact Xlt)
    (by simp [tableArrays, initialArrays]) (by exact List.mem_cons_self ..))
    fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.mono (Sa.copy v (aTable + k + 2) aY (by unfold aTable; omega_using [index])
    (by unfold aTable; omega_using []) (by unfold aTable; omega_using []) (by exact List.mem_cons_self ..))
    fun t ⟨St, Ot, Kt⟩ => ?_
  have values : setAt (setAt (tableValues A c g.w k) aY
      (Word32.mm c g.w (tableValues A c g.w k aY) (tableValues A c g.w k aX)))
      (aTable + k + 2) ((setAt (tableValues A c g.w k) aY
        (Word32.mm c g.w (tableValues A c g.w k aY) (tableValues A c g.w k aX))) aY) =
      tableValues A c g.w (k + 1) := by
    rw [setAt_self]
    exact tableValues_next A c g.w k
  rw [values] at St
  refine ⟨St.mono ?_ (fun _ mem => ⟨mem, rfl⟩),
    (mont_roundFrame Oa).trans (array_roundFrame Sa.data.context.ws.nowrap
      (by unfold roundArray aTable; omega_using [index]) Ot), (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
  intro j known
  exact ⟨List.mem_cons.mpr ((tableArrays_next k j).mp known), rfl⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TableInit`, which this module and modules that import it used -/

section

/-! # Initialize table powers zero and one and the product accumulator -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem tableInit_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A initialArrays V Ds s) :
    WP isa (seqs [copy aTable aOne, copy (aTable + 1) aX, copy aY aX]) s fun t =>
      Stage g capacity c p (tableValues A c g.w 0) (tableArrays 0) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  change WP isa (.seq (copy aTable aOne) (.seq (copy (aTable + 1) aX) (copy aY aX))) s _
  refine WP.seq (WP.mono (S.copy v aTable aOne (by decide) (by decide) (by decide) (by decide))
    fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.copy v (aTable + 1) aX (by decide) (by decide) (by decide) (by decide))
    fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.copy v aY aX (by decide) (by decide) (by decide) (by decide))
    fun t ⟨St, Ot, Kt⟩ => ?_
  refine ⟨St.mono ?_ (fun _ mem => ⟨mem, rfl⟩), ?_, (Ka.trans Kb).trans Kt⟩
  · intro j known
    refine ⟨?_, tableValues_initial A c g.w j known⟩
    change j ∈ [6, 12, 11, 0, 5, 9, 10, 27]
    change j ∈ [6, 11, 12, 0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact ((array_roundFrame S.data.context.ws.nowrap (by unfold roundArray aTable; simp) Oa).trans
      (array_roundFrame Sa.data.context.ws.nowrap (by unfold roundArray aTable; omega_using []) Ob)).trans
        (array_roundFrame Sb.data.context.ws.nowrap (by unfold roundArray aY; simp) Ot)

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.RunView`, which this module and modules that import it used -/

section

/-! # The exponent loop retains the table and constants while the witness is selected anew -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

def runArrays : List Nat := [aY, aOne, aMinusOne, aExponent, 0] ++ (List.range 16).map (aTable + ·)

def runValues (A : Nat → Nat) (c w : Nat) : Nat → Nat := setAt (tableValues A c w 14) aY (A aOne)

theorem runArrays_y : aY ∈ runArrays := by simp [runArrays]
theorem runArrays_one : aOne ∈ runArrays := by simp [runArrays]
theorem runArrays_minus : aMinusOne ∈ runArrays := by simp [runArrays]
theorem runArrays_exp : aExponent ∈ runArrays := by simp [runArrays]

theorem runArrays_power {j : Nat} (digit : j < 16) : aTable + j ∈ runArrays := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr digit, rfl⟩

theorem runArrays_notX : aX ∉ runArrays := by
  intro mem
  rcases List.mem_append.mp mem with mem | mem
  · change 5 ∈ [6, 9, 10, 27, 0] at mem
    contradiction
  · obtain ⟨j, _, eq⟩ := List.mem_map.mp mem
    unfold aTable aX at eq
    omega_using [eq]

theorem runValues_y (A : Nat → Nat) (c w : Nat) : runValues A c w aY = A aOne := setAt_self _ _ _
theorem runValues_one (A : Nat → Nat) (c w : Nat) : runValues A c w aOne = A aOne := rfl
theorem runValues_minus (A : Nat → Nat) (c w : Nat) : runValues A c w aMinusOne = A aMinusOne := rfl
theorem runValues_exp (A : Nat → Nat) (c w : Nat) : runValues A c w aExponent = A aExponent := rfl

theorem runValues_power (A : Nat → Nat) (c w : Nat) {j : Nat} (digit : j < 16) :
    runValues A c w (aTable + j) = Word32.tp c w (A aX) (A aOne) j := by
  rw [runValues, setAt_other _ _ (by unfold aTable aY; omega_using []), tableValues_power A c w digit]

theorem runValues_identity (A : Nat → Nat) (c w : Nat) : runValues A c w aY = runValues A c w aTable := by
  rw [runValues_y, show aTable = aTable + 0 by omega_using [], runValues_power A c w (by decide : 0 < 16)]
  rfl

end VG.Proof.MillerRabin.X86

end

end

/-! # The table and initial Montgomery one are ready before exponent scanning -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/Table.lean`, which only this module imported.
section

/-! # Fourteen prepared products build the complete sixteen-entry power table -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem table_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A initialArrays V Ds s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) :
    WP isa (table name code) s fun t =>
      Stage g capacity c p (tableValues A c g.w 14) (tableArrays 14) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold table
  rw [seqs_append_iff]
  refine WP.mono (tableInit_ok v S) fun a ⟨Sa, Oa, Ka⟩ => ?_
  let P : Nat → State → Prop := fun k t =>
    Stage g capacity c p (tableValues A c g.w k) (tableArrays k) V Ds t ∧
      WorkspaceFrame g (roundWrites g) a.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] a t
  have start : P 0 a := ⟨Sa, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
  refine WP.mono (seqs_range_ok 14
    (fun j => .seq (mulY name code aX) (copy (aTable + j + 2) aY)) P ?_ a start)
    fun t ⟨St, Ot, Kt⟩ => ⟨St, Oa.trans Ot, (Ka.mono (by decide)).trans Kt⟩
  intro k index t H
  obtain ⟨St, Ot, Kt⟩ := H
  refine WP.mono (tableStep_ok verified noSp stack v St length odd Xlt index)
    fun u ⟨Su, Ou, Ku⟩ => ?_
  exact ⟨Su, Ot.trans Ou, Kt.trans Ku⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageStore.lean`, which only this module imported.
section

/-! # Record a known register value in one permitted scratch word -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.storeRegister {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d : Nat) (scratch : scratchWord d) (r : Reg)
    (value : BitVec 32) (regValue : s.gpr r = value) :
    WP isa (.block [.store (slot d) r]) s fun t =>
      Stage g capacity c p A Js (setAt V d value) (d :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [] s t := by
  refine WP.mono (scalarStore_ok v S.data.context d scratch r) fun t ⟨Value, O, K, C⟩ => ?_
  rw [regValue] at Value
  have D := S.data.afterScalar v C d scratch value O Value
  have scratchList : ∀ e ∈ [d], scratchWord e := by
    intro e mem
    obtain rfl := List.mem_singleton.mp mem
    exact scratch
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] scratchList outs K (by decide),
    scalar_roundFrame S.data.context.ws.nowrap scratchList outs, K⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/InitWindows.lean`, which only this module imported.
section

/-! # Initialize the public exponent length and the secret pass flag -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem initWindows_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V [] s) :
    WP isa (.block initWindows) s fun t =>
      Stage g capacity c p A Js (setAt (setAt V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  unfold initWindows
  refine WP.block_append (WP.mono (words_ok v S.data.context) fun a ⟨Count, M, K⟩ => ?_)
  have Sa := S.keepMem K (by decide) (by decide) M
  have reg : a.gpr .esi = BitVec.ofNat 32 g.words := by
    apply BitVec.eq_of_toNat_eq
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.maxWidth; unfold Geometry.words; omega)]
  change WP isa (.block ([.store (slot sWords) .esi] ++ [.mov .eax (.imm 0), .store (slot sFlag) .eax])) a _
  refine WP.block_append (WP.mono (Sa.storeRegister v sWords (by unfold scratchWord sWords; simp) .esi _ reg)
    fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.literal v sFlag (by unfold scratchWord sFlag; simp) 0#32) fun t ⟨St, Ot, Kt⟩ => ?_
  rw [M] at Ob
  exact ⟨St, Ob.trans Ot, ((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem prepareRun_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A initialArrays V [] s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) :
    WP isa (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) s fun t =>
      Stage g capacity c p (runValues A c g.w) runArrays
        (setAt (setAt V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (table_ok verified noSp stack v S length odd Xlt) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.copy v aY aOne (by decide) (by decide) (by decide)
    (by simp [tableArrays, initialArrays])) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  change Stage g capacity c p (runValues A c g.w) (aY :: tableArrays 14) V [] b at Sb
  have Start : Stage g capacity c p (runValues A c g.w) runArrays V [] b :=
    Sb.mono (by
      intro j mem
      refine ⟨?_, rfl⟩
      rcases List.mem_append.mp mem with base | power
      · change j ∈ [6, 9, 10, 27, 0] at base
        simp only [List.mem_cons, List.not_mem_nil, or_false] at base
        rcases base with rfl | rfl | rfl | rfl | rfl <;> decide
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ power)))
      (fun _ mem => ⟨mem, rfl⟩)
  refine WP.mono (initWindows_ok v Start) fun t ⟨St, Ot, Kt⟩ => ?_
  exact ⟨St, (Oa.trans (array_roundFrame Sa.data.context.ws.nowrap
    (by unfold roundArray aY; simp) Ob)).trans Ot,
    (Ka.trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingSelect`, which only this module used -/

section

/-! # Masked selection reads every word at the same public addresses -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem loadMask_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g copyRegisters) (.block [.mov .ecx (.mem (slot sEq1))]) (Pair g copyRegisters) := by
  refine readonly_relCT (checkedBlockInvariant rfl rfl) ?_
  intro s C
  exact wp_movS (readSrc_ptr C.ws C.base (d := sEq1) (by have := v.headerFit; unfold sEq1; omega_using [this]))
    fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem selectLoop_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters))
    (.loop (.block selectBody) .ne) (VG.X86.Taint.Agree (roundTaint copyRegisters)) :=
  checkedProgramChange (τ' := roundTaint copyRegisters true)
    (hint := VG.Taint.hintOf taint (roundTaint copyRegisters) (.loop (.block selectBody) .ne)) (by kernel_rfl) (by kernel_rfl)

theorem selectEntry_trace {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (Pair g [.edi]) (selectEntry j) (VG.X86.Taint.Agree (roundTaint copyRegisters)) := by
  unfold selectEntry
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp (aTable + j) (by decide) (by unfold aTable; omega_using [digit]) [.edi] (by decide))
    (RelCT.block_append (RelCT.seq
      (pointer_pair_relCT v .ebx aX (by decide) (by decide) [.ebp, .edi] (by decide))
      (RelCT.block_append (RelCT.seq
        (words_pair_relCT v [.ebx, .ebp, .edi] (by decide)) (loadMask_relCT v))))))) ?_
  exact selectLoop_raw.mono (P' := Pair g copyRegisters) (fun _ _ H => H.2.2) (fun _ _ H => H)

def masked (g : Geometry) (s : State) : Prop :=
  ∃ bit : Bool, s.mem.readW (off g.W sEq1) 32 = if bit then BitVec.allOnes 32 else 0#32

theorem selectEntry_relCT {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ masked g s ∧ masked g t)
      (selectEntry j) (Pair g [.edi]) := by
  intro s t tr ur u z ⟨H, ⟨bs, Ms⟩, ⟨bt, Mt⟩⟩ E G
  obtain ⟨trace, A⟩ := selectEntry_trace v j digit _ _ _ _ _ _ H E G
  obtain ⟨_, _, _, Cu⟩ := wp_result (selectEntry_ok v H.1 j digit bs Ms) E
  obtain ⟨_, _, _, Cz⟩ := wp_result (selectEntry_ok v H.2.1 j digit bt Mt) G
  refine ⟨trace, Cu, Cz, round_add_regs (round_forget A) ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact round_regs A (by decide : .edi ∈ copyRegisters)

end VG.Proof.MillerRabin.X86

end

end

/-! # Private arithmetic state through the complete round's timing composition -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingScan.lean`, which only this module imported.
section

/-! # All sixteen powers are scanned independently of the secret digit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem maskIndex_pair_relCT {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (Pair g [.edi]) (.block (maskIndex j)) fun s t =>
      Pair g [.edi] s t ∧ masked g s ∧ masked g t := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := maskIndex_relCT j _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, _, _, Cu⟩ := wp_result (maskIndex_ok v H.1 j digit) E
  obtain ⟨Mz, _, _, Cz⟩ := wp_result (maskIndex_ok v H.2.1 j digit) G
  refine ⟨trace, ⟨Cu, Cz, A⟩, ?_, ?_⟩
  · refine ⟨decide ((s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j), ?_⟩
    simpa using Mu
  · refine ⟨decide ((t.mem.readW (off g.W sValue) 32 >>> 28).toNat = j), ?_⟩
    simpa using Mz

theorem scanFrom_relCT {g : Geometry} (v : g.Valid) (n : Nat) :
    ∀ j, j + n ≤ 16 → RelCT isa (Pair g [.edi]) (scanFrom j n) (Pair g [.edi]) := by
  induction n with
  | zero => intro j _; exact RelCT.block_nil (fun _ _ H => H)
  | succ n ih =>
    intro j bound
    exact RelCT.seq (maskIndex_pair_relCT v j (by omega))
      (RelCT.seq (selectEntry_relCT v j (by omega)) (ih (j + 1) (by omega)))

theorem scan_relCT {g : Geometry} (v : g.Valid) : RelCT isa (Pair g [.edi]) scan (Pair g [.edi]) :=
  RelCT.seq (copy_relCT v aX aTable (by decide) (by decide)) (scanFrom_relCT v 15 1 (by decide))

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingWindowFront.lean`, which only this module imported.
section

/-! # Window squaring and scanning retain each run's private canonical values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

structure WindowSecret where
  c : Nat
  A : Nat → Nat
  V : Nat → BitVec 32
  flag : Bool

def WindowMath (σ : WindowSecret) : Prop :=
  σ.c % 2 = 1 ∧ σ.A aY < σ.c ∧ σ.A aTable = σ.A aOne ∧
    (∀ j < 16, σ.A (aTable + j) < σ.c) ∧ σ.V sFlag = BitVec.ofNat 32 σ.flag.toNat

def WindowStart (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A runArrays σ.V windowFields s ∧ WindowMath σ

def windowFourV (σ : WindowSecret) : Nat → BitVec 32 := setAt (setAt σ.V sThreshold 0#32) sSquares 4#32

def WindowFour (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A runArrays (windowFourV σ) (sSquares :: sThreshold :: windowFields) s ∧ WindowMath σ

def WindowSquared (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (squareValues σ.A σ.c g.w 0 4 σ.flag 4) runArrays
    (windowSquaresV σ.V σ.A σ.c g.w σ.flag) (sSquares :: sThreshold :: windowFields) s ∧ WindowMath σ

def WindowScanned (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (windowScanA σ.V σ.A σ.c g.w σ.flag) (aX :: runArrays)
    (windowSquaresV σ.V σ.A σ.c g.w σ.flag) (sSquares :: sThreshold :: windowFields) s ∧ WindowMath σ

theorem windowFour_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (WindowStart g capacity p)) (.block fourSquares) (Two g (WindowFour g capacity p)) := by
  refine private_attach ((checkedBlockInvariant rfl rfl).mono (fun _ _ H => H.1.2.2) (fun _ _ H => H))
    ?_ (fun _ _ H => H.1.data.context)
  intro σ s ⟨S, math⟩
  exact WP.mono (fourSquares_ok v S) fun _ R => ⟨R.1, math⟩

theorem windowSquares_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (WindowFour g capacity p)) (squareLoop name code) (Two g (WindowSquared g capacity p)) := by
  have known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ sSquares :: sThreshold :: windowFields := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> decide
  have guard {s : State} {σ : WindowSecret} (H : WindowFour g capacity p σ s) : SquareInput g capacity p 4 s :=
    H.1.squareInput H.2.1 H.2.2.1 runArrays_y runArrays_minus (by decide : 0 < 2 ^ 31)
      (by decide : 4 < 2 ^ 31) σ.flag known rfl rfl H.2.2.2.2.2
  refine private_attach ((squareLoop_relCT (p := p) verified noSp stack v length (by decide : 0 < 4)).mono
    (fun _ _ H => ⟨H.1, guard H.2.1.choose_spec, guard H.2.2.choose_spec⟩) (fun _ _ H => H.2.2))
    ?_ (fun _ _ H => H.1.data.context)
  intro σ s ⟨S, math⟩
  refine WP.mono (squareLoop_ok verified noSp stack v S length math.1 math.2.1 runArrays_y runArrays_minus
    (by decide : 0 < 4) (by decide : 4 < 2 ^ 31) (by decide : 0 < 2 ^ 31) σ.flag
    known (by decide) rfl rfl math.2.2.2.2) fun _ R => ⟨R.1, math⟩

theorem windowScan_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (WindowSquared g capacity p)) scan (Two g (WindowScanned g capacity p)) := by
  refine private_lift (scan_relCT v) ?_
  intro σ s ⟨S, math⟩
  exact WP.mono (S.scan v (fun _ digit => runArrays_power digit) (by decide) (by decide)) fun _ R => ⟨R.1, math⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingWindow.lean`, which only this module imported.
section

/-! # A complete four-bit window has no secret-dependent address or branch -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86

theorem WindowScanned.mulInput {g : Geometry} {capacity : Nat} {p : BitVec 32}
    {σ : WindowSecret} {s : State} (H : WindowScanned g capacity p σ s) : MulInput g capacity aX p s := by
  refine H.1.mulInput H.2.1 (List.mem_cons_self ..) ?_
  rw [windowScanA, setAt_self, squareValues,
    setAt_other _ _ (by unfold aTable aY; omega_using [] : aTable + windowDigit σ.V ≠ aY)]
  exact H.2.2.2.2.1 (windowDigit σ.V) (digit_lt _)

theorem window_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (WindowStart g capacity p)) (window name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (.block fourSquares) (.seq (squareLoop name code) (.seq scan
    (.seq (mulY name code aX) (.seq (equal sEq1 aY aOne) (.seq (equal sEq2 aY aMinusOne) (.block windowEnd))))))) _
  refine RelCT.seq (windowFour_relCT v) (RelCT.seq (windowSquares_relCT verified noSp stack v length)
    (RelCT.seq (windowScan_relCT v) ?_))
  refine RelCT.seq ((mulY_relCT (p := p) verified noSp stack v length
    (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide)).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.mulInput, H.2.2.choose_spec.mulInput⟩) (fun _ _ H => H)) ?_
  refine RelCT.seq (equal_relCT v sEq1 aY aOne (by unfold scratchWord sEq1; simp) (by decide) (by decide)) ?_
  exact RelCT.seq (equal_relCT v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp) (by decide) (by decide))
    (windowEnd_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H))

def WindowInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ σ, WindowStart g capacity p σ s ∧ σ.V sWindows = BitVec.ofNat 32 q ∧ q < 2 ^ 32

theorem WindowInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WindowInput g capacity p q s) : Context g s := by
  obtain ⟨_, ⟨S, _⟩, _⟩ := I
  exact S.data.context

theorem WindowInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WindowInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (window name code) s fun t => WindowInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨σ, ⟨S, odd, lt, one, tableLt, flag⟩, count, bound⟩ := I
  refine WP.mono (window_ok verified noSp stack v S length odd lt runArrays_y runArrays_one runArrays_minus
    runArrays_notX (fun _ digit => runArrays_power digit) one tableLt positive bound σ.flag flag count)
    fun t ⟨St, Z, _, _⟩ => ?_
  let A := setAt σ.A aY (windowResult σ.V σ.A σ.c g.w σ.flag).1
  let V := windowCounters σ.V σ.A σ.c g.w q σ.flag
  let F := (windowResult σ.V σ.A σ.c g.w σ.flag).2
  refine ⟨⟨⟨σ.c, A, V, F⟩, ⟨St, odd, ?_, ?_, ?_, rfl⟩, rfl, by omega_using [bound]⟩, Z⟩
  · change (windowResult σ.V σ.A σ.c g.w σ.flag).1 < σ.c
    exact Word32.mm_lt (by omega_using [odd] : 0 < σ.c)
  · exact one
  · intro j digit
    change setAt σ.A aY _ (aTable + j) < σ.c
    rw [setAt_other _ _ (by unfold aTable aY; omega_using [])]
    exact tableLt j digit

theorem windowLoop_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ WindowInput g capacity p q s ∧ WindowInput g capacity p q t)
      (.loop (window name code) .ne) (Pair g [.edi]) := by
  refine (private_count_loop (F := fun q (_ : Unit) s => WindowInput g capacity p q s) ?_ q positive).mono
    (fun _ _ H => ⟨H.1, ⟨(), H.2.1⟩, ⟨(), H.2.2⟩⟩) (fun _ _ H => H.1)
  intro n positive
  refine private_control ?_ (fun _ s I => I.step verified noSp stack v length positive)
    (fun _ _ I => I.context) positive
  refine (window_trace (p := p) verified noSp stack v length).mono ?_ (fun _ _ H => H)
  intro s t ⟨P, ⟨_, σ, S, _⟩, ⟨_, ρ, T, _⟩⟩
  exact ⟨P, ⟨σ, S⟩, ⟨ρ, T⟩⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/WordPointer.lean`, which only this module imported.
section

/-! # Address the exponent word using the public native-word countdown -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def wordPointer : List Instr :=
  ptr .ebp aExponent ++ [.mov .eax (.mem (slot sWords)), .alu .sub .eax (.imm 1),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebp (.reg .eax)]

theorem wordPointer_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q ≤ g.words)
    (count : s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q) :
    WP isa (.block wordPointer) s fun t =>
      PtrAt t g.W .ebp (g.array aExponent + 4 * (q - 1)) ∧ t.mem = s.mem ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have header := v.headerFit
  have expFit := v.arrayFit (j := aExponent) (by decide)
  have small : q ≤ 256 := by have := v.maxWidth; unfold Geometry.words at bound; omega_using [bound, this]
  unfold wordPointer
  refine WP.block_append (WP.mono (C.ptr v aExponent (by decide) .ebp (by decide) (by decide))
    fun u ⟨P, Mu, Ku⟩ => ?_)
  have Cu := C.keepMem Ku (by decide) Mu
  refine wp_movS (Cu.readScalar sWords (by unfold sWords; omega_using [header])) fun a A _ => ?_
  refine wp_subS rfl fun b B _ => wp_addS rfl fun c D _ => wp_addS rfl fun d H _ => ?_
  have Kd : Keeps [.eax, .edx, .ebp] s d :=
    ((((Ku.mono (by decide)).widen A.keeps).widen B.keeps).widen D.keeps).widen H.keeps
  have Md : d.mem = s.mem := H.mem.trans (D.mem.trans (B.mem.trans (A.mem.trans Mu)))
  have bp : PtrAt d g.W .ebp (g.array aExponent) := by
    rw [PtrAt, H.other .ebp (by decide), D.other .ebp (by decide), B.other .ebp (by decide),
      A.other .ebp (by decide)]; exact P
  have indexVal : (d.gpr .eax).toNat = 4 * (q - 1) := by
    rw [H.gpr, D.gpr, B.gpr, A.gpr, Mu, count]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 +
      ((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
    omega_using [positive, small]
  refine wp_addS rfl fun e I _ => ?_
  have Ke : Keeps [.eax, .edx, .ebp] s e := Kd.widen I.keeps
  have Me : e.mem = s.mem := I.mem.trans Md
  have be : PtrAt e g.W .ebp (g.array aExponent + 4 * (q - 1)) := by
    rw [PtrAt, I.gpr, ptr_add bp, indexVal]
  exact WP.block_nil ⟨be, Me, Ke⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingLoadWord.lean`, which only this module imported.
section

/-! # Exponent loads use the public word counter, even for a secret exponent -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem wordPointer_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block wordPointer) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold wordPointer
  refine RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp aExponent (by decide) (by decide) [.edi] (by decide)) ?_)
  exact (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi]) (by kernel_rfl) (by kernel_rfl)).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem wordPointer_relCT {g : Geometry} (v : g.Valid) (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧
      s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q ∧
      t.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q)
      (.block wordPointer) (VG.X86.Taint.Agree (roundTaint [.edi, .ebp])) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, A⟩ := wordPointer_trace v _ _ _ _ _ _ H E G
  obtain ⟨Pu, _, _⟩ := wp_result (wordPointer_ok v H.1 q positive bound S) E
  obtain ⟨Pz, _, _⟩ := wp_result (wordPointer_ok v H.2.1 q positive bound T) G
  refine ⟨trace, round_add_regs (round_forget A) ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact round_regs A (by decide)
  · exact ptr_agree Pu Pz

theorem loadWord_trace {g : Geometry} (v : g.Valid) (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧
      s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q ∧
      t.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q)
      (.block loadWord) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.block (wordPointer ++ [.mov .eax (.mem (at_ .ebp 0)), .store (slot sValue) .eax,
    .mov .eax (.imm 8), .store (slot sWindows) .eax])) _
  exact RelCT.block_append (RelCT.seq (wordPointer_relCT v q positive bound)
    (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp, .eax]) (by kernel_rfl) (by kernel_rfl)))

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingWords.lean`, which only this module imported.
section

/-! # Exponent words execute eight windows and decrement a public counter -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def WordInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ σ : WindowSecret, Stage g capacity σ.c p σ.A runArrays σ.V wordFields s ∧ WindowMath σ ∧
    σ.V sWords = BitVec.ofNat 32 q ∧ q ≤ g.words

theorem WordInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) : Context g s := by
  obtain ⟨_, S, _⟩ := I
  exact S.data.context

theorem WordInput.count {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) : s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q := by
  obtain ⟨σ, S, _, count, _⟩ := I
  exact (S.data.slotValues sWords (by decide)).2.trans count

theorem WordInput.bound {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) : q ≤ g.words := by
  obtain ⟨_, _, _, _, bound⟩ := I
  exact bound

theorem WordInput.load {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) (positive : 0 < q) :
    WP isa (.block loadWord) s (WindowInput g capacity p 8) := by
  obtain ⟨σ, S, math, count, bound⟩ := I
  let x := s.mem.readW (off g.W (g.array aExponent + 4 * (q - 1))) 32
  refine WP.mono (S.loadWord v q positive bound count x rfl) fun t ⟨St, _, _⟩ => ?_
  refine ⟨⟨σ.c, σ.A, setAt (setAt σ.V sValue x) sWindows 8#32, σ.flag⟩,
    ⟨St, math.1, math.2.1, math.2.2.1, math.2.2.2.1, math.2.2.2.2⟩, rfl, by decide⟩

theorem wordStep_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ WordInput g capacity p q s ∧ WordInput g capacity p q t)
      (wordStep name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (.block loadWord) (.seq (.loop (window name code) .ne) (.block wordEnd))) _
  refine RelCT.seq (R := fun s t => Pair g [.edi] s t ∧ WindowInput g capacity p 8 s ∧ WindowInput g capacity p 8 t) ?_
    (RelCT.seq (windowLoop_relCT verified noSp stack v length (by decide : 0 < 8)) ?_)
  · intro s t tr ur u z ⟨H, S, T⟩ E G
    obtain ⟨trace, A⟩ := loadWord_trace v q positive S.bound _ _ _ _ _ _ ⟨H, S.count, T.count⟩ E G
    have U := wp_result (S.load v positive) E
    have Z := wp_result (T.load v positive) G
    exact ⟨trace, ⟨U.context, Z.context, A⟩, U, Z⟩
  · exact (checkedBlockInvariant rfl rfl).mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem WordInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (wordStep name code) s fun t => WordInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨σ, S, ⟨odd, lt, one, tableLt, flag⟩, count, bound⟩ := I
  refine WP.mono (wordStep_ok verified noSp stack v S length odd lt runArrays_y runArrays_one runArrays_minus
    runArrays_exp runArrays_notX (fun _ digit => runArrays_power digit) one tableLt positive bound σ.flag flag count)
    fun t ⟨St, Z, _, _⟩ => ?_
  let x := exponentWord (σ.A aExponent) (q - 1)
  let A := wordValues σ.A σ.c g.w x σ.flag 8
  let V := wordEndSlots σ.V σ.A σ.c g.w x σ.flag q
  let F := (wordState σ.A σ.c g.w x σ.flag 8).2
  refine ⟨⟨⟨σ.c, A, V, F⟩, St, ⟨odd, ?_, ?_, ?_, rfl⟩, rfl, by omega_using [bound]⟩, Z⟩
  · change (wordState σ.A σ.c g.w x σ.flag 8).1 < σ.c
    exact wordState_lt σ.A (by omega_using [odd] : 0 < σ.c) g.w x σ.flag lt 8
  · exact one
  · intro j digit
    change setAt σ.A aY _ (aTable + j) < σ.c
    rw [setAt_other _ _ (by unfold aTable aY; omega_using [])]
    exact tableLt j digit

theorem wordLoop_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ WordInput g capacity p q s ∧ WordInput g capacity p q t)
      (.loop (wordStep name code) .ne) (Pair g [.edi]) := by
  refine (private_count_loop (F := fun q (_ : Unit) s => WordInput g capacity p q s) ?_ q positive).mono
    (fun _ _ H => ⟨H.1, ⟨(), H.2.1⟩, ⟨(), H.2.2⟩⟩) (fun _ _ H => H.1)
  intro n positive
  refine private_control ?_ (fun _ s I => I.step verified noSp stack v length positive)
    (fun _ _ I => I.context) positive
  exact (wordStep_trace (p := p) verified noSp stack v length positive).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec, H.2.2.choose_spec⟩) (fun _ _ H => H)

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen VG.Impl.MillerRabin.X86

structure CoreSecret where
  c : Nat
  A : Nat → Nat
  V : Nat → BitVec 32
  k : Nat
  origin : Mem

def CoreMath (g : Geometry) (σ : CoreSecret) : Prop :=
  σ.c % 2 = 1 ∧ σ.A aX < σ.c ∧ σ.A aOne < σ.c ∧ σ.k < 64 ∧
    σ.origin.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ σ.k % 2 ^ 32) ∧
    σ.origin.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ σ.k / 2 ^ 32)

def CoreStart (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A initialArrays σ.V [] s ∧ CoreMath g σ ∧ s.mem = σ.origin

def runV (g : Geometry) (σ : CoreSecret) : Nat → BitVec 32 :=
  setAt (setAt σ.V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32

def CoreRun (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (runValues σ.A σ.c g.w) runArrays (runV g σ) wordFields s ∧
    CoreMath g σ ∧ WorkspaceFrame g (roundWrites g) σ.origin s.mem

def endA (g : Geometry) (σ : CoreSecret) : Nat → Nat :=
  exponentValues (runValues σ.A σ.c g.w) σ.c g.w g.words false g.words

def endV (g : Geometry) (σ : CoreSecret) : Nat → BitVec 32 :=
  exponentCounters (runV g σ) (runValues σ.A σ.c g.w) σ.c g.w g.words false g.words

def endFlag (g : Geometry) (σ : CoreSecret) : Bool :=
  (exponentState (runValues σ.A σ.c g.w) σ.c g.w g.words false g.words).2

def CoreWords (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (endA g σ) runArrays (endV g σ) wordFields s ∧
    CoreMath g σ ∧ WorkspaceFrame g (roundWrites g) σ.origin s.mem

def finalV (g : Geometry) (σ : CoreSecret) : Nat → BitVec 32 :=
  setAt (setAt (endV g σ) sThreshold (BitVec.ofNat 32 (4 - sigOf σ.k))) sSquares 3#32

def CoreFinal (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (endA g σ) runArrays (finalV g σ) ([sThreshold, sSquares] ++ wordFields) s ∧ CoreMath g σ

theorem CoreStart.prepare {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreStart g capacity p σ s) (length : g.L = 8 * capacity) :
    WP isa (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) s (CoreRun g capacity p σ) := by
  refine WP.mono (prepareRun_ok verified noSp stack v H.1 length H.2.1.1 H.2.1.2.1) fun _ R => ?_
  exact ⟨R.1, H.2.1, H.2.2 ▸ R.2.1⟩

theorem CoreMath.run_window {g : Geometry} {σ : CoreSecret} (H : CoreMath g σ) :
    WindowMath ⟨σ.c, runValues σ.A σ.c g.w, runV g σ, false⟩ := by
  refine ⟨H.1, ?_, ?_, ?_, rfl⟩
  · change runValues σ.A σ.c g.w aY < σ.c
    rw [runValues_y]; exact H.2.2.1
  · change runValues σ.A σ.c g.w aTable = runValues σ.A σ.c g.w aOne
    rw [← runValues_identity, runValues_y, runValues_one]
  · intro j digit
    change runValues σ.A σ.c g.w (aTable + j) < σ.c
    rw [runValues_power σ.A σ.c g.w digit]
    exact Word32.tp_lt (by have := H.2.1; omega_using [this] : 0 < σ.c) H.2.1 H.2.2.1 j

theorem CoreRun.wordInput {g : Geometry} {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreRun g capacity p σ s) : WordInput g capacity p g.words s :=
  ⟨⟨σ.c, runValues σ.A σ.c g.w, runV g σ, false⟩, H.1, H.2.1.run_window, rfl, Nat.le_refl _⟩

theorem CoreRun.words {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreRun g capacity p σ s) (length : g.L = 8 * capacity) :
    WP isa (.loop (wordStep name code) .ne) s (CoreWords g capacity p σ) := by
  have math := H.2.1.run_window
  refine WP.mono (wordLoop_ok verified noSp stack v H.1 length math.1 math.2.1 runArrays_y runArrays_one
    runArrays_minus runArrays_exp runArrays_notX (fun _ digit => runArrays_power digit) math.2.2.1 math.2.2.2.1
    false rfl rfl) fun _ R => ⟨R.1, H.2.1, H.2.2.trans R.2.1⟩

theorem CoreWords.marker {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    {σ : CoreSecret} {s : State} (H : CoreWords g capacity p σ s) :
    WP isa (.block lastSquares) s (CoreFinal g capacity p σ) := by
  have lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ σ.k % 2 ^ 32) := by
    have R := roundFrame_marker32 v H.2.2 (extra := 0) (Or.inl rfl)
    rw [Nat.add_zero] at R
    exact R.trans H.2.1.2.2.2.2.1
  have hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ σ.k / 2 ^ 32) :=
    (roundFrame_marker32 v H.2.2 (extra := 4) (Or.inr rfl)).trans H.2.1.2.2.2.2.2
  exact WP.mono (H.1.lastSquares v H.2.1.2.2.2.1 lo hi) fun _ R => ⟨R.1, H.2.1⟩

theorem CoreFinal.squareInput {g : Geometry} {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreFinal g capacity p σ s) : SquareInput g capacity p 3 s := by
  have lt : endA g σ aY < σ.c := by
    rw [endA, exponentValues, setAt_self]
    exact exponentState_lt _ (by have := H.2.2.1; omega_using [this] : 0 < σ.c) g.w g.words false
      (by rw [runValues_y]; exact H.2.2.2.1) g.words
  refine H.1.squareInput H.2.1 lt runArrays_y runArrays_minus
    (by omega_using [] : 4 - sigOf σ.k < 2 ^ 31) (by decide : 3 < 2 ^ 31) (endFlag g σ) ?_ rfl rfl rfl
  intro d mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> decide

end VG.Proof.MillerRabin.X86
