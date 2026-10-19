module

import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
meta import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallPack
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegment
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezePast
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegment
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.TCB.Axioms

/-!
# ML-DSA key generation on AArch64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The function, piece by piece, for any parameter set of Table 1 and any
verified implementations of the primitives (`keyGen_piece`): it returns 1 with
`KeyGen_internal(ξ)` in `pk` and `sk` if every sampler succeeded (for some
bounds), and 0 if key generation fails within the least bounds; it leaks only
the pointers, `ρ` and what `RejBoundedPoly` leaks; so it meets the shared
contract (`keyGen_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {i : Nat}
    (hi : i < p.k) : Piece p S' (KRx p (p.ℓ + p.k) p.ℓ i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (mul_piece hP hF hi).seq (Piece.seq ?_ ((inv_piece hP hF hi).seq ((addS2_piece hP hF hi).seq
    ((p2r_piece hP hF hi).seq ((sbp_piece hP hF hi).seq (bp_piece hP hF hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => RowI p i (tIs p fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => mulAdd_piece hP hF hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pa_zero (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

theorem pk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : KR p σ A S R np nj p.k s) :
    bytesAt s.mem (pa s (.x26, 0)) p.pkLen = pkK p A S (rhoOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x26) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.pk0
  rw [hF.pk, pa_zero, Proof.MlKem.bytesAt_add, h0,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x26) 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : KR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem (pa s (.x27, 0)) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x27) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 32) 32 = kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 :=
    htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, pa_zero, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (oT0 p) 416 p.k, skK]
  rw [flatMap_congr_mem (g := fun r => bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    flatMap_congr_mem (g := fun i => bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trHash_chk {p : Params} (hF : PFacts p) :
    hashChk kgR (kgW p) [⟨.x26, 0, p.pkLen⟩] ⟨.x27, 64, 64⟩ = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  unfold hashChk pieceChk; lay [hF.pk, hF.sk]

theorem trHash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P ((trHashWith keccak.callee) p) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaTrHashTaint p hp
  exact VectorTaint.relRegs bases hr hh

theorem trHash_piece {p : Params} (hF : PFacts p) {S' : Nat} (h16 : 16 ≤ S') (hSl : S' < 2 ^ 64) :
    Piece p S' (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) ((trHashWith keccak.callee) p) := by
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, rel_of (Q := Two p S') (trHash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHashWith
  refine WP.mono (shake_ok h16 hSl L (by simp) (trHash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨A, S, R, ?_, ?_⟩
  · have hc : KRChk p (p.ℓ + p.k) p.ℓ p.k [((.x28, 0), 200), ((.x28, 200), 640), ((.x27, 64), 64)] :=
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega)).append (ws₁ := [_])
      ((KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega)).append (ws₁ := [_])
      (KRChk.x27 hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega)) (by rw [hF.sk, oT0]; omega)))
    exact h.keep hF hp hP' x' hc
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), ho]
    exact congrArg (Spec.MlDsa.H · 64) (pk_bytes hF h)

/-! ## The return -/

theorem outcome_of {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    (hl : 0 < p.ℓ) (hG : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf σ)) (R.setWidth 32)
      (pkK p A S (rhoOf p σ), skK p A S (rhoOf p σ) (kOf p σ)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (xiOf σ) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem epi_piece {p : Params} (hF : PFacts p) {S' : Nat} :
    Piece p S' (KFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s)
      (.block epi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, rel_of (Q := Two p S') (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := scr_ge hF; lay)
    rwa [pa, h.kc.top.x28] at this
  refine WP.mono (epi_ok h.kc.top hin) fun s' ⟨ha, hr, hm⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  have e26 : pa s (.x26, 0) = σ.gpr .x1 := by rw [pa_zero, h.kc.top.x26]
  have e27 : pa s (.x27, 0) = σ.gpr .x2 := by rw [pa_zero, h.kc.top.x27]
  rw [hr, h.x24, hm, ← e26, ← e27, pk_bytes hF h, sk_bytes hF h htr]
  exact outcome_of (by have := hF.l; omega) h.good

/-! ## The function -/

theorem rest_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) :
    Piece p S' (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p) ((restWith keccak.callee) P p) := by
  unfold restWith
  refine (copies_piece hF).seq (Piece.seq (J := KRx p (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := KRx p (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := KRx p (p.ℓ + p.k) p.ℓ p.k) ?_
      (trHash_piece hF hP.s16 hP.s64))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p r 0 0) (p.ℓ + p.k) 0 fun r _ hr => packS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => nttS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => row_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p)
    (hs : (p.ℓ + p.k) % 4 = 0 ∨ (p.ℓ + p.k) % 4 = 3) :
    Piece p S' (fun σ s => s = σ)
      (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s) (keyGenWith keccak.callee P p) :=
  (pro_piece hF).seq ((seeds_piece hF hP.s16 hP.s64).seq ((sampAll_piece hP hF).seq
    ((Optimized.secrets_piece keccak.callee hF hs S').seq ((rest_piece hP hF).seq (epi_piece hF)))))

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls that use at most `S`
bytes of stack, if the contract is satisfiable. -/
theorem keyGen_verified {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : ∃ s, (Spec.MlDsa.keyGenContract p AArch64.abi S).pre s) :
    Verified AArch64.target (keyGenWith keccak.callee P p) (Spec.MlDsa.keyGenContract p AArch64.abi S) :=
  have hs : (p.ℓ + p.k) % 4 = 0 ∨ (p.ℓ + p.k) % 4 = 3 := by rcases hp with rfl | rfl | rfl <;> decide
  ⟨fun σ hσ => (keyGen_piece hP (pfacts hp) hs).ok σ σ (kgPre_of_shared hσ) rfl,
    fun s t l m u v hs' ht pub es et => relStart (Q := fun _ _ => True)
      (keyGen_piece hP (pfacts hp) hs).tr s t l m u v (kgPre_of_shared hs') (kgPre_of_shared ht) pub es et, hsat⟩

end VG.Proof.MlDsa.AArch64.KeyGen
