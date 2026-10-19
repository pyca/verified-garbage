module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
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
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLoad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCallTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintContract
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintSpec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCallTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowField
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHints
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZLayout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
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
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Arith

/-! ## From `OptimizedPairedLoopEndTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

abbrev PairedIX (p : Params) (S t : Nat) (x y : State) : Prop :=
  PositiveIX p S t x y ∧ PairedRoots S x ∧ PairedRoots S y ∧
    x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR"

theorem pairedEndPF_tr {p : Params} {S : Nat} (hp : Ok3 p) (hS : S<2^64) {t : Nat} :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s)
      (.block cntDec) (PairedIX p S t) :=
  paired_trace_frame (Nat.zero_le _) hS
    (RelCT.mono (positiveEndPF_tr hp (paramsOk hp) (lChk_ok hp))
      (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h))

theorem pairedEndB_tr {p : Params} {S : Nat} (hp : Ok3 p) (hS : S<2^64) {t : Nat} :
    RelCT isa (PairedRS p S (LeakEq p t) (PositiveEB p S · t))
      (.block cntDec) (PairedIX p S t) :=
  paired_trace_frame (Nat.zero_le _) hS
    (RelCT.mono (positiveEndB_tr hp (paramsOk hp) (lChk_ok hp))
      (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h))

theorem PairedIX.next {p : Params} {S t : Nat} {x y : State}
    (h : PairedIX p S t x y) (hz : x.gpr .x9≠0) :
    PairedRS p S (LeakEq p (t+1)) (PositiveIL p S · (t+1)) x y :=
  PairedRS.of_root (h.1.2.1 hz) h.2.1 h.2.2.1 h.2.2.2

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedBallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem positiveBall_step_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) {t : Nat} (ht : t<814) :
    RelCT isa (RootRS p D (LeakEq p t) (PositiveIC p D · t))
      (ballAt P (cLen p) p.τ cP) fun x y=>RootRS p D (LeakEq p t) (PositiveIB p D · t) x y ∧
        (x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32 := by
  have hc2 := bChk_ok h3
  have hc2' := hc2
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc2'
  refine RelCT.mono (liftRootQ (G := fun _ _=>True) (J := fun σ s=>PositiveIB p D σ t s) (F := fun _ _=>True)
    (fun _ _ _ h=>WP.mono (positiveBall_ok hP h3 hc2 h) fun _ h=>⟨h,trivial⟩)
    (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h,_⟩=>⟨h.1.lrel (fun _ _ h=>h.c.masks.l.st),by
      obtain ⟨σ,τ,_,_,_,he,hx,hy⟩ := h.1
      rw [hx.ct,hy.ct]; exact leq_ct he ht⟩) (fun _ _ h=>h))
    (fun σ τ x y x' y' ps pt pub he _ _ _ jx jy _ _ eq roots=>
      ⟨⟨⟨σ,τ,ps,pt,pub,he,jx,jy⟩,roots⟩,eq⟩))
    (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h)

theorem pairedBall_step_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {t : Nat} (ht : t<814)
    (hd : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p t) (PositiveIC p S · t))
      (ballAt P (cLen p) p.τ cP) fun x y=>PairedRS p S (LeakEq p t) (PositiveIB p S · t) x y ∧
        (x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32 :=
  RelCT.mono (paired_trace_frame hd hP.s64 (positiveBall_step_tr hP hp ht)) (fun _ _ h=>h)
    (fun _ _ h=>⟨PairedRS.of_root h.1.1 h.2.1 h.2.2.1 h.2.2.2,h.1.2⟩)

theorem pairedCommit_tr {keccak : Proof.Sha3.AArch64.Permutation}
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hp : Ok3 p)
    (hd : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIL p S · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p)
      (PairedRS p S E (PositiveIC p S · t)) :=
  RelCT.mono (paired_trace_frame hd hP.s64 (positiveCommit_tr hP hp)) (fun _ _ h=>h)
    (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedHintEndTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem positiveOnesOk_tr {p : Params} {S : Nat} (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIH p S · t p.k)) (.block (onesOk p))
      (RootRS p S E (PositiveKO p S · t)) :=
  liftRootT (fun _ _ h=>⟨h.1.b.l.st,h.1.b.l.k.d.roots⟩)
    (fun _ _ _ h=>positiveOnesOk_ok hc h)
    (lrel_tr (fun _ _ h=>h.1) (onesOk_taint p))

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedChecksPrefixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem positivePairedChallenge_tr {p : Params} {S : Nat} (hp : Ok3 p) (h16 : 16≤S)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt (positiveNttArgs cP))
      (PairedRS p S E (PositiveChallenge p S · t)) :=
  liftPairedR (fun _ _ _ h roots=>positivePairedChallenge_ok hp h16 roots h.1 h.2)
    (RelCT.mono (positiveChallenge_tr hp) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedChecksInit_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveChallenge p S · t)) (.block kInit)
      (PairedRS p S E (PositiveIZ p S · t 0)) :=
  liftPairedR (fun _ _ _ h roots=>positivePairedChecksInit_ok hp hc roots h)
    (RelCT.mono (positiveChecksInit_tr hp hc) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedChecksPrefix_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    (h16 : 16≤S) {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix p)
      (PairedRS p S E (PositiveIH p S · t 0)) := by
  refine RelCT.seq (RelCT.seq (positivePairedChallenge_tr hp h16)
    (RelCT.seq (positivePairedChecksInit_tr hp hc) (optimizedZ_paired_vector_tr hp))) ?_
  exact RelCT.mono (optimizedR0_paired_vector_tr hp)
    (fun _ _ h=>h.mono (fun _ _ hz=>positiveIR_of_IZ hz))
    (fun _ _ h=>h.mono (fun _ _ hr=>positiveIH_of_IR hr))

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedHintsTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedHint_pair_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p r) fun _ _=>True := by
  let I := fun tab s => (∃σ,PositiveIH p S σ t r s) ∧ PairedRoots S s ∧ s.syms "VG_MLDSA_INV_PAIR"=tab
  have ht (tab : Addr) : RelCT isa (fun x y => LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPair
    unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairRow
    refine seqL (I:=I tab) (J:=fun _=>True) ?_ ?_ ?_
    · apply Paired.pairedHintAt_tr (S:=S) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
      rintro x y ⟨L,⟨⟨σ,hx⟩,rx,ex⟩,⟨⟨τ,hy⟩,ry,ey⟩⟩
      exact ⟨pairedHint_ready hp hr rx hx,pairedHint_ready hp hr ry hy,
        L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.sp,ex.trans ey.symm⟩
    · rintro x _ ⟨⟨σ,hx⟩,rx,_⟩
      exact WP.mono (pairedHintRow_ok hp hr rx hx) fun _ h=>⟨⟨_,h.1⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.1.lrel (fun _ _ h=>h.1.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1.1
  exact ⟨x.syms "VG_MLDSA_INV_PAIR",L,⟨⟨σ,hx.1⟩,hx.2,rfl⟩,⟨⟨τ,hy.1⟩,hy.2,h.2.symm⟩⟩

theorem optimizedHint_pair_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p r) (PairedRS p S E (PositiveIH p S · t (r+2))) :=
  liftPairedR (fun _ _ _ h roots=>optimizedHint_pair_ok hp hr roots h) (optimizedHint_pair_trace hp hr)

theorem optimizedHint_paired_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t 0))
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector p) (PairedRS p S E (PositiveIH p S · t p.k)) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector
  have he : 2*(p.k/2)=p.k := by rcases hp with rfl|rfl|rfl <;> decide
  simpa only [Nat.mul_zero,Nat.zero_add,he] using
    seqR_tr (Q:=fun j=>PairedRS p S E (PositiveIH p S · t (2*j))) (p.k/2) 0
      (fun j _ hj=>by simpa only [Nat.mul_add,Nat.mul_one] using
        optimizedHint_pair_tr (E:=E) hp (by omega : 2*j+1<p.k))

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedChecksTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

theorem positivePairedOnesOk_tr {p : Params} {S : Nat} (hc : ksChk p=true)
    (hS : S<2^64) {t : Nat} {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t p.k)) (.block (onesOk p))
      (PairedRS p S E (PositiveKO p S · t)) :=
  liftPairedR (fun _ _ _ h roots=>WP.pairedRoots (positiveOnesOk_ok hc h) roots (Nat.zero_le _) hS)
    (RelCT.mono (positiveOnesOk_tr hc) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedKBranch_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    (hS : S<2^64) {t : Nat} {E : State → State → Prop}
    (hE : ∀σ τ,E σ τ → (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p τ (p.ℓ*t))).isSome →
      (PassV p σ (p.ℓ*t) ↔ PassV p τ (p.ℓ*t))) :
    RelCT isa (PairedRS p S E (PositiveKO p S · t))
      (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))
      (PairedRS p S E fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) :=
  liftPairedR (fun _ _ _ h roots=>WP.pairedRoots (positiveKBranch_ok hp hc h) roots (Nat.zero_le _) hS)
    (RelCT.mono (positiveKBranch_tr hp hc hE) (fun _ _ h=>h.root) (fun _ _ _=>trivial))

theorem positivePairedChecks_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    (h16 : 16≤S) (hS : S<2^64) {t : Nat} {E : State → State → Prop}
    (hE : ∀σ τ,E σ τ → (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome →
      (sampleInBall p.τ maxBounds.ball (CTv p τ (p.ℓ*t))).isSome →
      (PassV p σ (p.ℓ*t) ↔ PassV p τ (p.ℓ*t))) :
    RelCT isa (PairedRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)
      (PairedRS p S E fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  exact RelCT.seq (positivePairedChecksPrefix_tr hp hc h16)
    (RelCT.seq (optimizedHint_paired_vector_tr hp)
      (RelCT.seq (positivePairedOnesOk_tr hc hS) (positivePairedKBranch_tr hp hc hS hE)))

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

def PairedChecksCT (p : Params) (S : Nat) (checks : Prog isa) : Prop :=
  ∀t,t<814 → RelCT isa
    (PairedRS p S (LeakEq p t) fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
    checks (PairedRS p S (LeakEq p t) fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s)

theorem pairedIter_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) (PositiveIL p S · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks) (PairedIX p S t) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine RelCT.seq (pairedCommit_tr hP hp hcommit) (RelCT.seq (pairedBall_step_tr hP hp ht hball) ?_)
  refine RelCT.seq (R:=fun x y=>
      (PairedRS p S (LeakEq p t) (fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) x y ∧ True) ∨
      (PairedRS p S (LeakEq p t) (PositiveEB p S · t) x y ∧ True))
    (RelCT.ite ?_ ?_ ?_)
    (relOr (RelCT.mono (pairedEndPF_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h))
      (RelCT.mono (pairedEndB_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h)))
  · rintro x y ⟨_,he⟩; rw [eval_w0,eval_w0,he]
  · refine RelCT.mono (hchecks t ht) ?_ (fun _ _ h=>.inl ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h1 := x0_one hx.1.r01 hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h1⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h1⟩,hy.2⟩⟩,rs⟩,rp⟩
  · have hf : RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=0)
        (.block (([.movz .x .x24 0 0] : List Instr)++setQ (VG.Impl.MlDsa.AArch64.Call.sc oCNT) 1))
        (PairedRS p S (LeakEq p t) (PositiveEB p S · t)) :=
      RelCT.mono (paired_trace_frame (Nat.zero_le _) hP.s64 (positiveBallFailure_tr hp (lChk_ok hp)))
        (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
    refine RelCT.mono hf ?_ (fun _ _ h=>.inr ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h0 := x0_zero hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h0⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h0⟩,hy.2⟩⟩,rs⟩,rp⟩

theorem pairedSignLoop_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p 0) (PositiveIK p S))
      (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks) (PositiveOX p S) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine RelCT.seq (liftPairedR (J:=fun σ s=>PositiveIL p S σ 0 s)
    (fun _ _ _ h roots=>WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    (lrel_tr (fun _ _ h=>h.root.1.lrel (fun _ _ h=>h.d.im.st)) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M:=isa)
    (fun n x y=>∃t,n=814-t ∧ PairedRS p S (LeakEq p t) (PositiveIL p S · t) x y)
    (fun n=>?_) 814) (fun _ _ h=>⟨0,rfl,h⟩) (fun _ _ h=>h)
  intro x y tx ty x' y' ⟨t,hn,hr⟩ ex ey
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,hx,_⟩ := hr.1.1; exact hx.1.t_lt
  obtain ⟨htr,hi⟩ := pairedIter_tr hP hp hchecks hcommit hball ht _ _ _ _ _ _ hr ex ey
  exact ⟨htr,by rw [eval_x9,eval_x9,hi.1.1],fun h=>hi.1.2.2 (x9_zero h),
    fun h=>⟨814-(t+1),by omega,t+1,rfl,hi.next (x9_ne h)⟩⟩

end VG.Proof.MlDsa.AArch64.Sign

end
