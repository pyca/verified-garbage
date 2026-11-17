module

import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.MrLoopAt
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStep
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRound
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessCount
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAdvance
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportRegions
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Impl.RsaKeyGen.X86.OrScan
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessOdd
import Init.Prelude
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits32
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.RegionOutside
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessZeros
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessMont
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86.RoundCall
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.TCB.X86.Isa

/-! ### `RsaKeyGen.X86.WitnessStep`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessStatus`, which this module and modules that import it used -/

section

/-! # Native mask selection implements the reviewed round-count policy -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStatus
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessStatus

def status (passed : Bool) (rounds uniform checks : Nat) : Nat :=
  if passed then if rounds < 16 ∨ uniform < checks then 4 else 1 else 3

theorem mask_status (passed moreRounds moreUniform : Bool) :
    (((((if moreRounds then BitVec.allOnes 32 else 0) ||| (if moreUniform then BitVec.allOnes 32 else 0))
      &&& 3) + 1) &&& (0 - BitVec.ofNat 32 passed.toNat)) |||
      (((0 - BitVec.ofNat 32 passed.toNat) ^^^ BitVec.allOnes 32) &&& 3) =
    BitVec.ofNat 32 (if passed then if moreRounds || moreUniform then 4 else 1 else 3) := by
  cases passed <;> cases moreRounds <;> cases moreUniform <;> decide

theorem code_ok {s : State} {passed : Bool} (flag : s.gpr .esi = BitVec.ofNat 32 passed.toNat) :
    WP isa (.block code) s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 (status passed (s.gpr .eax).toNat (s.gpr .ebx).toNat (s.gpr .edx).toNat) ∧
      t.mem = s.mem ∧ Keeps [.ecx, .edx, .ebp] s t := by
  unfold code
  refine wp_cmpi fun a A carryA _ => wp_sbb_self carryA fun b B =>
    wp_cmp fun c C carryC _ => wp_sbb_self carryC fun d D =>
    wp_or fun e E => wp_andi fun f F => wp_addS rfl fun g G _ =>
    wp_movS rfl fun h H _ => wp_sub fun i I _ => wp_and fun j J =>
    wp_logicS (Or.inr rfl) rfl fun k K => wp_andi fun l L => wp_or fun t T => WP.block_nil ?_
  have keep : Keeps [.ecx, .edx, .ebp] s t := by
    exact ((((((((((((A.keeps [.ecx, .edx, .ebp]).widen B.keeps).widen (C.keeps [.ecx, .edx, .ebp])).widen D.keeps).widen E.keeps).widen F.keeps).widen G.keeps).widen H.keeps).widen I.keeps).widen J.keeps).widen K.keeps).widen L.keeps).widen T.keeps
  refine ⟨?_, ?_, keep⟩
  · rw [T.gpr, L.other .ecx (by decide), K.other .ecx (by decide), J.gpr,
      I.other .ecx (by decide), H.other .ecx (by decide), G.gpr, F.gpr, E.gpr,
      D.other .ecx (by decide), C.gpr, B.gpr, D.gpr,
      B.other .ebx (by decide), B.other .edx (by decide), A.gpr,
      L.gpr, K.gpr, I.gpr, H.gpr, H.other .esi (by decide),
      G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), C.gpr, B.other .esi (by decide)]
    simp only [show AluOp.xor ≠ AluOp.and by decide, ite_false]
    rw [J.other .ebp (by decide), I.gpr, H.gpr, H.other .esi (by decide),
      G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), C.gpr, B.other .esi (by decide), A.gpr, flag]
    rw [mask_status]
    simp only [status, Bool.or_eq_true, decide_eq_true_eq]
    rfl
  · exact T.mem.trans (L.mem.trans (K.mem.trans (J.mem.trans (I.mem.trans (H.mem.trans
      (G.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))))))))))

end VG.Proof.RsaKeyGen.X86.WitnessStatus

end

end

/-! ### `RsaKeyGen.X86.RoundCall`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.RoundPre`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.RoundEntry`, which this module and modules that import it used -/

section

/-! # The shared round's two arguments and the workspace preserved by their push -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

def entry (g : Geometry) (s : State) : State :=
  (pushed args s).callEntry.withRegions
    [⟨argAddr (pushed args s).callEntry 0, 8⟩] [⟨g.W, g.L⟩]

structure Arguments (g : Geometry) (capacity : Nat) (s : State) : Prop where
  base : s.gpr .edi = BitVec.ofNat 32 g.W.toNat
  length : s.gpr .edx = BitVec.ofNat 32 capacity

theorem entry_arg {g : Geometry} {s : State} {capacity : Nat}
    (A : Arguments g capacity s) (fit : 12 ≤ (s.gpr .esp).toNat) {i : Nat} (index : i < 2) :
    arg (entry g s) i = BitVec.ofNat 32 (if i = 0 then g.W.toNat else capacity) := by
  rw [entry, arg_withRegions, callEntry_arg (rs := args) (s := s) fit (by decide : Reg.esp ∉ args) index]
  have casesI : i = 0 ∨ i = 1 := by omega_using [index]
  rcases casesI with rfl | rfl <;>
    simp only [args, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte, A.base, A.length] <;> rfl

theorem entry_frame {g : Geometry} {s : State}
    (fit : 12 ≤ (s.gpr .esp).toNat) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 12)) :
    WorkspaceFrame g [] s.mem (entry g s).mem := by
  have F := callEntry_frame (rs := args) fit (by decide : Reg.esp ∉ args)
  intro i index _
  apply F.bytes (R := ⟨g.W, g.L⟩)
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact far
  · change g.L ≤ 2 ^ 64
    omega_using [nowrap]
  · exact index

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end

/-! # Prepared candidate data establishes the shared round's cdecl precondition -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/PreparedSpec.lean`, which only this module imported.
section

/-! # Candidate preparation satisfies the reviewed callable round's representation -/

section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem prepared_of {g : Geometry} {m : Mem} {c : Nat}
    (M : Modulus g c m) (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 m g.W (g.array 5) g.words < c)
    (one : val32 m g.W (g.array 9) g.words = 2 ^ (64 * g.w) % c)
    (minusOne : val32 m g.W (g.array 10) g.words = c - 2 ^ (64 * g.w) % c)
    (exponent : val32 m g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c)
    (marker : word m g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)) :
    Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact m g.W := by
  unfold Proof.MillerRabin.Round.Prepared
  rw [M.width]
  dsimp only
  rw [VG.Proof.Mont.X86.Compact.numAt_val32]
  simp only [show val32 m g.W (Proof.Rsa.Mont.arrAt g.w 0) (2 * g.w) = c from M.candidate]
  change 3 ≤ c ∧ _
  refine ⟨large, odd, M.inverse, ?_, ?_, ?_, ?_, marker⟩
  all_goals rw [VG.Proof.Mont.X86.Compact.numAt_val32]
  · exact witness
  · exact one
  · exact minusOne
  · exact exponent

end VG.Proof.RsaKeyGen.X86.Prepare
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

theorem entry_pre {g : Geometry} (v : g.Valid) {s : State} {c capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (A : Arguments g capacity s) (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (fit : 108 ≤ (s.gpr .esp).toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 108)) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre (entry g s) := by
  have sa := fun {i} (hi : i < 2) => entry_arg A (by omega_using [fit]) hi
  have capBound : capacity < 2 ^ 32 := by have := S.ready.scratch.nowrap; omega
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := S.ready.scratch.nowrap; have := v.headerFit; omega_arith
  have F := entry_frame (by omega_using [fit] : 12 ≤ (s.gpr .esp).toNat) S.ready.scratch.nowrap
    (far.sub_right (below_sub (by decide : 12 ≤ 108) fit))
  have Mu := S.ready.modulus.keep v F (by simp) (by simp)
  have lu : Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact (entry g s).mem g.W capacity := by
    unfold Proof.MillerRabin.Round.Layout
    rw [Mu.width]
    refine ⟨Or.inr rfl, ?_, v.minWidth, v.maxWidth, ?_, ?_⟩
    · have M := Mu.layout v (by rw [length]; omega_using [])
      simpa only [length, Nat.mul_div_cancel_left capacity (by decide : 0 < 8)] using M
    · change Proof.Rsa.Mont.arrAt g.w 28 ≤ 8 * capacity
      rw [← length]
      exact v.arraysFit
    · change (entry g s).mem.readW (off g.W 224) 64 = _
      rw [F.read64 (by have := v.headerFit; omega_using [this]) (by simp)]
      exact S.stride
  have pu : Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact (entry g s).mem g.W := by
    refine Prepare.prepared_of Mu odd large ?_ ?_ ?_ ?_ ?_
    · rw [F.val32 (v.arrayFit (by decide)) (by simp), witness]
      exact Nat.mod_lt _ (by omega_using [odd])
    · rw [F.val32 (v.arrayFit (by decide)) (by simp)]; exact S.one
    · rw [F.val32 (v.arrayFit (by decide)) (by simp)]; exact S.minusOne
    · rw [F.val32 (v.arrayFit (by decide)) (by simp)]; exact S.exponent
    · change (entry g s).mem.readW (off g.W (g.array 27 + 8 * g.w)) 64 = _
      rw [F.read64 (by have := Prepared.paddedFit v (j := 27) (by decide); omega_using [this]) (by simp)]
      exact S.marker
  have sp : (entry g s).gpr .esp = s.gpr .esp - 12#32 := by
    change (pushed args s).callEntry.gpr .esp = _
    exact callEntry_esp' args s
  have ar : argAddr (entry g s) 0 = (s.gpr .esp - 8#32).setWidth 64 := by
    rw [entry, argAddr_withRegions]
    exact callEntry_argAddr0 args s
  have rd : (entry g s).rd = [⟨argAddr (entry g s) 0, 8⟩] := by
    rw [entry, State.withRegions_rd, argAddr_withRegions]
  have wr : (entry g s).wr = [⟨g.W, g.L⟩] := rfl
  have sa0 : arg (entry g s) 0 = BitVec.ofNat 32 g.W.toNat := sa (by decide)
  have sa1 : arg (entry g s) 1 = BitVec.ofNat 32 capacity := sa (by decide)
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  generalize eu : entry g s = u at *
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa0, sa1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capBound, Nat.mod_eq_of_lt ptrBound,
    ptr, rd, wr, sp, ar, ← length, Nat.mul_comm capacity 8]
  have sp12 : (s.gpr .esp - 12#32).toNat = (s.gpr .esp).toNat - 12 := sub_toNat (by omega_using [fit])
  have nat8 : ((s.gpr .esp - 8#32).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega_using [fit])]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have nat12 : ((s.gpr .esp - 12#32).setWidth 64).toNat = (s.gpr .esp).toNat - 12 := by
    rw [BitVec.toNat_setWidth, sp12]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have saved : (s.gpr .esp - 12#32).setWidth 64 - 96#64 = (s.gpr .esp - 108#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [sp12]; omega_using [fit] : 96 ≤ (s.gpr .esp - 12#32).toNat)]
    congr 1
    rw [BitVec.sub_sub]
    rfl
  have nat68 : ((s.gpr .esp - 108#32).setWidth 64).toNat = (s.gpr .esp).toNat - 108 := by
    rw [BitVec.toNat_setWidth, sub_toNat fit]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have argSub : (⟨(s.gpr .esp - 8#32).setWidth 64, 8⟩ : Region).Sub (below (s.gpr .esp) 108) := below_sub (by decide) fit
  have retSub : (⟨(s.gpr .esp - 12#32).setWidth 64, 4⟩ : Region).Sub (below (s.gpr .esp) 108) :=
    fun x hx => below_sub (by decide : 12 ≤ 108) fit x ((Region.sub_prefix (by decide : 4 ≤ 12)) x hx)
  have saveSub : (⟨(s.gpr .esp - 12#32).setWidth 64 - 96#64, 96⟩ : Region).Sub (below (s.gpr .esp) 108) := by
    rw [saved]
    exact Region.sub_prefix (by decide : 96 ≤ 108)
  have retArgs : (⟨(s.gpr .esp - 12#32).setWidth 64, 4⟩ : Region).Disjoint ⟨(s.gpr .esp - 8#32).setWidth 64, 8⟩ :=
    Offset.disjoint_of_le (by simp only [nat12, nat8]; omega_using [fit]) (by simp only [nat8]; have := (s.gpr .esp).isLt; omega_using [])
  have saveArgs : (⟨(s.gpr .esp - 12#32).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨(s.gpr .esp - 8#32).setWidth 64, 8⟩ := by
    rw [saved]
    exact Offset.disjoint_of_le (by simp only [nat68, nat8]; omega_using [fit]) (by simp only [nat8]; have := (s.gpr .esp).isLt; omega_using [])
  exact ⟨by rw [sp12]; omega_using [fit], by rw [sp12]; have := (s.gpr .esp).isLt; omega_using [],
    trivial, trivial, far.sub_right argSub, (far.sub_right retSub).symm, retArgs,
    (far.sub_right saveSub).symm, saveArgs, S.ready.scratch.nowrap, lu, pu⟩

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end

/-! ### `RsaKeyGen.X86.RoundResult`, which only this module used -/

section

/-! # The reviewed round returns its test result and preserves prepared operands -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem reviewed_frame {g : Geometry} {capacity : Nat} {m m' : Mem}
    (length : g.L = 8 * capacity)
    (K : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact g.W capacity g.w m m') :
    WorkspaceFrame g (roundWrites g) m m' := by
  intro i index apart
  apply K i (by omega_arith)
  · intro k mem
    change k ∈ [23, 26, 29, 30, 1] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact apart (184, 8) (by simp [roundWrites])
    · exact apart (208, 8) (by simp [roundWrites])
    · exact apart (232, 8) (by simp [roundWrites])
    · exact apart (240, 8) (by simp [roundWrites])
    · exact apart (8, 8) (by simp [roundWrites])
  · intro j mem
    change j ∈ [2, 3, 5, 6, 8] at mem
    have a := apart (g.array 2, 16 * (g.w + 2)) (by simp [roundWrites])
    have b := apart (g.array 5, 16 * (g.w + 2)) (by simp [roundWrites])
    have c := apart (g.array 8, 8 * (g.w + 2)) (by simp [roundWrites])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at a b c ⊢ <;> omega_arith
  · have h := apart (g.array 11, 128 * (g.w + 2)) (by simp [roundWrites])
    change i < g.array 11 ∨ g.array 27 ≤ i
    have endOffset : g.array 11 + 128 * (g.w + 2) = g.array 27 := by
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
      omega_arith
    change i < g.array 11 ∨ g.array 11 + 128 * (g.w + 2) ≤ i at h
    rw [endOffset] at h
    exact h


theorem roundPost {g : Geometry} {s t : State} {capacity c b : Nat}
    (ptrBound : g.W.toNat < 2 ^ 32) (capBound : capacity < 2 ^ 32)
    (a0 : arg s 0 = BitVec.ofNat 32 g.W.toNat) (a1 : arg s 1 = BitVec.ofNat 32 capacity)
    (M : Modulus g c s.mem)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (post : (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).post s t) :
    (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact g.W capacity g.w s.mem t.mem := by
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  sig_post [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes] at post
  simp only [a0, a1, ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capBound, M.width] at post
  obtain ⟨result, keeps⟩ := post
  refine ⟨?_, keeps⟩
  have candidate : Proof.Rsa.Mont.numAt s.mem g.W g.w 0 = c := by
    rw [VG.Proof.Mont.X86.Compact.numAt_val32]
    exact M.candidate
  rw [candidate] at result
  have value := result b (by rw [VG.Proof.Mont.X86.Compact.numAt_val32]; exact witness)
  rw [BitVec.setWidth_append_eq_right] at value
  exact value

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end

/-! ### `RsaKeyGen.X86.RoundFrame`, which only this module used -/

section

/-! # The shared round retains candidate preparation and the caller's capacity slot -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CallerFrame.lean`, which only this module imported.
section

/-! # Retain a candidate's capacity slot across the larger shared-round stack -/

section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Caller.keepSizedFrame {g : Geometry} {capacity : Nat} {p : BitVec 32} {s t : State}
    (C : Caller g capacity p s) {rs : List Reg} {n : Nat} (K : Keeps rs s t) (sp : .esp ∉ rs)
    (lengthFar : (lengthRegion p).Disjoint (below p n))
    (F : Frame ([⟨g.W, g.L⟩] ++ [below p n]) s.mem t.mem) : Caller g capacity p t := by
  have spT : t.gpr .esp = p := (K.1 .esp sp).trans C.sp
  refine ⟨spT, C.low, C.stackFar, C.lengthFar, C.lengthStackFar, ?_⟩
  have same : readSrc t (.mem (at_ .esp 24)) = readSrc s (.mem (at_ .esp 24)) := by
    show t.load32 (t.ea (at_ .esp 24)) = s.load32 (s.ea (at_ .esp 24))
    have eaS : s.ea (at_ .esp 24) = (lengthRegion p).base := by
      change (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = _
      rw [C.sp]
      rfl
    have eaT : t.ea (at_ .esp 24) = (lengthRegion p).base := by
      change (t.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = _
      rw [spT]
      rfl
    simp only [State.load32, eaT, eaS, K.2.1, K.2.2]
    congr 1
    apply congrArg some
    apply F.readW (r := lengthRegion p) (Region.contains_self _ _) ?_ (by decide)
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact C.lengthFar
    · exact lengthFar
  exact same.trans C.readLen

end VG.Proof.RsaKeyGen.X86
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Context.keepRound {g : Geometry} (v : g.Valid) {s t : State} (C : Context g s)
    (K : Keeps [.eax, .ecx, .edx] s t)
    (F : WorkspaceFrame g (roundWrites g) s.mem t.mem) : Context g t := by
  have read {d : Nat} (fit : d + 4 ≤ g.L)
      (apart : d + 4 ≤ 8 ∨ 16 ≤ d ∧ d + 4 ≤ 184 ∨ 224 ≤ d ∧ d + 4 ≤ 232) :
      w32 t.mem g.W d = w32 s.mem g.W d := by
    apply congrArg BitVec.toNat
    apply F.read32 fit
    intro r mem
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [apart]
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Mont.X86.Rt.PtrAt, K.1 .edi (by decide)]; exact C.base
  · rw [read (by have := v.headerFit; omega_using [this]) (by decide)]; exact C.width
  · rw [read (by have := v.headerFit; omega_using [this]) (by decide)]; exact C.stride
  · intro j hj
    rw [read (by have := v.headerFit; omega_using [hj, this]) (by omega_using [hj])]; exact C.pointers j hj

theorem data_keep {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) (K : Keeps [.eax, .ecx, .edx] s t)
    (F : WorkspaceFrame g (roundWrites g) s.mem t.mem)
    (G : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem)
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) : Prepare.Data g c capacity p t := by
  have arrays {j : Nat} (index : j = 0 ∨ j = 4 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
      ∀ r ∈ roundWrites g, g.array j + 4 * g.words ≤ r.1 ∨ r.1 + r.2 ≤ g.array j := by
    intro r mem
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl | rfl | rfl <;>
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using []
  have header {d : Nat} (lo : 16 ≤ d) (hi : d + 8 ≤ 184) :
      ∀ r ∈ roundWrites g, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro r mem
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_arith
  have M := S.ready.modulus.keep v F (fun r mem => by
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [])
    (arrays (Or.inl rfl))
  refine ⟨⟨Context.keepRound v S.ready.context K F, M, VG.Proof.RsaKeyGen.X86.Caller.keepSizedFrame S.ready.caller K (by decide) lengthFar G,
    S.ready.scratch.of_keeps K (by decide)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega_using []))).trans S.r2
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega_using []))).trans S.one
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega_using []))).trans S.minusOne
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega_using []))).trans S.exponent
  · change t.mem.readW (off g.W (g.array 27 + 8 * g.w)) 64 = _
    rw [F.read64 (by have := Prepared.paddedFit v (j := 27) (by decide); omega_using [this]) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [])]
    exact S.marker
  · change t.mem.readW (off g.W 224) 64 = _
    rw [F.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [])]
    exact S.stride

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end


/-! # Reuse a verified Miller–Rabin round without rebuilding candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

theorem call_ok {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (noSp : NoSp round) (stack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s) (A : Arguments g capacity s)
    (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (call name round) s fun t =>
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  let rd : List Region := [⟨argAddr (pushed args s).callEntry 0, 8⟩]
  have rdEq : rd = [below (s.gpr .esp) 8] := by
    unfold rd
    rw [callEntry_argAddr0]
    rfl
  have cp : CallPre (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96) args rd [⟨g.W, g.L⟩] s := by
    refine ⟨entry_pre v length S A odd large witness (by rw [S.ready.caller.sp]; exact fit)
      (by rw [S.ready.caller.sp]; exact far), ?_, ?_⟩
    · rw [rdEq]
      apply Covers.of_mem
      intro r mem
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact List.mem_append_right _ (List.mem_cons_self ..)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ S.ready.context.ws.wr)
    · apply Covers.of_mem
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact List.mem_cons_of_mem _ S.ready.context.ws.wr
  refine WP.callWithReturn verified.1 noSp (by decide : args ≠ []) (by decide : Reg.esp ∉ args)
    (by rw [S.ready.caller.sp]; change 8 + stackUse round + 4 ≤ _; omega_using [stack, fit]) cp ?_
  intro t rdT wrT saved frame post
  obtain ⟨u, mem, reg, post⟩ := post
  have K : Keeps [.eax, .ecx, .edx] s t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp_all [calleeSaved]
  have far12 := far.sub_right (below_sub (by decide : 12 ≤ 108) fit)
  have F := entry_frame (by rw [S.ready.caller.sp]; omega_using [fit]) S.ready.scratch.nowrap
    (by rw [S.ready.caller.sp]; exact far12)
  have Mu := S.ready.modulus.keep v F (by simp) (by simp)
  have ptrBound : g.W.toNat < 2 ^ 32 := by have := S.ready.scratch.nowrap; have := v.headerFit; omega_arith
  have capBound : capacity < 2 ^ 32 := by have := S.ready.scratch.nowrap; omega
  have sa := fun {i} (hi : i < 2) => entry_arg A (by rw [S.ready.caller.sp]; omega_using [fit]) hi
  obtain ⟨value, keeps⟩ := roundPost ptrBound capBound (sa (by decide)) (sa (by decide)) Mu
    ((F.val32 (v.arrayFit (by decide)) (by simp)).trans witness) post
  rw [reg] at value
  -- The pop loses the arguments' frame, below `esp`, apart from the workspace.
  have L : WorkspaceFrame g [] u.mem t.mem := by
    intro i index _
    apply mem.bytes (R := ⟨g.W, g.L⟩)
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [S.ready.caller.sp]
      exact far.sub_right (below_sub (by decide : 8 ≤ 108) fit)
    · have := S.ready.scratch.nowrap
      change g.L ≤ 2 ^ 64
      omega_using [this]
    · exact index
  have W : WorkspaceFrame g (roundWrites g) s.mem t.mem :=
    ((F.mono (by simp)).trans (reviewed_frame length keeps)).trans (L.mono (by simp))
  have G : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem := by
    rw [← S.ready.caller.sp]
    exact VG.X86.Frame.below_mono frame (by change 8 + stackUse round + 4 ≤ 108; omega_using [stack])
      (by rw [S.ready.caller.sp]; exact fit)
  exact ⟨data_keep v S K W G lengthFar, value, W, G, K⟩

theorem code_ok {round : Prog isa} {name : String}
    (verified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (noSp : NoSp round) (stack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (odd : c % 2 = 1) (large : 3 ≤ c)
    (witness : val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (code name round) s fun t =>
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold code
  refine WP.seq (wp_movS S.ready.caller.readLen fun a A _ => WP.block_nil ?_)
  have Da := WitnessMont.data_outside v S
    (show Outside g.W (g.array 6) (4 * g.words) s.mem a.mem from by rw [A.mem]; exact Outside.refl _ _ _ _)
    A.keeps (by decide) (by decide)
  have callArgs : Arguments g capacity a := by
    refine ⟨?_, A.gpr⟩
    apply BitVec.eq_of_toNat_eq
    rw [A.other .edi (by decide), S.ready.scratch.edi_toNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := S.ready.scratch.nowrap; have := v.headerFit; omega_arith)).symm
  refine WP.mono (call_ok (b := b) verified noSp stack v length Da callArgs odd large (by rw [A.mem]; exact witness)
    fit far lengthFar) fun t ⟨D, result, W, F, K⟩ => ?_
  rw [A.mem] at W F
  exact ⟨D, result, W, F, (A.keeps.mono (by decide)).trans K⟩

end VG.Proof.RsaKeyGen.X86.RoundCall

end

end

/-! ### `RsaKeyGen.X86.WitnessMont`, which this module and modules that import it used -/

section

/-! # A witness conversion preserves all of the candidate's cached data -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/WitnessMont.lean`, which only this module imported.
section

/-! # Cached R² converts any sampled witness to Montgomery form -/

section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.MillerRabin

theorem witness_r2 {c w x : Nat} (odd : c % 2 = 1) :
    Word32.mm c w x (2 ^ (64 * w) * 2 ^ (64 * w) % c) = x * 2 ^ (64 * w) % c := by
  have cancel : (2 ^ (64 * w) * 2 ^ (64 * w) % c) * Word32.rinv c w % c = 2 ^ (64 * w) % c := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Word32.R_rinv odd,
      ← Nat.mul_mod, Nat.mul_one]
  unfold Word32.mm
  rw [Nat.mul_assoc, Nat.mul_mod, cancel, ← Nat.mul_mod]

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessMont
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (odd : c % 2 = 1) (positive : 0 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont) s fun t =>
      Prepare.Data g c capacity p t ∧
      val32 t.mem g.W (g.array 5) g.words = val32 s.mem g.W (g.array 6) g.words * 2 ^ (64 * g.w) % c ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessMont.code
  have A := S.ready
  refine WP.seq (WP.mono (mulY_ok verified noSp stack v A.context length A.modulus
    (by unfold Proof.Rsa.Mont.Operand; decide) odd (by rw [S.r2]; exact Nat.mod_lt _ positive)
    A.caller.readLen (by rw [A.caller.sp]; exact A.caller.low)
    (by rw [A.caller.sp]; exact A.caller.stackFar)) fun b ⟨Vb, Ob, Kb, Cb, Mb, Fb⟩ => ?_)
  rw [A.caller.sp] at Fb
  have B : Ready g c capacity p b := ⟨Cb, Mb, A.caller.keepFrame Kb (by decide) Fb,
    A.scratch.of_keeps Kb (by decide)⟩
  rw [S.r2, witness_r2 odd] at Vb
  refine WP.mono (Prepared.copy_ready v B 5 6 (by decide) (by decide) (by decide))
    fun t ⟨T, Vt, Ot, Kt⟩ => ?_
  have Wb := Ob.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ montWrites g 6, r ∈ ranges g)
  have Wt : WorkspaceFrame g (ranges g) b.mem t.mem :=
    WorkspaceFrame.of_outs B.scratch.nowrap (Outs.of_outside Ot (by simp [ranges]))
  have W := Wb.trans Wt
  have F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) b.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ot (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨data_keep v S T W, Vt.trans Vb, W, Fb.trans F, ?_⟩
  exact (Kb.mono (by unfold clob; decide)).widen Kt

end VG.Proof.RsaKeyGen.X86.WitnessMont

end

end

/-! ### `RsaKeyGen.X86.WitnessLoad`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessFallbackWord`, which this module and modules that import it used -/

section

/-! # Masked native updates select the fallback bits and retain uniform witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem low_value (old : BitVec 32) (uniform : Bool) :
    ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 2#32) ||| old).toNat) =
      if uniform then old.toNat else old.toNat ||| 2 := by
  cases uniform
  · change (2#32 ||| old).toNat = old.toNat ||| 2
    rw [BitVec.toNat_or, Nat.or_comm]
    rfl
  · change (0#32 ||| old).toNat = old.toNat
    rw [BitVec.zero_or]

theorem high_value (old : BitVec 32) (uniform : Bool) :
    ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 0x80000000#32) ^^^ BitVec.allOnes 32) &&& old).toNat =
      if uniform then old.toNat else old.toNat % 2 ^ 31 := by
  cases uniform
  · change (0x7fffffff#32 &&& old).toNat = old.toNat % 2 ^ 31
    rw [BitVec.toNat_and, Nat.and_comm]
    change old.toNat &&& (2 ^ 31 - 1) = old.toNat % 2 ^ 31
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  · change (BitVec.allOnes 32 &&& old).toNat = old.toNat
    rw [BitVec.allOnes_and]

theorem low_ok {s : State} {base : Addr} {size src : Nat} (scratch : Scr s base size)
    (fit : src + 4 ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (low src)) s fun t =>
      w32 t.mem base src = (if uniform then w32 s.mem base src else w32 s.mem base src ||| 2) ∧
      Outside base src 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold low
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  have Kc : Keeps [.ecx] s c := (A.keeps.widen B.keeps).widen C.keeps
  have load := readSrc_sc (scratch.of_keeps Kc (by decide)) fit
  rw [C.mem, B.mem, A.mem] at load
  refine wp_orS load fun d D => ?_
  have Kd : Keeps [.ecx] s d := Kc.widen D.keeps
  have Sd := scratch.of_keeps Kd (by decide)
  refine wp_storeS (Sd.ea (by omega_using [fit])) (Sd.write fit) fun t T => WP.block_nil ?_
  have V : d.gpr .ecx = (((cmask uniform ^^^ BitVec.allOnes 32) &&& 2#32) ||| s.mem.readW (off base src) 32) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Kd.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, V]
    exact low_value _ _
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega_using [fit, this])

theorem high_ok {s : State} {base : Addr} {size offset : Nat} (scratch : Scr s base size)
    (fit : offset + 4 ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (high offset)) s fun t =>
      w32 t.mem base offset = (if uniform then w32 s.mem base offset else w32 s.mem base offset % 2 ^ 31) ∧
      Outside base offset 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold high
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B =>
    wp_logicS (.inl rfl) rfl fun c C => wp_logicS (.inr rfl) rfl fun d D => ?_
  have Kd : Keeps [.ecx] s d := ((A.keeps.widen B.keeps).widen C.keeps).widen D.keeps
  have load := readSrc_sc (scratch.of_keeps Kd (by decide)) fit
  rw [D.mem, C.mem, B.mem, A.mem] at load
  refine wp_logicS (.inl rfl) load fun e E => ?_
  have Ke : Keeps [.ecx] s e := Kd.widen E.keeps
  have Se := scratch.of_keeps Ke (by decide)
  refine wp_storeS (Se.ea (by omega_using [fit])) (Se.write fit) fun t T => WP.block_nil ?_
  have V : e.gpr .ecx = ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 0x80000000#32) ^^^
      BitVec.allOnes 32) &&& s.mem.readW (off base offset) 32) := by
    rw [E.gpr, D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Ke.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, V]
    exact high_value _ _
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega_using [fit, this])

end VG.Proof.RsaKeyGen.X86.WitnessFallback

end

end

/-! ### `RsaKeyGen.X86.WitnessLowerMath`, which this module and modules that import it used -/

section

/-! # A witness is below two exactly when its high words and cleared low word are zero -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.Proof.Mont

theorem clear_low_zero (x : BitVec 32) :
    (x ||| 1#32) ^^^ 1#32 = 0#32 ↔ x.toNat < 2 := by
  rw [← BitVec.toNat_inj]
  change ((x ||| (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 0 ↔ x.toNat < 2
  rw [VG.Proof.Rsa.KeyBits32.bv_clr_one]
  change 2 * (x.toNat / 2) = 0 ↔ x.toNat < 2
  omega_using []

theorem below_two (m : Mem) (base : Addr) (src n : Nat) (positive : 0 < n) :
    val32 m base src n < 2 ↔
      val32 m base (src + 4) (n - 1) = 0 ∧ (m.readW (off base src) 32).toNat < 2 := by
  rw [show n = n - 1 + 1 by omega_using [positive], val32, show n - 1 + 1 - 1 = n - 1 by omega_using []]
  change w32 m base src + 2 ^ 32 * val32 m base (src + 4) (n - 1) < 2 ↔
    val32 m base (src + 4) (n - 1) = 0 ∧ w32 m base src < 2
  omega_using []

end VG.Proof.RsaKeyGen.X86.WitnessLower

end

end

/-! ### `RsaKeyGen.WitnessSample`, which this module and modules that import it used -/

section

/-! # Witness sampling as an interval mask and a fixed fallback, for a candidate of `32 k` bits -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG

theorem witness_sampleAt {c x k : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (bound : x < 2 ^ (32 * k)) :
    Spec.RsaKeyGen.witness (c - 1) x =
      (if decide (2 ≤ x ∧ x < c - 1) then x else (x ||| 2) % 2 ^ (32 * k - 1), decide (2 ≤ x ∧ x < c - 1)) := by
  unfold Spec.RsaKeyGen.witness
  simp only [shape, Nat.mod_eq_of_lt bound]
  by_cases h : 2 ≤ x ∧ x < c - 1 <;> simp [h]

/-- The witness depends only on the draw's low `32 k` bits. -/
theorem witness_mod {c x k : Nat} (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) :
    Spec.RsaKeyGen.witness (c - 1) (x % 2 ^ (32 * k)) = Spec.RsaKeyGen.witness (c - 1) x := by
  unfold Spec.RsaKeyGen.witness
  simp only [shape, Nat.mod_mod]

end VG.Proof.RsaKeyGen

end

end

/-! ### `Mont.LowUpdate32`, which this module and modules that import it used -/

section

/-! # Native low-word updates and restoration preserve the higher integer -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem val32_low_or_one {m m' : Mem} {base : Addr} {src n : Nat} (positive : 0 < n)
    (fit : src + 4 * n ≤ 2 ^ 64) (O : Outside base src 4 m m')
    (low : w32 m' base src = w32 m base src ||| 1) :
    val32 m' base src n = val32 m base src n + (1 - val32 m base src n % 2) := by
  rw [show n = n - 1 + 1 by omega_using [positive], val32, val32, low,
    O.val32 (d := src + 4) (k := n - 1) (by omega_using []) (by omega_using [positive, fit]), VG.Proof.Rsa.KeyBits32.or_one]
  omega_using []

theorem val32_restore_low {m m' : Mem} {base : Addr} {src n : Nat} (positive : 0 < n)
    (fit : src + 4 * n ≤ 2 ^ 64) (O : Outside base src 4 m m')
    (low : w32 m' base src = w32 m base src) : val32 m' base src n = val32 m base src n := by
  rw [show n = n - 1 + 1 by omega_using [positive], val32, val32, low,
    O.val32 (d := src + 4) (k := n - 1) (by omega_using []) (by omega_using [positive, fit])]

end VG.Proof.Mont

end

end

/-! ### `RsaKeyGen.X86.WitnessSample`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.WitnessUniform`, which only this module used -/

section

/-! # The native uniform mask is exactly the reviewed witness interval [2,c-1) -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/OrScan.lean`, which only this module imported.
section

/-! # The native OR scan detects exactly a zero integer without writing memory -/

section
namespace VG.Proof.RsaKeyGen.X86.OrScan
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.OrScan

theorem code_ok {s : State} {base : Addr} {size n src : Nat}
    (scratch : Scr s base size) (positive : 0 < n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      (t.gpr .ebx = 0#32 ↔ val32 s.mem base src n = 0) ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edx] s t := by
  let Inv := fun j t => t.mem = s.mem ∧ Keeps [.ebx, .ebp, .edx] s t ∧
    (t.gpr .ebx = 0#32 ↔ val32 s.mem base src j = 0)
  have stable : LoopStable Inv := by
    rintro j u t ⟨M, K, Z⟩ ⟨Mt, Rd, Wr, R⟩
    refine ⟨Mt.trans M, ⟨?_, Rd.trans K.2.1, Wr.trans K.2.2⟩, ?_⟩
    · intro r mem
      exact (R r (by intro eq; subst r; simp at mem) (by intro eq; subst r; simp at mem)).trans (K.1 r mem)
    · rw [R .ebx (by decide) (by decide)]
      exact Z
  unfold code
  refine WP.seq (wp_movS rfl fun a A _ => WP.block_nil ?_)
  refine wordLoop_ok Inv positive (by have := scratch.size_lt; omega) stable
    ⟨A.mem, A.keeps.mono (by decide), by rw [A.gpr]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩ ?_ ?_
  · intro j index t ⟨M, K, Z⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine wp_orS (readSrc_at' St pointer (d := src) (by omega)) fun u U => WP.block_nil ?_
    refine ⟨⟨U.mem.trans M, K.widen U.keeps, ?_⟩, U.other .ebp (by decide), U.other .edi (by decide)⟩
    rw [U.gpr, BitVec.or_eq_zero_iff, Z, M]
    have wordZero : s.mem.readW (off base (src + 4 * j)) 32 = 0#32 ↔ w32 s.mem base (src + 4 * j) = 0 :=
      ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
    rw [wordZero, val32_succ]
    have power : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    constructor
    · rintro ⟨left, right⟩
      rw [left, right, Nat.mul_zero]
    · intro sum
      have product : 2 ^ (32 * j) * w32 s.mem base (src + 4 * j) = 0 := by omega
      exact ⟨by omega, (Nat.mul_eq_zero.mp product).resolve_left (Nat.ne_of_gt power)⟩
  · intro t ⟨M, K, Z⟩
    exact ⟨Z, M, K⟩

end VG.Proof.RsaKeyGen.X86.OrScan
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessLowerFinish.lean`, which only this module imported.
section

/-! # Finish the witness lower-bound scan as an all-zero or all-one mask -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem finish_ok {s : State} {base : Addr} {size src upper : Nat} (scratch : Scr s base size)
    (fit : src + 4 ≤ size) (zero : s.gpr .ebx = 0#32 ↔ upper = 0) :
    WP isa (.block (finish src)) s fun t =>
      t.gpr .ebx = cmask (decide (¬(upper = 0 ∧ w32 s.mem base src < 2))) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch fit) fun a A _ => wp_orS rfl fun b B =>
    wp_logicS (.inr rfl) rfl fun c C => wp_orS rfl fun d D => ?_
  have low : c.gpr .eax = (s.mem.readW (off base src) 32 ||| 1#32) ^^^ 1#32 := by
    rw [C.gpr, B.gpr, A.gpr]
    rfl
  have combined : d.gpr .ebx = s.gpr .ebx ||| ((s.mem.readW (off base src) 32 ||| 1#32) ^^^ 1#32) := by
    rw [D.gpr, low, C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide)]
  have combinedZero : (d.gpr .ebx).toNat = 0 ↔ upper = 0 ∧ w32 s.mem base src < 2 := by
    rw [show (d.gpr .ebx).toNat = 0 ↔ d.gpr .ebx = 0#32 from @BitVec.toNat_inj 32 (d.gpr .ebx) (0#32),
      combined, BitVec.or_eq_zero_iff, zero, clear_low_zero]
  refine wp_cmpi fun e E cf _ => wp_sbb_self cf fun f F => wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ((((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).trans (E.keeps _)).widen F.keeps).widen T.keeps⟩
  · rw [T.gpr, F.gpr]
    change cmask (decide ((d.gpr .ebx).toNat < 1)) ^^^ BitVec.allOnes 32 = _
    rw [SigMask.flip_mask]
    exact congrArg cmask (decide_eq_decide.mpr (not_congr combinedZero))
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.WitnessLower
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessLower.lean`, which only this module imported.
section

/-! # The complete native witness scan detects exactly the lower bound two -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem code_ok {s : State} {base : Addr} {size n src : Nat} (scratch : Scr s base size)
    (positive : 2 ≤ n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      t.gpr .ebx = cmask (decide (2 ≤ val32 s.mem base src n)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ebp, .edx] s t := by
  refine WP.seq (WP.mono (OrScan.code_ok scratch (by omega_arith) (by omega_arith)) fun a ⟨Z, M, K⟩ => ?_)
  refine WP.mono (finish_ok (scratch.of_keeps K (by decide)) (by omega_arith) Z) fun t ⟨V, Mt, Kt⟩ => ?_
  rw [M] at V
  have compare : (¬(val32 s.mem base (src + 4) (n - 1) = 0 ∧ w32 s.mem base src < 2)) ↔
      2 ≤ val32 s.mem base src n := by
    rw [← below_two _ _ _ _ (by omega_arith)]
    omega_arith
  rw [decide_eq_decide.mpr compare] at V
  exact ⟨V, Mt.trans M, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessLower
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessOdd.lean`, which only this module imported.
section

/-! # The native range comparison sees x with bit zero set and then restores x -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessOdd
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessOdd

theorem mark_ok {s : State} {base : Addr} {size src n : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : src + 4 * n ≤ size) :
    WP isa (.block (mark src)) s fun t =>
      val32 t.mem base src n = val32 s.mem base src n + (1 - val32 s.mem base src n % 2) ∧
      t.gpr .esi = s.mem.readW (off base src) 32 ∧ Outside base src 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  unfold mark
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => wp_movS rfl fun b B _ => wp_orS rfl fun c C => ?_
  have K : Keeps [.eax, .esi] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have Sc := scratch.of_keeps K (by decide)
  refine wp_storeS (Sc.ea (by omega)) (Sc.write (by omega)) fun t T => WP.block_nil ?_
  have O : Outside base src 4 s.mem t.mem := by
    rw [T.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have low : w32 t.mem base src = w32 s.mem base src ||| 1 := by
    rw [T.mem, w32_write_self, C.gpr, B.gpr, A.gpr, BitVec.toNat_or]
    rfl
  refine ⟨val32_low_or_one positive (by have := scratch.nowrap; omega) O low, ?_, O, K.widen (T.keeps [])⟩
  rw [(T.keeps []).1 .esi (by decide), C.other .esi (by decide), B.other .esi (by decide), A.gpr]

theorem restore_ok {s original : State} {base : Addr} {size src n : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : src + 4 * n ≤ size) (O : Outside base src 4 original.mem s.mem)
    (saved : s.gpr .esi = original.mem.readW (off base src) 32) :
    WP isa (.block (restore src)) s fun t =>
      val32 t.mem base src n = val32 original.mem base src n ∧
      Outside base src 4 original.mem t.mem ∧ Keeps [] s t := by
  unfold restore
  refine wp_storeS (scratch.ea (by omega)) (scratch.write (by omega)) fun t T => WP.block_nil ?_
  have Ot : Outside base src 4 s.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have low : w32 t.mem base src = w32 original.mem base src := by rw [T.mem, w32_write_self, saved]
  exact ⟨val32_restore_low positive (by have := scratch.nowrap; omega) (O.trans Ot) low, O.trans Ot, T.keeps []⟩

end VG.Proof.RsaKeyGen.X86.WitnessOdd
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessUniform
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86 VG.Impl.RsaKeyGen.X86.WitnessUniform

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w src modulus : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (srcFit : src + 8 * w ≤ size) (modFit : modulus + 8 * w ≤ size)
    (apart : src + 8 * w ≤ modulus ∨ modulus + 8 * w ≤ src)
    (odd : val32 s.mem base modulus (2 * w) % 2 = 1) :
    WP isa (code w src modulus) s fun t =>
      t.gpr .eax = cmask (decide (2 ≤ val32 s.mem base src (2 * w) ∧
        val32 s.mem base src (2 * w) < val32 s.mem base modulus (2 * w) - 1)) ∧
      val32 t.mem base src (2 * w) = val32 s.mem base src (2 * w) ∧
      Outside base src 4 s.mem t.mem ∧ Keeps clob s t := by
  refine WP.seq (WP.mono (WitnessLower.code_ok scratch (by omega_using [positive]) (by omega_using [srcFit])) fun a ⟨lower, Ma, Ka⟩ => ?_)
  refine WP.seq (WP.mono (WitnessOdd.mark_ok (n := 2 * w) (scratch.of_keeps Ka (by decide)) (by omega_using [positive]) (by omega_using [srcFit]))
    fun b ⟨valueB, saved, Ob, Kb⟩ => ?_)
  rw [Ma] at valueB saved Ob
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.lessThan_ok w (scratch.of_keeps Ksb (by unfold clob; decide))
    positive srcFit modFit) fun c ⟨compared, Kc, Mc⟩ => ?_)
  rw [wordsVal_eq_val32, wordsVal_eq_val32, valueB,
    Ob.val32 (by omega_using [positive, apart]) (by have := scratch.nowrap; omega_using [modFit, this])] at compared
  have Ksc : Keeps clob s c := Ksb.widen Kc
  have Oc : Outside base src 4 s.mem c.mem := Mc ▸ Ob
  have savedC : c.gpr .esi = s.mem.readW (off base src) 32 := (Kc.1 .esi (by decide)).trans saved
  refine WP.seq (WP.mono (WitnessOdd.restore_ok (n := 2 * w) (scratch.of_keeps Ksc (by unfold clob; decide))
    (by omega_using [positive]) (by omega_using [srcFit]) Oc savedC) fun d ⟨valueD, Od, Kd⟩ => ?_)
  refine wp_and fun t T => WP.block_nil ?_
  have lowerD : d.gpr .ebx = mask32 (2 ≤ val32 s.mem base src (2 * w)) := by
    rw [Kd.1 .ebx (by decide), Kc.1 .ebx (by decide), Kb.1 .ebx (by decide), lower]
    simp only [cmask, mask32, decide_eq_true_eq]
  have comparedD : d.gpr .eax = mask32 (val32 s.mem base src (2 * w) +
      (1 - val32 s.mem base src (2 * w) % 2) < val32 s.mem base modulus (2 * w)) :=
    (Kd.1 .eax (by decide)).trans compared
  refine ⟨?_, ?_, ?_, ((Ksc.widen Kd).widen T.keeps)⟩
  · rw [T.gpr, comparedD, lowerD, mask32_and]
    have compare : (val32 s.mem base src (2 * w) + (1 - val32 s.mem base src (2 * w) % 2) <
        val32 s.mem base modulus (2 * w) ∧ 2 ≤ val32 s.mem base src (2 * w)) ↔
        (2 ≤ val32 s.mem base src (2 * w) ∧ val32 s.mem base src (2 * w) < val32 s.mem base modulus (2 * w) - 1) := by omega_using [odd]
    simp only [mask32, cmask, decide_eq_true_eq, compare]
  · rw [T.mem]; exact valueD
  · rw [T.mem]; exact Od

end VG.Proof.RsaKeyGen.X86.WitnessUniform

end

end

/-! ### `RsaKeyGen.X86.WitnessFallback`, which only this module used -/

section

/-! # Native fallback produces exactly the reviewed forced witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem codeAt_ok {s : State} {base : Addr} {size k src : Nat} (scratch : Scr s base size)
    (positive : 2 ≤ k) (fit : src + 4 * k ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (codeAt k src)) s fun t =>
      val32 t.mem base src k =
        (if uniform then val32 s.mem base src k else (val32 s.mem base src k ||| 2) % 2 ^ (32 * k - 1)) ∧
      Outside base src (4 * k) s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold codeAt
  refine WP.block_append (WP.mono (low_ok (uniform := uniform) scratch (by omega_using [positive, fit]) mask) fun a ⟨low, Oa, Ka⟩ => ?_)
  refine WP.mono (high_ok (uniform := uniform) (scratch.of_keeps Ka (by decide)) (by omega_using [positive, fit])
    (by rw [Ka.1 .eax (by decide)]; exact mask)) fun t ⟨top, Ot, Kt⟩ => ?_
  have lowSame : w32 t.mem base src = w32 a.mem base src := Ot.w32 (by omega_using [positive]) (by have := scratch.nowrap; omega_using [fit, this])
  have topSame : w32 a.mem base (src + 4 * k - 4) = w32 s.mem base (src + 4 * k - 4) :=
    Oa.w32 (by omega_using [positive]) (by have := scratch.nowrap; omega_using [fit, this])
  refine ⟨?_, (Oa.mono (by omega_using []) (by omega_using [positive])).trans (Ot.mono (by omega_using [positive]) (by omega_using [positive])), Ka.trans Kt⟩
  cases uniform
  · simp at low top
    change val32 t.mem base src k = (val32 s.mem base src k ||| 2) % 2 ^ (32 * k - 1)
    apply VG.Proof.RsaKeyGen.val32_witness_fallback (by omega_using [positive])
    · rw [lowSame, low]
    · rw [show src + 4 * (k - 1) = src + 4 * k - 4 by omega_using [positive], top, topSame]
    · intro j first last
      exact (Ot.w32 (by omega_using [last]) (by have := scratch.nowrap; omega_using [fit, last, this])).trans
        (Oa.w32 (by omega_using [first]) (by have := scratch.nowrap; omega_using [fit, last, this]))
  · simp at low top
    change val32 t.mem base src k = val32 s.mem base src k
    apply val32_congr
    intro j hj
    by_cases first : j = 0
    · subst j
      simpa only [Nat.mul_zero, Nat.add_zero] using lowSame.trans low
    · by_cases last : j = k - 1
      · subst j
        rw [show src + 4 * (k - 1) = src + 4 * k - 4 by omega_using [positive]]
        exact top.trans topSame
      · exact (Ot.w32 (by omega_using [last]) (by have := scratch.nowrap; omega_using [fit, hj, this])).trans
          (Oa.w32 (by omega_using [first]) (by have := scratch.nowrap; omega_using [fit, hj, this]))

end VG.Proof.RsaKeyGen.X86.WitnessFallback

end

end


/-! # Native witness sampling computes the exact reviewed value and uniform flag -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessSample
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessSample

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem codeAt_ok {s : State} {base : Addr} {size w k src modulus c x : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (two : 2 ≤ k) (narrow : k ≤ 2 * w) (srcFit : src + 8 * w ≤ size) (modFit : modulus + 8 * w ≤ size)
    (apart : src + 8 * w ≤ modulus ∨ modulus + 8 * w ≤ src)
    (candidate : val32 s.mem base modulus (2 * w) = c) (witness : val32 s.mem base src (2 * w) = x)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) (bound : x < 2 ^ (32 * k)) :
    WP isa (codeAt k w src modulus) s fun t =>
      val32 t.mem base src (2 * w) = (Spec.RsaKeyGen.witness (c - 1) x).1 ∧
      t.gpr .eax = cmask (Spec.RsaKeyGen.witness (c - 1) x).2 ∧
      Outside base src (8 * w) s.mem t.mem ∧ Keeps clob s t := by
  have sample := VG.Proof.RsaKeyGen.witness_sampleAt shape bound
  -- The words above the `k` low ones are zero.
  have split (m : Mem) : val32 m base src (2 * w) = val32 m base src k + 2 ^ (32 * k) * val32 m base (src + 4 * k) (2 * w - k) := by
    rw [← VG.Proof.Mont.val32_append, Nat.add_sub_cancel' narrow]
  have parts {lo hi v : Nat} (h : v = lo + 2 ^ (32 * k) * hi) (hv : v < 2 ^ (32 * k)) : lo = v ∧ hi = 0 := by
    rcases Nat.eq_zero_or_pos hi with e | e
    · subst e; rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨h.symm, rfl⟩
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) e; omega_using [h, hv, this]
  have lowX : val32 s.mem base src k = x ∧ val32 s.mem base (src + 4 * k) (2 * w - k) = 0 :=
    parts (by rw [← witness]; exact split s.mem) bound
  unfold codeAt
  refine WP.seq (WP.mono (WitnessUniform.code_ok scratch positive srcFit modFit apart
    (by rw [candidate]; exact odd)) fun a ⟨uniform, Va, Oa, Ka⟩ => ?_)
  rw [candidate, witness] at uniform
  have lowA : val32 a.mem base src k = x ∧ val32 a.mem base (src + 4 * k) (2 * w - k) = 0 :=
    parts (by rw [← (Va.trans witness)]; exact split a.mem) bound
  refine WP.mono (WitnessFallback.codeAt_ok (uniform := decide (2 ≤ x ∧ x < c - 1))
    (scratch.of_keeps Ka (by unfold WitnessUniform.clob; decide)) two (by omega_using [narrow, srcFit]) uniform)
    fun t ⟨V, Ot, Kt⟩ => ?_
  have high : val32 t.mem base (src + 4 * k) (2 * w - k) = 0 := by
    rw [← lowA.2]
    apply val32_congr
    intro j hj
    exact Ot.w32 (by omega_using []) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
  refine ⟨?_, ?_, (Oa.mono (by omega_using []) (by omega_using [positive])).trans (Ot.mono (by omega_using []) (by omega_using [narrow])), ?_⟩
  · rw [split t.mem, high, Nat.mul_zero, Nat.add_zero, V, lowA.1, sample]
  · rw [Kt.1 .eax (by decide), uniform, sample]
  · exact (Ka.mono (by unfold clob WitnessUniform.clob; decide)).widen Kt

end VG.Proof.RsaKeyGen.X86.WitnessSample

end

end


/-! # Entropy import and interval sampling retain all reusable candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem codeAt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) {D k : Nat} (width : 4 * input.count = D) (two : 2 ≤ k)
    (narrow : k ≤ input.count) (wide : input.count ≤ g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt D k g.w) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) D))
      Prepare.Data g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = sampled.1 ∧
      t.gpr .eax = cmask sampled.2 ∧ Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  rw [Prepared.slot_eq, Prepared.slot_eq, ← width, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  have arrayFit : g.array 6 + 4 * g.words ≤ g.L := v.arrayFit (by decide)
  have hw : g.words = 2 * g.w := rfl
  have dstAddr : input.dst.setWidth 64 = off g.W (g.array 6) := by
    rw [← destination]
    have fit : g.array 6 < g.L := by
      have := v.minWidth
      unfold Geometry.words at arrayFit
      omega_using [arrayFit, this]
    exact S.ready.scratch.ea fit
  have region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
    unfold Import.Geometry.destRegion
    rw [dstAddr]
  have load := Import.load_ok C source destination
  change WP isa (VG.Impl.RsaKeyGen.X86.Import.load input.count (g.array 6)) s _ at load
  refine WP.seq (WP.mono load fun a ⟨value, F, K⟩ => ?_)
  have Va : val32 a.mem g.W (g.array 6) input.count =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * input.count)) := by
    rw [dstAddr] at value
    rw [← VG.Proof.Bignum.read_eq_val32]
    exact value
  rw [region] at F
  have Oa := frame_outside F (by have := S.ready.scratch.nowrap; omega_using [wide, arrayFit, this])
  have A := WitnessMont.data_outside v S (Oa.mono (by omega_using []) (by omega_using [wide])) K (by decide) (by decide)
  refine WP.seq (WP.mono (WitnessLoad.zeros_ok A.ready.scratch (g.array 6 + 4 * k) (2 * g.w - k)
    (by omega_using [narrow, wide, arrayFit, hw])) fun b ⟨Zb, Ob, Kb⟩ => ?_)
  have B := WitnessMont.data_outside v A
    (Ob.mono (by have := g.arrayBefore (i := 5) (j := 6) (by decide); omega_using [])
      (by omega_using [narrow, wide, hw])) Kb (by decide) (by decide)
  -- The witness: the draw's low `32 k` bits, zeros above.
  have lowB : val32 b.mem g.W (g.array 6) k =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) (4 * input.count)) % 2 ^ (32 * k) := by
    rw [← Va, show input.count = k + (input.count - k) by omega_using [narrow], VG.Proof.Mont.val32_append,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
    exact Ob.val32 (by omega_using []) (by have := S.ready.scratch.nowrap; omega_using [narrow, wide, arrayFit, this])
  have wordsB : val32 b.mem g.W (g.array 6) (2 * g.w) = val32 b.mem g.W (g.array 6) k := by
    rw [show 2 * g.w = k + (2 * g.w - k) by omega_using [narrow, wide, hw], VG.Proof.Mont.val32_append, Zb,
      Nat.mul_zero, Nat.add_zero]
  refine WP.mono (WitnessSample.codeAt_ok B.ready.scratch (by have := v.minWidth; omega_using [this]) two
    (by omega_using [narrow, wide, hw])
    (by omega_using [arrayFit, hw])
    (by have := v.arrayFit (j := 0) (by decide); unfold Geometry.words at this; omega_using [this])
    (Or.inr (by have := g.arrayBefore (i := 0) (j := 6) (by decide); unfold Geometry.words at this; omega_using [this]))
    B.ready.modulus.candidate (wordsB.trans lowB) odd shape (Nat.mod_lt _ (Nat.two_pow_pos _)))
    fun t ⟨Vt, mask, Ot, Kt⟩ => ?_
  rw [VG.Proof.RsaKeyGen.witness_mod shape] at Vt mask
  have Ot' : Outside g.W (g.array 6) (4 * g.words) b.mem t.mem := by
    rw [show 4 * g.words = 8 * g.w by unfold Geometry.words; omega_using []]
    exact Ot
  exact ⟨WitnessMont.data_outside v B Ot' Kt (by unfold WitnessSample.clob; decide)
    (by unfold WitnessSample.clob; decide), Vt, mask,
    ((Oa.mono (by omega_using []) (by omega_using [wide])).trans
      (Ob.mono (by omega_using []) (by omega_using [narrow, wide, hw]))).trans Ot',
    ((K.mono (by unfold clob; decide)).widen Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessLoad

end

end

/-! ### `RsaKeyGen.X86.WitnessInput`, which this module and modules that import it used -/

section

/-! # Each remaining entropy block is a disjoint, readable native import source -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessInput
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

/-- The `count` native words at offset `used` of the entropy, into the witness array. -/
def geometryAt (g : Geometry) (rand : BitVec 32) (used count : Nat) : Import.Geometry :=
  ⟨rand + BitVec.ofNat 32 used, BitVec.ofNat 32 (g.W.toNat + g.array 6), count⟩

theorem source_address {rand : BitVec 32} {used : Nat} (fit : rand.toNat + used < 2 ^ 32) :
    (rand + BitVec.ofNat 32 used).setWidth 64 = off (rand.setWidth 64) used := by
  change addr rand used = _
  exact addr_eq fit

theorem destination_pointer {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used count : Nat} :
    (geometryAt g rand used count).dst = s.gpr .edi + BitVec.ofNat 32 (g.array 6) := by
  have arrBound : g.array 6 < 2 ^ 32 := by
    have := S.nowrap
    have a := v.arrayFit (j := 6) (by decide)
    have := v.minWidth
    unfold Geometry.words at a
    omega_arith
  apply BitVec.eq_of_toNat_eq
  simp only [geometryAt, BitVec.toNat_ofNat, BitVec.toNat_add, S.edi_toNat, Nat.mod_eq_of_lt arrBound]

theorem destination_address {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used count : Nat} :
    (geometryAt g rand used count).dst.setWidth 64 = off g.W (g.array 6) := by
  rw [destination_pointer v S]
  have fit : g.array 6 < g.L := by
    have a := v.arrayFit (j := 6) (by decide)
    have := v.minWidth
    unfold Geometry.words at a
    omega_using [a, this]
  exact S.ea fit

theorem context_okAt {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L)
    {rand : BitVec 32} {used length count : Nat} (noWrap : rand.toNat + length ≤ 2 ^ 32)
    (positive : 0 < count) (wide : count ≤ g.words) (enough : used + 4 * count ≤ length)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) length)
    (separate : (⟨rand.setWidth 64, length⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    Import.Context (geometryAt g rand used count) s := by
  have sourceFit : rand.toNat + used < 2 ^ 32 := by omega_using [noWrap, positive, enough]
  have sourceAddr := source_address sourceFit
  have destAddr := destination_address v S (rand := rand) (used := used) (count := count)
  have destPtr := destination_pointer v S (rand := rand) (used := used) (count := count)
  have hw : g.words = 2 * g.w := rfl
  apply Import.context_of_regions
  · exact positive
  · change (rand + BitVec.ofNat 32 used).toNat + 4 * count ≤ 2 ^ 32
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := used) (by omega_using [sourceFit]), Nat.mod_eq_of_lt sourceFit]
    omega_using [noWrap, enough]
  · change (geometryAt g rand used count).dst.toNat + 4 * count ≤ 2 ^ 32
    rw [destPtr, BitVec.toNat_add, S.edi_toNat, BitVec.toNat_ofNat]
    have bound : g.W.toNat + g.array 6 < 2 ^ 32 := by
      have := S.nowrap; have := v.arrayFit (j := 6) (by decide); have := v.minWidth; omega_arith
    rw [Nat.mod_eq_of_lt (a := g.array 6) (by omega_using [bound]), Nat.mod_eq_of_lt bound]
    have := S.nowrap
    have := v.arrayFit (j := 6) (by decide)
    omega_arith
  · change InRegions (s.rd ++ s.wr) ((rand + BitVec.ofNat 32 used).setWidth 64) (4 * count)
    rw [sourceAddr]
    obtain ⟨r, member, access⟩ := readable
    exact ⟨r, member, Import.contains_offset access enough⟩
  · change InRegions s.wr ((geometryAt g rand used count).dst.setWidth 64) (4 * count)
    rw [destAddr]
    exact S.write (by have := v.arrayFit (j := 6) (by decide); omega_using [wide, this])
  · change (⟨(rand + BitVec.ofNat 32 used).setWidth 64, 4 * count⟩ : Region).Disjoint
      ⟨(geometryAt g rand used count).dst.setWidth 64, 4 * count⟩
    rw [sourceAddr, destAddr]
    exact (separate.sub_left (Offset.sub_base _ enough)).sub_right
      (Offset.sub_base _ (by have := v.arrayFit (j := 6) (by decide); omega_using [wide, this]))

end VG.Proof.RsaKeyGen.X86.WitnessInput

end

end

/-! ### `RsaKeyGen.X86.WitnessAdvance`, which this module and modules that import it used -/

section

/-! # Advancing entropy retains preparation and accounts for exactly one witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessAdvance
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessAdvance

theorem codeAt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity used step : Nat} {p rand : BitVec 32}
    (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand)
    (consumed : w32 s.mem g.W usedOffset = used) (fit : used + step < 2 ^ 32) :
    WP isa (.block (codeAt step)) s fun t =>
      Prepare.Data g c capacity p t ∧ t.gpr .esi = rand + BitVec.ofNat 32 used ∧
      w32 t.mem g.W usedOffset = used + step ∧
      Outside g.W usedOffset 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  have head := v.headerFit
  unfold codeAt
  refine wp_movS (readSrc_sc S.ready.scratch (by omega_using [head])) fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (d := usedOffset) (by unfold usedOffset; omega_using [head])) fun b B _ =>
    wp_addS rfl fun d D _ => wp_addS rfl fun e E _ => ?_
  have K : Keeps [.eax, .esi] s e := (((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen E.keeps
  have Se := S.ready.scratch.of_keeps K (by decide)
  refine wp_storeS (Se.ea (by unfold usedOffset; omega_using [head])) (Se.write (by unfold usedOffset; omega_using [head])) fun t T => WP.block_nil ?_
  have Ot : Outside g.W usedOffset 4 s.mem t.mem := by
    rw [T.mem, E.mem, D.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by unfold usedOffset; decide)
  have Kt := K.widen (T.keeps [])
  refine ⟨S.keepGap v (by unfold usedOffset; decide) (by unfold usedOffset; decide) Ot Kt (by decide) (by decide), ?_, ?_, Ot, Kt⟩
  · rw [T.gpr, E.other .esi (by decide), D.gpr, B.other .esi (by decide), A.gpr, source,
      B.gpr, A.mem]
    have wordEq : s.mem.readW (off g.W usedOffset) 32 = BitVec.ofNat 32 used := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← consumed, Nat.mod_eq_of_lt (by change w32 s.mem g.W usedOffset < 2 ^ 32; exact (s.mem.readW _ 32).isLt)]
    rw [wordEq]
  · rw [T.mem, w32_write_self, E.gpr, D.other .eax (by decide), B.gpr, A.mem,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W usedOffset + step % 2 ^ 32) % 2 ^ 32 = _
    rw [consumed, Nat.mod_eq_of_lt (a := step) (by omega_using [fit]), Nat.mod_eq_of_lt fit]

end VG.Proof.RsaKeyGen.X86.WitnessAdvance

end

end

/-! ### `RsaKeyGen.X86.WitnessCount`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessCountNext`, which this module and modules that import it used -/

section

/-! # Accumulate one witness and its exact uniform-sampling bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessCount

def nextClob : List Reg := [.eax, .ebx, .edx, .esi]
def nextRanges : List (Nat × Nat) := [(roundsOffset, 4), (uniformOffset, 4)]

theorem mask_bit (uniform : Bool) : cmask uniform &&& 1 = BitVec.ofNat 32 uniform.toNat := by
  cases uniform <;> decide

theorem next_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32} {uniform : Bool}
    (S : Prepare.Data g c capacity p s) (mask : s.mem.readW (off g.W 144) 32 = cmask uniform)
    (roundsFit : w32 s.mem g.W roundsOffset + 1 < 2 ^ 32)
    (uniformFit : w32 s.mem g.W uniformOffset + uniform.toNat < 2 ^ 32) :
    WP isa (.block next) s fun t =>
      Prepare.Data g c capacity p t ∧
      t.gpr .esi = s.gpr .eax ∧
      t.gpr .eax = BitVec.ofNat 32 (w32 s.mem g.W roundsOffset + 1) ∧
      t.gpr .ebx = BitVec.ofNat 32 (w32 s.mem g.W uniformOffset + uniform.toNat) ∧
      t.gpr .edx = s.mem.readW (off g.W checksOffset) 32 ∧
      w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 ∧
      w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat ∧
      Outs g.W nextRanges s.mem t.mem ∧ Keeps nextClob s t := by
  have head := v.headerFit
  unfold next
  refine wp_movS rfl fun a A _ => ?_
  obtain Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by unfold roundsOffset; omega_using [head])) fun b B _ =>
    wp_addS rfl fun d D _ => ?_
  obtain Kd : Keeps nextClob s d := ((A.keeps.mono (by unfold nextClob; decide)).widen B.keeps).widen D.keeps
  obtain Sd := S.ready.scratch.of_keeps Kd (by unfold nextClob; decide)
  obtain valueD : d.gpr .eax = BitVec.ofNat 32 (w32 s.mem g.W roundsOffset + 1) := by
    rw [D.gpr, B.gpr, A.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W roundsOffset + 1) % 2 ^ 32 = (w32 s.mem g.W roundsOffset + 1) % 2 ^ 32
    rfl
  refine wp_storeS (Sd.ea (by unfold roundsOffset; omega_using [head])) (Sd.write (by unfold roundsOffset; omega_using [head])) fun e E => ?_
  obtain Ke := Kd.widen (E.keeps [])
  obtain Se := S.ready.scratch.of_keeps Ke (by unfold nextClob; decide)
  obtain Oe : Outside g.W roundsOffset 4 s.mem e.mem := by
    rw [E.mem, D.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by unfold roundsOffset; decide)
  obtain sampleE : e.mem.readW (off g.W 144) 32 = cmask uniform := by
    exact (BitVec.eq_of_toNat_eq (Oe.w32 (d := 144)
      (by unfold roundsOffset; decide) (by decide))).trans mask
  refine wp_movS (readSrc_sc Se (d := 144) (by omega_using [head])) fun f F _ => wp_andi fun h H => ?_
  obtain Kh := (Ke.widen F.keeps).widen H.keeps
  obtain Sh := S.ready.scratch.of_keeps Kh (by unfold nextClob; decide)
  obtain uRead := readSrc_sc Sh (d := uniformOffset) (by unfold uniformOffset; omega_using [head])
  refine wp_addS uRead fun i I _ => ?_
  obtain Ki := Kh.widen I.keeps
  obtain Si := S.ready.scratch.of_keeps Ki (by unfold nextClob; decide)
  obtain valueI : i.gpr .ebx = BitVec.ofNat 32 (w32 s.mem g.W uniformOffset + uniform.toNat) := by
    obtain same : h.mem.readW (off g.W uniformOffset) 32 = s.mem.readW (off g.W uniformOffset) 32 := by
      rw [H.mem, F.mem]
      exact BitVec.eq_of_toNat_eq (Oe.w32 (by unfold uniformOffset roundsOffset; decide) (by unfold uniformOffset; decide))
    rw [I.gpr, H.gpr, F.gpr, sampleE, mask_bit, same]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := uniform.toNat) (by have := Bool.toNat_le uniform; omega_using [uniformFit])]
    change (uniform.toNat + w32 s.mem g.W uniformOffset) % 2 ^ 32 = (w32 s.mem g.W uniformOffset + uniform.toNat) % 2 ^ 32
    rw [Nat.add_comm]
  refine wp_storeS (Si.ea (by unfold uniformOffset; omega_using [head])) (Si.write (by unfold uniformOffset; omega_using [head])) fun j J => ?_
  obtain Kj := Ki.widen (J.keeps [])
  obtain Sj := S.ready.scratch.of_keeps Kj (by unfold nextClob; decide)
  refine wp_movS (readSrc_sc Sj (d := checksOffset) (by unfold checksOffset; omega_using [head])) fun t T _ => WP.block_nil ?_
  obtain K := Kj.widen T.keeps
  obtain Oj : Outside g.W uniformOffset 4 e.mem j.mem := by
    rw [J.mem, I.mem, H.mem, F.mem]
    exact writeW32_outside _ _ _ (by unfold uniformOffset; decide)
  obtain O : Outs g.W nextRanges s.mem t.mem := by
    rw [T.mem]
    exact (Outs.of_outside Oe (by simp [nextRanges])).trans (Outs.of_outside Oj (by simp [nextRanges]))
  obtain gap : Outside g.W 128 96 s.mem t.mem := by
    rw [T.mem]
    exact (Oe.mono (by unfold roundsOffset; decide) (by unfold roundsOffset; decide)).trans
      (Oj.mono (by unfold uniformOffset; decide) (by unfold uniformOffset; decide))
  obtain roundT : w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 := by
    rw [T.mem, Oj.w32 (by unfold uniformOffset roundsOffset; decide) (by unfold roundsOffset; decide),
      E.mem, w32_write_self, valueD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt roundsFit]
  obtain uniformT : w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat := by
    rw [T.mem, J.mem, w32_write_self, valueI, BitVec.toNat_ofNat, Nat.mod_eq_of_lt uniformFit]
  obtain checksT : t.gpr .edx = s.mem.readW (off g.W checksOffset) 32 := by
    rw [T.gpr]
    exact BitVec.eq_of_toNat_eq ((Oj.w32 (by unfold uniformOffset checksOffset; decide) (by unfold checksOffset; decide)).trans
      (Oe.w32 (by unfold roundsOffset checksOffset; decide) (by unfold checksOffset; decide)))
  refine ⟨S.keepHeader v (by decide) (by decide) gap K (by unfold nextClob; decide) (by unfold nextClob; decide),
    ?_, ?_, ?_, checksT, roundT, uniformT, O, K⟩
  · rw [T.other .esi (by decide), J.gpr, I.other .esi (by decide), H.other .esi (by decide),
      F.other .esi (by decide), E.gpr, D.other .esi (by decide), B.other .esi (by decide)]
    exact A.gpr
  · rw [T.other .eax (by decide), J.gpr, I.other .eax (by decide), H.other .eax (by decide), F.other .eax (by decide), E.gpr]
    exact valueD
  · rw [T.other .ebx (by decide), J.gpr]; exact valueI

end VG.Proof.RsaKeyGen.X86.WitnessCount

end

end

/-! # The complete masked counting policy retains candidate preparation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessCount

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
def ranges : List (Nat × Nat) := nextRanges ++ [(statusOffset, 4)]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32} {passed uniform : Bool}
    (S : Prepare.Data g c capacity p s) (flag : s.gpr .eax = BitVec.ofNat 32 passed.toNat)
    (mask : s.mem.readW (off g.W 144) 32 = cmask uniform)
    (roundsFit : w32 s.mem g.W roundsOffset + 1 < 2 ^ 32)
    (uniformFit : w32 s.mem g.W uniformOffset + uniform.toNat < 2 ^ 32) :
    WP isa code s fun t =>
      Prepare.Data g c capacity p t ∧
      w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 ∧
      w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat ∧
      w32 t.mem g.W statusOffset = WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
        (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) ∧
      Outs g.W ranges s.mem t.mem ∧ Keeps clob s t := by
  unfold code
  refine WP.seq (WP.mono (next_ok v S mask roundsFit uniformFit)
    fun a ⟨A, flagA, roundsA, uniformA, checksA, countA, uniA, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (WitnessStatus.code_ok (flagA.trans flag)) fun b ⟨statusB, memB, Kb⟩ => ?_)
  rw [roundsA, uniformA, checksA, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt roundsFit, Nat.mod_eq_of_lt uniformFit] at statusB
  have B : Prepare.Data g c capacity p b :=
    A.keepHeader v (d := 128) (bytes := 0) (by decide) (by decide)
      (by rw [memB]; exact Outside.refl _ _ _ _) Kb (by decide) (by decide)
  refine wp_storeS (B.ready.scratch.ea (by have := v.headerFit; unfold statusOffset; omega_using [this]))
    (B.ready.scratch.write (by have := v.headerFit; unfold statusOffset; omega_using [this])) fun t T => WP.block_nil ?_
  have Ot : Outside g.W statusOffset 4 b.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by unfold statusOffset; decide)
  have statusBound : WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
      (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) < 2 ^ 32 := by
    unfold WitnessStatus.status
    split <;> first | decide | (split <;> decide)
  have statusT : w32 t.mem g.W statusOffset = WitnessStatus.status passed (w32 s.mem g.W roundsOffset + 1)
      (w32 s.mem g.W uniformOffset + uniform.toNat) (w32 s.mem g.W checksOffset) := by
    rw [T.mem, w32_write_self, statusB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusBound]
  have countT : w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 := by
    rw [Ot.w32 (by unfold statusOffset roundsOffset; decide) (by unfold roundsOffset; decide), memB]
    exact countA
  have uniT : w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat := by
    rw [Ot.w32 (by unfold statusOffset uniformOffset; decide) (by unfold uniformOffset; decide), memB]
    exact uniA
  have Oab : Outs g.W ranges s.mem b.mem := by
    rw [memB]
    exact Oa.mono (fun r mem => List.mem_append_left _ mem)
  exact ⟨B.keepGap v (by unfold statusOffset; decide) (by unfold statusOffset; decide) Ot (T.keeps []) (by decide) (by decide),
    countT, uniT, statusT, Oab.trans (Outs.of_outside Ot (by simp [ranges])),
    ((Ka.mono (by unfold clob nextClob; decide)).widen Kb).widen (T.keeps [])⟩

end VG.Proof.RsaKeyGen.X86.WitnessCount

end

end

/-! ### `RsaKeyGen.X86.WitnessRoundFrame`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.WitnessRound`, which this module and modules that import it used -/

section

/-! # Each witness iteration computes the exact sampled Miller–Rabin test -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRound
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRound

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]
def ranges (g : Geometry) : List (Nat × Nat) := WitnessMont.ranges g ++ roundWrites g ++ [(uniformOffset, 4)]

theorem codeAt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s) {input : Import.Geometry}
    (C : Import.Context input s) {draw k : Nat} (width : 4 * input.count = draw) (two : 2 ≤ k)
    (narrow : k ≤ input.count) (wide : input.count ≤ g.words)
    (source : s.gpr .esi = input.src)
    (destination : s.gpr .edi + BitVec.ofNat 32 (g.array 6) = input.dst)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (codeAt draw k g.w montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) draw))
      Prepare.Data g c capacity p t ∧ (t.gpr .eax).toNat = (if Proof.MillerRabin.Round.round c sampled.1 then 1 else 0) ∧
      t.mem.readW (off g.W uniformOffset) 32 = cmask sampled.2 ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps clob s t := by
  unfold codeAt
  refine WP.seq (WP.mono (WitnessLoad.codeAt_ok v S C width two narrow wide source destination odd shape)
    fun a ⟨A, Va, uniform, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Prepare.storeGap_ok v A (d := uniformOffset) (by decide) (by decide))
    fun b ⟨B, uniformB, Ob, Kb⟩ => ?_)
  rw [uniform] at uniformB
  have Vb := (Ob.val32 (Or.inr (by have := v.arrayHeader 6; unfold uniformOffset; omega_using [this]))
    (by have := A.ready.scratch.nowrap; have := v.arrayFit (j := 6) (by decide); omega_arith)).trans Va
  refine WP.seq (WP.mono (WitnessMont.code_ok montVerified montNoSp montStack v length B odd (by omega_using [odd]))
    fun d ⟨D, Vd, Wd, Fd, Kd⟩ => ?_)
  rw [Vb] at Vd
  have uniformD : d.mem.readW (off g.W uniformOffset) 32 = b.mem.readW (off g.W uniformOffset) 32 :=
    Wd.read32 (by have := v.headerFit; unfold uniformOffset; omega_using [this]) (fun r mem => by
      simp only [WitnessMont.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | rfl <;>
        exact Or.inl (by simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))
  refine WP.mono (RoundCall.code_ok (b := (Spec.RsaKeyGen.witness (c - 1)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (input.src.setWidth 64) draw))).1)
    roundVerified roundNoSp roundStack v length D odd large
    (by rw [Nat.mod_mul_mod]; exact Vd) fit far lengthFar) fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have uniformT : t.mem.readW (off g.W uniformOffset) 32 = d.mem.readW (off g.W uniformOffset) 32 :=
    Wt.read32 (by have := v.headerFit; unfold uniformOffset; omega_using [this]) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [uniformOffset, Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [])
  have Wa : WorkspaceFrame g (ranges g) s.mem a.mem :=
    WorkspaceFrame.of_outs S.ready.scratch.nowrap (Outs.of_outside
      (Oa.mono (o' := g.array 6) (n' := 8 * (g.w + 2)) (Nat.le_refl _) (by unfold Geometry.words; omega_using []))
      (by simp [ranges, WitnessMont.ranges, montWrites]))
  have Wb : WorkspaceFrame g (ranges g) a.mem b.mem :=
    WorkspaceFrame.of_outs A.ready.scratch.nowrap (Outs.of_outside Ob (by simp [ranges]))
  have Wd' := Wd.mono (fun r mem => List.mem_append_left _ (List.mem_append_left _ mem) : ∀ r ∈ WitnessMont.ranges g, r ∈ ranges g)
  have Wt' := Wt.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ roundWrites g, r ∈ ranges g)
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fb : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) a.mem b.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ob (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold uniformOffset; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  have Fd' := VG.X86.Frame.below_mono Fd (by decide : 80 ≤ 108) fit
  exact ⟨T, result, (uniformT.trans uniformD).trans uniformB,
    ((Wa.trans Wb).trans Wd').trans Wt', ((Fa.trans Fb).trans Fd').trans Ft,
    (((Ka.mono (by unfold clob WitnessLoad.clob; decide)).widen Kb).widen Kd).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessRound

end

end

/-! # Witness tests retain entropy bookkeeping and the two outer round counters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRound
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def safeHeader (d : Nat) : Prop :=
  d + 4 ≤ 8 ∨ 16 ≤ d ∧ d + 4 ≤ 144 ∨ 148 ≤ d ∧ d + 4 ≤ 184 ∨
    192 ≤ d ∧ d + 4 ≤ 208 ∨ 216 ≤ d ∧ d + 4 ≤ 232 ∨ 248 ≤ d ∧ d + 4 ≤ 256

theorem ranges_apart32 {g : Geometry} {d : Nat} (safe : safeHeader d) :
    ∀ r ∈ ranges g, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  intro r mem
  simp only [ranges, WitnessMont.ranges, montWrites, roundWrites, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with (((rfl | rfl | rfl) | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | rfl <;>
    simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset] <;> unfold safeHeader at safe <;> omega_using [safe]

theorem header32 {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {d : Nat} (safe : safeHeader d) : w32 t g.W d = w32 s g.W d :=
  congrArg BitVec.toNat (F.read32 (by have := v.headerFit; unfold safeHeader at safe; omega_using [safe, this]) (ranges_apart32 safe))

end VG.Proof.RsaKeyGen.X86.WitnessRound

end

end

/-! # A complete loop step accounts for entropy and both witness counters exactly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStep
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessStep

def ranges (g : Geometry) : List (Nat × Nat) :=
  [(152, 4)] ++ WitnessRound.ranges g ++ WitnessCount.ranges

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem flag_value {x : BitVec 32} {b : Bool} (h : x.toNat = if b then 1 else 0) :
    x = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> simpa using h

theorem codeAt_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity used randLen draw k : Nat} {p rand : BitVec 32}
    (two : 2 ≤ k) (narrow : 4 * k ≤ draw) (wide : draw ≤ 8 * g.w) (four : draw % 4 = 0)
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand) (consumed : w32 s.mem g.W 152 = used)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + draw ≤ randLen)
    (readable : InRegions (s.rd ++ s.wr) (rand.setWidth 64) randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (odd : c % 2 = 1) (large : 3 ≤ c) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k)
    (roundsFit : w32 s.mem g.W 176 + 1 < 2 ^ 32) (uniformFit : w32 s.mem g.W 192 + 1 < 2 ^ 32)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    WP isa (codeAt draw k g.w montName mont roundName round) s fun t =>
      let sampled := Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 152 = used + draw ∧
      w32 t.mem g.W 176 = w32 s.mem g.W 176 + 1 ∧
      w32 t.mem g.W 192 = w32 s.mem g.W 192 + sampled.2.toNat ∧
      w32 t.mem g.W 168 = WitnessStatus.status (Proof.MillerRabin.Round.round c sampled.1)
        (w32 s.mem g.W 176 + 1) (w32 s.mem g.W 192 + sampled.2.toNat) (w32 s.mem g.W 200) ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem ∧ Keeps clob s t := by
  unfold codeAt
  refine WP.seq (WP.mono (WitnessAdvance.codeAt_ok (step := draw) v S source consumed (by omega_using [randLenFit, enough]))
    fun a ⟨A, sourceA, usedA, Oa, Ka⟩ => ?_)
  let input := WitnessInput.geometryAt g rand used (draw / 4)
  have readA : InRegions (a.rd ++ a.wr) (rand.setWidth 64) randLen := by
    rw [Ka.2.1, Ka.2.2]; exact readable
  have C := WitnessInput.context_okAt (used := used) (count := draw / 4) v A.ready.scratch randFit (by omega_using [two, narrow])
    (by unfold Geometry.words; omega_using [wide]) (by omega_using [enough]) readA separate
  have inputSource : input.src.setWidth 64 = off (rand.setWidth 64) used :=
    WitnessInput.source_address (by omega_using [two, narrow, randFit, enough])
  have bytesA : Spec.Rsa.bytesAt a.mem (input.src.setWidth 64) draw =
      Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw := by
    rw [inputSource]
    apply VG.Proof.Bignum.scratch_bytes
      (Oa.mono (o' := 0) (n' := g.L) (by decide) (by have := v.headerFit; unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; omega_using [this]))
      (by have := randLenFit; omega_using [randFit, enough])
    exact separate.sub_left (Offset.sub_base _ enough)
  refine WP.seq (WP.mono (WitnessRound.codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v length A
    C (by change 4 * (draw / 4) = draw; omega_using [four]) two (by change k ≤ draw / 4; omega_using [narrow])
    (by change draw / 4 ≤ g.words; unfold Geometry.words; omega_using [wide]) sourceA
    (WitnessInput.destination_pointer v A.ready.scratch).symm odd large shape fit far lengthFar)
    fun b ⟨B, resultB, uniformB, Wb, Fb, Kb⟩ => ?_)
  rw [bytesA] at resultB uniformB
  have roundB : w32 b.mem g.W 176 = w32 s.mem g.W 176 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have uniB : w32 b.mem g.W 192 = w32 s.mem g.W 192 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have checksB : w32 b.mem g.W 200 = w32 s.mem g.W 200 :=
    (WitnessRound.header32 v Wb (by unfold WitnessRound.safeHeader; decide)).trans
      (Oa.w32 (by unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; decide) (by decide))
  have flagB : b.gpr .eax = BitVec.ofNat 32 (Proof.MillerRabin.Round.round c
      (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))).1).toNat := by
    exact flag_value resultB
  refine WP.mono (WitnessCount.code_ok v B flagB uniformB (by change w32 b.mem g.W 176 + 1 < 2 ^ 32; rw [roundB]; exact roundsFit)
    (by change w32 b.mem g.W 192 + _ < 2 ^ 32; rw [uniB]; have := Bool.toNat_le (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (off (rand.setWidth 64) used) draw))).2; omega_using [uniformFit, this]))
    fun t ⟨T, countT, uniT, statusT, Ot, Kt⟩ => ?_
  dsimp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
    VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.checksOffset] at countT uniT statusT
  rw [roundB] at countT
  rw [uniB] at uniT
  rw [roundB, uniB, checksB] at statusT
  have usedB := (WitnessRound.header32 v Wb (d := 152) (by unfold WitnessRound.safeHeader; decide)).trans usedA
  have usedT : w32 t.mem g.W 152 = used + draw := by
    have same := (WorkspaceFrame.of_outs B.ready.scratch.nowrap Ot).read32
      (d := 152) (by have := v.headerFit; omega_using [this]) (by
        intro r mem
        simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with (rfl | rfl) | rfl <;> left <;> decide)
    rw [show w32 t.mem g.W 152 = w32 b.mem g.W 152 from congrArg BitVec.toNat same]
    exact usedB
  have Wa : WorkspaceFrame g (ranges g) s.mem a.mem := WorkspaceFrame.of_outs S.ready.scratch.nowrap
    (Outs.of_outside Oa (by simp [ranges, VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset]))
  have Wb' := Wb.mono (fun r mem => List.mem_append_left _ (List.mem_append_right _ mem) : ∀ r ∈ WitnessRound.ranges g, r ∈ ranges g)
  have Wt : WorkspaceFrame g (ranges g) b.mem t.mem := WorkspaceFrame.of_outs B.ready.scratch.nowrap
    (Ot.mono (fun r mem => List.mem_append_right _ mem))
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; unfold VG.Impl.RsaKeyGen.X86.WitnessAdvance.usedOffset; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) b.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl) | rfl <;> have := v.headerFit <;>
        simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
          VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨T, usedT, countT, uniT, statusT, (Wa.trans Wb').trans Wt, (Fa.trans Fb).trans Ft,
    ((Ka.mono (by unfold clob; decide)).widen Kb).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessStep

end

end

/-! ### `RsaKeyGen.X86.WitnessAvailable`, which this module and modules that import it used -/

section

/-! # The entropy availability comparison is exact and cannot underflow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessAvailable
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessAvailable

theorem codeAt_ok {s : State} {base : Addr} {size D remaining used : Nat}
    (S : Scr s base size) (head : 256 ≤ size) (width : D < 2 ^ 32)
    (length : w32 s.mem base 32 = remaining) (consumed : w32 s.mem base 152 = used)
    (bound : used ≤ remaining) :
    WP isa (.block (codeAt D)) s fun t =>
      t.cf = some (decide (remaining - used < D)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold codeAt
  refine wp_movS (readSrc_sc S (by omega_using [head])) fun a A _ => ?_
  have Sa := S.of_keeps A.keeps (by decide)
  refine wp_subS (readSrc_sc Sa (d := 152) (by omega_using [head])) fun b B _ => ?_
  have value : (b.gpr .eax).toNat = remaining - used := by
    rw [B.gpr, A.gpr, A.mem, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change w32 s.mem base 152 ≤ w32 s.mem base 32; rw [length, consumed]; exact bound)]
    change w32 s.mem base 32 - w32 s.mem base 152 = _
    rw [length, consumed]
  refine wp_cmpi fun t T carry _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans (T.keeps _)⟩
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt width] at carry
  exact carry

end VG.Proof.RsaKeyGen.X86.WitnessAvailable

end

end

/-! ### `RsaKeyGen.X86.MillerRabinExhausted`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MillerRabinAfterDraw`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.MillerRabinPreserve`, which this module and modules that import it used -/

section

/-! # A witness step retains the entropy buffer and the outer loop's fixed metadata -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem step_header32 {g : Geometry} (v : g.Valid) {s t : Mem}
    (F : WorkspaceFrame g (WitnessStep.ranges g) s t) {d : Nat} (index : d = 28 ∨ d = 32 ∨ d = 200) :
    w32 t g.W d = w32 s g.W d := by
  apply congrArg BitVec.toNat
  apply F.read32 (by have := v.headerFit; omega_using [index, this])
  intro r mem
  simp only [WitnessStep.ranges, List.mem_append, List.mem_singleton] at mem
  rcases mem with (rfl | mem) | mem
  · rcases index with rfl | rfl | rfl <;> omega_using []
  · exact WitnessRound.ranges_apart32 (by rcases index with rfl | rfl | rfl <;> unfold WitnessRound.safeHeader <;> decide) r mem
  · simp only [WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl <;> rcases mem with (rfl | rfl) | rfl <;>
      simp only [VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset,
        VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset] <;> omega_using []

theorem StateAt.next {P : Parameters} (v : P.Valid) {s t : State} {k n : Nat} (S : StateAt P k n s)
    (T : Prepare.Data P.g P.candidate P.capacity P.p t)
    (used : w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes)
    (rounds : w32 t.mem P.g.W 176 = k + 1)
    (uniform : w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2)
    (atLoop : MrLoopAt P.candidate P.checks P.twos.1 P.twos.2 P.bytes P.start P.entropy (k + 1) (n - 1))
    (W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem)
    (F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem)
    (K : Keeps WitnessStep.clob s t) : StateAt P (k + 1) (n - 1) t := by
  refine ⟨T, ?_, ?_, ?_, (step_header32 v.geometry W (Or.inr (Or.inl rfl))).trans S.randLength,
    ?_, rounds, uniform, (step_header32 v.geometry W (Or.inr (Or.inr rfl))).trans S.checks, atLoop⟩
  · rw [K.2.1, K.2.2]; exact S.readable
  · exact (frame_bytesAt F (by
      intro r mem
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar) (by have := v.randLenFit; omega_using [this])).trans S.entropy
  · exact (BitVec.eq_of_toNat_eq (step_header32 v.geometry W (Or.inl rfl))).trans S.randPtr
  · rw [used, Nat.mul_succ]; omega_using []

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! ### `RsaKeyGen.X86.MillerRabinControl`, which this module and modules that import it used -/

section

/-! # Entropy exhaustion and the continuation flag of the blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem word_equal4 (x : BitVec 32) : (x - 4#32 == 0#32) = decide (x.toNat = 4) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj, BitVec.toNat_sub]
  change (2 ^ 32 - 4 + x.toNat) % 2 ^ 32 = 0 ↔ x.toNat = 4
  have := x.isLt
  omega_using []

theorem again_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L) :
    WP isa (.block again) s fun t =>
      t.zf = some (decide (w32 s.mem g.W 168 = 4)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold again
  refine wp_movS (readSrc_sc S (by have := v.headerFit; omega_using [this])) fun a A _ =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans (T.keeps _)⟩
  rw [Z, A.gpr]
  change some (s.mem.readW (off g.W 168) 32 - 4#32 == 0#32) = _
  rw [word_equal4]

theorem exhausted_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) :
    WP isa (.block exhausted) s fun t =>
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 168 = 0 ∧
      Outside g.W 168 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  have head := v.headerFit
  unfold exhausted
  refine wp_movS rfl fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega_using [head])) (Sa.write (by omega_using [head])) fun t T => WP.block_nil ?_
  have O : Outside g.W 168 4 s.mem t.mem := by
    rw [T.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)
  have K := A.keeps.widen (T.keeps [])
  exact ⟨S.keepGap v (by decide) (by decide) O K (by decide) (by decide),
    by rw [T.mem, w32_write_self, A.gpr]; rfl, O, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! ### `RsaKeyGen.X86.MillerRabinOutcome`, which this module and modules that import it used -/

section

/-! # Match native loop status with the reviewed primality result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

def Result (P : Parameters) (s : State) : Prop :=
  match P.test with
  | none => w32 s.mem P.g.W 168 = 0
  | some (prime, rest) => w32 s.mem P.g.W 168 = (if prime then 1 else 3) ∧
      w32 s.mem P.g.W 152 = P.entropy.length - rest.length

/-- The result, whatever the bytes outside the workspace are. -/
theorem Result.workspace {P : Parameters} {s t : State} (h : Result P s)
    (W : VG.Proof.MillerRabin.X86.WorkspaceFrame P.g [] s.mem t.mem) (fit : 172 ≤ P.g.L) : Result P t := by
  have e168 : w32 t.mem P.g.W 168 = w32 s.mem P.g.W 168 := by
    rw [w32, w32, W.read32 (by omega_using [fit]) (by intro r mem; nomatch mem)]
  have e152 : w32 t.mem P.g.W 152 = w32 s.mem P.g.W 152 := by
    rw [w32, w32, W.read32 (by omega_using [fit]) (by intro r mem; nomatch mem)]
  unfold Result at h ⊢
  rw [e168, e152]
  exact h

theorem count_policy (P : Parameters) (k : Nat) :
    WitnessStatus.status
      (Proof.MillerRabin.Round.round P.candidate (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1)
      (k + 1) ((mrSB P.candidate P.bytes P.start P.entropy k).2 +
        (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).2.toNat) P.checks =
      if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
          (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
        if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
      else 3 := by
  have counts : (k + 1 < 16 ∨ (mrSB P.candidate P.bytes P.start P.entropy k).2 +
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).2.toNat < P.checks) ↔
      goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) := by
    unfold goS
    rw [mrSB_first, mrSB_uniform_next]
    unfold Spec.RsaKeyGen.blindedChecks
    omega_using []
  unfold WitnessStatus.status
  simp only [counts]
  rfl

theorem StateAt.noEntropy {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (short : ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    n = 0 ∧ P.test = none :=
  mrLoopAt_short S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact short)

theorem StateAt.failed {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen)
    (failed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 = false) :
    n = 0 ∧ P.test =
      some (false, P.entropy.drop (P.start + P.bytes * k + P.bytes)) :=
  mrLoopAt_fail S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact enough) failed

theorem StateAt.accepted {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen)
    (passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 = true)
    (done : ¬ goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))) :
    n = 0 ∧ P.test =
      some (true, P.entropy.drop (P.start + P.bytes * k + P.bytes)) :=
  mrLoopAt_done S.atLoop v.witnessBytes (by have := v.narrow; have := v.two; omega_arith)
    (by rw [v.entropyLength]; exact enough) passed done

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # A passing witness continues or accepts; a failing witness rejects -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MillerRabinDraw.lean`, which only this module imported.
section

/-! # A native witness draw advances the reviewed loop's exact counters and status -/

section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem draw_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧
      w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes ∧ w32 t.mem P.g.W 176 = k + 1 ∧
      w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2 ∧
      w32 t.mem P.g.W 168 =
        (if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
            (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
          if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
        else 3) ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have counts := S.countFit v
  refine WP.mono (WitnessStep.codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v.geometry
    v.two v.narrow v.wide v.four
    v.length S.prepared S.randPtr S.used v.randFit v.randLenFit enough S.readable v.randSeparate v.odd (by have := v.large; omega)
    v.shape counts.1 counts.2 v.low v.stackFar v.lengthFar) fun t ⟨T, used, rounds, uniform, status, W, F, K⟩ => ?_
  rw [S.rounds] at rounds
  rw [S.sample enough, S.uniform, ← mrSB_uniform_next] at uniform
  rw [S.sample enough, S.rounds, S.uniform, S.checks, count_policy] at status
  exact ⟨T, used, rounds, uniform, status, W, F, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Outcome (P : Parameters) (k n : Nat) (t : State) : Prop :=
  (isa.eval .e t = some false ∧ n = 0 ∧ Result P t) ∨
    (isa.eval .e t = some true ∧ 0 < n ∧ StateAt P (k + 1) (n - 1) t)

theorem draw_again_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (draw_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v S enough)
    fun a ⟨A, usedA, roundsA, uniformA, statusA, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem := by rw [mem]; exact Wa
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem := by rw [mem]; exact Fa
  refine ⟨T, ?_, W, F, Ka.widen Kt⟩
  have ev : isa.eval .e t = some (decide (w32 a.mem P.g.W 168 = 4)) := Z
  cases passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 with
  | false =>
    have failed := S.failed v enough passed
    simp only [passed] at statusA
    refine Or.inl ⟨?_, failed.1, ?_⟩
    · rw [ev, statusA]; rfl
    · unfold Result
      rw [failed.2, mem]
      refine ⟨statusA, ?_⟩
      rw [usedA, List.length_drop]
      have bound := enough
      rw [← v.entropyLength] at bound
      omega_using [bound]
  | true =>
    by_cases more : goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))
    · have next := mrLoopAt_next S.atLoop v.witnessBytes
        (by have := v.narrow; have := v.two; omega_arith)
        (by rw [v.entropyLength]; exact enough) passed more
      simp only [passed, ↓reduceIte, more] at statusA
      have nextState := StateAt.next v S A usedA roundsA uniformA next.2 Wa Fa Ka
      refine Or.inr ⟨?_, next.1, nextState.keepMem v mem Kt (by decide) (by decide)⟩
      rw [ev, statusA]; rfl
    · have done := S.accepted v enough passed more
      simp only [passed, ↓reduceIte, more] at statusA
      refine Or.inl ⟨?_, done.1, ?_⟩
      · rw [ev, statusA]; rfl
      · unfold Result
        rw [done.2, mem]
        refine ⟨statusA, ?_⟩
        rw [usedA, List.length_drop]
        have bound := enough
        rw [← v.entropyLength] at bound
        omega_using [bound]

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # Too little entropy terminates the primality test with its specified failure -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem exhausted_again_ok {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (short : ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (.block exhausted) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have failed := S.noEntropy v short
  refine WP.seq (WP.mono (exhausted_ok v.geometry S.prepared) fun a ⟨A, statusA, Oa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have K : Keeps WitnessStep.clob s t := (Ka.mono (by unfold WitnessStep.clob; decide)).widen Kt
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have Ot : Outside P.g.W 168 4 s.mem t.mem := by rw [mem]; exact Oa
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem :=
    WorkspaceFrame.of_outs S.prepared.ready.scratch.nowrap (Outs.of_outside Ot
      (by simp [WitnessStep.ranges, WitnessCount.ranges, VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset]))
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ot (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.geometry.headerFit; omega_using [this])).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨T, Or.inl ⟨?_, failed.1, ?_⟩, W, F, K⟩
  · change t.zf = some false
    rw [Z, statusA]; rfl
  · unfold Result
    rw [failed.2, mem]
    exact statusA

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop

end

end

/-! # A complete blinded-loop step either stops or decreases its specified iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem step_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (stepAt P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used
    rw [v.entropyLength] at this
    exact this
  unfold stepAt
  refine WP.seq (WP.mono (WitnessAvailable.codeAt_ok S.prepared.ready.scratch v.geometry.headerFit
    (by have := v.geometry.maxWidth; have := v.wide; omega_arith) S.randLength S.used usedBound) fun a ⟨CF, mem, Ka⟩ => ?_)
  have A := S.keepMem v mem Ka (by decide) (by decide)
  have condition : isa.eval .b a = some (decide (¬ P.start + P.bytes * k + P.bytes ≤ P.randLen)) := by
    change a.cf = _
    rw [CF]
    congr 1
    apply decide_eq_decide.mpr
    change (P.randLen - (P.start + P.bytes * k) < P.bytes) ↔ ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen
    omega_using [usedBound]
  refine WP.seq ?_
  by_cases enough : P.start + P.bytes * k + P.bytes ≤ P.randLen
  · refine WP.ite false (by rw [condition]; simp only [enough, not_true_eq_false, decide_false])
      (fun impossible => nomatch impossible) (fun _ => ?_)
    apply WP.seq_iff.mp
    refine WP.mono (draw_again_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v A enough)
      fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite true (by rw [condition]; simp only [enough, not_false_eq_true, decide_true])
      (fun _ => ?_) (fun impossible => nomatch impossible)
    apply WP.seq_iff.mp
    refine WP.mono (exhausted_again_ok v A enough) fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
