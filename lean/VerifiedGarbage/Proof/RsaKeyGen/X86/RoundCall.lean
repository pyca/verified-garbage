module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.Framework.X86.CallReturn
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.X86.RoundCall
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

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
  rw [mem] at keeps
  rw [reg] at value
  have W : WorkspaceFrame g (roundWrites g) s.mem t.mem :=
    (F.mono (by simp)).trans (reviewed_frame length keeps)
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
