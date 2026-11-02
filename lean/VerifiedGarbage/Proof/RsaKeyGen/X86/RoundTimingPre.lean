module

public import VerifiedGarbage.Proof.Framework.X86.CallWith

public import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundEntry
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
import VerifiedGarbage.Proof.RsaKeyGen.X86.RoundPre
import VerifiedGarbage.Proof.Framework.Sig

/-! # A shared round exposes only the workspace pointer, capacity and width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.RoundCall

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c b, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 3 ≤ c ∧
    val32 s.mem g.W (g.array 5) g.words = b % c * 2 ^ (64 * g.w) % c

def Ready (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Input g capacity p s ∧ Arguments g capacity s

theorem Ready.sp {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g capacity p s) : s.gpr .esp = p := by
  obtain ⟨c, b, D, _, _, _⟩ := S.1
  exact D.ready.caller.sp

theorem Ready.entry_eq {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Ready g capacity p s) :
    (pushed args s).callEntry.withRegions [below p 8] [⟨g.W, g.L⟩] = entry g s := by
  unfold entry
  rw [callEntry_argAddr0, S.sp]
  rfl

theorem Ready.callPre {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (R : Ready g capacity p s) (length : g.L = 8 * capacity)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    CallPre (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96) args [below p 8] [⟨g.W, g.L⟩] s := by
  obtain ⟨c, b, S, odd, large, witness⟩ := R.1
  refine ⟨?_, ?_, ?_⟩
  · rw [R.entry_eq]
    exact entry_pre v length S R.2 odd large witness (by rw [R.sp]; exact fit) (by rw [R.sp]; exact far)
  · rw [← R.sp]
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

theorem Ready.width {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (R : Ready g capacity p s) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    Proof.Rsa.Mont.wOf (entry g s).mem g.W = g.w := by
  obtain ⟨c, b, S, _, _, _⟩ := R.1
  have F := entry_frame (by rw [R.sp]; omega) S.ready.scratch.nowrap
    (by rw [R.sp]; exact far.sub_right (below_sub (by decide : 12 ≤ 108) fit))
  exact (S.ready.modulus.keep v F (by simp) (by simp)).width

theorem Ready.publicInputs {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s t : State}
    (S : Ready g capacity p s) (T : Ready g capacity p t) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108)) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub (entry g s) (entry g t) := by
  have sa := fun {i} (hi : i < 2) => entry_arg S.2 (by rw [S.sp]; omega) hi
  have ta := fun {i} (hi : i < 2) => entry_arg T.2 (by rw [T.sp]; omega) hi
  obtain ⟨c, b, D, _, _, _⟩ := S.1
  have bound : g.W.toNat < 2 ^ 32 := by have := D.ready.scratch.nowrap; have := v.headerFit; omega
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  have sp : (entry g s).gpr .esp = (entry g t).gpr .esp := by
    change (pushed args s).callEntry.gpr .esp = (pushed args t).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', S.sp, T.sp]
  have width : [Proof.Rsa.Mont.wOf (entry g s).mem g.W] = [Proof.Rsa.Mont.wOf (entry g t).mem g.W] := by
    rw [S.width v fit far, T.width v fit far]
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 2), sa (by decide : 1 < 2), ta (by decide : 0 < 2), ta (by decide : 1 < 2), ↓reduceIte, ptr]
  exact ⟨sp, width, trivial, trivial⟩

end VG.Proof.RsaKeyGen.X86.RoundCall
