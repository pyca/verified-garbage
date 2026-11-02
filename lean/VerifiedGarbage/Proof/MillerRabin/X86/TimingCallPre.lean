module

public import VerifiedGarbage.Proof.MillerRabin.X86.CallEntry
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.MillerRabin.X86.CallPre
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus

/-! # Prepared Montgomery calls have public arguments and public limb count -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure MulReady (g : Geometry) (capacity b : Nat) (p : BitVec 32) (s : State) : Prop where
  context : Context g s
  modulus : ∃ c, Modulus g c s.mem ∧ val32 s.mem g.W (g.array b) g.words < c
  args : MulArguments g capacity b s
  low : 80 ≤ (s.gpr .esp).toNat
  far : (⟨g.W, g.L⟩ : Region).Disjoint (below (s.gpr .esp) 80)
  sp : s.gpr .esp = p

theorem MulReady.callPre {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    {s : State} (R : MulReady g capacity b p s) (length : g.L = 8 * capacity)
    (right : Proof.Rsa.Mont.Operand b) :
    CallPre (Proof.Rsa.Mont.mulContract abi 56) mulArgs [below p 20] [⟨g.W, g.L⟩] s := by
  obtain ⟨c, M, lt⟩ := R.modulus
  have rd : [below p 20] = [⟨argAddr (pushed mulArgs s).callEntry 0, 20⟩] := by
    rw [callEntry_argAddr0, R.sp]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [rd]
    exact mulEntry_pre v R.context length M R.args right lt R.low R.far
  · rw [← R.sp]
    apply Covers.of_mem
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ R.context.ws.wr)
  · apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact List.mem_cons_of_mem _ R.context.ws.wr

theorem MulReady.width {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    {s : State} (S : MulReady g capacity b p s) : Proof.Rsa.Mont.wOf (mulEntry g s).mem g.W = g.w := by
  obtain ⟨c, M, _⟩ := S.modulus
  have far := S.far.sub_right (below_sub (by decide : 24 ≤ 80) S.low)
  have frame := mulEntry_frame (by have := S.low; omega) S.context.ws.nowrap far
  exact (M.keep v frame (by simp) (by simp)).width


theorem MulReady.publicInputs {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    {s t : State} (S : MulReady g capacity b p s) (T : MulReady g capacity b p t) :
    (Proof.Rsa.Mont.mulContract abi 56).pub (mulEntry g s) (mulEntry g t) := by
  have sa := fun {i} (hi : i < 5) => mulEntry_arg S.args (by have := S.low; omega) hi
  have ta := fun {i} (hi : i < 5) => mulEntry_arg T.args (by have := T.low; omega) hi
  have bound : g.W.toNat < 2 ^ 32 := by
    have := S.context.ws.nowrap
    have := v.headerFit
    omega
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  have sp : (mulEntry g s).gpr .esp = (mulEntry g t).gpr .esp := by
    change (pushed mulArgs s).callEntry.gpr .esp = (pushed mulArgs t).callEntry.gpr .esp
    rw [callEntry_esp', callEntry_esp', S.sp, T.sp]
  have width : [Proof.Rsa.Mont.wOf (mulEntry g s).mem g.W] = [Proof.Rsa.Mont.wOf (mulEntry g t).mem g.W] := by
    rw [S.width v, T.width v]
  sig_pub [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes]
  simp only [sa (by decide : 0 < 5), sa (by decide : 1 < 5), sa (by decide : 2 < 5),
    sa (by decide : 3 < 5), sa (by decide : 4 < 5), ta (by decide : 0 < 5),
    ta (by decide : 1 < 5), ta (by decide : 2 < 5), ta (by decide : 3 < 5), ta (by decide : 4 < 5), ↓reduceIte, ptr]
  exact ⟨sp, width, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.MillerRabin.X86
