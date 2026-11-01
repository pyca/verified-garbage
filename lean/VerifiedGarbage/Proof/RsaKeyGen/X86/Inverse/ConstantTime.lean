module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! # `vg_rsa_keygen_inverse` reads only its arguments as addresses and counts -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- Inside the frame: the stack pointer and the three arguments above it are public. -/
def frameTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 16, stk := [some 16] }

def inner : Prog isa := .seq (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi VG.Impl.RsaKeyGen.X86.Inverse.lay))
  (.seq (VG.Impl.Rsa.X86.KeyRt.inverse VG.Impl.RsaKeyGen.X86.Inverse.lay) (.block VG.Impl.Mont.X86.Compact.restoreRegs))

theorem inner_checked : (VG.Taint.check sseTaint frameTaint inner (VG.Taint.hintOf sseTaint frameTaint inner)).isSome = true := by
  taint_decide

theorem Entry.saved_sp_nat {s : State} (A : Entry s) :
    ((Compact.entered s).gpr .esp).toNat + 16 = (s.gpr .esp).toNat := by
  have := A.low
  rw [Compact.entered, pushed_esp, show 4 * Compact.savedRegisters.length = 16 from rfl, sub_toNat (by omega)]
  omega

theorem Entry.saved_argByte {s : State} (A : Entry s) (k : Nat) :
    VG.X86.Taint.argByte (Compact.entered s) (16 + k) = VG.X86.Taint.argByte s k := by
  have H := VG.X86.Taint.argByte_move (s := s) (s' := Compact.entered s) (d := 0) (d' := 16)
    (by rw [A.saved_sp_nat, Nat.add_zero]) k
  simpa only [Nat.zero_add] using H

theorem Entry.pushed_arg {s : State} (A : Entry s) {i : Nat} (hi : i < 3) :
    (Compact.entered s).mem.readW (argAddr s i) 32 = arg s i := by
  have H := (A.argument hi).value
  unfold VG.Proof.Dsa.X86.stackValue at H
  rwa [entered_address] at H

theorem Entry.frame_wf {s : State} (A : Entry s) : VG.X86.Taint.Wf frameTaint (Compact.entered s) := by
  have top := A.argsFit
  have position := A.saved_sp_nat
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have addrBase : VG.X86.Taint.argByte (Compact.entered s) 16 = (s.gpr .esp).setWidth 64 := by
    have H := A.saved_argByte 0
    simpa only [Nat.add_zero, VG.X86.Taint.argByte, BitVec.add_zero] using H
  have frameBase : below (s.gpr .esp) 16 = ⟨((Compact.entered s).gpr .esp).setWidth 64, 16⟩ := by
    unfold Compact.entered Compact.savedRegisters below
    rw [pushed_esp]
    rfl
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun _ h => (List.not_mem_nil h).elim,
    ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
  · intro _
    refine ⟨by change ((Compact.entered s).gpr .esp).toNat + 16 + 16 ≤ 2 ^ 32; omega, ?_⟩
    intro r member
    change (⟨VG.X86.Taint.argByte (Compact.entered s) 16, 16⟩ : Region).Disjoint r
    rw [addrBase]
    rw [Compact.entered, pushed_wr, A.wr] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change (⟨(s.gpr .esp).setWidth 64, 16⟩ : Region).Disjoint (below (s.gpr .esp) 16)
      unfold below
      rw [Taint.sub_setWidth fit]
      exact Offset.base_disjoint_below _ (by decide)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) A.returnWs A.wsArgs.symm
  · change ((Compact.entered s).gpr .esp).toNat + 16 < 2 ^ 32
    rw [position]
    exact (s.gpr .esp).isLt
  · intro p member
    change p ∈ [(0, 0, 16)] at member
    obtain rfl := List.mem_singleton.mp member
    change (Compact.entered s).wr[0]? = some ⟨addr ((Compact.entered s).gpr .esp) 0, 16⟩
    change some (below (s.gpr .esp) 16) = some ⟨addr ((Compact.entered s).gpr .esp) 0, 16⟩
    rw [frameBase]
    simp only [addr, BitVec.add_zero]

theorem entered_agree {s t : State} (A : Entry s) (B : Entry t)
    (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 3, arg s i = arg t i) :
    VG.X86.Taint.Agree frameTaint (Compact.entered s) (Compact.entered t) := by
  have savedSp : (Compact.entered s).gpr .esp = (Compact.entered t).gpr .esp := by
    rw [Compact.entered, Compact.entered, pushed_esp, pushed_esp, sp]
  refine ⟨⟨?_, fun h => nomatch h⟩, fun h => absurd rfl h, A.frame_wf, B.frame_wf,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => savedSp, ?_⟩
  · intro r member
    simp only [frameTaint, RegSet.mem_ofList, List.mem_singleton] at member
    subst r; exact savedSp
  · intro k low high
    change (Compact.entered s).mem (VG.X86.Taint.argByte (Compact.entered s) (16 + k)) =
      (Compact.entered t).mem (VG.X86.Taint.argByte (Compact.entered t) (16 + k))
    have bound : k < 16 := high
    rw [A.saved_argByte, B.saved_argByte, VG.X86.Taint.argByte_eq (by have := A.argsFit; omega) low bound,
      VG.X86.Taint.argByte_eq (by have := B.argsFit; omega) low bound,
      Mem.readW_byte (Compact.entered s).mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte (Compact.entered t).mem _ (Nat.mod_lt _ (by decide)),
      A.pushed_arg (by omega), B.pushed_arg (by omega), args _ (by omega)]

theorem frame_trace : RelCT isa (fun s t => contract.pre s ∧ contract.pre t ∧ contract.pub s t)
    VG.Impl.RsaKeyGen.X86.Inverse.code (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Inverse.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := fun _ _ => True) (fun _ _ P => by
    have H := P.2.2
    sig_pub [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
      abi, argSlots, argVal, argBytes] at H
    exact H.1)
  rintro _ _ tr ur u v ⟨s, t, ⟨HS, HT, HP⟩, rfl, rfl⟩ E F
  sig_pub [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes] at HP
  obtain ⟨sp, a0, a1, a2⟩ := HP
  obtain ⟨out, checked⟩ := Option.isSome_iff_exists.mp inner_checked
  have agree := entered_agree (entry HS) (entry HT) sp (by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2)
  exact ⟨(VG.Taint.check_sound checked agree E F).1, trivial⟩

theorem constantTime : ConstantTime isa contract.pre contract.pub VG.Impl.RsaKeyGen.X86.Inverse.code := by
  apply RelCT.constantTime
  intro s t tr ur u z P A B
  exact frame_trace _ _ _ _ _ _ P A B

end VG.Proof.RsaKeyGen.X86.Inverse
