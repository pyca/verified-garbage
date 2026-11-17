module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Framed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! ### `RsaKeyGen.X86.Inverse.Correct`, which only this module used -/

section

/-! # `vg_rsa_keygen_inverse` meets its contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (kw)

theorem done_frame {s t : State} (A : Entry s) (D : Done s t) {i : Nat} (hi : i < size s)
    (hw : ¬ Proof.RsaKeyGen.inverseWrites (len s) i) :
    t.mem (base s + BitVec.ofNat 64 i) = s.mem (base s + BitVec.ofNat 64 i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have wsFit := A.wsFit
  have offset : ofs (base s) (base s + BitVec.ofNat 64 i) = i := by
    unfold ofs
    exact Mem.sub_ofNat_toNat _ (by unfold size at *; omega_using [hi])
  have inner : t.mem (base s + BitVec.ofNat 64 i) = (Compact.entered s).mem (base s + BitVec.ofNat 64 i) := by
    apply D.keep
    intro r hr
    rw [offset]
    by_contra c
    apply hw
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map] at hr
    unfold Proof.RsaKeyGen.inverseWrites Proof.RsaKeyGen.inverseBytes
    rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
    · right
      refine ⟨j, ?_, ?_⟩
      · simp only [VG.Proof.Rsa.X86.Keys.invArrs, VG.Impl.Rsa.X86.Keys.aT1, VG.Impl.Rsa.X86.Keys.aT2,
          VG.Impl.Rsa.X86.Keys.aT3, VG.Impl.Rsa.X86.Keys.aT4, List.mem_cons, List.not_mem_nil, or_false] at hj
        omega_using [hj]
      · simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw,
          Spec.Rsa.modulusWords] at c
        rw [Nat.add_mul, Nat.one_mul]
        rw [show 4 * (2 * ((len s + 7) / 8) + 2) = 8 * ((len s + 7) / 8) + 8 by omega_using []] at c
        omega_using [c]
    · left
      simp only [VG.Proof.Rsa.X86.Keys.invSlots, VG.Impl.Rsa.X86.Keys.sOdd, VG.Impl.Rsa.X86.Keys.sB,
        VG.Impl.Rsa.X86.Keys.sC, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
  rw [inner]
  apply pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  have frameWs : (below (s.gpr .esp) 16).Disjoint ⟨base s, size s⟩ := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact A.stackWs.sub_left (Offset.sub_below _ (by decide) (by decide))
  intro contains
  exact frameWs _ contains (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, wsFit]))

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa VG.Impl.RsaKeyGen.X86.Inverse.code s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  have A := entry h
  obtain ⟨trace, t, run, preserved, t₀, D, F⟩ := framed_ok h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have frameWs : (below (s.gpr .esp) 16).Disjoint ⟨base s, size s⟩ := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact A.stackWs.sub_left (Offset.sub_below _ (by decide) (by decide))
  have wk : VG.Proof.MillerRabin.X86.WorkspaceFrame ⟨base s, size s, 0⟩ [] t₀.mem t.mem := fun i index _ =>
    F.bytes (R := ⟨base s, size s⟩) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact frameWs.symm)
      (by change size s ≤ 2 ^ 64; have := A.wsFit; unfold size at *; omega_using [this]) index
  have room := A.room
  have numEq1 : VG.Proof.Rsa.X86.Keys.num t.mem (base s) (kw (len s)) 1 =
      VG.Proof.Rsa.X86.Keys.num t₀.mem (base s) (kw (len s)) 1 :=
    wk.val32 (by
      change VG.Proof.Rsa.X86.Keys.arr (kw (len s)) 1 + 4 * kw (len s) ≤ size s
      simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw,
        Spec.Rsa.modulusWords] at room ⊢
      unfold Proof.RsaKeyGen.inverseBytes at room
      omega_using [room]) (fun _ mem => nomatch mem)
  have numEq3 : VG.Proof.Rsa.X86.Keys.num t.mem (base s) (kw (len s)) 3 =
      VG.Proof.Rsa.X86.Keys.num t₀.mem (base s) (kw (len s)) 3 :=
    wk.val32 (by
      change VG.Proof.Rsa.X86.Keys.arr (kw (len s)) 3 + 4 * kw (len s) ≤ size s
      simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw,
        Spec.Rsa.modulusWords] at room ⊢
      unfold Proof.RsaKeyGen.inverseBytes at room
      omega_using [room]) (fun _ mem => nomatch mem)
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes]
  change (∀ i, i < size s → ¬ Proof.RsaKeyGen.inverseWrites (len s) i →
      t.mem (base s + BitVec.ofNat 64 i) = s.mem (base s + BitVec.ofNat 64 i)) ∧
    Proof.RsaKeyGen.inverseNum t.mem (base s) (len s) 1 =
      Nat.gcd (Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 0) (Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8) ∧
    (Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8 : Int) ∣
      (Proof.RsaKeyGen.inverseNum t.mem (base s) (len s) 3 : Int) * Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 0 -
        Proof.RsaKeyGen.inverseNum t.mem (base s) (len s) 1 ∧
    Proof.RsaKeyGen.inverseNum t.mem (base s) (len s) 3 < Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8
  simp only [inverseNum_num]
  rw [numEq1, numEq3]
  exact ⟨fun i hi hw => (wk i hi (fun _ mem => nomatch mem)).trans (done_frame A D hi hw), D.gcd, D.bezout, D.lt⟩

end VG.Proof.RsaKeyGen.X86.Inverse

end

end


/-! # `vg_rsa_keygen_inverse` is verified against its contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x10000
  | 1 => 50
  | _ => 8

/-- A call with numbers of 8 octets: `m = 3` (numbers 1 and 8), 1, 0, `2^64 − 3` and 0, in a
workspace of 50 words at `0x10000`; the arguments above the stack pointer `0x4000`. -/
def satMemory : Mem := fun a =>
  if (a - 0x4004).toNat < 12 then
    (satArgument ((a - 0x4004).toNat / 4)).extractLsb' (8 * ((a - 0x4004).toNat % 4)) 8
  else if a = 0x100b0 then 3 else if a = 0x100c0 then 1 else if a = 0x10120 then 3 else
    if a = 0x10130 then 0xfd else if (a - 0x10131).toNat < 7 then 0xff else 0

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x4004, 12⟩]
  wr := [⟨0x10000, 400⟩]

theorem sat_argument0 : arg satState 0 = satArgument 0 := by decide +kernel
theorem sat_argument1 : arg satState 1 = satArgument 1 := by decide +kernel
theorem sat_argument2 : arg satState 2 = satArgument 2 := by decide +kernel

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sat_argument0, sat_argument1, sat_argument2]
  sig_and_intros
  all_goals first
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.Inverse.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Inverse
