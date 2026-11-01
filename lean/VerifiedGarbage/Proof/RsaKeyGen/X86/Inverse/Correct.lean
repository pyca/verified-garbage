module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Framed
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! # `vg_rsa_keygen_inverse` meets its contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (kw)

theorem done_frame {s t : State} (A : Entry s) (D : Done s t) {i : Nat} (hi : i < size s)
    (hw : ¬ Proof.RsaKeyGen.inverseWrites (len s) i) :
    t.mem (base s + BitVec.ofNat 64 i) = s.mem (base s + BitVec.ofNat 64 i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have wsFit := A.wsFit
  have offset : ofs (base s) (base s + BitVec.ofNat 64 i) = i := by
    unfold ofs
    exact Mem.sub_ofNat_toNat _ (by unfold size at *; omega)
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
        omega
      · simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr, kw,
          Spec.Rsa.modulusWords] at c
        rw [Nat.add_mul, Nat.one_mul]
        rw [show 4 * (2 * ((len s + 7) / 8) + 2) = 8 * ((len s + 7) / 8) + 8 by omega] at c
        omega
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
  exact frameWs _ contains (Offset.contains_base _ (by omega) (by omega))

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa VG.Impl.RsaKeyGen.X86.Inverse.code s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  have A := entry h
  obtain ⟨trace, t, run, preserved, D⟩ := framed_ok h
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
  exact ⟨fun i hi hw => done_frame A D hi hw, D.gcd, D.bezout, D.lt⟩

end VG.Proof.RsaKeyGen.X86.Inverse
