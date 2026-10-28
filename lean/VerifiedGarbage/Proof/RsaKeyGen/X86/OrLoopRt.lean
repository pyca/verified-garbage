module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # An OR of `N` words through a pointer, at a run-time count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86 (at_)

theorem orLoop_ok {t₀ : State} {W : Addr} {L x N : Nat} (hw : Ws t₀ W L) (positive : 0 < N)
    (fit : x + 4 * N ≤ L) (P : PtrAt t₀ W .ebp x) (count : (t₀.gpr .ecx).toNat = N) (zero : t₀.gpr .ebx = 0#32) :
    WP isa (.loop (.block [.alu .or .ebx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne) t₀
      fun u => (u.gpr .ebx = 0#32 ↔ val32 t₀.mem W x N = 0) ∧ u.mem = t₀.mem ∧
        PtrAt u W .ebp (x + 4 * N) ∧ Keeps [.ebx, .ebp, .ecx] t₀ u := by
  have nowrap := hw.nowrap
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop positive (fun j t =>
      Keeps [.ebx, .ebp, .ecx] t₀ t ∧ t.mem = t₀.mem ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .ecx).toNat = N - j ∧ (t.gpr .ebx = 0#32 ↔ val32 t₀.mem W x j = 0)) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using P, by simpa using count, by rw [zero]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩)
    fun u ⟨K, M, Pu, _, Z⟩ => ⟨Z, M, Pu, K⟩
  rintro j t index ⟨K, M, Pt, cnt, Z⟩
  have ht := hw.of_keeps K
  refine wp_orS (readSrc_ptr ht Pt (d := 0) (by omega)) fun a A => wp_addS rfl fun b B _ =>
    wp_subZ rfl fun u U Zf => WP.block_nil ?_
  obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf cnt index
  have ecxB : b.gpr .ecx = t.gpr .ecx := by rw [B.other .ecx (by decide), A.other .ecx (by decide)]
  refine ⟨⟨K.trans (((A.keeps.mono (by decide)).widen B.keeps).widen U.keeps), ?_, ?_, by rw [U.gpr, ecxB]; exact next, ?_⟩,
    by rw [Zf, ecxB, last]⟩
  · rw [U.mem, B.mem, A.mem, M]
  · rw [PtrAt, U.other .ebp (by decide), B.gpr, A.other .ebp (by decide)]
    exact VG.Proof.Bignum.X86.PublicRt.ptr4 Pt
  · rw [U.other .ebx (by decide), B.other .ebx (by decide), A.gpr, BitVec.or_eq_zero_iff, Z, M, Nat.add_zero]
    have wordZero : t₀.mem.readW (off W (x + 4 * j)) 32 = 0#32 ↔ w32 t₀.mem W (x + 4 * j) = 0 :=
      ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
    rw [wordZero, val32_succ]
    have power : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    constructor
    · rintro ⟨left, right⟩
      rw [left, right, Nat.mul_zero]
    · intro sum
      have product : 2 ^ (32 * j) * w32 t₀.mem W (x + 4 * j) = 0 := by omega
      exact ⟨by omega, (Nat.mul_eq_zero.mp product).resolve_left (Nat.ne_of_gt power)⟩

end VG.Proof.RsaKeyGen.X86.FrontRt
