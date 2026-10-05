import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Scrypt.X86.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Impl.Scrypt.X86.RoMix
import VerifiedGarbage.Proof.Framework.X86.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.RoMixFun`. -/
section

section

/-!
# scryptROMix on x86 (32-bit): the precondition

The regions the function works on, and `BlockMixSpec`: what a call of
`vg_scrypt_blockmix` in a frame of its arguments does (the verified one meets
it: `Proof/Scrypt/X86/RoMixCT.lean`). As on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`), with the pointers and lengths read from the
arguments on the stack, which nothing writes, and the calls using the 36 bytes
below `esp` (`stkR`), which the memory frames include.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix integerify leNat)
open VG.Proof.Scrypt (bytesAt_add' bytesAt_length' leNat_append leNat_bytesAt blk_bytesAt')
open VG.Proof.Sha256.X86.Stream (addr_toNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off
  disj_off InRegions.of_mem)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c`, in a frame of its arguments pushed from `esi`, `ecx`,
`edx`, `ecx` and `eax`, writes scryptBlockMix of the `128 r` bytes at `esi`
to `edx`, with the 128 bytes at `eax` as working space, using the 36 bytes
below `esp`. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : BitVec 32) (r : Nat), s.gpr .esi = src →
    s.gpr .ecx = BitVec.ofNat 32 r → s.gpr .edx = dst → s.gpr .eax = scr → 0 < r → 128 * r < 2 ^ 32 →
    Region.Disjoint ⟨dst.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩ →
    Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨dst.setWidth 64, 128 * r⟩ →
    Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 32 → dst.toNat + 128 * r ≤ 2 ^ 32 → scr.toNat + 128 ≤ 2 ^ 32 →
    36 ≤ (s.gpr .esp).toNat →
    (below (s.gpr .esp) 36).Disjoint ⟨src.setWidth 64, 128 * r⟩ →
    (below (s.gpr .esp) 36).Disjoint ⟨dst.setWidth 64, 128 * r⟩ →
    (below (s.gpr .esp) 36).Disjoint ⟨scr.setWidth 64, 128⟩ →
    InRegions (s.rd ++ s.wr) (src.setWidth 64) (128 * r) → InRegions s.wr (dst.setWidth 64) (128 * r) →
    InRegions s.wr (scr.setWidth 64) 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨dst.setWidth 64, 128 * r⟩, ⟨scr.setWidth 64, 128⟩, below (s.gpr .esp) 36] s.mem s'.mem →
        bytesAt s'.mem (dst.setWidth 64) (128 * r) =
          blockMix r (bytesAt s.mem (src.setWidth 64) (128 * r)) → Q s') →
    WP isa (.frame (.push [.eax, .ecx, .edx, .ecx, .esi]) (.call "vg_scrypt_blockmix" c) (.pop .eax 5)) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev bP : BitVec 32 := VG.X86.arg s₀ 0
abbrev rr : Nat := (VG.X86.arg s₀ 1).toNat
abbrev vP : BitVec 32 := VG.X86.arg s₀ 2
abbrev vl : Nat := (VG.X86.arg s₀ 3).toNat
abbrev sc : BitVec 32 := VG.X86.arg s₀ 4
/-- `N`. -/
abbrev NN : Nat := VG.Proof.Scrypt.X86.RoMix.vl s₀ / VG.Proof.Scrypt.X86.RoMix.rr s₀
abbrev bA : Addr := (VG.Proof.Scrypt.X86.RoMix.bP s₀).setWidth 64
abbrev vA : Addr := (VG.Proof.Scrypt.X86.RoMix.vP s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.Scrypt.X86.RoMix.sc s₀).setWidth 64
abbrev bR : Region := ⟨VG.Proof.Scrypt.X86.RoMix.bA s₀, VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128⟩
abbrev vR : Region := ⟨VG.Proof.Scrypt.X86.RoMix.vA s₀, VG.Proof.Scrypt.X86.RoMix.vl s₀ * 128⟩
abbrev scR : Region := ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, (VG.Proof.Scrypt.X86.RoMix.rr s₀ + 2) * 128⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64, 4⟩
/-- The stack the calls use. -/
abbrev stkR : Region := below (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) 36
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)
/-- `(V[i]'(by omega))`. -/
abbrev vAt (i : Nat) : Addr := VG.Proof.Scrypt.X86.RoMix.vA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * i)
/-- `(V[i]'(by omega))`, as the pointer the code computes. -/
abbrev vAt32 (i : Nat) : BitVec 32 := VG.Proof.Scrypt.X86.RoMix.vP s₀ + BitVec.ofNat 32 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 192
abbrev tP32 : BitVec 32 := VG.Proof.Scrypt.X86.RoMix.sc s₀ + BitVec.ofNat 32 192

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 ·) s₀.gpr rmSaved

/-- The regions the function writes, and the stack its calls use. -/
abbrev frs : List Region := [VG.Proof.Scrypt.X86.RoMix.bR s₀, VG.Proof.Scrypt.X86.RoMix.vR s₀, VG.Proof.Scrypt.X86.RoMix.scR s₀, VG.Proof.Scrypt.X86.RoMix.stkR s₀]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Scrypt.X86.RoMix.argR s₀]
  wr : s₀.wr = [VG.Proof.Scrypt.X86.RoMix.bR s₀, VG.Proof.Scrypt.X86.RoMix.vR s₀, VG.Proof.Scrypt.X86.RoMix.scR s₀]
  b_v : (VG.Proof.Scrypt.X86.RoMix.bR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.vR s₀)
  b_s : (VG.Proof.Scrypt.X86.RoMix.bR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.scR s₀)
  v_s : (VG.Proof.Scrypt.X86.RoMix.vR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.scR s₀)
  a_b : (VG.Proof.Scrypt.X86.RoMix.argR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.bR s₀)
  a_v : (VG.Proof.Scrypt.X86.RoMix.argR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.vR s₀)
  a_s : (VG.Proof.Scrypt.X86.RoMix.argR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.scR s₀)
  ret_b : (VG.Proof.Scrypt.X86.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.bR s₀)
  ret_v : (VG.Proof.Scrypt.X86.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.vR s₀)
  ret_s : (VG.Proof.Scrypt.X86.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.scR s₀)
  stk_b : (VG.Proof.Scrypt.X86.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.bR s₀)
  stk_v : (VG.Proof.Scrypt.X86.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.vR s₀)
  stk_s : (VG.Proof.Scrypt.X86.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.scR s₀)
  b_nw : (VG.Proof.Scrypt.X86.RoMix.bP s₀).toNat + VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128 ≤ 2 ^ 32
  v_nw : (VG.Proof.Scrypt.X86.RoMix.vP s₀).toNat + VG.Proof.Scrypt.X86.RoMix.vl s₀ * 128 ≤ 2 ^ 32
  s_nw : (VG.Proof.Scrypt.X86.RoMix.sc s₀).toNat + (VG.Proof.Scrypt.X86.RoMix.rr s₀ + 2) * 128 ≤ 2 ^ 32
  sp_lo : 36 ≤ (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).toNat
  sp_fit : (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).toNat + 28 ≤ 2 ^ 32
  pos : 0 < VG.Proof.Scrypt.X86.RoMix.rr s₀
  vl_eq : VG.Proof.Scrypt.X86.RoMix.vl s₀ = VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀
  pow : (VG.Proof.Scrypt.X86.RoMix.NN s₀).isPowerOfTwo

/-- The 36 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 36 ≤ E.toNat) : below E 36 = ⟨E.setWidth 64 - 36, 36⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixX86.pre s₀) : VG.Proof.Scrypt.X86.RoMix.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23⟩ := h
  have e := VG.Proof.Scrypt.X86.RoMix.stk_eq h18
  simp only [h23] at h2 h4 h5 h8 h11 h14 h17
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by rw [VG.Proof.Scrypt.X86.RoMix.stkR, e]; exact h12,
    by rw [VG.Proof.Scrypt.X86.RoMix.stkR, e]; exact h13, by rw [VG.Proof.Scrypt.X86.RoMix.stkR, e]; exact h14, h15, h16, h17, h18, h19, h20, ?_, h22⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h21)).symm

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀)
include hp

theorem NN_pos : 0 < VG.Proof.Scrypt.X86.RoMix.NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

theorem vl_mul : VG.Proof.Scrypt.X86.RoMix.vl s₀ * 128 = 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀ := by
  rw [hp.vl_eq, Nat.mul_comm, ← Nat.mul_assoc]

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀ < 2 ^ 32 := by
  rw [← VG.Proof.Scrypt.X86.RoMix.vl_mul hp]
  by_contra hc
  have hv : VG.Proof.Scrypt.X86.RoMix.vA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.v_nw; omega
  have hs : (VG.Proof.Scrypt.X86.RoMix.scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (VG.Proof.Scrypt.X86.RoMix.sc s₀).isLt
  refine hp.v_s (VG.Proof.Scrypt.X86.RoMix.scA s₀) ?_ ?_
  · show (VG.Proof.Scrypt.X86.RoMix.scA s₀ - VG.Proof.Scrypt.X86.RoMix.vA s₀).toNat + 1 ≤ VG.Proof.Scrypt.X86.RoMix.vl s₀ * 128
    rw [hv, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega
  · show (VG.Proof.Scrypt.X86.RoMix.scA s₀ - VG.Proof.Scrypt.X86.RoMix.scA s₀).toNat + 1 ≤ (VG.Proof.Scrypt.X86.RoMix.rr s₀ + 2) * 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega

theorem r_lt : 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ < 2 ^ 32 := by
  have := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have := VG.Proof.Scrypt.X86.RoMix.NN_pos hp
  have : 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀ := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem NN_lt : VG.Proof.Scrypt.X86.RoMix.NN s₀ < 2 ^ 32 := by
  have := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have : VG.Proof.Scrypt.X86.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  omega

omit hp in
theorem v_le {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * i + 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- `(V[i]'(by omega))` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86.RoMix.vR s₀) := by
  have := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have := VG.Proof.Scrypt.X86.RoMix.v_le hi
  show Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.vA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * i), 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86.RoMix.vA s₀, VG.Proof.Scrypt.X86.RoMix.vl s₀ * 128⟩
  exact sub_off (by rw [VG.Proof.Scrypt.X86.RoMix.vl_mul hp]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) (hk : k < VG.Proof.Scrypt.X86.RoMix.NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ k, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ := by
  have := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have h1 := VG.Proof.Scrypt.X86.RoMix.v_le hi
  have h2 := VG.Proof.Scrypt.X86.RoMix.v_le hk
  refine disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  · right; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h

/-- `(V[i]'(by omega))` as an address. -/
theorem vAt_addr {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : (VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i).setWidth 64 = VG.Proof.Scrypt.X86.RoMix.vAt s₀ i := by
  have := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have := VG.Proof.Scrypt.X86.RoMix.v_le hi
  have := hp.v_nw
  have := VG.Proof.Scrypt.X86.RoMix.vl_mul hp
  have := hp.pos
  exact addr_add (by omega)

theorem vAt_nw {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : (VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i).toNat + 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ ≤ 2 ^ 32 := by
  have := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have := VG.Proof.Scrypt.X86.RoMix.v_le hi
  have := hp.v_nw
  have := VG.Proof.Scrypt.X86.RoMix.vl_mul hp
  have := hp.pos
  rw [toNat_add32 (by omega)]
  omega

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86.RoMix.scR s₀) := by
  have := hp.s_nw
  exact sub_off (by omega) (by omega)

theorem t_addr : (VG.Proof.Scrypt.X86.RoMix.tP32 s₀).setWidth 64 = VG.Proof.Scrypt.X86.RoMix.tP s₀ := addr_add (by have := hp.s_nw; omega)

theorem t_nw : (VG.Proof.Scrypt.X86.RoMix.tP32 s₀).toNat + 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ ≤ 2 ^ 32 := by
  have := hp.s_nw
  rw [toNat_add32 (by omega)]
  omega

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, 128⟩ (VG.Proof.Scrypt.X86.RoMix.scR s₀) := Region.sub_prefix (by omega)

theorem t_w : Region.Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := disj_off (VG.Proof.Scrypt.X86.RoMix.scA s₀) (o₁ := 192) (n₁ := 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

/-- The argument words are in the arguments' region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) :
    Region.Sub ⟨addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) d, 4⟩ (VG.Proof.Scrypt.X86.RoMix.argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [show (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) 4 from rfl,
    addr_eq (by omega)]
  generalize (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨VG.Proof.Scrypt.X86.RoMix.argR s₀, by simp [hp.rd], ?_⟩
  show (addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) d - addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) 4).toNat + 4 ≤ 24
  rw [addr_eq (by omega), addr_eq (by omega),
    show (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem stk_arg : (VG.Proof.Scrypt.X86.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.argR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains, argAddr] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [show (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) 4 from rfl,
    addr_eq (by omega)] at h₂
  have hE : ((VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64).toNat = (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).toNat := addr_toNat _
  generalize (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (VG.Proof.Scrypt.X86.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64).toNat = (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).toNat := addr_toNat _
  generalize (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are kept by anything that writes only our regions and the
stack below `esp`. -/
theorem arg_keep {m : Mem} (hf : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem m) {d : Nat} (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ 28) : m.readW (addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.a_b.sub_left (VG.Proof.Scrypt.X86.RoMix.arg_sub hp hd₁ hd)
  · exact hp.a_v.sub_left (VG.Proof.Scrypt.X86.RoMix.arg_sub hp hd₁ hd)
  · exact hp.a_s.sub_left (VG.Proof.Scrypt.X86.RoMix.arg_sub hp hd₁ hd)
  · exact (VG.Proof.Scrypt.X86.RoMix.stk_arg hp).symm.sub_left (VG.Proof.Scrypt.X86.RoMix.arg_sub hp hd₁ hd)

/-- Argument `i`, read from memory that differs from the initial one only in
our regions and the stack below `esp`. -/
theorem arg_read {m : Mem} (hf : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) (4 + 4 * i)) 32 = VG.X86.arg s₀ i :=
  VG.Proof.Scrypt.X86.RoMix.arg_keep hp hf (by omega) (by omega)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (VG.Proof.Scrypt.X86.RoMix.scR s₀).Contains (VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.X86.RoMix.scR s₀) :=
  sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: our caller's registers -/

/-- Bytes `[128, 192)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 128, 64⟩

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 4 ≤ 192) :
    Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 d, 4⟩ (VG.Proof.Scrypt.X86.RoMix.keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← add_ofNat]
  exact sub_off (by omega) (by omega)

theorem saved_offs : ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 144 ∧ p.1 ≠ .eax := by decide

theorem Saved.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : VG.Proof.Scrypt.X86.RoMix.Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.Scrypt.X86.RoMix.keepR s₀).Disjoint r) : VG.Proof.Scrypt.X86.RoMix.Saved s₀ m' := by
  intro p hp
  have ho := VG.Proof.Scrypt.X86.RoMix.saved_offs p hp
  rw [← h p hp]
  exact hf.readW (r := ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (VG.Proof.Scrypt.X86.RoMix.word_sub s₀ ho.1 (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (VG.Proof.Scrypt.X86.RoMix.keepR s₀) (VG.Proof.Scrypt.X86.RoMix.scR s₀) := VG.Proof.Scrypt.X86.RoMix.s_sub s₀ (by omega)

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀)
include hp

theorem keep_b : (VG.Proof.Scrypt.X86.RoMix.keepR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.bR s₀) := hp.b_s.symm.sub_left (VG.Proof.Scrypt.X86.RoMix.keep_sub s₀)
theorem keep_v : (VG.Proof.Scrypt.X86.RoMix.keepR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.vR s₀) := hp.v_s.symm.sub_left (VG.Proof.Scrypt.X86.RoMix.keep_sub s₀)
theorem keep_stk : (VG.Proof.Scrypt.X86.RoMix.keepR s₀).Disjoint (VG.Proof.Scrypt.X86.RoMix.stkR s₀) := hp.stk_s.symm.sub_left (VG.Proof.Scrypt.X86.RoMix.keep_sub s₀)

omit hp in
theorem keep_w : (VG.Proof.Scrypt.X86.RoMix.keepR s₀).Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, 128⟩ := by
  have := disj_off (VG.Proof.Scrypt.X86.RoMix.scA s₀) (o₁ := 128) (n₁ := 64) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

theorem keep_t : (VG.Proof.Scrypt.X86.RoMix.keepR s₀).Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact disj_off (VG.Proof.Scrypt.X86.RoMix.scA s₀) (o₁ := 128) (n₁ := 64) (o₂ := 192) (n₂ := 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) (by omega)
    (by omega) (by omega) (by omega) (by omega)

omit hp in
theorem b_sub' : Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.bA s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86.RoMix.bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

/-! ## `Integerify`, from a 32-bit word -/

theorem leNat_bytesAt32_mod (m : Mem) (a : Addr) {e : Nat} (he : e ≤ 32) :
    leNat (bytesAt m a 64) % 2 ^ e = (m.readW a 32).toNat % 2 ^ e := by
  rw [show (64 : Nat) = 4 + 60 from rfl, bytesAt_add', leNat_append, bytesAt_length',
    show (256 : Nat) ^ 4 = 2 ^ e * 2 ^ (32 - e) by rw [← Nat.pow_add, Nat.add_sub_cancel' he],
    Nat.mul_assoc, Nat.add_mul_mod_self_left, leNat_bytesAt]
  simp only [Mem.readW, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- `Integerify (X) mod 2^e`, for `e ≤ 32`, is the first 4 bytes of `X`'s last
64-byte block, read little-endian, mod `2^e`. -/
theorem integerify_mod32 (m : Mem) (p : Addr) {r e : Nat} (hr : 0 < r) (he : e ≤ 32) :
    integerify r (bytesAt m p (128 * r)) % 2 ^ e =
      (m.readW (p + BitVec.ofNat 64 (128 * r - 64)) 32).toNat % 2 ^ e := by
  rw [integerify, blk_bytesAt' _ _ (by omega), show 64 * (2 * r - 1) = 128 * r - 64 by omega,
    VG.Proof.Scrypt.X86.RoMix.leNat_bytesAt32_mod _ _ he]

theorem and_mask32 (w : BitVec 32) {e : Nat} (he : e ≤ 32) :
    (w &&& BitVec.ofNat 32 (2 ^ e - 1)).toNat = w.toNat % 2 ^ e := by
  have := Nat.pow_le_pow_right (by omega : 0 < 2) he
  have := Nat.one_le_two_pow (n := e)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

theorem shr_ofNat32 {a : Nat} (n : Nat) (h : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86.RoMix

end

section

/-!
# scryptROMix on x86 (32-bit): the small loops

The copy (`copyLoop`) and exclusive-or (`xorLoop`) of 16-byte blocks and the
computation of `2 N` by doubling (`nLoop`), as on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`). Words are 4 bytes, and pointers 32 bits,
which address memory by their zero extensions.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_cmp
  ofNat_beq_zero sub_beq)

/-! ## Arithmetic -/

/-- A pointer advanced by one 16-byte block. -/
theorem next16 (p : BitVec 32) (k : Nat) :
    p + BitVec.ofNat 32 (16 * k) + 16 = p + BitVec.ofNat 32 (16 * (k + 1)) := by
  rw [add32_lit, Nat.mul_succ]

theorem ofNat_zero_add16 (p : BitVec 32) : p + BitVec.ofNat 32 (16 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-- A 16-byte block of a region, as an address. -/
theorem block_addr {p : BitVec 32} {n k : Nat} (hp : p.toNat + 16 * n ≤ 2 ^ 32) (hk : k < n) :
    addr (p + BitVec.ofNat 32 (16 * k)) 0 = p.setWidth 64 + BitVec.ofNat 64 (16 * k) := by
  rw [addr_zero, addr_add (by omega)]

/-! ## `copyLoop` -/

/-- After `k` blocks of `copyLoop`. -/
structure CopyInv (s : State) (src dst : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r
  eax : t.gpr .eax = src + BitVec.ofNat 32 (16 * k)
  ecx : t.gpr .ecx = dst + BitVec.ofNat 32 (16 * k)
  edx : t.gpr .edx = BitVec.ofNat 32 (n - k)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (dst.setWidth 64) (bytesAt s.mem (src.setWidth 64) (16 * k))

theorem copy_step {s : State} {src dst : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fs : src.toNat + 16 * n ≤ 2 ^ 32) (fd : dst.toNat + 16 * n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (dst.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hsep : Region.Disjoint ⟨src.setWidth 64, 16 * n⟩ ⟨dst.setWidth 64, 16 * n⟩) {k : Nat} (hk : k < n)
    {t : State} (h : VG.Proof.Scrypt.X86.RoMix.CopyInv s src dst n k t) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .eax 0), .movdquStore (at_ .ecx 0) .xmm0,
      .alu .add .eax (.imm 16), .alu .add .ecx (.imm 16), .alu .sub .edx (.imm 1)]) t
      fun t' => VG.Proof.Scrypt.X86.RoMix.CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_ldq (a := src.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, h.eax, VG.Proof.Scrypt.X86.RoMix.block_addr fs hk]) (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ R₁ m₁ x₁ _ => ?_
  refine wp_stq (a := dst.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, R₁.gpr, h.ecx, VG.Proof.Scrypt.X86.RoMix.block_addr fd hk])
    (by rw [R₁.wr, h.wr]; exact hout k hk) fun t₂ R₂ m₂ _ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : t₂.gpr = t.gpr := by rw [R₂.gpr, R₁.gpr]
  have e2 : t₄.gpr .edx = BitVec.ofNat 32 (n - k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g, h.edx]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, R₂.rd, R₁.rd, h.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, R₂.wr, R₁.wr, h.wr], fun r h0 h1 h2 h3 => ?_, ?_, ?_,
    by rw [u₅.gpr, e2, dec_count hk], ?_⟩, by rw [z₅, e2, dec_z hk hn]⟩
  · rw [u₅.other r h2, u₄.other r h1, u₃.other r h0, g, h.other r h0 h1 h2 h3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g, h.eax, VG.Proof.Scrypt.X86.RoMix.next16]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g, h.ecx, VG.Proof.Scrypt.X86.RoMix.next16]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, x₁, m₁, h.mem, Nat.mul_succ]
    exact Proof.Scrypt.Memory.copy_mem s.mem _ _ k 16
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)

/-- `copyLoop` copies `16 n` bytes from `eax` to `ecx` (`edx = n > 0` blocks). -/
theorem copyLoop_ok {s : State} {src dst : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fs : src.toNat + 16 * n ≤ 2 ^ 32) (fd : dst.toNat + 16 * n ≤ 2 ^ 32)
    (h0 : s.gpr .eax = src) (h1 : s.gpr .ecx = dst) (h2 : s.gpr .edx = BitVec.ofNat 32 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (dst.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hsep : Region.Disjoint ⟨src.setWidth 64, 16 * n⟩ ⟨dst.setWidth 64, 16 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (dst.setWidth 64) (bytesAt s.mem (src.setWidth 64) (16 * n)) := by
  refine WP.mono (count_loop hn (VG.Proof.Scrypt.X86.RoMix.CopyInv s src dst n)
    (fun k hk t h => VG.Proof.Scrypt.X86.RoMix.copy_step hlt fs fd hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [VG.Proof.Scrypt.X86.RoMix.ofNat_zero_add16, h0],
    by rw [VG.Proof.Scrypt.X86.RoMix.ofNat_zero_add16, h1], by rw [h2, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (VG.WriteBytes.writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` blocks of `xorLoop`. -/
structure XorInv (s : State) (x y d : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .esi → t.gpr r = s.gpr r
  eax : t.gpr .eax = x + BitVec.ofNat 32 (16 * k)
  ecx : t.gpr .ecx = y + BitVec.ofNat 32 (16 * k)
  edx : t.gpr .edx = d + BitVec.ofNat 32 (16 * k)
  edi : t.gpr .edi = BitVec.ofNat 32 (n - k)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (d.setWidth 64)
    (xorBytes (bytesAt s.mem (x.setWidth 64) (16 * k)) (bytesAt s.mem (y.setWidth 64) (16 * k)))

theorem xor_step {s : State} {x y d : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fx : x.toNat + 16 * n ≤ 2 ^ 32) (fy : y.toNat + 16 * n ≤ 2 ^ 32) (fd : d.toNat + 16 * n ≤ 2 ^ 32)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨x.setWidth 64, 16 * n⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨y.setWidth 64, 16 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : VG.Proof.Scrypt.X86.RoMix.XorInv s x y d n k t) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .ecx 0), xb .pxor .xmm0 .xmm1,
      .movdquStore (at_ .edx 0) .xmm0, .alu .add .eax (.imm 16), .alu .add .ecx (.imm 16),
      .alu .add .edx (.imm 16), .alu .sub .edi (.imm 1)]) t
      fun t' => VG.Proof.Scrypt.X86.RoMix.XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_ldq (a := x.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, h.eax, VG.Proof.Scrypt.X86.RoMix.block_addr fx hk]) (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ R₁ m₁ x₁ _ => ?_
  refine wp_ldq (a := y.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, R₁.gpr, h.ecx, VG.Proof.Scrypt.X86.RoMix.block_addr fy hk])
    (by rw [R₁.rd, R₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ R₂ m₂ x₂ o₂ => ?_
  refine wp_xbin fun t₃ R₃ m₃ x₃ _ => ?_
  refine wp_stq (a := d.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, R₃.gpr, R₂.gpr, R₁.gpr, h.edx, VG.Proof.Scrypt.X86.RoMix.block_addr fd hk])
    (by rw [R₃.wr, R₂.wr, R₁.wr, h.wr]; exact hout k hk) fun t₄ R₄ m₄ _ => ?_
  refine wp_addi fun t₅ u₅ => wp_addi fun t₆ u₆ => wp_addi fun t₇ u₇ => wp_subi fun t₈ u₈ z₈ =>
    WP.block_nil ?_
  have g : t₄.gpr = t.gpr := by rw [R₄.gpr, R₃.gpr, R₂.gpr, R₁.gpr]
  have e7 : t₇.gpr .edi = BitVec.ofNat 32 (n - k) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g, h.edi]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, R₄.rd, R₃.rd, R₂.rd, R₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, R₄.wr, R₃.wr, R₂.wr, R₁.wr, h.wr],
    fun r h0 h1 h2 h3 h4 => ?_, ?_, ?_, ?_, by rw [u₈.gpr, e7, dec_count hk], ?_⟩,
    by rw [z₈, e7, dec_z hk hn]⟩
  · rw [u₈.other r h3, u₇.other r h2, u₆.other r h1, u₅.other r h0, g, h.other r h0 h1 h2 h3 h4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g, h.eax, VG.Proof.Scrypt.X86.RoMix.next16]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g, h.ecx, VG.Proof.Scrypt.X86.RoMix.next16]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g, h.edx, VG.Proof.Scrypt.X86.RoMix.next16]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, x₃, o₂ .xmm0 (by decide), x₁, x₂, m₃, m₂, m₁, h.mem]
    exact xor_mem16 s.mem hk (by omega) hdx hdy

/-- `xorLoop` writes `[eax] xor [ecx]` to `edx`, `16 n` bytes (`edi = n > 0` blocks). -/
theorem xorLoop_ok {s : State} {x y d : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fx : x.toNat + 16 * n ≤ 2 ^ 32) (fy : y.toNat + 16 * n ≤ 2 ^ 32) (fd : d.toNat + 16 * n ≤ 2 ^ 32)
    (h0 : s.gpr .eax = x) (h1 : s.gpr .ecx = y) (h2 : s.gpr .edx = d)
    (h3 : s.gpr .edi = BitVec.ofNat 32 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨x.setWidth 64, 16 * n⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨y.setWidth 64, 16 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .esi → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (d.setWidth 64)
        (xorBytes (bytesAt s.mem (x.setWidth 64) (16 * n)) (bytesAt s.mem (y.setWidth 64) (16 * n))) := by
  refine WP.mono (count_loop hn (VG.Proof.Scrypt.X86.RoMix.XorInv s x y d n)
    (fun k hk t h => VG.Proof.Scrypt.X86.RoMix.xor_step hlt fx fy fd hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [VG.Proof.Scrypt.X86.RoMix.ofNat_zero_add16, h0],
    by rw [VG.Proof.Scrypt.X86.RoMix.ofNat_zero_add16, h1], by rw [VG.Proof.Scrypt.X86.RoMix.ofNat_zero_add16, h2], by rw [h3, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (VG.WriteBytes.writeBytes_nil _ _).symm⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .eax → r' ≠ .ecx → t.gpr r' = s.gpr r'
  eax : t.gpr .eax = BitVec.ofNat 32 (r * 2 ^ k)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (2 ^ k)

theorem dbl_pow32 (x k : Nat) : BitVec.ofNat 32 (x * 2 ^ k) + BitVec.ofNat 32 (x * 2 ^ k) =
    BitVec.ofNat 32 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h2 : s.gpr .edx = BitVec.ofNat 32 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : VG.Proof.Scrypt.X86.RoMix.NInv s r k t) :
    WP isa (.block [.alu .add .eax (.reg .eax), .alu .add .ecx (.reg .ecx), .alu .cmp .eax (.reg .edx)]) t
      fun t' => VG.Proof.Scrypt.X86.RoMix.NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_cmp fun t₃ f₃ _ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .eax = BitVec.ofNat 32 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.eax, VG.Proof.Scrypt.X86.RoMix.dbl_pow32]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [f₃.mem, u₂.mem, u₁.mem, h.mem], fun r' h0 h1 => ?_, by rw [f₃.gpr, ax], ?_⟩, ?_⟩
  · rw [f₃.gpr, u₂.other r' h1, u₁.other r' h0, h.other r' h0 h1]
  · rw [f₃.gpr, u₂.gpr, u₁.other _ (by decide), h.ecx, ← Nat.one_mul (2 ^ k), VG.Proof.Scrypt.X86.RoMix.dbl_pow32, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), h2, sub_beq (by omega) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, hh]

/-- `nLoop` doubles `eax` (from `r`) and `ecx` (from 1) until `eax = edx = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h0 : s.gpr .eax = BitVec.ofNat 32 r) (h1 : s.gpr .ecx = 1)
    (h2 : s.gpr .edx = BitVec.ofNat 32 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ecx → s'.gpr r' = s.gpr r') ∧
      s'.gpr .ecx = BitVec.ofNat 32 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (VG.Proof.Scrypt.X86.RoMix.NInv s r)
    (fun k hk t h => VG.Proof.Scrypt.X86.RoMix.n_step hr hlt h2 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.ecx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [h0, Nat.pow_zero, Nat.mul_one],
    by rw [h1]; rfl⟩

end VG.Proof.Scrypt.X86.RoMix

end

/-!
# scryptROMix on x86 (32-bit): correctness

The prologue saves our caller's registers in `scratch`; `N` is computed by
doubling; step 2 and step 3 are loops whose bodies call `vg_scrypt_blockmix`
(through `BlockMixSpec`) in a frame of its arguments; the epilogue restores
the registers. As on 32-bit ARM (`Proof/Scrypt/Arm/RoMixCT.lean`), with the
pointers and `r` read from the arguments when needed.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_add wp_addi wp_subi wp_shr)
open VG.Proof.Scrypt (vList vList_getD roMix_eq roMixIndices_eq mixLoop_succ_fst mixLoop_succ_snd)
open VG.Proof.Scrypt.Memory (add_ofNat contains_off sub_off InRegions.of_mem
  InRegions.right frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep bytesAt_length
  xorBytes_length)

/-! ## The prologue -/

theorem prologue_eq : rmPrologue =
    .mov .eax (.mem (at_ .esp 20)) :: (rmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
      ([.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.imm 1), .mov .edx (.mem (at_ .esp 16)),
        .alu .add .edx (.reg .edx)] : List Instr)) := rfl

theorem rmSaved_fits : Spill.Fits 144 rmSaved := by decide

theorem rmSaved_addr (s₀ : State) (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) :
    ∀ p ∈ rmSaved, addr (VG.Proof.Scrypt.X86.RoMix.sc s₀) p.2 = VG.Proof.Scrypt.X86.RoMix.scA s₀ + BitVec.ofNat 64 p.2 :=
  Spill.addr_eq_of_fits (by have := hp.s_nw; omega) VG.Proof.Scrypt.X86.RoMix.rmSaved_fits

theorem save_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r) → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → Frame [VG.Proof.Scrypt.X86.RoMix.scR s₀] s₀.mem s₁.mem → VG.Proof.Scrypt.X86.RoMix.Saved s₀ s₁.mem → WP isa (.block rest) s₁ Q) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 20)) ::
      (rmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest))) s₀ Q := by
  have hs := hp.s_nw
  refine wp_movm (a := addr (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) 20) rfl (VG.Proof.Scrypt.X86.RoMix.arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = VG.Proof.Scrypt.X86.RoMix.sc s₀ := u₁.gpr
  have ha := VG.Proof.Scrypt.X86.RoMix.rmSaved_addr s₀ hp
  refine Spill.save_ok rmSaved (fun p hp' => ?_) fun s₂ u₂ => ?_
  · rw [e, u₁.wr, hp.wr, ha p hp']
    exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.RoMix.in_s s₀ (by have := rmSaved_fits.1 p hp'; omega))
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_ ?_
  · rw [u₂.mem, e, u₁.mem]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      rw [ha p hp']; exact VG.Proof.Scrypt.X86.RoMix.in_s s₀ (by have := rmSaved_fits.1 p hp'; omega)
  · rw [u₂.mem, e, u₁.mem]
    exact (Spill.saveMem_saved_addr _ _ VG.Proof.Scrypt.X86.RoMix.rmSaved_fits (by have := hp.s_nw; omega)).congr ha
      fun p hp' => u₁.other _ (VG.Proof.Scrypt.X86.RoMix.saved_offs p hp').2.2

/-- The memory and registers the function starts each piece with. -/
structure Base (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Scrypt.X86.RoMix.esp₀ s₀
  frame : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem s.mem

theorem Base.arg {s₀ s : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  rw [h.esp]; exact VG.Proof.Scrypt.X86.RoMix.arg_read hp h.frame hi

theorem Base.arg_in {s₀ s : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {i : Nat} (hi : i < 6) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  rw [h.esp, h.rd, h.wr]; exact RoMix.arg_in hp (by omega) (by omega)

/-- A `mov` of argument `i` into `d`. -/
theorem wp_arg {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {d : Reg} {i : Nat} (hi : i < 6)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ .esp (4 + 4 * i))) :: is)) s Q :=
  wp_movm (by rw [ea_at]) (h.arg_in hp hi) fun s' u => k s' (by rw [← h.arg hp hi]; exact u)

theorem Base.upd {s₀ s s' : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .esp) : VG.Proof.Scrypt.X86.RoMix.Base s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm hd)).trans h.esp, by rw [u.mem]; exact h.frame⟩

theorem toNat_rr (s₀ : State) : BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀) = VG.X86.arg s₀ 1 :=
  (ofNat_toNat32 _).symm

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop extends VG.Proof.Scrypt.X86.RoMix.Base s₀ s where
  scf : Frame [VG.Proof.Scrypt.X86.RoMix.scR s₀] s₀.mem s.mem
  saved : VG.Proof.Scrypt.X86.RoMix.Saved s₀ s.mem
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀)
  ecx : s.gpr .ecx = 1
  edx : s.gpr .edx = BitVec.ofNat 32 (2 * VG.Proof.Scrypt.X86.RoMix.vl s₀)

theorem dbl32 (x : BitVec 32) : x + x = BitVec.ofNat 32 (2 * x.toNat) := by
  conv_lhs => rw [ofNat_toNat32 x]
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) : WP isa (.block rmPrologue) s₀ (VG.Proof.Scrypt.X86.RoMix.P1 s₀) := by
  rw [VG.Proof.Scrypt.X86.RoMix.prologue_eq]
  refine VG.Proof.Scrypt.X86.RoMix.save_ok hp fun s₁ g hrd hwr hf hsv => ?_
  have b₁ : VG.Proof.Scrypt.X86.RoMix.Base s₀ s₁ := ⟨hrd, hwr, g _ (by decide), hf.mono (by simp)⟩
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 1) hp b₁ (by omega) fun a ua => ?_
  refine wp_movi fun b ub => ?_
  have bb : VG.Proof.Scrypt.X86.RoMix.Base s₀ b := (b₁.upd ua (by decide)).upd ub (by decide)
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 3) hp bb (by omega) fun c uc => wp_add fun d ud => WP.block_nil ?_
  have bc := bb.upd uc (by decide)
  refine ⟨bc.upd ud (by decide), by rw [ud.mem, uc.mem, ub.mem, ua.mem]; exact hf,
    by rw [ud.mem, uc.mem, ub.mem, ua.mem]; exact hsv, ?_, ?_, ?_⟩
  · rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr, VG.Proof.Scrypt.X86.RoMix.toNat_rr]
  · rw [ud.other _ (by decide), uc.other _ (by decide), ub.gpr]
  · rw [ud.gpr, uc.gpr, VG.Proof.Scrypt.X86.RoMix.dbl32]

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop extends VG.Proof.Scrypt.X86.RoMix.Base s₀ s where
  scf : Frame [VG.Proof.Scrypt.X86.RoMix.scR s₀] s₀.mem s.mem
  saved : VG.Proof.Scrypt.X86.RoMix.Saved s₀ s.mem
  ecx : s.gpr .ecx = BitVec.ofNat 32 (2 * VG.Proof.Scrypt.X86.RoMix.NN s₀)

theorem nloop_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.P1 s₀ s) : WP isa nLoop s (VG.Proof.Scrypt.X86.RoMix.N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have e2 : VG.Proof.Scrypt.X86.RoMix.rr s₀ * 2 ^ (e + 1) = 2 * VG.Proof.Scrypt.X86.RoMix.vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * VG.Proof.Scrypt.X86.RoMix.vl s₀ < 2 ^ 32 := by have := VG.Proof.Scrypt.X86.RoMix.vl_mul hp; omega
  refine WP.mono (VG.Proof.Scrypt.X86.RoMix.nLoop_ok (r := VG.Proof.Scrypt.X86.RoMix.rr s₀) (e := e) hp.pos (by omega) h.eax h.ecx
    (by rw [h.edx, e2])) fun t ⟨rd, wr, mem, oth, r1⟩ => ?_
  exact ⟨⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [oth _ (by decide) (by decide), h.esp],
    by rw [mem]; exact h.frame⟩, by rw [mem]; exact h.scf, by rw [mem]; exact h.saved,
    by rw [r1, he, Nat.pow_succ, Nat.mul_comm]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Scrypt.X86.RoMix.Base s₀ s where
  i_le : i ≤ VG.Proof.Scrypt.X86.RoMix.NN s₀
  ebx : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i)
  esi : s.gpr .esi = VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀)
  saved : VG.Proof.Scrypt.X86.RoMix.Saved s₀ s.mem
  x : bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) i (VG.Proof.Scrypt.X86.RoMix.B s₀)
  done : ∀ k < i, bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86.RoMix.B s₀)

theorem setup2_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.N1 s₀ s) :
    WP isa (.block rmSetup) s (VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ 0) := by
  have lt := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  have n1 := VG.Proof.Scrypt.X86.RoMix.NN_pos hp
  have : 2 * VG.Proof.Scrypt.X86.RoMix.NN s₀ < 2 ^ 32 := by
    have : 2 * VG.Proof.Scrypt.X86.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * VG.Proof.Scrypt.X86.RoMix.NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_shr (by decide) fun t1 u1 => wp_mov fun t2 u2 => wp_mov fun t3 u3 => ?_
  have hd : t1.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀) := by
    rw [u1.gpr, h.ecx, VG.Proof.Scrypt.X86.RoMix.shr_ofNat32 _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  have b3 : VG.Proof.Scrypt.X86.RoMix.Base s₀ t3 := ((h.toBase.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 2) hp b3 (by omega) fun t4 u4 => WP.block_nil ?_
  have hm : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨b3.upd u4 (by decide), Nat.zero_le _, ?_, ?_, ?_, by rw [hm]; exact h.saved, ?_,
    fun k hk => absurd hk (by omega)⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hd, Nat.sub_zero]
  · rw [u4.gpr]; simp
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hd]
  · rw [hm]
    refine frame_bytesAt h.scf (fun r hr => ?_) (by have := VG.Proof.Scrypt.X86.RoMix.r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (VG.Proof.Scrypt.X86.RoMix.b_sub' (s₀ := s₀))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

theorem b_in {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86.RoMix.scA s₀) 128 := by
  rw [hp.wr]
  refine InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- A block that may be the source of a call of `vg_scrypt_blockmix` into `b`. -/
structure SrcOK (s₀ : State) (A : BitVec 32) : Prop where
  b : Region.Disjoint ⟨A.setWidth 64, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86.RoMix.bA s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩
  w : Region.Disjoint ⟨A.setWidth 64, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, 128⟩
  stk : (VG.Proof.Scrypt.X86.RoMix.stkR s₀).Disjoint ⟨A.setWidth 64, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩
  nw : A.toNat + 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ ≤ 2 ^ 32
  inr : InRegions (s₀.rd ++ s₀.wr) (A.setWidth 64) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)

/-- The call's memory frame: `b`, the block-mix working space and the stack. -/
abbrev cfr (s₀ : State) : List Region := [⟨VG.Proof.Scrypt.X86.RoMix.bA s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, 128⟩, VG.Proof.Scrypt.X86.RoMix.stkR s₀]

/-- Making the call, with its arguments set. -/
theorem bmFrame_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State}
    {A : BitVec 32} (hA : VG.Proof.Scrypt.X86.RoMix.SrcOK s₀ A) (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) (hsi : s.gpr .esi = A)
    (hax : s.gpr .eax = VG.Proof.Scrypt.X86.RoMix.sc s₀) (hcx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀)) (hdx : s.gpr .edx = VG.Proof.Scrypt.X86.RoMix.bP s₀)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀) s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) =
        blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀) (bytesAt s.mem (A.setWidth 64) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)) → Q s') :
    WP isa (.frame (.push [.eax, .ecx, .edx, .ecx, .esi]) (.call "vg_scrypt_blockmix" c) (.pop .eax 5))
      s Q := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have hsub : Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.scA s₀, 128⟩ (VG.Proof.Scrypt.X86.RoMix.scR s₀) := VG.Proof.Scrypt.X86.RoMix.w_sub
  exact hS s A (VG.Proof.Scrypt.X86.RoMix.bP s₀) (VG.Proof.Scrypt.X86.RoMix.sc s₀) (VG.Proof.Scrypt.X86.RoMix.rr s₀) hsi hcx hdx hax hp.pos lt
    ((hp.b_s.sub_left VG.Proof.Scrypt.X86.RoMix.b_sub').sub_right hsub) hA.b hA.w hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.esp]; exact hp.sp_lo) (by rw [h.esp]; exact hA.stk)
    (by rw [h.esp]; exact hp.stk_b.sub_right VG.Proof.Scrypt.X86.RoMix.b_sub') (by rw [h.esp]; exact hp.stk_s.sub_right hsub)
    (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact VG.Proof.Scrypt.X86.RoMix.b_in hp) (by rw [h.wr]; exact VG.Proof.Scrypt.X86.RoMix.w_in hp)
    Q fun s' hrd hwr hcs hf hb => hQ s' hrd hwr hcs (by rw [h.esp] at hf; exact hf) hb

/-- Setting up the arguments of the call. -/
theorem bmArgs_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Scrypt.X86.RoMix.Base s₀ s' → s'.mem = s.mem → (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.gpr .eax = VG.Proof.Scrypt.X86.RoMix.sc s₀ → s'.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀) → s'.gpr .edx = VG.Proof.Scrypt.X86.RoMix.bP s₀ → Q s') :
    WP isa (.block bmArgs) s Q := by
  unfold bmArgs
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 4) hp h (by omega) fun a ua => ?_
  have ba := h.upd ua (by decide)
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 1) hp ba (by omega) fun b ub => ?_
  have bb := ba.upd ub (by decide)
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 0) hp bb (by omega) fun d ud => WP.block_nil ?_
  exact k d (bb.upd ud (by decide)) (by rw [ud.mem, ub.mem, ua.mem])
    (fun r h1 h2 h3 => by rw [ud.other _ h3, ub.other _ h2, ua.other _ h1])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr]) (by rw [ud.other _ (by decide),
      ub.gpr, VG.Proof.Scrypt.X86.RoMix.toNat_rr]) ud.gpr

/-- Setting up the arguments and making the call, with `esi = A`. -/
theorem bm_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State}
    {A : BitVec 32} (hA : VG.Proof.Scrypt.X86.RoMix.SrcOK s₀ A) (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) (hsi : s.gpr .esi = A) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀) s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) =
        blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀) (bytesAt s.mem (A.setWidth 64) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)) → Q s') :
    WP isa (blockMixTo c) s Q := by
  unfold blockMixTo
  refine WP.seq (VG.Proof.Scrypt.X86.RoMix.bmArgs_ok hp h fun d bd em k hax hcx hdx => ?_)
  refine VG.Proof.Scrypt.X86.RoMix.bmFrame_ok hS hp hA bd (by rw [k _ (by decide) (by decide) (by decide), hsi]) hax hcx hdx
    fun s' hrd hwr hcs hf hb => hQ s' (by rw [hrd, bd.rd, h.rd]) (by rw [hwr, bd.wr, h.wr])
      (fun r hr => by
        rw [hcs r hr]
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact k _ (by decide) (by decide) (by decide))
      (by rw [em] at hf; exact hf) (by rw [em] at hb; exact hb)

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀)
include hp

theorem vAt_in {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) := by
  rw [hp.wr]
  have e := VG.Proof.Scrypt.X86.RoMix.vl_mul hp
  have := VG.Proof.Scrypt.X86.RoMix.v_le hi
  have lt := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

/-- `(V[i]'(by omega))` and the parts of `scratch` we use. -/
theorem vAt_b {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : Region.Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86.RoMix.bR s₀) :=
  hp.b_v.symm.sub_left (VG.Proof.Scrypt.X86.RoMix.vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : Region.Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86.RoMix.scR s₀) :=
  hp.v_s.sub_left (VG.Proof.Scrypt.X86.RoMix.vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : (VG.Proof.Scrypt.X86.RoMix.stkR s₀).Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ :=
  hp.stk_v.sub_right (VG.Proof.Scrypt.X86.RoMix.vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀) m m') : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Scrypt.X86.RoMix.bR s₀, by simp, VG.Proof.Scrypt.X86.RoMix.b_sub'⟩
    · exact ⟨VG.Proof.Scrypt.X86.RoMix.scR s₀, by simp, VG.Proof.Scrypt.X86.RoMix.w_sub⟩
    · exact ⟨VG.Proof.Scrypt.X86.RoMix.stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `(V[k]'(by omega))`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀) m m') {k : Nat} (hk : k < VG.Proof.Scrypt.X86.RoMix.NN s₀) :
    bytesAt m' (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = bytesAt m (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := VG.Proof.Scrypt.X86.RoMix.r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (VG.Proof.Scrypt.X86.RoMix.vAt_b hp hk).sub_right VG.Proof.Scrypt.X86.RoMix.b_sub'
  · exact (VG.Proof.Scrypt.X86.RoMix.vAt_s hp hk).sub_right VG.Proof.Scrypt.X86.RoMix.w_sub
  · exact (VG.Proof.Scrypt.X86.RoMix.vAt_stk hp hk).symm

theorem call_saved {m m' : Mem} (hf : Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀) m m') (h : VG.Proof.Scrypt.X86.RoMix.Saved s₀ m) : VG.Proof.Scrypt.X86.RoMix.Saved s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (VG.Proof.Scrypt.X86.RoMix.keep_b hp).sub_right VG.Proof.Scrypt.X86.RoMix.b_sub'
    · exact VG.Proof.Scrypt.X86.RoMix.keep_w
    · exact VG.Proof.Scrypt.X86.RoMix.keep_stk hp

theorem srcOK_v {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) : VG.Proof.Scrypt.X86.RoMix.SrcOK s₀ (VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i) := by
  have e := VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hi
  exact ⟨by rw [e]; exact (VG.Proof.Scrypt.X86.RoMix.vAt_b hp hi).sub_right VG.Proof.Scrypt.X86.RoMix.b_sub', by rw [e]; exact (VG.Proof.Scrypt.X86.RoMix.vAt_s hp hi).sub_right VG.Proof.Scrypt.X86.RoMix.w_sub,
    by rw [e]; exact VG.Proof.Scrypt.X86.RoMix.vAt_stk hp hi, VG.Proof.Scrypt.X86.RoMix.vAt_nw hp hi, by rw [e]; exact InRegions.right (VG.Proof.Scrypt.X86.RoMix.vAt_in hp hi)⟩

theorem t_b : Region.Disjoint ⟨VG.Proof.Scrypt.X86.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86.RoMix.bA s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩ :=
  (hp.b_s.symm.sub_left (VG.Proof.Scrypt.X86.RoMix.t_sub hp)).sub_right VG.Proof.Scrypt.X86.RoMix.b_sub'

theorem t_in : InRegions s₀.wr (VG.Proof.Scrypt.X86.RoMix.tP s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem srcOK_t : VG.Proof.Scrypt.X86.RoMix.SrcOK s₀ (VG.Proof.Scrypt.X86.RoMix.tP32 s₀) := by
  have e := VG.Proof.Scrypt.X86.RoMix.t_addr hp
  exact ⟨by rw [e]; exact VG.Proof.Scrypt.X86.RoMix.t_b hp, by rw [e]; exact VG.Proof.Scrypt.X86.RoMix.t_w hp,
    by rw [e]; exact hp.stk_s.sub_right (VG.Proof.Scrypt.X86.RoMix.t_sub hp), VG.Proof.Scrypt.X86.RoMix.t_nw hp,
    by rw [e]; exact InRegions.right (VG.Proof.Scrypt.X86.RoMix.t_in hp)⟩

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀) (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) m₃)
    (b₃ : bytesAt m₃ (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)
      (bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i)
        (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) :
    Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem m₃ ∧ VG.Proof.Scrypt.X86.RoMix.Saved s₀ m₃ ∧
    bytesAt m₃ (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) (i + 1) (VG.Proof.Scrypt.X86.RoMix.B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86.RoMix.B s₀) := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have hl : (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)).length = 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i)
      (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) i (VG.Proof.Scrypt.X86.RoMix.B s₀) := by
    have := bytesAt_writeBytes_self s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))
      (by rw [hl]; omega)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩] s.mem
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s.mem
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86.RoMix.vR s₀, by simp, VG.Proof.Scrypt.X86.RoMix.vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (VG.Proof.Scrypt.X86.RoMix.call_frame f₃), VG.Proof.Scrypt.X86.RoMix.call_saved hp f₃ (h.saved.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.Scrypt.X86.RoMix.keep_v hp).sub_right (VG.Proof.Scrypt.X86.RoMix.vAt_sub hp hi)
  · rw [VG.Proof.Scrypt.X86.RoMix.call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact VG.Proof.Scrypt.X86.RoMix.vAt_disj hp (by omega) hi hki) (by omega)]
      exact h.done k (by omega)

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i + BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128) = VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ (i + 1) := by
  show _ = VG.Proof.Scrypt.X86.RoMix.vP s₀ + BitVec.ofNat 32 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * (i + 1))
  rw [add32, Nat.mul_succ (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) i, Nat.mul_comm (VG.Proof.Scrypt.X86.RoMix.rr s₀) 128]

theorem b_word {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {k : Nat} (hk : k < 8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Scrypt.X86.RoMix.bA s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  have := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.bR s₀) (by simp) (contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {i k : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) (hk : k < 8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) :
    InRegions s₀.wr ((VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
  rw [hp.wr, VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hi]
  have e := VG.Proof.Scrypt.X86.RoMix.vl_mul hp
  have := VG.Proof.Scrypt.X86.RoMix.v_le hi
  have lt := VG.Proof.Scrypt.X86.RoMix.v_lt hp
  show InRegions _ (VG.Proof.Scrypt.X86.RoMix.vA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * i) + BitVec.ofNat 64 (16 * k)) 16
  rw [add_ofNat]
  exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

theorem t_word {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {k : Nat} (hk : k < 8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) :
    InRegions s₀.wr ((VG.Proof.Scrypt.X86.RoMix.tP32 s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
  have := hp.s_nw
  rw [hp.wr, VG.Proof.Scrypt.X86.RoMix.t_addr hp, add_ofNat]
  exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem mul8 (s₀ : State) :
    BitVec.ofNat 32 ((VG.X86.arg s₀ 1).toNat * (8 : BitVec 32).toNat) = BitVec.ofNat 32 (8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) := by
  rw [show (8 : BitVec 32).toNat = 8 from rfl, Nat.mul_comm]

theorem mul128 (s₀ : State) :
    BitVec.ofNat 32 ((VG.X86.arg s₀ 1).toNat * (128 : BitVec 32).toNat) = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128) := by
  rw [show (128 : BitVec 32).toNat = 128 from rfl]

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {i : Nat}
    (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀)) := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have pos := hp.pos
  have hN := VG.Proof.Scrypt.X86.RoMix.NN_lt hp
  have hb := hp.b_nw
  unfold step2
  refine WP.seq (timesR_ok (r := VG.X86.arg s₀ 1) (h.arg hp (i := 1) (by omega))
    (h.arg_in hp (i := 1) (by omega)) fun t e o mt rdt wrt => ?_)
  have bt : VG.Proof.Scrypt.X86.RoMix.Base s₀ t := ⟨rdt.trans h.rd, wrt.trans h.wr,
    (o _ (by decide) (by decide) (by decide)).trans h.esp, by rw [mt]; exact h.frame⟩
  refine wp_mov fun a ua => VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 0) hp (bt.upd ua (by decide)) (by omega) fun b ub =>
    wp_mov fun d ud => WP.block_nil ?_
  have bd : VG.Proof.Scrypt.X86.RoMix.Base s₀ d := ((bt.upd ua (by decide)).upd ub (by decide)).upd ud (by decide)
  have ke : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h2, ub.other _ h1, ua.other _ h3, o r h1 h2 h3]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem, mt]
  have e4 : 16 * (8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ := by omega
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.copyLoop_ok (src := VG.Proof.Scrypt.X86.RoMix.bP s₀) (dst := VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i) (n := 8 * VG.Proof.Scrypt.X86.RoMix.rr s₀)
    (by omega) (by omega) (by omega) (by rw [e4]; exact VG.Proof.Scrypt.X86.RoMix.vAt_nw hp hi)
    (by rw [ud.other _ (by decide), ub.gpr])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), o _ (by decide) (by decide)
      (by decide), h.esi])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, e, VG.Proof.Scrypt.X86.RoMix.mul8 s₀])
    (fun k hk => by rw [bd.rd, bd.wr]; exact VG.Proof.Scrypt.X86.RoMix.b_word hp hk)
    (fun k hk => by rw [bd.wr]; exact VG.Proof.Scrypt.X86.RoMix.v_word hp hi hk)
    (by rw [e4, VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hi]; exact (VG.Proof.Scrypt.X86.RoMix.vAt_b hp hi).symm.sub_left VG.Proof.Scrypt.X86.RoMix.b_sub'))
    fun t' ⟨rdt', wrt', gt', mt'⟩ => ?_)
  rw [hme, e4, VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hi] at mt'
  have kt : ∀ r ∈ calleeSaved, r ≠ .edi → t'.gpr r = s.gpr r := fun r hr h4 => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h4 | rw [gt' _ (by decide) (by decide) (by decide) (by decide),
        ke _ (by decide) (by decide) (by decide)]
  have ft : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem t'.mem := by
    rw [mt']
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨VG.Proof.Scrypt.X86.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [bytesAt_length]; exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86.RoMix.vR s₀, by simp, VG.Proof.Scrypt.X86.RoMix.vAt_sub hp hi⟩
  have bt' : VG.Proof.Scrypt.X86.RoMix.Base s₀ t' := ⟨by rw [rdt', bd.rd], by rw [wrt', bd.wr],
    by rw [kt _ (by simp [calleeSaved]) (by decide), h.esp], ft⟩
  refine WP.seq (VG.Proof.Scrypt.X86.RoMix.bm_ok hS hp (VG.Proof.Scrypt.X86.RoMix.srcOK_v hp hi) bt' (by rw [kt _ (by simp [calleeSaved]) (by decide), h.esi])
    fun s4 rd4 wr4 cs4 f4 b4 => ?_)
  rw [mt'] at f4 b4
  rw [VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hi] at b4
  obtain ⟨F, K, X, D⟩ := VG.Proof.Scrypt.X86.RoMix.mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, r ≠ .edi → s4.gpr r = s.gpr r := fun r hr h4 => by
    rw [cs4 r hr, kt r hr h4]
  have b4' : VG.Proof.Scrypt.X86.RoMix.Base s₀ s4 := ⟨by rw [rd4, bt'.rd], by rw [wr4, bt'.wr],
    by rw [k4 _ (by simp [calleeSaved]) (by decide), h.esp], F⟩
  refine timesR_ok (r := VG.X86.arg s₀ 1) (b4'.arg hp (i := 1) (by omega))
    (b4'.arg_in hp (i := 1) (by omega)) fun t5 e5 o5 m5 rd5 wr5 => ?_
  refine wp_add fun s6 u6 => wp_subi fun s7 u7 z7 => WP.block_nil ?_
  have e3 : s6.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i) := by
    rw [u6.other _ (by decide), o5 _ (by decide) (by decide) (by decide),
      k4 _ (by simp [calleeSaved]) (by decide), h.ebx]
  have m7 : s7.mem = s4.mem := by rw [u7.mem, u6.mem, m5]
  refine ⟨⟨⟨by rw [u7.rd, u6.rd, rd5, b4'.rd], by rw [u7.wr, u6.wr, wr5, b4'.wr],
    by rw [u7.other _ (by decide), u6.other _ (by decide), o5 _ (by decide) (by decide) (by decide),
      b4'.esp], by rw [m7]; exact F⟩, by omega, by rw [u7.gpr, e3, dec_count hi], ?_, ?_,
    by rw [m7]; exact K, by rw [m7]; exact X, by rw [m7]; exact D⟩, by rw [z7, e3, dec_z hi hN]⟩
  · rw [u7.other _ (by decide), u6.gpr, o5 _ (by decide) (by decide) (by decide), e5,
      k4 _ (by simp [calleeSaved]) (by decide), h.esi, VG.Proof.Scrypt.X86.RoMix.mul128 s₀, VG.Proof.Scrypt.X86.RoMix.vAt_succ]
  · rw [u7.other _ (by decide), u6.other _ (by decide), o5 _ (by decide) (by decide) (by decide),
      k4 _ (by simp [calleeSaved]) (by decide), h.ebp]

theorem loop2_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State}
    (h : VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀)) :=
  count_loop (VG.Proof.Scrypt.X86.RoMix.NN_pos hp) (VG.Proof.Scrypt.X86.RoMix.Inv2 s₀) (fun _ hi _ h => VG.Proof.Scrypt.X86.RoMix.step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Scrypt.X86.RoMix.Base s₀ s where
  i_le : i ≤ VG.Proof.Scrypt.X86.RoMix.NN s₀
  ebx : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀)
  saved : VG.Proof.Scrypt.X86.RoMix.Saved s₀ s.mem
  v : ∀ k < VG.Proof.Scrypt.X86.RoMix.NN s₀, bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86.RoMix.B s₀)
  x : (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)) (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i)
    (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))).1 = roMix (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)) (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i)
    (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)).drop i

theorem mid_ok {s₀ : State} {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s) :
    WP isa (.block rmMid) s (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ 0) := by
  unfold rmMid
  refine wp_mov fun b ub => WP.block_nil ?_
  have hm : b.mem = s.mem := ub.mem
  refine ⟨h.toBase.upd ub (by decide), Nat.zero_le _, by rw [ub.gpr, h.ebp]; rfl,
    by rw [ub.other _ (by decide), h.ebp], by rw [hm]; exact h.saved,
    fun k hk => by rw [hm]; exact h.done k hk, ?_, ?_⟩
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (VG.Proof.Scrypt.X86.RoMix.rr s₀) (bytesAt m (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)) % VG.Proof.Scrypt.X86.RoMix.NN s₀

theorem jOf_lt {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (m : Mem) : VG.Proof.Scrypt.X86.RoMix.jOf s₀ m < VG.Proof.Scrypt.X86.RoMix.NN s₀ :=
  Nat.mod_lt _ (VG.Proof.Scrypt.X86.RoMix.NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (m : Mem) :
    m.readW (VG.Proof.Scrypt.X86.RoMix.bA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ - 64)) 32 &&& BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - 1) =
      BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := VG.Proof.Scrypt.X86.RoMix.NN_lt hp
  have he' : e ≤ 32 := by
    by_contra hc
    have : 2 ^ 32 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Scrypt.X86.RoMix.jOf_lt hp m; omega), he, VG.Proof.Scrypt.X86.RoMix.and_mask32 _ he',
    VG.Proof.Scrypt.X86.RoMix.jOf, he, VG.Proof.Scrypt.X86.RoMix.integerify_mod32 _ _ hp.pos he']

theorem jOf_lt32 {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (m : Mem) : VG.Proof.Scrypt.X86.RoMix.jOf s₀ m < 2 ^ 32 := by
  have := VG.Proof.Scrypt.X86.RoMix.jOf_lt hp m; have := VG.Proof.Scrypt.X86.RoMix.NN_lt hp; omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame (VG.Proof.Scrypt.X86.RoMix.cfr s₀)
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))
        (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ (VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem)) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)
      (bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))
        (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ (VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem)) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)))) (VG.Proof.Scrypt.X86.RoMix.tP s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))) :
    Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem m₄ ∧ VG.Proof.Scrypt.X86.RoMix.Saved s₀ m₄ ∧
    (∀ k < VG.Proof.Scrypt.X86.RoMix.NN s₀, bytesAt m₄ (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86.RoMix.B s₀)) ∧
    (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)) (VG.Proof.Scrypt.X86.RoMix.NN s₀ - (i + 1))
      (bytesAt m₄ (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))).1 = roMix (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀) ∧
    (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)) (VG.Proof.Scrypt.X86.RoMix.NN s₀ - (i + 1))
      (bytesAt m₄ (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)).drop (i + 1) := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have hj := VG.Proof.Scrypt.X86.RoMix.jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀))
    (bytesAt s.mem (VG.Proof.Scrypt.X86.RoMix.vAt s₀ (VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem)) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀)) with hT
  have hl : T.length = 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.tP s₀) T) (VG.Proof.Scrypt.X86.RoMix.tP s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (VG.Proof.Scrypt.X86.RoMix.tP s₀) T (by rw [hl]; omega)
    rwa [hl] at this
  have f₂ : Frame [⟨VG.Proof.Scrypt.X86.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86.RoMix.tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86.RoMix.scR s₀, by simp, VG.Proof.Scrypt.X86.RoMix.t_sub hp⟩
  have hv : ∀ k < VG.Proof.Scrypt.X86.RoMix.NN s₀, bytesAt m₄ (VG.Proof.Scrypt.X86.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86.RoMix.B s₀) :=
    fun k hk => by
      rw [VG.Proof.Scrypt.X86.RoMix.call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (VG.Proof.Scrypt.X86.RoMix.vAt_s hp hk).sub_right (VG.Proof.Scrypt.X86.RoMix.t_sub hp)) (by omega)]
      exact h.v k hk
  have e : VG.Proof.Scrypt.X86.RoMix.NN s₀ - i = VG.Proof.Scrypt.X86.RoMix.NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (VG.Proof.Scrypt.X86.RoMix.call_frame f₄),
    VG.Proof.Scrypt.X86.RoMix.call_saved hp f₄ (h.saved.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Scrypt.X86.RoMix.keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

/-- `jBlock`: `eax = j`, `edi = 128 r`. -/
theorem j_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀)) :
    WP isa (.block jBlock) s fun s' => s'.gpr .eax = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem) ∧
      s'.gpr .edi = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ VG.Proof.Scrypt.X86.RoMix.Base s₀ s' ∧
      s'.mem = s.mem := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have := hp.pos
  have hb := hp.b_nw
  have n1 := VG.Proof.Scrypt.X86.RoMix.NN_pos hp
  unfold jBlock
  refine timesR_ok (r := VG.X86.arg s₀ 1) (h.arg hp (i := 1) (by omega))
    (h.arg_in hp (i := 1) (by omega)) fun t e o mt rdt wrt => ?_
  rw [VG.Proof.Scrypt.X86.RoMix.mul128] at e
  have bt : VG.Proof.Scrypt.X86.RoMix.Base s₀ t := ⟨rdt.trans h.rd, wrt.trans h.wr,
    (o _ (by decide) (by decide) (by decide)).trans h.esp, by rw [mt]; exact h.frame⟩
  refine wp_mov fun a ua => VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 0) hp (bt.upd ua (by decide)) (by omega) fun b ub =>
    wp_add fun c uc => wp_subi fun d ud _ => ?_
  have bd : VG.Proof.Scrypt.X86.RoMix.Base s₀ d :=
    (((bt.upd ua (by decide)).upd ub (by decide)).upd uc (by decide)).upd ud (by decide)
  have ed : d.gpr .eax = VG.Proof.Scrypt.X86.RoMix.bP s₀ + BitVec.ofNat 32 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ - 64) := by
    rw [ud.gpr, uc.gpr, ub.other _ (by decide), ua.other _ (by decide), e, ub.gpr, BitVec.add_comm,
      sub32 _ (by omega), Nat.mul_comm]
  have md : d.mem = s.mem := by rw [ud.mem, uc.mem, ub.mem, ua.mem, mt]
  refine wp_movm (a := VG.Proof.Scrypt.X86.RoMix.bA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ - 64))
    (by rw [ea_at, ed, addr_zero, addr_add (by omega)])
    (by rw [bd.rd, bd.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.RoMix.bR s₀) (by simp) (contains_off (by omega) (by omega)))
    fun f uf => wp_mov fun g ug => wp_subi fun i ui _ => wp_and fun l ul => WP.block_nil ?_
  have ki : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → l.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [ul.other _ h1, ui.other _ h2, ug.other _ h2, uf.other _ h1, ud.other _ h1, uc.other _ h1,
        ub.other _ h2, ua.other _ h4, o r h1 h2 h3]
  refine ⟨?_, ?_, ki, ?_, by rw [ul.mem, ui.mem, ug.mem, uf.mem, md]⟩
  · rw [ul.gpr, ui.other _ (by decide), ug.other _ (by decide), uf.gpr, ui.gpr, ug.gpr,
      uf.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), o _ (by decide) (by decide) (by decide), hbp, ofNat_pred32 n1, md,
      VG.Proof.Scrypt.X86.RoMix.jOf_eq hp]
  · rw [ul.other _ (by decide), ui.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr, e]
  · exact (((bd.upd uf (by decide)).upd ug (by decide)).upd ui (by decide)).upd ul (by decide)

/-- `vjBlock`: `ecx = (V[j]'(by omega))`, `eax = X`, `edx = T`, `edi = 8 r`. -/
theorem vj_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {j : Nat} (hj : j < VG.Proof.Scrypt.X86.RoMix.NN s₀)
    (hax : s.gpr .eax = BitVec.ofNat 32 j) (hdi : s.gpr .edi = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128)) :
    WP isa (.block vjBlock) s fun s' => s'.gpr .ecx = VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ j ∧ s'.gpr .eax = VG.Proof.Scrypt.X86.RoMix.bP s₀ ∧
      s'.gpr .edx = VG.Proof.Scrypt.X86.RoMix.tP32 s₀ ∧ s'.gpr .edi = BitVec.ofNat 32 (8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ VG.Proof.Scrypt.X86.RoMix.Base s₀ s' ∧
      s'.mem = s.mem := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have hN := VG.Proof.Scrypt.X86.RoMix.NN_lt hp
  unfold vjBlock
  refine wp_mul fun a ea oa ma rda wra => ?_
  have ba : VG.Proof.Scrypt.X86.RoMix.Base s₀ a := ⟨rda.trans h.rd, wra.trans h.wr, (oa _ (by decide) (by decide)).trans h.esp,
    by rw [ma]; exact h.frame⟩
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 2) hp ba (by omega) fun b ub => wp_add fun c uc =>
    VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 0) hp ((ba.upd ub (by decide)).upd uc (by decide)) (by omega) fun d ud => ?_
  have bd := ((ba.upd ub (by decide)).upd uc (by decide)).upd ud (by decide)
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 4) hp bd (by omega) fun f uf => wp_addi fun g ug => wp_shr (by decide) fun l ul =>
    WP.block_nil ?_
  have eax : a.gpr .eax = BitVec.ofNat 32 (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ * j) := by
    rw [ea, hax, hdi, Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega),
      Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega), Nat.mul_comm, Nat.mul_comm (VG.Proof.Scrypt.X86.RoMix.rr s₀) 128]
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩
  · rw [ul.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.gpr, ub.other _ (by decide), eax]
  · rw [ul.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide), ud.gpr]
  · rw [ul.other _ (by decide), ug.gpr, uf.gpr]; rfl
  · rw [ul.gpr, ug.other _ (by decide), uf.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), oa _ (by decide) (by decide), hdi,
      VG.Proof.Scrypt.X86.RoMix.shr_ofNat32 _ (by omega)]
    congr 1; omega
  · rw [ul.other _ h4, ug.other _ h3, uf.other _ h3, ud.other _ h1, uc.other _ h2, ub.other _ h2,
      oa _ h1 h3]
  · exact ((bd.upd uf (by decide)).upd ug (by decide)).upd ul (by decide)
  · rw [ul.mem, ug.mem, uf.mem, ud.mem, uc.mem, ub.mem, ma]

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {i : Nat}
    (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀)) := by
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have pos := hp.pos
  have hN := VG.Proof.Scrypt.X86.RoMix.NN_lt hp
  have hj := VG.Proof.Scrypt.X86.RoMix.jOf_lt hp s.mem
  have hb := hp.b_nw
  have e4 : 16 * (8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀ := by omega
  unfold step3
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.j_ok hp h.toBase h.ebp) fun a ⟨aax, adi, oa, ba, ma⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.vj_ok hp ba hj aax adi) fun b ⟨bcx, bax, bdx, bdi, ob, bb, mb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.xorLoop_ok (x := VG.Proof.Scrypt.X86.RoMix.bP s₀) (y := VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ (VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem)) (d := VG.Proof.Scrypt.X86.RoMix.tP32 s₀)
    (n := 8 * VG.Proof.Scrypt.X86.RoMix.rr s₀) (by omega) (by omega) (by omega)
    (by rw [e4]; exact VG.Proof.Scrypt.X86.RoMix.vAt_nw hp hj) (by rw [e4]; exact VG.Proof.Scrypt.X86.RoMix.t_nw hp) bax bcx bdx bdi
    (fun k hk => by rw [bb.rd, bb.wr]; exact VG.Proof.Scrypt.X86.RoMix.b_word hp hk)
    (fun k hk => by rw [bb.rd, bb.wr]; exact InRegions.right (VG.Proof.Scrypt.X86.RoMix.v_word hp hj hk))
    (fun k hk => by rw [bb.wr]; exact VG.Proof.Scrypt.X86.RoMix.t_word hp hk)
    (by rw [e4, VG.Proof.Scrypt.X86.RoMix.t_addr hp]; exact VG.Proof.Scrypt.X86.RoMix.t_b hp)
    (by rw [e4, VG.Proof.Scrypt.X86.RoMix.t_addr hp, VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hj]; exact (VG.Proof.Scrypt.X86.RoMix.vAt_s hp hj).symm.sub_left (VG.Proof.Scrypt.X86.RoMix.t_sub hp)))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [mb, ma, e4, VG.Proof.Scrypt.X86.RoMix.t_addr hp, VG.Proof.Scrypt.X86.RoMix.vAt_addr hp hj] at mt
  have kt : ∀ r ∈ calleeSaved, r ≠ .edi → r ≠ .esi → t.gpr r = s.gpr r := fun r hr h4 h5 => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h4 | exact absurd rfl h5 |
      rw [gt _ (by decide) (by decide) (by decide) (by decide) (by decide),
        ob _ (by decide) (by decide) (by decide) (by decide), oa _ (by decide) (by decide) (by decide)
        (by decide)]
  have ft : Frame (VG.Proof.Scrypt.X86.RoMix.frs s₀) s₀.mem t.mem := by
    rw [mt]
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨VG.Proof.Scrypt.X86.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86.RoMix.rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
      exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86.RoMix.scR s₀, by simp, VG.Proof.Scrypt.X86.RoMix.t_sub hp⟩
  have bt : VG.Proof.Scrypt.X86.RoMix.Base s₀ t := ⟨by rw [rdt, bb.rd], by rw [wrt, bb.wr],
    by rw [kt _ (by simp [calleeSaved]) (by decide) (by decide), h.esp], ft⟩
  refine WP.seq (VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 4) hp bt (by omega) fun q uq => wp_addi fun q1 v1 => WP.block_nil ?_)
  have bq := (bt.upd uq (by decide)).upd v1 (by decide)
  have kq : ∀ r ∈ calleeSaved, r ≠ .edi → r ≠ .esi → q1.gpr r = s.gpr r := fun r hr h4 h5 => by
    rw [v1.other _ h5, uq.other _ h5, kt r hr h4 h5]
  refine WP.seq (VG.Proof.Scrypt.X86.RoMix.bm_ok hS hp (VG.Proof.Scrypt.X86.RoMix.srcOK_t hp) bq (by rw [v1.gpr, uq.gpr]; rfl)
    fun s4 rd4 wr4 cs4 f4 b4 => ?_)
  rw [v1.mem, uq.mem, mt] at f4 b4
  rw [VG.Proof.Scrypt.X86.RoMix.t_addr hp] at b4
  obtain ⟨F, K, V, X, J⟩ := VG.Proof.Scrypt.X86.RoMix.mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, r ≠ .edi → r ≠ .esi → s4.gpr r = s.gpr r := fun r hr h4 h5 => by
    rw [cs4 r hr, kq r hr h4 h5]
  refine wp_subi fun s5 u5 z5 => WP.block_nil ?_
  have e8 : s4.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i) := by
    rw [k4 _ (by simp [calleeSaved]) (by decide) (by decide), h.ebx]
  refine ⟨⟨⟨by rw [u5.rd, rd4, bq.rd], by rw [u5.wr, wr4, bq.wr],
    by rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]) (by decide) (by decide), h.esp],
    by rw [u5.mem]; exact F⟩, by omega, by rw [u5.gpr, e8, dec_count hi],
    by rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]) (by decide) (by decide), h.ebp],
    by rw [u5.mem]; exact K, by rw [u5.mem]; exact V, by rw [u5.mem]; exact X,
    by rw [u5.mem]; exact J⟩, by rw [z5, e8, dec_z hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State}
    (h : VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀)) :=
  count_loop (VG.Proof.Scrypt.X86.RoMix.NN_pos hp) (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀) (fun _ hi _ h => VG.Proof.Scrypt.X86.RoMix.step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem epilogue_eq : rmEpilogue =
    .mov .eax (.mem (at_ .esp 20)) :: (rmSaved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ []) :=
  rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  rw [VG.Proof.Scrypt.X86.RoMix.epilogue_eq]
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 4) hp h.toBase (by omega) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = VG.Proof.Scrypt.X86.RoMix.sc s₀ := u₁.gpr
  have ha := VG.Proof.Scrypt.X86.RoMix.rmSaved_addr s₀ hp
  refine Spill.restore_ok rmSaved (by decide) (fun p hp' => ?_)
    (by rw [e, u₁.mem]; exact h.saved.congr (fun p hp' => (ha p hp').symm) fun _ _ => rfl)
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, u₁.mem],
      u.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp])⟩
  rw [e, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr, ha p hp']
  exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.RoMix.in_s s₀ (by have := rmSaved_fits.1 p hp'; omega))

/-! ## The whole function -/

theorem correct {c : Prog isa} (hS : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Scrypt.roMixX86.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.loop2_ok hS hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.mid_ok h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.RoMix.loop3_ok hS hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86.RoMix.restore_ok hp h₆) fun s' ⟨hm', hg'⟩ => ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₆.frame.readW (r := VG.Proof.Scrypt.X86.RoMix.retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.ret_b, hp.ret_v, hp.ret_s, VG.Proof.Scrypt.X86.RoMix.ret_stk hp]
  · show bytesAt s'.mem (VG.Proof.Scrypt.X86.RoMix.bA s₀) (128 * VG.Proof.Scrypt.X86.RoMix.rr s₀) = roMix (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)
    rw [hm', ← h₆.x, Nat.sub_self]
    rfl

end VG.Proof.Scrypt.X86.RoMix

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.RoMixCT`. -/
section

/-!
# scryptROMix on x86 (32-bit): verified

`BlockMixSpec` of the verified `vg_scrypt_blockmix`, from its proof by
`WP.callWith`; then constant time, up to the indices `j`, as on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`): the taint analysis cannot follow the calls
(scryptBlockMix stores secrets through pointers into the middle of `y`, and
restores its caller's registers from memory), so we relate two runs piece by
piece (`RelCT`). Correctness determines our registers from the public
arguments, so they agree between the calls, where the taint analysis proves
each piece constant time, reading the pointers and `r` from the arguments,
which nothing writes; the calls are constant time by scryptBlockMix's own
proof (`RelCT.callWith`). In step 3, the address of `V[j]` depends on `j`,
which the contract declares public: the two runs compute the same `j`, since
both compute their indices in order (`Inv3.js`) and agree on the whole list.
The proof is written against a contract under which the code only reads its
arguments, and moved to the shared contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_addi wp_subi addr_toNat)
open VG.Proof.Scrypt.Memory (InRegions.right frame_bytesAt)

/-! ## The call of `vg_scrypt_blockmix` -/

theorem blockMix_nosp : NoSp Impl.Scrypt.X86.blockMix := NoSp.of_all (by decide +kernel)

theorem blockMix_stack : stackUse Impl.Scrypt.X86.blockMix = 12 := by decide +kernel

/-- The registers the call pushes, as its arguments. -/
abbrev bmRegs : List Reg := [.eax, .ecx, .edx, .ecx, .esi]

/-- The regions the callee may read and write. -/
def bmRd (E src : BitVec 32) (r : Nat) : List Region :=
  [⟨src.setWidth 64, r * 128⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
def bmWr (dst scr : BitVec 32) (r : Nat) : List Region :=
  [⟨dst.setWidth 64, r * 128⟩, ⟨scr.setWidth 64, 128⟩]

section
variable {s : State} {src dst scr : BitVec 32} {r : Nat} (h0 : s.gpr .esi = src)
  (h1 : s.gpr .ecx = BitVec.ofNat 32 r) (h2 : s.gpr .edx = dst) (h3 : s.gpr .eax = scr)
  (hlo : 36 ≤ (s.gpr .esp).toNat)
include h0 h1 h2 h3 hlo

theorem bm_args :
    VG.X86.arg (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry 0 = src ∧ VG.X86.arg (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry 1 = BitVec.ofNat 32 r ∧
    VG.X86.arg (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry 2 = dst ∧ VG.X86.arg (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry 3 = BitVec.ofNat 32 r ∧
    VG.X86.arg (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry 4 = scr := by
  have hrs : Reg.esp ∉ VG.Proof.Scrypt.X86.RoMix.bmRegs := by decide
  have fit : 4 * bmRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit hrs (by simp)] <;> simp [h0, h1, h2, h3]

/-- The callee's precondition, and the permissions it is given. -/
theorem bm_callPre (hr : 0 < r) (hlt : 128 * r < 2 ^ 32)
    (hds : Region.Disjoint ⟨dst.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩)
    (hsd : Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨dst.setWidth 64, 128 * r⟩)
    (hss : Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 32) (ndst : dst.toNat + 128 * r ≤ 2 ^ 32)
    (nscr : scr.toNat + 128 ≤ 2 ^ 32)
    (dsrc : (below (s.gpr .esp) 36).Disjoint ⟨src.setWidth 64, 128 * r⟩)
    (ddst : (below (s.gpr .esp) 36).Disjoint ⟨dst.setWidth 64, 128 * r⟩)
    (dscr : (below (s.gpr .esp) 36).Disjoint ⟨scr.setWidth 64, 128⟩)
    (isrc : InRegions (s.rd ++ s.wr) (src.setWidth 64) (128 * r))
    (idst : InRegions s.wr (dst.setWidth 64) (128 * r)) (iscr : InRegions s.wr (scr.setWidth 64) 128) :
    CallPre Proof.Scrypt.blockMixX86 VG.Proof.Scrypt.X86.RoMix.bmRegs (VG.Proof.Scrypt.X86.RoMix.bmRd (s.gpr .esp) src r) (VG.Proof.Scrypt.X86.RoMix.bmWr dst scr r) s := by
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  obtain ⟨a0, a1, a2, a3, a4⟩ := VG.Proof.Scrypt.X86.RoMix.bm_args h0 h1 h2 h3 hlo
  have eA : argAddr (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.Scrypt.X86.RoMix.bmRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  have b20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 36) := below_sub (by omega) hlo
  have r4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 36) := by
    have := below_inner (sp := s.gpr .esp) (a := 4) (b := 36) (k := 20) (by omega) hlo
    rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      bv_omega]
    exact this
  have s12 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 - 12, 12⟩ (below (s.gpr .esp) 36) := by
    intro a ha
    simp only [Region.Contains] at ha ⊢
    rw [Taint.sub_setWidth (by omega)] at ha ⊢
    have := (s.gpr .esp).isLt
    have hE : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := addr_toNat _
    generalize (s.gpr .esp).setWidth 64 = b at *
    bv_omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Scrypt.blockMixX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eSp, tr,
      VG.Proof.Scrypt.X86.RoMix.bmRd, VG.Proof.Scrypt.X86.RoMix.bmWr, eA]
    rw [c128] at *
    refine ⟨trivial, trivial, hds, hsd, hss, ddst.sub_left b20, dscr.sub_left b20, ddst.sub_left r4,
      dscr.sub_left r4, dsrc.sub_left s12, ddst.sub_left s12, dscr.sub_left s12, nsrc, ndst, nscr,
      ?_, ?_, trivial, hr⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨R, hR, hcn⟩
    simp only [VG.Proof.Scrypt.X86.RoMix.bmRd, VG.Proof.Scrypt.X86.RoMix.bmWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hR
    rw [c128] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · obtain ⟨R', hR', hc'⟩ := isrc
      refine InRegions_append_cons.mpr (.inr ⟨R', hR', ?_⟩)
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · exact InRegions_append_cons.mpr (.inl hcn)
    · obtain ⟨R', hR', hc'⟩ := idst
      refine InRegions_append_cons.mpr (.inr ⟨R', List.mem_append_right _ hR', ?_⟩)
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · obtain ⟨R', hR', hc'⟩ := iscr
      refine InRegions_append_cons.mpr (.inr ⟨R', List.mem_append_right _ hR', ?_⟩)
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
  · intro a n ⟨R, hR, hcn⟩
    simp only [VG.Proof.Scrypt.X86.RoMix.bmWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rw [c128] at hR
    rcases hR with rfl | rfl
    · obtain ⟨R', hR', hc'⟩ := idst
      refine ⟨R', List.mem_cons_of_mem _ hR', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · obtain ⟨R', hR', hc'⟩ := iscr
      refine ⟨R', List.mem_cons_of_mem _ hR', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega

end

theorem blockMixSpec : VG.Proof.Scrypt.X86.RoMix.BlockMixSpec Impl.Scrypt.X86.blockMix := by
  intro s src dst scr r h0 h1 h2 h3 hr hlt hds hsd hss nsrc ndst nscr hlo dsrc ddst dscr isrc idst iscr
    Q hQ
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  have hrs : Reg.esp ∉ VG.Proof.Scrypt.X86.RoMix.bmRegs := by decide
  have fit : 4 * bmRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨a0, a1, a2, -, -⟩ := VG.Proof.Scrypt.X86.RoMix.bm_args h0 h1 h2 h3 hlo
  have e36 : 4 * bmRegs.length + stackUse Impl.Scrypt.X86.blockMix + 4 = 36 := by
    rw [VG.Proof.Scrypt.X86.RoMix.blockMix_stack]; rfl
  refine WP.callWith (k := Proof.Scrypt.blockMixX86) BlockMix.blockMix_correct VG.Proof.Scrypt.X86.RoMix.blockMix_nosp (by simp) hrs
    (by rw [e36]; exact hlo)
    (VG.Proof.Scrypt.X86.RoMix.bm_callPre h0 h1 h2 h3 hlo hr hlt hds hsd hss nsrc ndst nscr dsrc ddst dscr isrc idst iscr)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [e36] at f'
  have hsE := callEntry_frame fit hrs
  rw [show 4 * bmRegs.length + 4 = 24 from rfl] at hsE
  simp only [Proof.Scrypt.blockMixX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂, tr]
    at post
  refine hQ s' rd' wr' cs' (f'.mono fun R hR => by simpa [VG.Proof.Scrypt.X86.RoMix.bmWr, c128] using hR) ?_
  rw [post]
  congr 1
  refine frame_bytesAt hsE (fun R hR => ?_) (by omega)
  simp only [List.mem_singleton] at hR; subst hR
  exact (dsrc.sub_left (below_sub (by omega) hlo)).symm

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 6, VG.X86.arg s₀ i = VG.X86.arg s₀' i

section
variable {s₀ s₀' : State} (hq : VG.Proof.Scrypt.X86.RoMix.PubEq s₀ s₀')
include hq

theorem PubEq.esp₀ : VG.Proof.Scrypt.X86.RoMix.esp₀ s₀ = VG.Proof.Scrypt.X86.RoMix.esp₀ s₀' := hq.esp
theorem PubEq.rr : VG.Proof.Scrypt.X86.RoMix.rr s₀ = VG.Proof.Scrypt.X86.RoMix.rr s₀' := by simp only [RoMix.rr, hq.args 1 (by omega)]
theorem PubEq.NN : VG.Proof.Scrypt.X86.RoMix.NN s₀ = VG.Proof.Scrypt.X86.RoMix.NN s₀' := by
  simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.args 1 (by omega), hq.args 3 (by omega)]
theorem PubEq.vAt32 (i : Nat) : VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i = VG.Proof.Scrypt.X86.RoMix.vAt32 s₀' i := by
  simp only [RoMix.vAt32, RoMix.vP, RoMix.rr, hq.args 1 (by omega), hq.args 2 (by omega)]
theorem PubEq.tP32 : VG.Proof.Scrypt.X86.RoMix.tP32 s₀ = VG.Proof.Scrypt.X86.RoMix.tP32 s₀' := by simp only [RoMix.tP32, RoMix.sc, hq.args 4 (by omega)]

end

/-- The taint state in which the registers `rs` and the arguments are public. -/
def τk (rs : List Reg) : VG.X86.Taint.T := { regs := .ofList rs, flags := false, argLen := 28 }

theorem wf_k {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (rs : List Reg) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) :
    VG.X86.Taint.Wf (VG.Proof.Scrypt.X86.RoMix.τk rs) s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by rw [h.esp]; exact hs, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [h.wr, hp.wr, h.esp, VG.Proof.Scrypt.X86.RoMix.τk, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_b hp.a_b
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_v hp.a_v
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_s hp.a_s

theorem Base.argW {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (argAddr s i) 32 = VG.X86.arg s₀ i :=
  h.arg hp hi

/-- Two runs agree on `esp`, the arguments and the registers `rs`. -/
theorem agree_k {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86.RoMix.PubEq s₀ s₀') {rs : List Reg}
    {s s' : State} (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) (h' : VG.Proof.Scrypt.X86.RoMix.Base s₀' s') (hr : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    VG.X86.Taint.Agree (VG.Proof.Scrypt.X86.RoMix.τk (.esp :: rs)) s s' := by
  have f₁ : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := by rw [h.esp]; exact hp.sp_fit
  have f₂ : (s'.gpr .esp).toNat + 28 ≤ 2 ^ 32 := by rw [h'.esp]; exact hp'.sp_fit
  refine ⟨⟨fun r hr' => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, VG.Proof.Scrypt.X86.RoMix.wf_k hp _ h, VG.Proof.Scrypt.X86.RoMix.wf_k hp' _ h',
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => by rw [h.esp, h'.esp, hq.esp₀], fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Scrypt.X86.RoMix.τk, RegSet.mem_ofList, List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · rw [h.esp, h'.esp, hq.esp₀]
    · exact hr r hr'
  · simp only [VG.Proof.Scrypt.X86.RoMix.τk] at hk
    rw [show VG.X86.Taint.depth (VG.Proof.Scrypt.X86.RoMix.τk (.esp :: rs)).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s'.mem _ (Nat.mod_lt _ (by omega)),
      h.argW hp (i := (k - 4) / 4) (by omega), h'.argW hp' (i := (k - 4) / 4) (by omega),
      hq.args _ (by omega)]

/-- The registers the pieces of an iteration keep: `ebx = q` and `ebp = N`. -/
structure KR (s₀ : State) (q : BitVec 32) (s : State) : Prop extends VG.Proof.Scrypt.X86.RoMix.Base s₀ s where
  ebx : s.gpr .ebx = q
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀)

/-- Whether an instruction writes none of `rs`. -/
def free (rs : List Reg) (i : Instr) : Bool := rs.all fun r => !Taint.clobbers i r

/-- Registers that code writing none of them keeps. -/
theorem exec_keeps {c : Prog isa} {rs : List Reg} (hc : c.allInstrs (VG.Proof.Scrypt.X86.RoMix.free rs) = true) {s s' : State}
    {t : List Leak} (he : Exec isa c s t s') : ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  intro r hr
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine Exec.gpr (fun i hi => ?_) he
  have := hc i hi
  simp only [VG.Proof.Scrypt.X86.RoMix.free, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this r hr

/-- `Base` survives code without calls that never writes `esp`. -/
theorem Base.exec {c : Prog isa} (hc : c.allInstrs (VG.Proof.Scrypt.X86.RoMix.free [.esp]) = true) (hn : c.noCalls = true)
    {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : VG.Proof.Scrypt.X86.RoMix.Base s₀ s) :
    VG.Proof.Scrypt.X86.RoMix.Base s₀ s' := by
  obtain ⟨rd, wr, f⟩ := Exec.regions he hn
  refine ⟨rd.trans h.rd, wr.trans h.wr, by rw [VG.Proof.Scrypt.X86.RoMix.exec_keeps hc he _ (by simp), h.esp],
    h.frame.trans (f.mono ?_)⟩
  rw [h.wr, hp.wr]; simp

/-- `KR` survives code without calls that writes none of `esp`, `ebx` and `ebp`. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs (VG.Proof.Scrypt.X86.RoMix.free [.esp, .ebx, .ebp]) = true)
    (hn : c.noCalls = true) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {q : BitVec 32} {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (h : VG.Proof.Scrypt.X86.RoMix.KR s₀ q s) : VG.Proof.Scrypt.X86.RoMix.KR s₀ q s' := by
  have k := VG.Proof.Scrypt.X86.RoMix.exec_keeps hc he
  obtain ⟨rd, wr, f⟩ := Exec.regions he hn
  exact ⟨⟨rd.trans h.rd, wr.trans h.wr, by rw [k _ (by simp), h.esp],
    h.frame.trans (f.mono (by rw [h.wr, hp.wr]; simp))⟩, by rw [k _ (by simp), h.ebx],
    by rw [k _ (by simp), h.ebp]⟩

/-- A relation that each run keeps, from what its own run does. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True)
    (hk : ∀ s s' t t' u u', P s s' → Exec isa c s t u → Exec isa c s' t' u' → F₁ u ∧ F₂ u') :
    RelCT isa P c fun u u' => F₁ u ∧ F₂ u' :=
  fun _ _ _ _ _ _ hp e e' => ⟨(h _ _ _ _ _ _ hp e e').1, hk _ _ _ _ _ _ hp e e'⟩

theorem RelCT.assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

theorem eval_zf {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map (!·) = _; rw [h]; rfl

/-! ## The call of `vg_scrypt_blockmix`, in two runs -/

section
variable {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86.RoMix.PubEq s₀ s₀')
include hp hp' hq

theorem call_rel {A A' : BitVec 32} (hA : VG.Proof.Scrypt.X86.RoMix.SrcOK s₀ A) (hA' : VG.Proof.Scrypt.X86.RoMix.SrcOK s₀' A') (hAA : A = A')
    {q q' : BitVec 32} :
    RelCT isa (fun s s' => (VG.Proof.Scrypt.X86.RoMix.KR s₀ q s ∧ s.gpr .esi = A) ∧ (VG.Proof.Scrypt.X86.RoMix.KR s₀' q' s' ∧ s'.gpr .esi = A'))
      (blockMixTo Impl.Scrypt.X86.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86.RoMix.KR s₀ q s ∧ s.gpr .esi = A) ∧ (VG.Proof.Scrypt.X86.RoMix.KR s₀' q' s' ∧ s'.gpr .esi = A') := by
  subst hAA
  have lt := VG.Proof.Scrypt.X86.RoMix.r_lt hp
  have er : VG.Proof.Scrypt.X86.RoMix.rr s₀' = VG.Proof.Scrypt.X86.RoMix.rr s₀ := hq.rr.symm
  have eb : VG.Proof.Scrypt.X86.RoMix.bP s₀' = VG.Proof.Scrypt.X86.RoMix.bP s₀ := (hq.args 0 (by omega)).symm
  have es : VG.Proof.Scrypt.X86.RoMix.sc s₀' = VG.Proof.Scrypt.X86.RoMix.sc s₀ := (hq.args 4 (by omega)).symm
  -- The arguments, set in each run.
  let F (t₀ : State) (q : BitVec 32) (s : State) : Prop :=
    VG.Proof.Scrypt.X86.RoMix.KR t₀ q s ∧ s.gpr .esi = A ∧ s.gpr .eax = VG.Proof.Scrypt.X86.RoMix.sc t₀ ∧ s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr t₀) ∧
      s.gpr .edx = VG.Proof.Scrypt.X86.RoMix.bP t₀
  have wpArgs : ∀ {t₀ : State} {q : BitVec 32}, VG.Proof.Scrypt.X86.RoMix.Pre t₀ → ∀ s, VG.Proof.Scrypt.X86.RoMix.KR t₀ q s ∧ s.gpr .esi = A →
      WP isa (.block bmArgs) s (F t₀ q) := fun hp s h =>
    VG.Proof.Scrypt.X86.RoMix.bmArgs_ok hp h.1.toBase fun s' b' m' k' hax hcx hdx =>
      ⟨⟨b', by rw [k' _ (by decide) (by decide) (by decide), h.1.ebx],
        by rw [k' _ (by decide) (by decide) (by decide), h.1.ebp]⟩,
        by rw [k' _ (by decide) (by decide) (by decide), h.2], hax, hcx, hdx⟩
  have ar : RelCT isa (fun s s' => (VG.Proof.Scrypt.X86.RoMix.KR s₀ q s ∧ s.gpr .esi = A) ∧ (VG.Proof.Scrypt.X86.RoMix.KR s₀' q' s' ∧ s'.gpr .esi = A))
      (.block bmArgs) fun s s' => F s₀ q s ∧ F s₀' q' s' :=
    RelCT.mono ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp]) (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq (rs := [])
      h.1.1.toBase h.2.1.toBase (by simp)) (by taint_decide)).wp
      fun s s' h => ⟨wpArgs hp s h.1, wpArgs hp' s' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2
  -- The call, from each run's `F`.
  have wpCall : ∀ {t₀ : State} {q : BitVec 32}, VG.Proof.Scrypt.X86.RoMix.Pre t₀ → VG.Proof.Scrypt.X86.RoMix.SrcOK t₀ A → ∀ s, F t₀ q s →
      WP isa (.frame (.push VG.Proof.Scrypt.X86.RoMix.bmRegs) (.call "vg_scrypt_blockmix" Impl.Scrypt.X86.blockMix) (.pop .eax 5))
        s (fun s' => VG.Proof.Scrypt.X86.RoMix.KR t₀ q s' ∧ s'.gpr .esi = A) := fun hp hA s h =>
    VG.Proof.Scrypt.X86.RoMix.bmFrame_ok VG.Proof.Scrypt.X86.RoMix.blockMixSpec hp hA h.1.toBase h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      fun s' hrd hwr hcs hf _ => ⟨⟨⟨by rw [hrd, h.1.rd], by rw [hwr, h.1.wr],
        by rw [hcs _ (by simp [calleeSaved]), h.1.esp], h.1.frame.trans (VG.Proof.Scrypt.X86.RoMix.call_frame hf)⟩,
        by rw [hcs _ (by simp [calleeSaved]), h.1.ebx], by rw [hcs _ (by simp [calleeSaved]), h.1.ebp]⟩,
        by rw [hcs _ (by simp [calleeSaved]), h.2.1]⟩
  have cl : RelCT isa (fun s s' => F s₀ q s ∧ F s₀' q' s')
      (.frame (.push VG.Proof.Scrypt.X86.RoMix.bmRegs) (.call "vg_scrypt_blockmix" Impl.Scrypt.X86.blockMix) (.pop .eax 5))
      fun s s' => (VG.Proof.Scrypt.X86.RoMix.KR s₀ q s ∧ s.gpr .esi = A) ∧ (VG.Proof.Scrypt.X86.RoMix.KR s₀' q' s' ∧ s'.gpr .esi = A) := by
    refine RelCT.mono ((RelCT.callWith (k := Proof.Scrypt.blockMixX86) BlockMix.blockMix_correct
      BlockMix.blockMix_ct (VG.Proof.Scrypt.X86.RoMix.bmRd (VG.Proof.Scrypt.X86.RoMix.esp₀ s₀) A (VG.Proof.Scrypt.X86.RoMix.rr s₀)) (VG.Proof.Scrypt.X86.RoMix.bmWr (VG.Proof.Scrypt.X86.RoMix.bP s₀) (VG.Proof.Scrypt.X86.RoMix.sc s₀) (VG.Proof.Scrypt.X86.RoMix.rr s₀))
      fun s s' ⟨h, h'⟩ => ?_).wp fun s s' h => ⟨wpCall hp hA s h.1, wpCall hp' hA' s' h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2
    have pre : ∀ {t₀ : State} {q : BitVec 32} {s : State}, VG.Proof.Scrypt.X86.RoMix.Pre t₀ → VG.Proof.Scrypt.X86.RoMix.SrcOK t₀ A → F t₀ q s →
        CallPre Proof.Scrypt.blockMixX86 VG.Proof.Scrypt.X86.RoMix.bmRegs (VG.Proof.Scrypt.X86.RoMix.bmRd (VG.Proof.Scrypt.X86.RoMix.esp₀ t₀) A (VG.Proof.Scrypt.X86.RoMix.rr t₀)) (VG.Proof.Scrypt.X86.RoMix.bmWr (VG.Proof.Scrypt.X86.RoMix.bP t₀) (VG.Proof.Scrypt.X86.RoMix.sc t₀) (VG.Proof.Scrypt.X86.RoMix.rr t₀)) s := by
        intro t₀ _ s hp hA h
        have hsub : Region.Sub ⟨VG.Proof.Scrypt.X86.RoMix.scA t₀, 128⟩ (VG.Proof.Scrypt.X86.RoMix.scR t₀) := VG.Proof.Scrypt.X86.RoMix.w_sub
        have := VG.Proof.Scrypt.X86.RoMix.bm_callPre h.2.1 h.2.2.2.1 h.2.2.2.2 h.2.2.1 (by rw [h.1.esp]; exact hp.sp_lo) hp.pos
          (VG.Proof.Scrypt.X86.RoMix.r_lt hp) ((hp.b_s.sub_left VG.Proof.Scrypt.X86.RoMix.b_sub').sub_right hsub) hA.b hA.w hA.nw
          (by have := hp.b_nw; omega) (by have := hp.s_nw; omega) (by rw [h.1.esp]; exact hA.stk)
          (by rw [h.1.esp]; exact hp.stk_b.sub_right VG.Proof.Scrypt.X86.RoMix.b_sub') (by rw [h.1.esp]; exact hp.stk_s.sub_right hsub)
          (by rw [h.1.rd, h.1.wr]; exact hA.inr) (by rw [h.1.wr]; exact VG.Proof.Scrypt.X86.RoMix.b_in hp)
          (by rw [h.1.wr]; exact VG.Proof.Scrypt.X86.RoMix.w_in hp)
        rwa [h.1.esp] at this
    have p₁ := pre hp hA h
    have p₂ := pre hp' hA' h'
    rw [show VG.Proof.Scrypt.X86.RoMix.esp₀ s₀' = VG.Proof.Scrypt.X86.RoMix.esp₀ s₀ from hq.esp₀.symm, er, eb, es] at p₂
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.1.esp, h'.1.esp, hq.esp₀]
    have fit : 4 * bmRegs.length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.1.esp]; have := hp.sp_lo; simp only [List.length_cons, List.length_nil]; omega
    refine ⟨p₁, p₂, hsp, ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp], fun i hi => ?_⟩⟩
    simp only [arg_withRegions]
    have hi' : i < bmRegs.length := by simp only [List.length_cons, List.length_nil]; omega
    refine callEntry_arg_eq (by decide) fit hsp (fun r hr => ?_) hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h.2.2.1, h'.2.2.1, es]
    · rw [h.2.2.2.1, h'.2.2.2.1, er]
    · rw [h.2.2.2.2, h'.2.2.2.2, eb]
    · rw [h.2.2.2.1, h'.2.2.2.1, er]
    · rw [h.2.1, h'.2.1]
  exact ar.seq cl

end

/-- `KR` and `esi` survive code without calls that writes none of `esp`,
`ebx`, `ebp` and `esi`. -/
theorem KR.exec' {c : Prog isa} (hc : c.allInstrs (VG.Proof.Scrypt.X86.RoMix.free [.esp, .ebx, .ebp, .esi]) = true)
    (hn : c.noCalls = true) {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {q x : BitVec 32} {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (h : VG.Proof.Scrypt.X86.RoMix.KR s₀ q s ∧ s.gpr .esi = x) : VG.Proof.Scrypt.X86.RoMix.KR s₀ q s' ∧ s'.gpr .esi = x := by
  have k := VG.Proof.Scrypt.X86.RoMix.exec_keeps hc he
  obtain ⟨rd, wr, f⟩ := Exec.regions he hn
  exact ⟨⟨⟨rd.trans h.1.rd, wr.trans h.1.wr, by rw [k _ (by simp), h.1.esp],
    h.1.frame.trans (f.mono (by rw [h.1.wr, hp.wr]; simp))⟩, by rw [k _ (by simp), h.1.ebx],
    by rw [k _ (by simp), h.1.ebp]⟩, by rw [k _ (by simp), h.2]⟩

/-- `tBlock`: `esi = T`. -/
theorem t_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) {q : BitVec 32} {s : State} (h : VG.Proof.Scrypt.X86.RoMix.KR s₀ q s) :
    WP isa (.block tBlock) s fun s' => VG.Proof.Scrypt.X86.RoMix.KR s₀ q s' ∧ s'.gpr .esi = VG.Proof.Scrypt.X86.RoMix.tP32 s₀ := by
  unfold tBlock
  refine VG.Proof.Scrypt.X86.RoMix.wp_arg (i := 4) hp h.toBase (by omega) fun a ua => wp_addi fun b ub => WP.block_nil ?_
  exact ⟨⟨(h.toBase.upd ua (by decide)).upd ub (by decide),
    by rw [ub.other _ (by decide), ua.other _ (by decide), h.ebx],
    by rw [ub.other _ (by decide), ua.other _ (by decide), h.ebp]⟩, by rw [ub.gpr, ua.gpr]; rfl⟩

/-! ## Step 2, in two runs -/

section
variable {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86.RoMix.PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' i s') (step2 Impl.Scrypt.X86.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀))) ∧
        (VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀'))) := by
  have hi' : i < VG.Proof.Scrypt.X86.RoMix.NN s₀' := hq.NN ▸ hi
  have ev : VG.Proof.Scrypt.X86.RoMix.vAt32 s₀ i = VG.Proof.Scrypt.X86.RoMix.vAt32 s₀' i := hq.vAt32 i
  have eq : BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i) = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀' - i) := by rw [hq.NN]
  have en : BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀) = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀') := by rw [hq.NN]
  let K (t₀ t : State) : Prop := VG.Proof.Scrypt.X86.RoMix.KR t₀ (BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN t₀ - i)) t ∧ t.gpr .esi = VG.Proof.Scrypt.X86.RoMix.vAt32 t₀ i
  have regs : ∀ {s s'}, K s₀ s → K s₀' s' → ∀ r ∈ [Reg.ebx, .esi, .ebp], s.gpr r = s'.gpr r := by
    intro s s' h h' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.1.ebx, h'.1.ebx, eq]
    · rw [h.2, h'.2, ev]
    · rw [h.1.ebp, h'.1.ebp, en]
  have Kof : ∀ {t₀ t : State}, VG.Proof.Scrypt.X86.RoMix.Inv2 t₀ i t → K t₀ t := fun h => ⟨⟨h.toBase, h.ebx, h.ebp⟩, h.esi⟩
  have ac : RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' i s')
      (.seq (.block (timesR 8 ++ ([.mov .edx (.reg .eax), .mov .eax (.mem (at_ .esp 4)),
        .mov .ecx (.reg .esi)] : List Instr))) copyLoop) fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.post (RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ebx, .esi, .ebp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.1.toBase h.2.toBase (regs (Kof h.1) (Kof h.2)))
      (by taint_decide))
      fun _ _ _ _ _ _ h e e' => ⟨KR.exec' (by decide +kernel) (by decide +kernel) hp e (Kof h.1),
        KR.exec' (by decide +kernel) (by decide +kernel) hp' e' (Kof h.2)⟩
  have cl := VG.Proof.Scrypt.X86.RoMix.call_rel hp hp' hq (VG.Proof.Scrypt.X86.RoMix.srcOK_v hp hi) (VG.Proof.Scrypt.X86.RoMix.srcOK_v hp' hi') ev
    (q := BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i)) (q' := BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block (timesR 128 ++ ([.alu .add .esi (.reg .eax), .alu .sub .ebx (.imm 1)] : List Instr)))
      fun _ _ => True :=
    RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ebx, .esi, .ebp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (regs h.1 h.2)) (by taint_decide)
  have body := RelCT.assoc (ac.seq (cl.seq e))
  exact (body.wp fun _ _ h => ⟨VG.Proof.Scrypt.X86.RoMix.step2_ok VG.Proof.Scrypt.X86.RoMix.blockMixSpec hp hi h.1, VG.Proof.Scrypt.X86.RoMix.step2_ok VG.Proof.Scrypt.X86.RoMix.blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ 0 s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' 0 s')
      (.loop (step2 Impl.Scrypt.X86.blockMix) .ne)
      fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' (VG.Proof.Scrypt.X86.RoMix.NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.X86.blockMix)
    (c := .ne) (Q := fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' (VG.Proof.Scrypt.X86.RoMix.NN s₀') s')
    (fun n s s' => ∃ i, n = VG.Proof.Scrypt.X86.RoMix.NN s₀ - i ∧ i < VG.Proof.Scrypt.X86.RoMix.NN s₀ ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := VG.Proof.Scrypt.X86.RoMix.body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [VG.Proof.Scrypt.X86.RoMix.eval_zf z, VG.Proof.Scrypt.X86.RoMix.eval_zf z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ VG.Proof.Scrypt.X86.RoMix.NN s₀ := by simpa using ht'
        exact ⟨VG.Proof.Scrypt.X86.RoMix.NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (VG.Proof.Scrypt.X86.RoMix.NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, VG.Proof.Scrypt.X86.RoMix.NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3, in two runs -/

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀)).drop i = VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem :: rest := by
  have e : VG.Proof.Scrypt.X86.RoMix.NN s₀ - i = VG.Proof.Scrypt.X86.RoMix.NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

section
variable {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86.RoMix.PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) (j : Nat) :
    RelCT isa (fun s s' => (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem = j) ∧ (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' i s' ∧ VG.Proof.Scrypt.X86.RoMix.jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.X86.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀))) ∧
        (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀'))) := by
  have hi' : i < VG.Proof.Scrypt.X86.RoMix.NN s₀' := hq.NN ▸ hi
  have eq : BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i) = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀' - i) := by rw [hq.NN]
  have en : BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀) = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀') := by rw [hq.NN]
  have er : BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀ * 128) = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr s₀' * 128) := by rw [hq.rr]
  let K (t₀ t : State) : Prop := VG.Proof.Scrypt.X86.RoMix.KR t₀ (BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN t₀ - i)) t
  have regs : ∀ {s s'}, K s₀ s → K s₀' s' → ∀ r ∈ [Reg.ebx, .ebp], s.gpr r = s'.gpr r := by
    intro s s' h h' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.ebx, h'.ebx, eq]
    · rw [h.ebp, h'.ebp, en]
  let J (t₀ t : State) : Prop :=
    K t₀ t ∧ t.gpr .eax = BitVec.ofNat 32 j ∧ t.gpr .edi = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.rr t₀ * 128)
  have Kof : ∀ {t₀ t : State}, VG.Proof.Scrypt.X86.RoMix.Inv3 t₀ i t → K t₀ t := fun h => ⟨h.toBase, h.ebx, h.ebp⟩
  have jwp : ∀ {t₀ t : State}, VG.Proof.Scrypt.X86.RoMix.Pre t₀ → VG.Proof.Scrypt.X86.RoMix.Inv3 t₀ i t ∧ VG.Proof.Scrypt.X86.RoMix.jOf t₀ t.mem = j →
      WP isa (.block jBlock) t (J t₀) := fun hp h =>
    WP.mono (VG.Proof.Scrypt.X86.RoMix.j_ok hp h.1.toBase h.1.ebp) fun _ ⟨ax, di, o, b, _⟩ =>
      ⟨⟨b, by rw [o _ (by decide) (by decide) (by decide) (by decide), h.1.ebx],
        by rw [o _ (by decide) (by decide) (by decide) (by decide), h.1.ebp]⟩, by rw [ax, h.2], di⟩
  have jb : RelCT isa (fun s s' => (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem = j) ∧
        (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' i s' ∧ VG.Proof.Scrypt.X86.RoMix.jOf s₀' s'.mem = j)) (.block jBlock) fun s s' => J s₀ s ∧ J s₀' s' :=
    RelCT.mono ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ebx, .ebp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (regs (Kof h.1.1) (Kof h.2.1)))
      (by taint_decide)).wp fun _ _ h => ⟨jwp hp h.1, jwp hp' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => J s₀ s ∧ J s₀' s') (.seq (.block vjBlock) xorLoop)
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.post (RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .eax, .edi, .ebx, .ebp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2, h.2.2.2, er]
        · exact regs h.1.1 h.2.1 _ (by simp)
        · exact regs h.1.1 h.2.1 _ (by simp)))
      (by taint_decide))
      fun _ _ _ _ _ _ h e e' => ⟨KR.exec (by decide +kernel) (by decide +kernel) hp e h.1.1,
        KR.exec (by decide +kernel) (by decide +kernel) hp' e' h.2.1⟩
  have tb : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block tBlock)
      fun s s' => (K s₀ s ∧ s.gpr .esi = VG.Proof.Scrypt.X86.RoMix.tP32 s₀) ∧ (K s₀' s' ∧ s'.gpr .esi = VG.Proof.Scrypt.X86.RoMix.tP32 s₀') :=
    RelCT.mono ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ebx, .ebp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.1.toBase h.2.toBase (regs h.1 h.2)) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86.RoMix.t_wp hp h.1, VG.Proof.Scrypt.X86.RoMix.t_wp hp' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2
  have cl := VG.Proof.Scrypt.X86.RoMix.call_rel hp hp' hq (VG.Proof.Scrypt.X86.RoMix.srcOK_t hp) (VG.Proof.Scrypt.X86.RoMix.srcOK_t hp') hq.tP32
    (q := BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀ - i)) (q' := BitVec.ofNat 32 (VG.Proof.Scrypt.X86.RoMix.NN s₀' - i))
  have e : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .esi = VG.Proof.Scrypt.X86.RoMix.tP32 s₀) ∧ (K s₀' s' ∧ s'.gpr .esi = VG.Proof.Scrypt.X86.RoMix.tP32 s₀'))
      (.block [.alu .sub .ebx (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ebx, .ebp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (regs h.1.1 h.2.1)) (by taint_decide)
  have body := jb.seq (RelCT.assoc (mx.seq (tb.seq (cl.seq e))))
  exact (body.wp fun _ _ h => ⟨VG.Proof.Scrypt.X86.RoMix.step3_ok VG.Proof.Scrypt.X86.RoMix.blockMixSpec hp hi h.1.1,
    VG.Proof.Scrypt.X86.RoMix.step3_ok VG.Proof.Scrypt.X86.RoMix.blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86.RoMix.rr s₀) (VG.Proof.Scrypt.X86.RoMix.NN s₀) (VG.Proof.Scrypt.X86.RoMix.B s₀) =
  Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86.RoMix.rr s₀') (VG.Proof.Scrypt.X86.RoMix.NN s₀') (VG.Proof.Scrypt.X86.RoMix.B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < VG.Proof.Scrypt.X86.RoMix.NN s₀) :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' i s') (step3 Impl.Scrypt.X86.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀))) ∧
        (VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀'))) := by
  have hi' : i < VG.Proof.Scrypt.X86.RoMix.NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists_ fun (j : Nat) => VG.Proof.Scrypt.X86.RoMix.body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := VG.Proof.Scrypt.X86.RoMix.drop_js hi h
  obtain ⟨r', hr'⟩ := VG.Proof.Scrypt.X86.RoMix.drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨VG.Proof.Scrypt.X86.RoMix.jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ 0 s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' 0 s')
      (.loop (step3 Impl.Scrypt.X86.blockMix) .ne)
      fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' (VG.Proof.Scrypt.X86.RoMix.NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.X86.blockMix)
    (c := .ne) (Q := fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' (VG.Proof.Scrypt.X86.RoMix.NN s₀') s')
    (fun n s s' => ∃ i, n = VG.Proof.Scrypt.X86.RoMix.NN s₀ - i ∧ i < VG.Proof.Scrypt.X86.RoMix.NN s₀ ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := VG.Proof.Scrypt.X86.RoMix.body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [VG.Proof.Scrypt.X86.RoMix.eval_zf z, VG.Proof.Scrypt.X86.RoMix.eval_zf z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = VG.Proof.Scrypt.X86.RoMix.NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ VG.Proof.Scrypt.X86.RoMix.NN s₀ := by simpa using ht'
        exact ⟨VG.Proof.Scrypt.X86.RoMix.NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (VG.Proof.Scrypt.X86.RoMix.NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, VG.Proof.Scrypt.X86.RoMix.NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.X86.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.X86.blockMix) _
  unfold roMixWith
  have b₀ : VG.Proof.Scrypt.X86.RoMix.Base s₀ s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  have b₀' : VG.Proof.Scrypt.X86.RoMix.Base s₀' s₀' := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => VG.Proof.Scrypt.X86.RoMix.P1 s₀ s ∧ VG.Proof.Scrypt.X86.RoMix.P1 s₀' s' :=
    ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp]) (P := fun s s' => s = s₀ ∧ s' = s₀')
      (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq (rs := []) b₀ b₀' (by simp))
      (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := VG.Proof.Scrypt.X86.RoMix.P1 s₀) (F₂ := VG.Proof.Scrypt.X86.RoMix.P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨VG.Proof.Scrypt.X86.RoMix.prologue_ok hp, VG.Proof.Scrypt.X86.RoMix.prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.P1 s₀ s ∧ VG.Proof.Scrypt.X86.RoMix.P1 s₀' s') nLoop fun s s' => VG.Proof.Scrypt.X86.RoMix.N1 s₀ s ∧ VG.Proof.Scrypt.X86.RoMix.N1 s₀' s' :=
    ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .eax, .ecx, .edx])
      (fun _ _ ⟨h, h'⟩ => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.toBase h'.toBase fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.eax, h'.eax, hq.rr]
        · rw [h.ecx, h'.ecx]
        · rw [h.edx, h'.edx, RoMix.vl, RoMix.vl, hq.args 3 (by omega)]) (c := nLoop)
      (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86.RoMix.nloop_ok hp h.1, VG.Proof.Scrypt.X86.RoMix.nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.N1 s₀ s ∧ VG.Proof.Scrypt.X86.RoMix.N1 s₀' s') (.block rmSetup)
      fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ 0 s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ecx])
      (fun _ _ ⟨h, h'⟩ => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.toBase h'.toBase fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.ecx, h'.ecx, hq.NN]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86.RoMix.setup2_ok hp h.1, VG.Proof.Scrypt.X86.RoMix.setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86.RoMix.Inv2 s₀' (VG.Proof.Scrypt.X86.RoMix.NN s₀') s') (.block rmMid)
      fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ 0 s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp, .ebp])
      (fun _ _ ⟨h, h'⟩ => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq h.toBase h'.toBase fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.ebp, h'.ebp, hq.NN]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86.RoMix.mid_ok h.1, VG.Proof.Scrypt.X86.RoMix.mid_ok h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => VG.Proof.Scrypt.X86.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86.RoMix.Inv3 s₀' (VG.Proof.Scrypt.X86.RoMix.NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := sseTaint) (VG.Proof.Scrypt.X86.RoMix.τk [.esp])
      (fun _ _ h => VG.Proof.Scrypt.X86.RoMix.agree_k hp hp' hq (rs := []) h.1.toBase h.2.toBase (by simp)) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((VG.Proof.Scrypt.X86.RoMix.loop2_rel hp hp' hq).seq
    (md.seq ((VG.Proof.Scrypt.X86.RoMix.loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixX86.pub s₁ s₂) : VG.Proof.Scrypt.X86.RoMix.PubEq s₁ s₂ := ⟨h.1, h.2.1⟩

theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.roMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixX86.post s s' :=
  VG.Proof.Scrypt.X86.RoMix.correct VG.Proof.Scrypt.X86.RoMix.blockMixSpec (VG.Proof.Scrypt.X86.RoMix.pre_of hs)

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixX86.pre Proof.Scrypt.roMixX86.pub
    Impl.Scrypt.X86.roMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (VG.Proof.Scrypt.X86.RoMix.roMix_rel (VG.Proof.Scrypt.X86.RoMix.pre_of h₁) (VG.Proof.Scrypt.X86.RoMix.pre_of h₂) (VG.Proof.Scrypt.X86.RoMix.pubEq_of hpub) hpub.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x3000, 3` at `0x5004`: `b` at
`0x1000`, `v` at `0x2000` (`N = 1`) and the scratch space at `0x3000` (384 bytes). -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500d then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5015 then 0x30 else if a = 0x5018 then 3 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Scrypt.X86.RoMix.satMem
  rd := [⟨0x5004, 24⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem sat_pre : Proof.Scrypt.roMixX86.pre VG.Proof.Scrypt.X86.RoMix.sat := by
  have a0 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.sat 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.sat 1 = 1 := by decide
  have a2 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.sat 2 = 0x2000 := by decide
  have a3 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.sat 3 = 1 := by decide
  have a4 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.sat 4 = 0x3000 := by decide
  have a5 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.sat 5 = 3 := by decide
  have e : argAddr VG.Proof.Scrypt.X86.RoMix.sat 0 = 0x5004 := by decide
  simp only [Proof.Scrypt.roMixX86, a0, a1, a2, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ⟨0, rfl⟩, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-! ## The shared contract -/

/-- `roMixX86` with its arguments writable, as the shared contract lets them be. -/
def roMixWide : Contract isa :=
  { Proof.Scrypt.roMixX86 with
    pre := fun s =>
      let r := (VG.X86.arg s 1).toNat
      let b : Region := ⟨(VG.X86.arg s 0).setWidth 64, r * 128⟩
      let v : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat * 128⟩
      let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat * 128⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 36, 36⟩
      s.rd = [] ∧ s.wr = [b, v, scratch, args] ∧
      b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
      args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
      ret.Disjoint b ∧ ret.Disjoint v ∧ ret.Disjoint scratch ∧
      stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
      (VG.X86.arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat * 128 ≤ 2 ^ 32 ∧ 36 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      0 < r ∧ (VG.X86.arg s 3).toNat % r = 0 ∧ ((VG.X86.arg s 3).toNat / r).isPowerOfTwo ∧ (VG.X86.arg s 5).toNat = r + 2 }

/-- The regions `roMixX86` lets the code read and write. -/
def narrowRd (s : State) : List Region := [⟨argAddr s 0, 24⟩]
def narrowWr (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat * 128⟩, ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat * 128⟩,
    ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat * 128⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Scrypt.roMixX86, VG.Proof.Scrypt.X86.RoMix.roMixWide,
    VG.Proof.Scrypt.X86.RoMix.narrowRd, VG.Proof.Scrypt.X86.RoMix.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem roMixWide_pre (s : State) (h : roMixWide.pre s) :
    Proof.Scrypt.roMixX86.pre (s.withRegions (VG.Proof.Scrypt.X86.RoMix.narrowRd s) (VG.Proof.Scrypt.X86.RoMix.narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀,
    h₂₁, h₂₂, h₂₃⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, h₂₁, h₂₂, h₂₃⟩

/-- A state satisfying `roMixWide.pre`. -/
def wideSat : State :=
  { VG.Proof.Scrypt.X86.RoMix.sat with
             rd := [], wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩, ⟨0x5004, 24⟩] }

theorem roMixWide_implies : roMixWide.Implies (Spec.Scrypt.roMixContract X86.abi 36) := by
  have a0 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.wideSat 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.wideSat 1 = 1 := by decide
  have a2 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.wideSat 2 = 0x2000 := by decide
  have a3 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.wideSat 3 = 1 := by decide
  have a4 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.wideSat 4 = 0x3000 := by decide
  have a5 : VG.X86.arg VG.Proof.Scrypt.X86.RoMix.wideSat 5 = 3 := by decide
  have e : argAddr VG.Proof.Scrypt.X86.RoMix.wideSat 0 = 0x5004 := by decide
  have esp : wideSat.gpr .esp = 0x5000 := rfl
  sig_implies [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig, VG.Proof.Scrypt.X86.RoMix.roMixWide,
    Proof.Scrypt.roMixX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using VG.Proof.Scrypt.X86.RoMix.wideSat

/-- The proof is written against `roMixX86`, widened to writable arguments. -/
theorem roMix_verified :
    Verified X86.target Impl.Scrypt.X86.roMix (Spec.Scrypt.roMixContract X86.abi 36) :=
  have hsat := roMixWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct VG.Proof.Scrypt.X86.RoMix.roMix_correct VG.Proof.Scrypt.X86.RoMix.roMix_ct (.refl ⟨VG.Proof.Scrypt.X86.RoMix.sat, VG.Proof.Scrypt.X86.RoMix.sat_pre⟩))
    VG.Proof.Scrypt.X86.RoMix.narrowRd VG.Proof.Scrypt.X86.RoMix.narrowWr VG.Proof.Scrypt.X86.RoMix.roMixWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [VG.Proof.Scrypt.X86.RoMix.narrowRd, VG.Proof.Scrypt.X86.RoMix.narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [VG.Proof.Scrypt.X86.RoMix.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies VG.Proof.Scrypt.X86.RoMix.roMixWide_implies

end VG.Proof.Scrypt.X86.RoMix

end
