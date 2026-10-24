module

import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Xor
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Save
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Init
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.Pbkdf2.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Spec.Pbkdf2
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common

/-!
# PBKDF2 over any streaming hash function on PPC64LE: a step of `iterate`

`Iter.step` computes `U ← HMAC (K₀, U)` and `T ← T ⊕ U` (`step_ok`): it
copies the inner key state into `st` (which then represents `K₀ ⊕ ipad`,
`HashOK.reloc`), absorbs `U` (in `ub`) with `update`, finalizes into `dig`,
copies the outer key state's hash value over `st`'s (which then represents
`K₀ ⊕ opad`), absorbs the inner digest, finalizes into `ub`, and
exclusive-ors the new `U` into `T`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE.Iter

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.Pbkdf2.Stream.PPC64LE.Iter (st dig ub bytes)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK untouched untouched_pres Saved saved_keep)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_mov wp_addi wp_subi contains_offset)
open VG.Proof.Hmac.Stream.PPC64LE.Init (cover_self cover_pre cover_off Regs)
open VG.WriteBytes (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)
open Spec.Pbkdf2 (xorBytes)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev kp : Addr := s₀.gpr .r3
abbrev up : Addr := s₀.gpr .r4
abbrev tp : Addr := s₀.gpr .r6
abbrev scr : Addr := s₀.gpr .r7
abbrev kR : Region := ⟨kp s₀, 2 * H.S⟩
abbrev uR : Region := ⟨up s₀, H.D⟩
abbrev tR : Region := ⟨tp s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, bytes H⟩
/-- Everything the code writes. -/
abbrev all : List Region := [tR H s₀, scR H s₀, below s₀.sp 48]

end

/-- `iterate`'s precondition, with the stack pointer below its frame: its
callees' frames are in the 48 bytes below it. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [kR H s₀, uR H s₀]
  wr : s₀.wr = [tR H s₀, scR H s₀]
  k_t : (kR H s₀).Disjoint (tR H s₀)
  k_s : (kR H s₀).Disjoint (scR H s₀)
  u_t : (uR H s₀).Disjoint (tR H s₀)
  u_s : (uR H s₀).Disjoint (scR H s₀)
  t_s : (tR H s₀).Disjoint (scR H s₀)
  sp48 : 48 ≤ s₀.sp.toNat
  sk : (below s₀.sp 48).Disjoint (kR H s₀)
  su : (below s₀.sp 48).Disjoint (uR H s₀)
  st : (below s₀.sp 48).Disjoint (tR H s₀)
  ss : (below s₀.sp 48).Disjoint (scR H s₀)

/-- Our variables in `r20`, `r21` and `r23`, and the callee-saved registers
we never write. -/
structure Vars (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = kp s₀
  r21 : s.gpr .r21 = scr s₀
  r23 : s.gpr .r23 = tp s₀
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

variable {H : Hash} (hH : HashOK H) {s₀ : State}

theorem Vars.of_pres {s s' : State} (h : Vars s₀ s) (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Vars s₀ s' :=
  ⟨(hc _ (by decide)).trans h.r20, (hc _ (by decide)).trans h.r21, (hc _ (by decide)).trans h.r23,
    fun r hr => (hc r (untouched_pres r hr)).trans (h.un r hr)⟩

/-- `Vars` after code writing only `r3`–`r9` and `r22`. -/
theorem Vars.of_keep {s s' : State} (h : Vars s₀ s)
    (hc : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r22 →
      s'.gpr r = s.gpr r) : Vars s₀ s' := by
  have k : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28, .r29, .r30, .r31, .r20,
      .r21, .r23], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.r20, (k _ (by simp)).trans h.r21, (k _ (by simp)).trans h.r23,
    fun r hr => (k r (by revert r; decide)).trans (h.un r hr)⟩

/-! ## The scratch space -/

/-- The sizes the layout lemmas need. -/
structure Sz (H : Hash) : Prop where
  W : H.W ≤ 1024
  S : H.S ≤ 192
  FD : H.FD ≤ 64
  D : H.D ≤ H.FD

include hH in
theorem sz : Sz H := by
  have hN := hH.dims.N
  have hW := hH.dims.so
  have hB := hH.dims.B
  exact ⟨hW.2, by simp only [Hash.S]; omega, hH.hFD64, hH.hDF⟩

section
variable (hz : Sz H) (p : Addr)

theorem w_sub : Region.Sub ⟨p, H.W⟩ ⟨p, bytes H⟩ := Region.sub_prefix (by simp [bytes, ub, dig, st]<;> omega)
theorem sv_sub : Region.Sub ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p, bytes H⟩ :=
  Offset.sub_base p (by simp [bytes, ub, dig, st]<;> omega)
theorem st_sub : Region.Sub ⟨p + BitVec.ofNat 64 (st H), H.S⟩ ⟨p, bytes H⟩ :=
  Offset.sub_base p (by simp [bytes, ub, dig, st]<;> omega)
theorem dig_sub : Region.Sub ⟨p + BitVec.ofNat 64 (dig H), H.FD⟩ ⟨p, bytes H⟩ :=
  Offset.sub_base p (by simp [bytes, ub, dig, st]<;> omega)
theorem ub_sub : Region.Sub ⟨p + BitVec.ofNat 64 (ub H), H.FD⟩ ⟨p, bytes H⟩ :=
  Offset.sub_base p (by simp [bytes, ub, dig, st])
include hz in
theorem ubD_sub : Region.Sub ⟨p + BitVec.ofNat 64 (ub H), H.D⟩ ⟨p, bytes H⟩ :=
  Offset.sub_base p (by have := hz.D; simp [bytes, ub, dig, st]<;> omega)
include hz in
theorem w_st : Region.Disjoint ⟨p, H.W⟩ ⟨p + BitVec.ofNat 64 (st H), H.S⟩ :=
  Offset.base_disjoint p (by simp [st]) (by have := hz.W; have := hz.S; simp [st]<;> omega)
include hz in
theorem w_dig : Region.Disjoint ⟨p, H.W⟩ ⟨p + BitVec.ofNat 64 (dig H), H.FD⟩ :=
  Offset.base_disjoint p (by simp [dig, st]<;> omega) (by have := hz.W; have := hz.S; have := hz.FD; simp [dig, st]<;> omega)
include hz in
theorem w_ub : Region.Disjoint ⟨p, H.W⟩ ⟨p + BitVec.ofNat 64 (ub H), H.FD⟩ :=
  Offset.base_disjoint p (by simp [ub, dig, st]<;> omega) (by have := hz.W; have := hz.S; have := hz.FD; simp [ub, dig, st]<;> omega)
include hz in
theorem w_sv : Region.Disjoint ⟨p, H.W⟩ ⟨p + BitVec.ofNat 64 H.W, 48⟩ :=
  Offset.base_disjoint p (Nat.le_refl _) (by have := hz.W<;> omega)
include hz in
theorem st_dig : Region.Disjoint ⟨p + BitVec.ofNat 64 (st H), H.S⟩ ⟨p + BitVec.ofNat 64 (dig H), H.FD⟩ :=
  Offset.disjoint p (.inl (by simp [dig])) (by have := hz.W; have := hz.S; simp [st]<;> omega)
    (by have := hz.W; have := hz.S; have := hz.FD; simp [dig, st]<;> omega)
include hz in
theorem st_ub : Region.Disjoint ⟨p + BitVec.ofNat 64 (st H), H.S⟩ ⟨p + BitVec.ofNat 64 (ub H), H.FD⟩ :=
  Offset.disjoint p (.inl (by simp [ub, dig]<;> omega)) (by have := hz.W; have := hz.S; simp [st]<;> omega)
    (by have := hz.W; have := hz.S; have := hz.FD; simp [ub, dig, st]<;> omega)
include hz in
theorem dig_ub : Region.Disjoint ⟨p + BitVec.ofNat 64 (dig H), H.FD⟩ ⟨p + BitVec.ofNat 64 (ub H), H.FD⟩ :=
  Offset.disjoint p (.inl (by simp [ub])) (by have := hz.W; have := hz.S; have := hz.FD; simp [dig, st]<;> omega)
    (by have := hz.W; have := hz.S; have := hz.FD; simp [ub, dig, st]<;> omega)
include hz in
theorem sv_st : Region.Disjoint ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p + BitVec.ofNat 64 (st H), H.S⟩ :=
  Offset.disjoint p (.inl (by simp [st])) (by have := hz.W<;> omega) (by have := hz.W; have := hz.S; simp [st]<;> omega)
include hz in
theorem sv_dig : Region.Disjoint ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p + BitVec.ofNat 64 (dig H), H.FD⟩ :=
  Offset.disjoint p (.inl (by simp [dig, st]<;> omega)) (by have := hz.W<;> omega)
    (by have := hz.W; have := hz.S; have := hz.FD; simp [dig, st]<;> omega)
include hz in
theorem sv_ub : Region.Disjoint ⟨p + BitVec.ofNat 64 H.W, 48⟩ ⟨p + BitVec.ofNat 64 (ub H), H.FD⟩ :=
  Offset.disjoint p (.inl (by simp [ub, dig, st]<;> omega)) (by have := hz.W<;> omega)
    (by have := hz.W; have := hz.S; have := hz.FD; simp [ub, dig, st]<;> omega)

end

/-! ## A step -/

/-- Bytes of a region the frame's regions leave alone. -/
theorem keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

theorem contains_at {p : Addr} {len o n : Nat} (h : o + n ≤ len) (hl : len < 2 ^ 64) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 o) n :=
  contains_offset h (by omega)

theorem contains_start {p : Addr} {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem in_wr {s : State} {R : Region} (h : R ∈ s.wr) {a : Addr} {n : Nat} (hc : R.Contains a n) :
    InRegions s.wr a n := ⟨R, h, hc⟩

theorem in_rdwr {s : State} {R : Region} (h : R ∈ s.rd ++ s.wr) {a : Addr} {n : Nat} (hc : R.Contains a n) :
    InRegions (s.rd ++ s.wr) a n := ⟨R, h, hc⟩

/-- The hypotheses of `iterate`'s postcondition: the key states represent
`K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
def Hyp (s₀ : State) (k0 : List Byte) : Prop :=
  k0.length = H.B ∧ hH.SH.Repr s₀.mem (kp s₀) (xorPad k0 ipad) ∧
    hH.SH.Repr s₀.mem (kp s₀ + BitVec.ofNat 64 H.S) (xorPad k0 opad)

include hH in
/-- One step: `U ← HMAC (K₀, U)`, `T ← T ⊕ U`. -/
theorem step_ok (hp : Pre H s₀) {s : State} (hr : Regs s₀ s) (hv : Vars s₀ s) (hf : Frame (all H s₀) s₀.mem s.mem)
    (hsv : Saved H.W (scr s₀) s₀.gpr s.mem) :
    WP isa (VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.step H) s fun s' => Regs s₀ s' ∧ Vars s₀ s' ∧
      s'.gpr .r22 = s.gpr .r22 - 1 ∧ Frame (all H s₀) s₀.mem s'.mem ∧ Saved H.W (scr s₀) s₀.gpr s'.mem ∧
      ∀ k0, Hyp hH s₀ k0 →
        bytesAt s'.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D =
          hmacBlockKey hH.SH.H k0 (bytesAt s.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D) ∧
        bytesAt s'.mem (tp s₀) H.D = xorBytes (bytesAt s.mem (tp s₀) H.D)
          (hmacBlockKey hH.SH.H k0 (bytesAt s.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D)) := by
  have hz := sz hH
  have hN : 0 < H.N ∧ H.N ≤ 64 := hH.dims.N
  have hW : H.W % 8 = 0 ∧ H.W ≤ 1024 := hH.dims.so
  have hB : H.B = 64 ∨ H.B = 128 := hH.dims.B
  have hS : H.S = H.N + H.B := rfl
  have hD := hH.hD64
  have hFD := hH.hFD64
  have hDF := hH.hDF
  have hD4 := hH.hD4
  have hN4 := hH.hN4
  have hS4 : 4 * (H.S / 4) = H.S := by rw [hS]; rcases hB with h | h <;> rw [h] <;> omega
  have hNq : 4 * (H.N / 4) = H.N := by omega
  have hDq : 4 * (H.D / 4) = H.D := by omega
  have e0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => by simp
  have hbytes : bytes H = H.W + 48 + H.S + H.FD + H.FD := by simp [bytes, ub, dig, st] <;> omega
  -- The regions in `scratch`.
  let stR : Region := ⟨scr s₀ + BitVec.ofNat 64 (st H), H.S⟩
  let digR : Region := ⟨scr s₀ + BitVec.ofNat 64 (dig H), H.FD⟩
  let digD : Region := ⟨scr s₀ + BitVec.ofNat 64 (dig H), H.D⟩
  let ubR : Region := ⟨scr s₀ + BitVec.ofNat 64 (ub H), H.FD⟩
  let ubD : Region := ⟨scr s₀ + BitVec.ofNat 64 (ub H), H.D⟩
  let wR : Region := ⟨scr s₀, H.W⟩
  let svR : Region := ⟨scr s₀ + BitVec.ofNat 64 H.W, 48⟩
  have dsub : Region.Sub digD digR := Region.sub_prefix hDF
  have usub : Region.Sub ubD ubR := Region.sub_prefix hDF
  -- What the code never writes.
  have key_keep : ∀ m, Frame (all H s₀) s₀.mem m → ∀ i < 2 * H.S,
      m (kp s₀ + BitVec.ofNat 64 i) = s₀.mem (kp s₀ + BitVec.ofNat 64 i) := by
    intro m hf' i hi
    refine hf'.bytes (R := kR H s₀) ?_ (by have := hz.S; show 2 * H.S ≤ 2 ^ 64; omega) hi
    simp only [all, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hp.k_t, hp.k_s, hp.sk.symm]
  have wrs : ∀ R ∈ [stR, digR, ubR, wR, svR], R ∈ s.wr → True := fun _ _ _ => trivial
  -- Frames within `scratch` (or below the stack pointer) are frames of `all`.
  have inAll : ∀ R : Region, Region.Sub R (scR H s₀) → ∃ r' ∈ all H s₀, Region.Sub R r' :=
    fun R h => ⟨scR H s₀, by simp [all], h⟩
  have spAll : ∃ r' ∈ all H s₀, Region.Sub (below s₀.sp 48) r' := ⟨below s₀.sp 48, by simp [all], fun _ h => h⟩
  have rd0 : s.rd = [kR H s₀, uR H s₀] := hr.rd.trans hp.rd
  have wr0 : s.wr = [tR H s₀, scR H s₀] := hr.wr.trans hp.wr
  have scW : scR H s₀ ∈ s.wr := by rw [wr0]; simp
  have scRW : scR H s₀ ∈ s.rd ++ s.wr := List.mem_append_right _ scW
  have kRW : kR H s₀ ∈ s.rd ++ s.wr := List.mem_append_left _ (by rw [rd0]; simp)
  have tW : tR H s₀ ∈ s.wr := by rw [wr0]; simp
  have hbl : bytes H < 2 ^ 64 := by rw [hbytes]; have := hz.S; omega
  have hst : st H + H.S + H.FD + H.FD = bytes H := by simp [bytes, ub, dig] <;> omega
  have add_off := VG.Proof.Hmac.Stream.PPC64LE.add_off
  -- The inner key state into `st`.
  unfold VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.step
  refine WP.seq (VG.Proof.Hmac.Stream.PPC64LE.copy32_ok (src := .r20) (dst := .r21) (by decide) (by decide)
    (by decide) (by decide) 0 (st H) (H.S / 4) ⟨by have := hz.S; omega, by have := hz.S; have := hz.W; simp [st]; omega⟩
    _ s _
    (fun k hk => in_rdwr kRW (by rw [hv.r20, e0]; exact contains_at (by omega) (by have := hz.S; omega)))
    (fun k hk => in_wr scW (by rw [hv.r21, ← add_off]; exact contains_at (by omega) hbl))
    (by
      rw [hv.r20, hv.r21, e0, hS4]
      exact hp.k_s.sep (contains_start (by omega)) (contains_at (by omega) hbl))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_)
  rw [hv.r20, hv.r21, e0, hS4] at m₁
  let U := bytesAt s.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D
  have hU : U.length = H.D := VG.Proof.Hmac.Common.bytesAt_length _ _ _
  have fS₁ : Frame [stR] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]; exact contains_start (Nat.le_refl _))
  have v₁ : Vars s₀ s₁ := hv.of_keep fun r _ _ _ _ _ h8 _ _ => g₁ r h8
  have f₁ : Frame (all H s₀) s₀.mem s₁.mem := hf.trans (fS₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inAll _ (st_sub _))
  have sv₁ : Saved H.W (scr s₀) s₀.gpr s₁.mem := saved_keep hsv fS₁ (by
    simp only [List.mem_singleton]; rintro r rfl; exact sv_st hz _)
  have u₁ : bytesAt s₁.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D = U :=
    keep fS₁ (by simp only [List.mem_singleton]; rintro r rfl; exact ((st_ub hz _).sub_right usub).symm)
      (by omega)
  have hI₁ : ∀ k0, Hyp hH s₀ k0 → hH.SH.Repr s₁.mem (scr s₀ + BitVec.ofNat 64 (st H)) (xorPad k0 ipad) := by
    intro k0 ⟨hk0, hI, _⟩
    refine hH.reloc s₀.mem s₁.mem (kp s₀) _ _ (by simp [xorPad, hk0]) (fun i hi => ?_) hI
    rw [m₁, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length]; simp only [Hash.S]; omega)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; have := hz.S; omega),
      VG.Proof.Hmac.Common.bytesAt_getD' _ _ (by simp only [Hash.S]; omega)]
    exact key_keep _ hf i (by simp only [Hash.S]; omega)
  -- `update` with `U`.
  refine wp_addi (by have := hz.W; show H.W + 48 < 2 ^ 15; omega) fun s₂ x₂ => wp_li (by rcases hB with h | h <;> rw [h] <;> decide)
    fun s₃ x₃ => wp_addi (by have := hz.W; have := hz.S; have := hz.FD; show H.W + 48 + H.S + H.FD < 2 ^ 15; omega) fun s₄ x₄ =>
    wp_li (by omega) fun s₅ x₅ => wp_mov fun s₆ x₆ => WP.block_nil ?_
  have r₆ : Regs s₀ s₆ :=
    ⟨by rw [x₆.rd, x₅.rd, x₄.rd, x₃.rd, x₂.rd, rd₁, hr.rd], by rw [x₆.wr, x₅.wr, x₄.wr, x₃.wr, x₂.wr, wr₁, hr.wr],
      by rw [x₆.sp, x₅.sp, x₄.sp, x₃.sp, x₂.sp, sp₁, hr.sp]⟩
  have m₆ : s₆.mem = s₁.mem := by rw [x₆.mem, x₅.mem, x₄.mem, x₃.mem, x₂.mem]
  have v₆ : Vars s₀ s₆ := v₁.of_keep fun r a b c d e _ _ _ => by
    rw [x₆.other r e, x₅.other r d, x₄.other r c, x₃.other r b, x₂.other r a]
  -- Covers within `scratch`.
  have cS : ∀ {o n : Nat}, o + n ≤ bytes H → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (⟨scr s₀ + BitVec.ofNat 64 o, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun h => cover_off scRW h
  have cW : ∀ {o n : Nat}, o + n ≤ bytes H → ∃ r' ∈ s.wr, ∃ off,
      (⟨scr s₀ + BitVec.ofNat 64 o, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun h => cover_off scW h
  have cS0 : ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (⟨scr s₀, H.W⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + H.W ≤ r'.len :=
    cover_pre scRW (show H.W ≤ bytes H by rw [hbytes]; omega)
  have cW0 : ∃ r' ∈ s.wr, ∃ off,
      (⟨scr s₀, H.W⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧ off + H.W ≤ r'.len :=
    cover_pre scW (show H.W ≤ bytes H by rw [hbytes]; omega)
  have hst' : st H = H.W + 48 := rfl
  have hdig : dig H = H.W + 48 + H.S := rfl
  have hub : ub H = H.W + 48 + H.S + H.FD := rfl
  refine WP.seq (hH.callUpd_ok (st := scr s₀ + BitVec.ofNat 64 (st H)) (dat := scr s₀ + BitVec.ofNat 64 (ub H))
    (scr := scr s₀) (len := H.D)
    (by rw [x₆.other _ (by decide), x₅.other _ (by decide), x₄.other _ (by decide), x₃.other _ (by decide),
      x₂.gpr, v₁.r21])
    (by rw [x₆.other _ (by decide), x₅.other _ (by decide), x₄.gpr, x₃.other _ (by decide),
      x₂.other _ (by decide), v₁.r21])
    (by rw [x₆.other _ (by decide), x₅.gpr]; exact VG.Proof.MdStream.PPC64LE.toNat_ofNat_lt (by omega))
    (by rw [x₆.gpr, x₅.other _ (by decide), x₄.other _ (by decide), x₃.other _ (by decide),
      x₂.other _ (by decide), v₁.r21])
    (w_st hz _).symm ((st_ub hz _).sub_right usub).symm ((w_ub hz _).sub_right usub).symm
    (by rw [r₆.sp]; exact hp.sp48) (by rw [r₆.sp]; exact hp.ss.sub_right (st_sub _))
    (by rw [r₆.sp]; exact hp.ss.sub_right (ubD_sub hz _)) (by rw [r₆.sp]; exact hp.ss.sub_right (w_sub _))
    (by
      rw [r₆.rd, r₆.wr, ← hr.rd, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cS (by have := hz.D; rw [← hst]; simp [ub, dig]; omega)
      · exact cS (by rw [← hst]; omega)
      · exact cS0)
    (by
      rw [r₆.wr, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cW (by rw [← hst]; omega)
      · exact cW0)
    fun s₇ rd₇ wr₇ sp₇ f₇ cs₇ hup₇ => ?_)
  rw [r₆.sp] at f₇
  have r₇ : Regs s₀ s₇ := ⟨rd₇.trans r₆.rd, wr₇.trans r₆.wr, sp₇.trans r₆.sp⟩
  have v₇ : Vars s₀ s₇ := v₆.of_pres cs₇
  have f₇' : Frame (all H s₀) s₀.mem s₇.mem := f₁.trans (by
    rw [← m₆]
    exact f₇.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact inAll _ (st_sub _)
      · exact inAll _ (w_sub _)
      · exact spAll)
  have sv₇ : Saved H.W (scr s₀) s₀.gpr s₇.mem := saved_keep (by rw [m₆]; exact sv₁) f₇ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact sv_st hz _
    · exact (w_sv hz _).symm
    · exact (hp.ss.sub_right (sv_sub _)).symm)
  have hI₇ : ∀ k0, Hyp hH s₀ k0 → hH.SH.Repr s₇.mem (scr s₀ + BitVec.ofNat 64 (st H)) (xorPad k0 ipad ++ U) := by
    intro k0 h
    have hk0 := h.1
    have := hup₇ _ (by rw [m₆]; exact hI₁ k0 h)
      (by rw [x₆.other _ (by decide), x₅.other _ (by decide), x₄.other _ (by decide), x₃.gpr]
          simp [xorPad, hk0])
    rwa [m₆, u₁] at this
  have t₇ : bytesAt s₇.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D := by
    rw [keep f₇ (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hp.t_s.sub_right (st_sub _)
      · exact hp.t_s.sub_right (w_sub _)
      · exact hp.st.symm) (by omega), m₆]
    exact keep fS₁ (by simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right (st_sub _)) (by omega)
  -- `finalize` into `dig`.
  refine WP.seq (wp_addi (by have := hz.W; show H.W + 48 < 2 ^ 15; omega) fun s₈ x₈ =>
    wp_li (by rcases hB with h | h <;> rw [h] <;> omega) fun s₉ x₉ =>
    wp_addi (by have := hz.W; have := hz.S; show H.W + 48 + H.S < 2 ^ 15; omega) fun s₁₀ x₁₀ =>
    wp_mov fun s₁₁ x₁₁ => WP.block_nil ?_)
  have r₁₁ : Regs s₀ s₁₁ :=
    ⟨by rw [x₁₁.rd, x₁₀.rd, x₉.rd, x₈.rd, r₇.rd], by rw [x₁₁.wr, x₁₀.wr, x₉.wr, x₈.wr, r₇.wr],
      by rw [x₁₁.sp, x₁₀.sp, x₉.sp, x₈.sp, r₇.sp]⟩
  have m₁₁ : s₁₁.mem = s₇.mem := by rw [x₁₁.mem, x₁₀.mem, x₉.mem, x₈.mem]
  have v₁₁ : Vars s₀ s₁₁ := v₇.of_keep fun r a b c d _ _ _ _ => by
    rw [x₁₁.other r d, x₁₀.other r c, x₉.other r b, x₈.other r a]
  refine WP.seq (hH.callFin_ok (st := scr s₀ + BitVec.ofNat 64 (st H)) (o := scr s₀ + BitVec.ofNat 64 (dig H))
    (scr := scr s₀)
    (by rw [x₁₁.other _ (by decide), x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.gpr, v₇.r21])
    (by rw [x₁₁.other _ (by decide), x₁₀.gpr, x₉.other _ (by decide), x₈.other _ (by decide), v₇.r21])
    (by rw [x₁₁.gpr, x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.other _ (by decide), v₇.r21])
    (st_dig hz _) (w_st hz _).symm (w_dig hz _).symm
    (by rw [r₁₁.sp]; exact hp.sp48) (by rw [r₁₁.sp]; exact hp.ss.sub_right (st_sub _))
    (by rw [r₁₁.sp]; exact hp.ss.sub_right (dig_sub _)) (by rw [r₁₁.sp]; exact hp.ss.sub_right (w_sub _))
    (by
      rw [r₁₁.rd, r₁₁.wr, ← hr.rd, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cS (by rw [← hst]; omega)
      · exact cS (by rw [← hst]; simp [dig] <;> omega)
      · exact cS0)
    (by
      rw [r₁₁.wr, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cW (by rw [← hst]; omega)
      · exact cW (by rw [← hst]; simp [dig] <;> omega)
      · exact cW0)
    fun s₁₂ rd₁₂ wr₁₂ sp₁₂ f₁₂ cs₁₂ hfin₁₂ => ?_)
  rw [r₁₁.sp] at f₁₂
  have r₁₂ : Regs s₀ s₁₂ := ⟨rd₁₂.trans r₁₁.rd, wr₁₂.trans r₁₁.wr, sp₁₂.trans r₁₁.sp⟩
  have v₁₂ : Vars s₀ s₁₂ := v₁₁.of_pres cs₁₂
  have fr₁₂ : ∀ r ∈ [stR, digR, wR] ++ [below s₀.sp 48], ∃ r' ∈ all H s₀, Region.Sub r r' := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact inAll _ (st_sub _)
    · exact inAll _ (dig_sub _)
    · exact inAll _ (w_sub _)
    · exact spAll
  have f₁₂' : Frame (all H s₀) s₀.mem s₁₂.mem := f₇'.trans (by rw [← m₁₁]; exact f₁₂.sub fr₁₂)
  have sv₁₂ : Saved H.W (scr s₀) s₀.gpr s₁₂.mem := saved_keep (by rw [m₁₁]; exact sv₇) f₁₂ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact sv_st hz _
    · exact sv_dig hz _
    · exact (w_sv hz _).symm
    · exact (hp.ss.sub_right (sv_sub _)).symm)
  have tk₁₂ : ∀ r ∈ [stR, digR, wR] ++ [below s₀.sp 48], Region.Disjoint (tR H s₀) r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.t_s.sub_right (st_sub _)
    · exact hp.t_s.sub_right (dig_sub _)
    · exact hp.t_s.sub_right (w_sub _)
    · exact hp.st.symm
  have t₁₂ : bytesAt s₁₂.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D := by
    rw [keep f₁₂ tk₁₂ (by omega), m₁₁, t₇]
  have hd₁₂ : ∀ k0, Hyp hH s₀ k0 → bytesAt s₁₂.mem (scr s₀ + BitVec.ofNat 64 (dig H)) H.D =
      hH.SH.H.hash (xorPad k0 ipad ++ U) := by
    intro k0 h
    have hk0 := h.1
    have hl : (xorPad k0 ipad ++ U).length = H.B + H.D := by simp [xorPad, hk0, hU]
    rw [VG.Proof.Hmac.Stream.PPC64LE.bytesAt_take _ _ hDF, hfin₁₂ _ (by rw [m₁₁]; exact hI₇ k0 h)
      (by rw [hl]; omega)
      (by rw [x₁₁.other _ (by decide), x₁₀.other _ (by decide), x₉.gpr, hl]), hH.hashTake]
  -- The outer key state's hash value over `st`'s.
  refine WP.seq (VG.Proof.Hmac.Stream.PPC64LE.copy32_ok (src := .r20) (dst := .r21) (by decide) (by decide)
    (by decide) (by decide) H.S (st H) (H.N / 4)
    ⟨by have := hz.S; omega, by have := hz.S; have := hz.W; show H.W + 48 + 4 * (H.N / 4) ≤ 2 ^ 15; omega⟩
    _ s₁₂ _
    (fun k hk => in_rdwr (by rw [r₁₂.rd, r₁₂.wr, ← hr.rd, ← hr.wr]; exact kRW)
      (by rw [v₁₂.r20, ← add_off]; exact contains_at (by simp only [Hash.S] at *; omega) (by have := hz.S; omega)))
    (fun k hk => in_wr (by rw [r₁₂.wr, ← hr.wr]; exact scW)
      (by rw [v₁₂.r21, ← add_off]; exact contains_at (by rw [← hst]; simp only [Hash.S] at *; omega) hbl))
    (by
      rw [v₁₂.r20, v₁₂.r21, hNq]
      exact hp.k_s.sep (contains_at (by simp only [Hash.S]; omega) (by have := hz.S; omega))
        (contains_at (by rw [← hst]; simp only [Hash.S]; omega) hbl))
    fun s₁₃ g₁₃ rd₁₃ wr₁₃ sp₁₃ m₁₃ => ?_)
  rw [v₁₂.r20, v₁₂.r21, hNq] at m₁₃
  have fS₁₃ : Frame [stR] s₁₂.mem s₁₃.mem := by
    rw [m₁₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.Hmac.Common.bytesAt_length]; exact contains_start (by simp only [Hash.S]; omega))
  have v₁₃ : Vars s₀ s₁₃ := v₁₂.of_keep fun r _ _ _ _ _ h8 _ _ => g₁₃ r h8
  have hO₁₃ : ∀ k0, Hyp hH s₀ k0 → hH.SH.Repr s₁₃.mem (scr s₀ + BitVec.ofNat 64 (st H)) (xorPad k0 opad) := by
    intro k0 ⟨hk0, _, hO⟩
    refine hH.reloc s₀.mem s₁₃.mem (kp s₀ + BitVec.ofNat 64 H.S) _ _ (by simp [xorPad, hk0]) (fun i hi => ?_) hO
    rw [m₁₃, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length]; exact hi)
      (by rw [VG.Proof.Hmac.Common.bytesAt_length]; omega),
      VG.Proof.Hmac.Common.bytesAt_getD' _ _ hi, ← add_off]
    exact key_keep _ f₁₂' (H.S + i) (by simp only [Hash.S] at *; omega)
  have d₁₃ : ∀ k0, Hyp hH s₀ k0 →
      bytesAt s₁₃.mem (scr s₀ + BitVec.ofNat 64 (dig H)) H.D = hH.SH.H.hash (xorPad k0 ipad ++ U) := by
    intro k0 h
    rw [keep fS₁₃ (by simp only [List.mem_singleton]; rintro r rfl; exact ((st_dig hz _).sub_right dsub).symm)
      (by omega), hd₁₂ k0 h]
  -- `update` with the inner digest.
  refine wp_addi (by have := hz.W; show H.W + 48 < 2 ^ 15; omega) fun s₁₄ x₁₄ =>
    wp_li (by rcases hB with h | h <;> rw [h] <;> decide) fun s₁₅ x₁₅ =>
    wp_addi (by have := hz.W; have := hz.S; show H.W + 48 + H.S < 2 ^ 15; omega) fun s₁₆ x₁₆ =>
    wp_li (by omega) fun s₁₇ x₁₇ => wp_mov fun s₁₈ x₁₈ => WP.block_nil ?_
  have r₁₈ : Regs s₀ s₁₈ :=
    ⟨by rw [x₁₈.rd, x₁₇.rd, x₁₆.rd, x₁₅.rd, x₁₄.rd, rd₁₃, r₁₂.rd],
      by rw [x₁₈.wr, x₁₇.wr, x₁₆.wr, x₁₅.wr, x₁₄.wr, wr₁₃, r₁₂.wr],
      by rw [x₁₈.sp, x₁₇.sp, x₁₆.sp, x₁₅.sp, x₁₄.sp, sp₁₃, r₁₂.sp]⟩
  have m₁₈ : s₁₈.mem = s₁₃.mem := by rw [x₁₈.mem, x₁₇.mem, x₁₆.mem, x₁₅.mem, x₁₄.mem]
  have v₁₈ : Vars s₀ s₁₈ := v₁₃.of_keep fun r a b c d e _ _ _ => by
    rw [x₁₈.other r e, x₁₇.other r d, x₁₆.other r c, x₁₅.other r b, x₁₄.other r a]
  refine WP.seq (hH.callUpd_ok (st := scr s₀ + BitVec.ofNat 64 (st H)) (dat := scr s₀ + BitVec.ofNat 64 (dig H))
    (scr := scr s₀) (len := H.D)
    (by rw [x₁₈.other _ (by decide), x₁₇.other _ (by decide), x₁₆.other _ (by decide), x₁₅.other _ (by decide),
      x₁₄.gpr, v₁₃.r21])
    (by rw [x₁₈.other _ (by decide), x₁₇.other _ (by decide), x₁₆.gpr, x₁₅.other _ (by decide),
      x₁₄.other _ (by decide), v₁₃.r21])
    (by rw [x₁₈.other _ (by decide), x₁₇.gpr]; exact VG.Proof.MdStream.PPC64LE.toNat_ofNat_lt (by omega))
    (by rw [x₁₈.gpr, x₁₇.other _ (by decide), x₁₆.other _ (by decide), x₁₅.other _ (by decide),
      x₁₄.other _ (by decide), v₁₃.r21])
    (w_st hz _).symm ((st_dig hz _).sub_right dsub).symm ((w_dig hz _).sub_right dsub).symm
    (by rw [r₁₈.sp]; exact hp.sp48) (by rw [r₁₈.sp]; exact hp.ss.sub_right (st_sub _))
    (by rw [r₁₈.sp]; exact hp.ss.sub_right (fun a h => dig_sub _ a (dsub a h)))
    (by rw [r₁₈.sp]; exact hp.ss.sub_right (w_sub _))
    (by
      rw [r₁₈.rd, r₁₈.wr, ← hr.rd, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cS (by rw [← hst]; simp [dig] <;> omega)
      · exact cS (by rw [← hst]; omega)
      · exact cS0)
    (by
      rw [r₁₈.wr, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact cW (by rw [← hst]; omega)
      · exact cW0)
    fun s₁₉ rd₁₉ wr₁₉ sp₁₉ f₁₉ cs₁₉ hup₁₉ => ?_)
  rw [r₁₈.sp] at f₁₉
  have r₁₉ : Regs s₀ s₁₉ := ⟨rd₁₉.trans r₁₈.rd, wr₁₉.trans r₁₈.wr, sp₁₉.trans r₁₈.sp⟩
  have v₁₉ : Vars s₀ s₁₉ := v₁₈.of_pres cs₁₉
  have fr₁₉ : ∀ r ∈ [stR, wR] ++ [below s₀.sp 48], ∃ r' ∈ all H s₀, Region.Sub r r' := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inAll _ (st_sub _)
    · exact inAll _ (w_sub _)
    · exact spAll
  have f₁₉' : Frame (all H s₀) s₀.mem s₁₉.mem := f₁₂'.trans
    ((fS₁₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inAll _ (st_sub _)).trans
      (by rw [← m₁₈]; exact f₁₉.sub fr₁₉))
  have sv₁₉ : Saved H.W (scr s₀) s₀.gpr s₁₉.mem := saved_keep (by
      rw [m₁₈]; exact saved_keep sv₁₂ fS₁₃ (by simp only [List.mem_singleton]; rintro r rfl; exact sv_st hz _))
    f₁₉ (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact sv_st hz _
      · exact (w_sv hz _).symm
      · exact (hp.ss.sub_right (sv_sub _)).symm)
  have tk₁₉ : ∀ r ∈ [stR, wR] ++ [below s₀.sp 48], Region.Disjoint (tR H s₀) r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.t_s.sub_right (st_sub _)
    · exact hp.t_s.sub_right (w_sub _)
    · exact hp.st.symm
  have t₁₉ : bytesAt s₁₉.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D := by
    rw [keep f₁₉ tk₁₉ (by omega), m₁₈, keep fS₁₃ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right (st_sub _)) (by omega), t₁₂]
  have hO₁₉ : ∀ k0, Hyp hH s₀ k0 → hH.SH.Repr s₁₉.mem (scr s₀ + BitVec.ofNat 64 (st H))
      (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ U)) := by
    intro k0 h
    have hk0 := h.1
    have := hup₁₉ _ (by rw [m₁₈]; exact hO₁₃ k0 h)
      (by rw [x₁₈.other _ (by decide), x₁₇.other _ (by decide), x₁₆.other _ (by decide), x₁₅.gpr]
          simp [xorPad, hk0])
    rwa [m₁₈, d₁₃ k0 h] at this
  -- `finalize` into `ub`.
  refine WP.seq (wp_addi (by have := hz.W; show H.W + 48 < 2 ^ 15; omega) fun s₂₀ x₂₀ =>
    wp_li (by rcases hB with h | h <;> rw [h] <;> omega) fun s₂₁ x₂₁ =>
    wp_addi (by have := hz.W; have := hz.S; have := hz.FD; show H.W + 48 + H.S + H.FD < 2 ^ 15; omega)
      fun s₂₂ x₂₂ =>
    wp_mov fun s₂₃ x₂₃ => WP.block_nil ?_)
  have r₂₃ : Regs s₀ s₂₃ :=
    ⟨by rw [x₂₃.rd, x₂₂.rd, x₂₁.rd, x₂₀.rd, r₁₉.rd], by rw [x₂₃.wr, x₂₂.wr, x₂₁.wr, x₂₀.wr, r₁₉.wr],
      by rw [x₂₃.sp, x₂₂.sp, x₂₁.sp, x₂₀.sp, r₁₉.sp]⟩
  have m₂₃ : s₂₃.mem = s₁₉.mem := by rw [x₂₃.mem, x₂₂.mem, x₂₁.mem, x₂₀.mem]
  have v₂₃ : Vars s₀ s₂₃ := v₁₉.of_keep fun r a b c d _ _ _ _ => by
    rw [x₂₃.other r d, x₂₂.other r c, x₂₁.other r b, x₂₀.other r a]
  refine WP.seq (hH.callFin_ok (st := scr s₀ + BitVec.ofNat 64 (st H)) (o := scr s₀ + BitVec.ofNat 64 (ub H))
    (scr := scr s₀)
    (by rw [x₂₃.other _ (by decide), x₂₂.other _ (by decide), x₂₁.other _ (by decide), x₂₀.gpr, v₁₉.r21])
    (by rw [x₂₃.other _ (by decide), x₂₂.gpr, x₂₁.other _ (by decide), x₂₀.other _ (by decide), v₁₉.r21])
    (by rw [x₂₃.gpr, x₂₂.other _ (by decide), x₂₁.other _ (by decide), x₂₀.other _ (by decide), v₁₉.r21])
    (st_ub hz _) (w_st hz _).symm (w_ub hz _).symm
    (by rw [r₂₃.sp]; exact hp.sp48) (by rw [r₂₃.sp]; exact hp.ss.sub_right (st_sub _))
    (by rw [r₂₃.sp]; exact hp.ss.sub_right (ub_sub _)) (by rw [r₂₃.sp]; exact hp.ss.sub_right (w_sub _))
    (by
      rw [r₂₃.rd, r₂₃.wr, ← hr.rd, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cS (by rw [← hst]; omega)
      · exact cS (by rw [← hst]; simp [ub, dig] <;> omega)
      · exact cS0)
    (by
      rw [r₂₃.wr, ← hr.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cW (by rw [← hst]; omega)
      · exact cW (by rw [← hst]; simp [ub, dig] <;> omega)
      · exact cW0)
    fun s₂₄ rd₂₄ wr₂₄ sp₂₄ f₂₄ cs₂₄ hfin₂₄ => ?_)
  rw [r₂₃.sp] at f₂₄
  have r₂₄ : Regs s₀ s₂₄ := ⟨rd₂₄.trans r₂₃.rd, wr₂₄.trans r₂₃.wr, sp₂₄.trans r₂₃.sp⟩
  have v₂₄ : Vars s₀ s₂₄ := v₂₃.of_pres cs₂₄
  have f₂₄' : Frame (all H s₀) s₀.mem s₂₄.mem := f₁₉'.trans (by
    rw [← m₂₃]
    exact f₂₄.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact inAll _ (st_sub _)
      · exact inAll _ (ub_sub _)
      · exact inAll _ (w_sub _)
      · exact spAll)
  have sv₂₄ : Saved H.W (scr s₀) s₀.gpr s₂₄.mem := saved_keep (by rw [m₂₃]; exact sv₁₉) f₂₄ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact sv_st hz _
    · exact sv_ub hz _
    · exact (w_sv hz _).symm
    · exact (hp.ss.sub_right (sv_sub _)).symm)
  have t₂₄ : bytesAt s₂₄.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D := by
    rw [keep f₂₄ (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.t_s.sub_right (st_sub _)
      · exact hp.t_s.sub_right (ub_sub _)
      · exact hp.t_s.sub_right (w_sub _)
      · exact hp.st.symm) (by omega), m₂₃, t₁₉]
  have hu₂₄ : ∀ k0, Hyp hH s₀ k0 →
      bytesAt s₂₄.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D = hmacBlockKey hH.SH.H k0 U := by
    intro k0 h
    have hk0 := h.1
    have hl : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ U)).length = H.B + H.D := by
      simp [xorPad, hk0, hH.hashLen]
    rw [VG.Proof.Hmac.Stream.PPC64LE.bytesAt_take _ _ hDF, hfin₂₄ _ (by rw [m₂₃]; exact hO₁₉ k0 h)
      (by rw [hl]; omega)
      (by rw [x₂₃.other _ (by decide), x₂₂.other _ (by decide), x₂₁.gpr, hl]), ← hH.hashTake]
    rfl
  -- `T ← T ⊕ U`, and the steps left.
  have uLen : (bytesAt s₂₄.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D).length = H.D :=
    VG.Proof.Hmac.Common.bytesAt_length _ _ _
  refine xor32_ok (src := .r21) (dst := .r23) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
    (by decide) (ub H) (H.D / 4)
    ⟨by have := hz.W; have := hz.S; have := hz.FD; show H.W + 48 + H.S + H.FD + 4 * (H.D / 4) ≤ 2 ^ 15; omega,
      by omega⟩ _ s₂₄ _
    (fun k hk => in_rdwr (by rw [r₂₄.rd, r₂₄.wr, ← hr.rd, ← hr.wr]; exact scRW)
      (by rw [v₂₄.r21, ← add_off]; exact contains_at (by rw [← hst]; simp [ub, dig]; omega) hbl))
    (fun k hk => in_wr (by rw [r₂₄.wr, ← hr.wr]; exact tW)
      (by rw [v₂₄.r23]; exact contains_at (by omega) (by omega)))
    (by
      rw [v₂₄.r21, v₂₄.r23, hDq]
      exact (hp.t_s.sub_right (ubD_sub hz _)).symm.sep (contains_start (Nat.le_refl _))
        (contains_start (Nat.le_refl _)))
    fun s₂₅ g₂₅ rd₂₅ wr₂₅ sp₂₅ m₂₅ => ?_
  rw [v₂₄.r21, v₂₄.r23, hDq, t₂₄] at m₂₅
  refine wp_subi (by decide) fun s₂₆ x₂₆ => WP.block_nil ?_
  have fT : Frame [tR H s₀] s₂₄.mem s₂₅.mem := by
    rw [m₂₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [xorBytes_length _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length, uLen]),
        VG.Proof.Hmac.Common.bytesAt_length]
      exact contains_start (Nat.le_refl _))
  refine ⟨⟨by rw [x₂₆.rd, rd₂₅, r₂₄.rd], by rw [x₂₆.wr, wr₂₅, r₂₄.wr], by rw [x₂₆.sp, sp₂₅, r₂₄.sp]⟩,
    (v₂₄.of_keep fun r _ _ _ _ _ h8 h9 _ => g₂₅ r h8 h9).of_keep fun r _ _ _ _ _ _ _ h22 => x₂₆.other r h22,
    ?_, ?_, ?_, ?_⟩
  · rw [x₂₆.gpr, g₂₅ _ (by decide) (by decide), cs₂₄ _ (by decide), x₂₃.other _ (by decide),
      x₂₂.other _ (by decide), x₂₁.other _ (by decide), x₂₀.other _ (by decide), cs₁₉ _ (by decide),
      x₁₈.other _ (by decide), x₁₇.other _ (by decide), x₁₆.other _ (by decide), x₁₅.other _ (by decide),
      x₁₄.other _ (by decide), g₁₃ _ (by decide), cs₁₂ _ (by decide), x₁₁.other _ (by decide),
      x₁₀.other _ (by decide), x₉.other _ (by decide), x₈.other _ (by decide), cs₇ _ (by decide),
      x₆.other _ (by decide), x₅.other _ (by decide), x₄.other _ (by decide), x₃.other _ (by decide),
      x₂.other _ (by decide), g₁ _ (by decide)]
    rfl
  · rw [x₂₆.mem]
    exact f₂₄'.trans (fT.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨tR H s₀, by simp [all], fun _ h => h⟩)
  · rw [x₂₆.mem]
    exact saved_keep sv₂₄ fT (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.t_s.sub_right (sv_sub _)).symm)
  · intro k0 h
    refine ⟨?_, ?_⟩
    · rw [x₂₆.mem, keep fT (by simp only [List.mem_singleton]; rintro r rfl; exact (hp.t_s.sub_right (ubD_sub hz _)).symm)
        (by omega), hu₂₄ k0 h]
    · rw [x₂₆.mem, m₂₅, ← hu₂₄ k0 h]
      have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₂₄.mem (tp s₀)
        (xorBytes (bytesAt s.mem (tp s₀) H.D) (bytesAt s₂₄.mem (scr s₀ + BitVec.ofNat 64 (ub H)) H.D))
        (by rw [xorBytes_length _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length, uLen]),
          VG.Proof.Hmac.Common.bytesAt_length]; omega)
      rwa [xorBytes_length _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length, uLen]),
        VG.Proof.Hmac.Common.bytesAt_length] at this

end VG.Proof.Pbkdf2.Stream.PPC64LE.Iter
