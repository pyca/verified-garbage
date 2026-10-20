module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Finalize
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming TDEA-CMAC on x86-64: arithmetic, memory and copying bytes

The number of bytes held back, as the code computes it from `count`
(`held_bv`); the bytes `writeBytes` leaves; and `copy`, which copies the
`rcx` bytes at `r13` to `rdx`, a byte at a time (none if `rcx` is 0),
changing only `rax`, `r10` and the flags.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.CmacTripleDes.Stream (held held_pos held_zero)

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
theorem sx400 : BitVec.signExtend 64 (400 : BitVec 32) = BitVec.ofNat 64 400 := by decide
theorem sx408 : BitVec.signExtend 64 (408 : BitVec 32) = BitVec.ofNat 64 408 := by decide

theorem and7 (x : BitVec 64) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, as `sub 1; and 7; add 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - 1) &&& 7) + 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  have := c.isLt
  omega

theorem beq_zero_iff (c : BitVec 64) : (c == 0) = decide (c.toNat = 0) := by
  by_cases h : c = 0
  · subst h; rfl
  · have : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simpa [this] using h

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## Bytes written -/

section
open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

end

/-! ## Copying bytes -/

section
open VG.Impl.CmacTripleDes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacTripleDes.X86_64 (succ_ofNat bytesAt_succ)

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hc : s.gpr .r13 = P) (hd : s.gpr .rdx = C)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (h8 : s.gpr .rcx = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hc, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .rdx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = C + BitVec.ofNat 64 i := by
    rw [hd, hi, BitVec.mul_one]; simp
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, copyBody, srcByte, dstByte, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, 
      ea₁, ea₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, h8]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · rfl
  · rfl

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (hc : s.gpr .r13 = P)
    (hd : s.gpr .rdx = C) (h8 : s.gpr .rcx = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁,
      runBlock isa [.mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L = 0)) ∧
      (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, ↓reduceIte,
      and_self, BitVec.reduceSetWidth, BitVec.and_self, h8, beq_zero_iff, toNat_ofNat hL]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₁]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r _ h => g₁ r h, rd₁, wr₁⟩
  refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, by omega, r10₁, by rw [m₁]; simp [Spec.Aes.bytesAt, writeBytes_nil],
      fun r _ h₂ => g₁ r h₂, rd₁, wr₁⟩
  rintro n t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t
    (by rw [g _ (by decide) (by decide), hc]) (by rw [g _ (by decide) (by decide), hd]) r10
    (by rw [g _ (by decide) (by decide), h8])
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i)
      (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end

end VG.Proof.CmacTripleDes.Stream.X86_64
