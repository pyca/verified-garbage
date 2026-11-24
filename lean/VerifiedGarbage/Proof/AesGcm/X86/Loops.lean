module
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Proof.Framework.WriteBytes

import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-!
# AES-GCM on x86: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `ecx` bytes
from `edi` to `edx`, and `xorLoop` XORs the `ecx` bytes at `edx` into those
at `edi`, a byte at a time, advancing both pointers (`copyLoop_ok`,
`xorLoop_ok`); the buffers do not overlap. Both are constant time from the
pointers and the count (`copyLoop_ct`, `xorLoop_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega_using [hi]) (by omega_using [hi, hn])⟩

/-- What the loops need of the state: the source `S` (`edi`), the
destination `D` (`edx`) and the count `n` (`ecx`). -/
structure LoopPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  edi : s.gpr .edi = S
  edx : s.gpr .edx = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fS : S.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem succ_ofNat32 (x : BitVec 32) (i : Nat) :
    x + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = x + BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem add_zero32 (x : BitVec 32) : x + BitVec.ofNat 32 0 = x := BitVec.add_zero x

theorem pred_count {n i : Nat} (h : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - (i + 1)) := by
  rw [ofNat_sub32 (by omega_using [h]) (by omega_using [hn])]; congr 1

theorem pred_beq {n i : Nat} (h : i < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = decide (i + 1 = n) := by
  rw [pred_count h hn, VG.X86.Wp.ofNat_beq_zero (by omega_using [hn])]
  simp only [decide_eq_decide]
  omega_using [h]

theorem setWidth8_32 (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  ext j hj; simp [hj]

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .store8 (at_ .edx 0) .al, .alu .add .edi (imm 1),
    .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]

theorem copyStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .edi = S + BitVec.ofNat 32 i)
    (hd : s.gpr .edx = D + BitVec.ofNat 32 i) (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i))
    (eS : w64 (S + BitVec.ofNat 32 i) = w64 S + BitVec.ofNat 64 i)
    (eD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 D + BitVec.ofNat 64 i) (s.mem (w64 S + BitVec.ofNat 64 i)) ∧
      s'.gpr .edi = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .edx = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [copyBody, add_zero32, hs, hd, eS, eD, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, ite_true, setWidth8_32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, succ_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, succ_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · simp only [zf_setMem, gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 32) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega_using [hi]) (by omega_using [hi, hn])) (Region.sub_prefix (by omega_using [hi]) _ hcon)

/-- What `copyLoop` leaves. -/
structure CopyPost (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n)
  edi : s'.gpr .edi = S + BitVec.ofNat 32 n
  edx : s'.gpr .edx = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copyLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s (CopyPost s S D n) := by
  have hn : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .edi = S + BitVec.ofNat 32 i ∧
      t.gpr .edx = D + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) i) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr)
    ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.edi, add_zero32], by rw [h.edx, add_zero32], by rw [h.ecx, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, edi, edx, ecx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', edi', edx', ecx', zf', g', rd', wr'⟩ := copyStep_ok t edi edx ecx
    (w64_add (by have := h.fS; omega_using [hi, this])) (w64_add (by have := h.fD; omega_using [hi, this]))
    (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega_using [hn]))
    (by rw [wr]; exact in_of_covers h.wr hi (by omega_using [hn]))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem (w64 S) i).length = i := length_bytesAt _ _ _
  have hmem : t'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem (w64 D) (bytesAt s.mem (w64 S) i) _ (by rw [hlen]; omega_using [hn, hi]), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by rw [zf', pred_beq hi hn]
  have gg : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edi', he], by rw [edx', he], gg,
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], edi', edx',
      by rw [ecx', pred_count hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## `xorLoop` -/

abbrev xorBodyG (to : Bool) : List Instr :=
  [.movzx8 .eax (at_ .edx 0), .movzx8 .ebx (at_ (xorSrc to) 0), .alu .xor .eax (.reg .ebx),
    .store8 (at_ .edi 0) .al, .alu .add .edi (imm 1)] ++ (if to then [.alu .add .esi (imm 1)] else []) ++
    [.alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : BitVec 32)).setWidth 8 = a ^^^ b := by
  ext j hj; simp [hj]

/-- One step of `xorLoopG`: byte `i` of the keystream at `K` XORed with that
of the source `Sr` into the destination `D` (`Sr = D` in place). -/
theorem xorStep_ok (to : Bool) (s : State) {K Sr D : BitVec 32} {i n : Nat} (hs : s.gpr .edx = K + BitVec.ofNat 32 i)
    (hd : s.gpr .edi = D + BitVec.ofNat 32 i) (hr : s.gpr (xorSrc to) = Sr + BitVec.ofNat 32 i)
    (hsame : to = false → Sr = D) (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i))
    (eK : w64 (K + BitVec.ofNat 32 i) = w64 K + BitVec.ofNat 64 i)
    (eS : w64 (Sr + BitVec.ofNat 32 i) = w64 Sr + BitVec.ofNat 64 i)
    (eD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 K + BitVec.ofNat 64 i) 1)
    (rS : InRegions (s.rd ++ s.wr) (w64 Sr + BitVec.ofNat 64 i) 1)
    (w : InRegions s.wr (w64 D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (xorBodyG to) s = some s' ∧
      s'.mem = s.mem.writeW (w64 D + BitVec.ofNat 64 i)
        (s.mem (w64 K + BitVec.ofNat 64 i) ^^^ s.mem (w64 Sr + BitVec.ofNat 64 i)) ∧
      s'.gpr .edx = K + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .edi = D + BitVec.ofNat 32 (i + 1) ∧
      (to = true → s'.gpr .esi = Sr + BitVec.ofNat 32 (i + 1)) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → (to = true → r ≠ .esi) →
        s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases to
  · obtain rfl := hsame rfl
    refine ⟨_, by xrun [xorBodyG, xorSrc, add_zero32, hs, hd, eK, eD, r, w, in_left w], ?_, ?_, ?_,
      fun h => by simp at h, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, setWidth8_xor]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, succ_ofNat32]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, succ_ofNat32]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
    · simp only [zf_setMem, gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
        reduceCtorEq, hc]
    · intro r h₁ h₂ h₃ h₄ h₅ _; simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄, h₅]
    all_goals rfl
  · simp only [xorSrc, ite_true] at hr
    refine ⟨_, by xrun [xorBodyG, xorSrc, add_zero32, hs, hd, hr, eK, eS, eD, r, rS, w], ?_, ?_, ?_, fun _ => ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, setWidth8_xor]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, succ_ofNat32]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, succ_ofNat32]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hr, succ_ofNat32]
    · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
    · simp only [zf_setMem, gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
        reduceCtorEq, hc]
    · intro r h₁ h₂ h₃ h₄ h₅ h₆; have h₆ := h₆ rfl; simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄, h₅, h₆]
    all_goals rfl

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    xorBytes m D S (i + 1) = xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [xorBytes, bytesAt_succ, List.zipWith_append, length_bytesAt]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (xorBytes m D S n).length = n := by
  simp [xorBytes, length_bytesAt]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [hi, hn]), Nat.lt_irrefl, ite_false]

/-- What `xorLoopG` needs: the keystream `K` in `edx`, the destination `D` in
`edi`, and the source `Sr`, `D` itself in place or apart from it, in `esi`
out of place. -/
structure XorPreG (to : Bool) (s : State) (K Sr D : BitVec 32) (n : Nat) : Prop where
  edx : s.gpr .edx = K
  edi : s.gpr .edi = D
  src : s.gpr (xorSrc to) = Sr
  same : to = false → Sr = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fK : K.toNat + n ≤ 2 ^ 32
  fS : Sr.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 K, n⟩] (s.rd ++ s.wr)
  rdS : Covers [⟨w64 Sr, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 K, n⟩ : Region).Disjoint ⟨w64 D, n⟩
  sd : Sr = D ∨ (⟨w64 Sr, n⟩ : Region).Disjoint ⟨w64 D, n⟩

/-- What `xorLoopG` leaves. -/
structure XorPostG (to : Bool) (s : State) (K Sr D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 Sr) (w64 K) n)
  edx : s'.gpr .edx = K + BitVec.ofNat 32 n
  edi : s'.gpr .edi = D + BitVec.ofNat 32 n
  esi : to = true → s'.gpr .esi = Sr + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → (to = true → r ≠ .esi) →
    s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem xorLoopG_ok (to : Bool) (s : State) {K Sr D : BitVec 32} {n : Nat} (h : XorPreG to s K Sr D n) :
    WP isa (xorLoopG to) s (XorPostG to s K Sr D n) := by
  have hn : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block (xorBodyG to)) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .edx = K + BitVec.ofNat 32 i ∧
      t.gpr .edi = D + BitVec.ofNat 32 i ∧ t.gpr (xorSrc to) = Sr + BitVec.ofNat 32 i ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 Sr) (w64 K) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → (to = true → r ≠ .esi) → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.edx, add_zero32], by rw [h.edi, add_zero32], by rw [h.src, add_zero32],
      by rw [h.ecx, Nat.sub_zero], by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, edx, edi, esr, ecx, mem, g, rd, wr⟩
  have wD : InRegions t.wr (w64 D + BitVec.ofNat 64 i) 1 := by rw [wr]; exact in_of_covers h.wr hi (by omega_using [hn])
  obtain ⟨t', run', mem', edx', edi', esi', ecx', zf', g', rd', wr'⟩ := xorStep_ok to t edx edi esr h.same ecx
    (w64_add (by have := h.fK; omega_using [hi, this])) (w64_add (by have := h.fS; omega_using [hi, this])) (w64_add (by have := h.fD; omega_using [hi, this]))
    (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega_using [hn])) (by rw [rd, wr]; exact in_of_covers h.rdS hi (by omega_using [hn]))
    wD
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_xorBytes s.mem (w64 Sr) (w64 K) i
  have kS : writeBytes s.mem (w64 D) (xorBytes s.mem (w64 Sr) (w64 K) i) (w64 Sr + BitVec.ofNat 64 i) =
      s.mem (w64 Sr + BitVec.ofNat 64 i) := by
    rcases h.sd with e | d
    · subst e; exact dst_kept hi hn _ hlen
    · exact src_kept d hi hn _ hlen
  have hmem : t'.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 Sr) (w64 K) (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, kS, xorBytes_succ, BitVec.xor_comm,
      writeBytes_snoc s.mem (w64 D) _ _ (by rw [hlen]; omega_using [hn, hi]), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by rw [zf', pred_beq hi hn]
  have esr' : t'.gpr (xorSrc to) = Sr + BitVec.ofNat 32 (i + 1) := by
    cases to
    · obtain rfl := h.same rfl; exact edi'
    · exact esi' rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → (to = true → r ≠ .esi) →
      t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ h₆ => by rw [g' r h₁ h₂ h₃ h₄ h₅ h₆, g r h₁ h₂ h₃ h₄ h₅ h₆]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edx', he], by rw [edi', he], fun ht => ?_, gg,
      by rw [rd', rd], by rw [wr', wr]⟩
    subst ht; rw [← he]; exact esr'
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], edx', edi', esr',
      by rw [ecx', pred_count hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-- What `xorLoop` (source `S` in `edx`, destination `D` in `edi`) leaves. -/
structure XorPost (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 D) (w64 S) n)
  edx : s'.gpr .edx = S + BitVec.ofNat 32 n
  edi : s'.gpr .edi = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What `xorLoop` needs: the source `S` in `edx`, the destination `D` in `edi`. -/
structure XorPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  edx : s.gpr .edx = S
  edi : s.gpr .edi = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fS : S.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩

/-- `xorLoopG` in place. -/
theorem xorLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : XorPre s S D n) :
    WP isa xorLoop s (XorPost s S D n) :=
  WP.mono (xorLoopG_ok false s (Sr := D) ⟨h.edx, h.edi, h.edi, fun _ => rfl, h.ecx, h.pos, h.lt, h.fS, h.fD, h.fD,
      h.rd, covers_left h.wr, h.wr, h.disj, .inl rfl⟩)
    fun _ p => ⟨p.mem, p.edx, p.edi, fun r h₁ h₂ h₃ h₄ h₅ => p.other r h₁ h₂ h₃ h₄ h₅ (fun h => by simp at h), p.rd, p.wr⟩

/-! ## Constant time -/

theorem copyLoop_ct {I : State → Prop} (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r) :
    CT I copyLoop :=
  CT.taint _ hr (by taint_decide)

theorem xorLoopTo_ct {I : State → Prop}
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx, .esi], s₁.gpr r = s₂.gpr r) :
    CT I (xorLoopG true) :=
  CT.taint _ hr (by taint_decide)

theorem xorLoop_ct {I : State → Prop} (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r) :
    CT I xorLoop :=
  CT.taint _ hr (by taint_decide)

/-! ## `maskWords` -/

theorem mask_word32 (w : BitVec 32) (c : Bool) :
    (w &&& ((0 : BitVec 32) - (if c then 1 else 0))) = if c then w else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    rfl

theorem add4_ofNat32 (x : BitVec 32) (i : Nat) :
    x + BitVec.ofNat 32 i + BitVec.ofNat 32 4 = x + BitVec.ofNat 32 (i + 4) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem in4_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i + 4 ≤ n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p hi (by omega_using [hi, hn])⟩

/-- The first `j` bytes of the data at `P`, kept (`c`) or zeroed. -/
abbrev masked (m : Mem) (P : Addr) (c : Bool) (j : Nat) : List Byte :=
  if c then bytesAt m P j else List.replicate j 0

theorem length_masked (m : Mem) (P : Addr) (c : Bool) (j : Nat) : (masked m P c j).length = j := by
  cases c <;> simp [masked, length_bytesAt]

/-- A word of the data, kept or zeroed after the `j` bytes before it. -/
theorem masked_word (m : Mem) (P : Addr) (c : Bool) (j : Nat) (hj : j + 4 < 2 ^ 64) :
    (writeBytes m P (masked m P c j)).writeW (P + BitVec.ofNat 64 j)
      (if c then (writeBytes m P (masked m P c j)).readW (P + BitVec.ofNat 64 j) 32 else 0 : BitVec 32) =
      writeBytes m P (masked m P c (j + 4)) := by
  obtain hl := length_masked m P c j
  obtain hk : ∀ k < 4, writeBytes m P (masked m P c j) (P + BitVec.ofNat 64 j + BitVec.ofNat 64 k) =
      m (P + BitVec.ofNat 64 (j + k)) := fun k hk => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [writeBytes, hl]
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, hk]),
      ite_eq_right (by omega_using [])]
  show Mem.write _ _ 4 _ = _
  rw [write_eq_writeBytes]
  obtain ha := writeBytes_append m P (masked m P c j)
    ((List.range 4).map fun k => (BitVec.setWidth (8 * 4)
      (if c then (writeBytes m P (masked m P c j)).readW (P + BitVec.ofNat 64 j) 32 else 0 : BitVec 32)).extractLsb'
        (8 * k) 8) (by rw [hl]; simp only [List.length_map, List.length_range]; omega_using [hj])
  rw [hl] at ha
  rw [ha]
  refine congrArg (writeBytes m P) ?_
  cases c
  · show List.replicate j 0 ++ _ = List.replicate (j + 4) 0
    rw [← List.replicate_append_replicate]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain e : bytesAt m P (j + 4) =
        bytesAt m P j ++ (List.range 4).map fun k => m (P + BitVec.ofNat 64 (j + k)) := by
      simp only [bytesAt, List.range_add, List.map_append, List.map_map]
      rfl
    show bytesAt m P j ++ _ = bytesAt m P (j + 4)
    rw [e]
    refine congrArg _ (List.map_congr_left fun k hk' => ?_)
    obtain hk4 := List.mem_range.mp hk'
    show BitVec.extractLsb' (8 * k) 8 (BitVec.setWidth 32 ((writeBytes m P (masked m P true j)).readW _ 32)) = _
    rw [BitVec.setWidth_eq, ← Mem.readW_byte _ _ hk4, hk k hk4]

theorem maskWord_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 4) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 4) :
    ∃ s', runBlock isa maskWord s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i)
        (if c then s.mem.readW (w64 P + BitVec.ofNat 64 i) 32 else 0 : BitVec 32) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 4) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 4 ∧
      s'.cf = some (decide ((BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 4).toNat < (BitVec.ofNat 32 4).toNat)) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [maskWord, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, hb, mask_word32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, add4_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · simp only [cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, hc]
  · intro r h₁ h₂ h₃; simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What `maskWords` leaves of `n` bytes at `D`: the first `j` masked, with
fewer than 4 left. -/
theorem maskWords_ok (s : State) {D : BitVec 32} {n : Nat} {c : Bool} (hn : n < 2 ^ 32) (hfit : D.toNat + n ≤ 2 ^ 32)
    (hdi : s.gpr .edi = D) (hcx : s.gpr .ecx = BitVec.ofNat 32 n) (hbx : s.gpr .ebx = 0 - (if c then 1 else 0))
    (hrd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)) (hwr : Covers [⟨w64 D, n⟩] s.wr) :
    WP isa maskWords s fun t => ∃ j, j ≤ n ∧ n - j < 4 ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧ t.mem = writeBytes s.mem (w64 D) (masked s.mem (w64 D) c j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, m₁, cf₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .ecx (imm 4)] s = some s₁ ∧
      s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.cf = some (decide (n < 4)) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · simp only [cf_arithFlags, hcx]
      rw [toNat_ofNat32 hn]
      rfl
    · rfl
    · rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 4)) (show isa.eval .b s₁ = _ from cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · exact ⟨0, Nat.zero_le _, by simpa using of_decide_eq_true hb, by rw [g₁, hdi, add_zero32],
      by rw [g₁, hcx, Nat.sub_zero], by rw [m₁]; cases c <;> simp [masked, bytesAt, writeBytes_nil],
      fun r _ _ _ => by rw [g₁], rd₁, wr₁⟩
  obtain h4 : 4 ≤ n := Nat.le_of_not_lt (of_decide_eq_false hb)
  refine WP.loop (M := isa) (body := .block maskWord) (c := .ae)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j + 4 ≤ n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧ t.mem = writeBytes s.mem (w64 D) (masked s.mem (w64 D) c j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h4, by rw [g₁, hdi, add_zero32], by rw [g₁, hcx, Nat.sub_zero],
      by rw [m₁]; cases c <;> simp [masked, bytesAt, writeBytes_nil], fun r _ _ _ => by rw [g₁], rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', cf', g', rd', wr'⟩ := maskWord_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), hbx]) (w64_add (by omega_using [hj, hfit]))
    (by rw [rd, wr]; exact in4_of_covers hrd hj (by omega_using [hn]))
    (by rw [wr]; exact in4_of_covers hwr hj (by omega_using [hn]))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  obtain hmem : t'.mem = writeBytes s.mem (w64 D) (masked s.mem (w64 D) c (j + 4)) := by
    rw [mem', mem, masked_word _ _ _ _ (by omega_using [hj, hn])]
  obtain cxn : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 4 = BitVec.ofNat 32 (n - (j + 4)) := by
    rw [ofNat_sub32 (by omega_using [hj]) (by omega_using [hn])]; congr 1
  obtain hcf : t'.cf = some (decide (n - (j + 4) < 4)) := by
    rw [cf', cxn, toNat_ofNat32 (by omega_using [hn])]; rfl
  obtain gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : n - (j + 4) < 4
  · left
    exact ⟨by simp [eval, hcf, he], j + 4, hj, he, di', by rw [cx', cxn], hmem, gg, by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    exact ⟨by simp [eval, hcf, he], n - (j + 4), by omega_using [hj], j + 4, rfl, by omega_using [he], di',
      by rw [cx', cxn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## Direct word and byte XOR -/

private theorem writeXorWord (m : Mem) (a b dst : Addr) :
    m.writeW dst (m.readW a 32 ^^^ m.readW b 32) = writeBytes m dst (xorBytes m a b 4) := by
  rw [Mem.writeW, write_eq_writeBytes]
  congr 1
  apply List.ext_getElem
  · simp [xorBytes, bytesAt]
  · intro j h _
    have hj : j < 4 := by simpa using h
    simp [xorBytes, bytesAt, BitVec.extractLsb'_xor, X86.byte_readW _ _ (by omega : 8 * (j+1) ≤ 32)]

private theorem xorChunk {m : Mem} {K S D : Addr} {i k n : Nat} (h : i+k≤n) (lt : n<2^64)
    (hk : (⟨K,n⟩ : Region).Disjoint ⟨D,n⟩) (hs : S=D ∨ (⟨S,n⟩ : Region).Disjoint ⟨D,n⟩) :
    let m' := writeBytes m D (xorBytes m S K i)
    writeBytes m' (D + BitVec.ofNat 64 i) (xorBytes m' (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) k) =
      writeBytes m D (xorBytes m S K (i+k)) := by
  dsimp only
  have frame := writeBytes_frame m D (xorBytes m S K i)
    (R:=⟨D,i⟩) (by rw [length_xorBytes]; exact Region.contains_self _ _)
  have one {p : Addr} (hd : (⟨p,k⟩ : Region).Disjoint ⟨D,i⟩) :
      bytesAt (writeBytes m D (xorBytes m S K i)) p k = bytesAt m p k :=
    Proof.Cmac.bytesAt_frame frame (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hd) (by omega)
  have source : (⟨S+BitVec.ofNat 64 i,k⟩ : Region).Disjoint ⟨D,i⟩ := by
    rcases hs with same | apart
    · rw [same]
      exact Offset.disjoint_base D (Nat.le_refl _) (by omega)
    · exact (apart.sub_left (Offset.sub_base S h)).sub_right (Region.sub_prefix (by omega))
  have key := (hk.sub_left (Offset.sub_base K h)).sub_right (Region.sub_prefix (show i≤n by omega))
  have suffix :
      xorBytes (writeBytes m D (xorBytes m S K i)) (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) k =
        xorBytes m (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) k := by
    change List.zipWith _ (bytesAt _ _ _) (bytesAt _ _ _) = _
    rw [one source, one key]
    rfl
  rw [suffix]
  have app := writeBytes_append m D (xorBytes m S K i) (xorBytes m (S+BitVec.ofNat 64 i) (K+BitVec.ofNat 64 i) k)
    (by simp only [length_xorBytes]; omega)
  rw [length_xorBytes] at app
  rw [app]
  congr 1
  simp only [xorBytes, Proof.Cmac.Stream.bytesAt_append]
  rw [List.zipWith_append (by simp only [length_bytesAt])]

private structure Cursors (s : State) (K S D : BitVec 32) (n i : Nat) (t : State) : Prop where
  key : t.gpr .edx = K + BitVec.ofNat 32 i
  src : t.gpr .esi = S + BitVec.ofNat 32 i
  dst : t.gpr .edi = D + BitVec.ofNat 32 i
  len : t.gpr .ecx = BitVec.ofNat 32 (n-i)
  mem : t.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 S) (w64 K) i)
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → r ≠ .esi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

private theorem cursorWord {s t : State} {K S D : BitVec 32} {n i : Nat} (h : XorPreG true s K S D n)
    (cur : Cursors s K S D n i t) (hi : i+4 ≤ n) :
    ∃ u, runBlock isa xorWordStep t = some u ∧ Cursors s K S D n (i+4) u ∧
      u.cf = some (decide (n-(i+4) < 4)) := by
  have lt := h.lt
  have k := w64_add (x:=K) (k:=i) (by have f:=h.fK; omega)
  have src := w64_add (x:=S) (k:=i) (by have f:=h.fS; omega)
  have dst := w64_add (x:=D) (k:=i) (by have f:=h.fD; omega)
  have rk : InRegions (t.rd++t.wr) (w64 K+BitVec.ofNat 64 i) 4 := by
    rw [cur.rd,cur.wr]; exact h.rd _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hi (by omega)⟩
  have rs : InRegions (t.rd++t.wr) (w64 S+BitVec.ofNat 64 i) 4 := by
    rw [cur.rd,cur.wr]; exact h.rdS _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hi (by omega)⟩
  have wd : InRegions t.wr (w64 D+BitVec.ofNat 64 i) 4 := by
    rw [cur.wr]; exact h.wr _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hi (by omega)⟩
  have rem : BitVec.ofNat 32 (n-i) - 4#32 = BitVec.ofNat 32 (n-(i+4)) := by
    rw [show 4#32=BitVec.ofNat 32 4 from rfl, Offset.ofNat_sub_ofNat (by omega),Nat.sub_add_eq]
  refine ⟨_,by xrun [xorWordStep,add_zero32,cur.key,cur.src,cur.dst,k,src,dst,rk,rs,wd],?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,cur.rd,cur.wr⟩
    · simp [gpr_setReg,add4_ofNat32]
    · simp [gpr_setReg,add4_ofNat32]
    · simp [gpr_setReg,add4_ofNat32]
    · simp [gpr_setReg,cur.len,rem]
    · simp only [mem_arithFlags,mem_setReg,mem_setMem]
      rw [BitVec.xor_comm, writeXorWord,cur.mem]
      exact xorChunk hi (by omega) h.disj (h.sd.imp (congrArg w64) id)
    · intro r a b c d e f
      simpa [gpr_setMem,gpr_setReg,a,c,d,e,f] using cur.other r a b c d e f
  · simp [cur.len,rem,toNat_ofNat32 (show n-(i+4)<2^32 by omega)]

private theorem words_ok {s t : State} {K S D : BitVec 32} {n : Nat} (h : XorPreG true s K S D n)
    (init : Cursors s K S D n 0 t) (flag : t.cf = some (decide (n<4))) :
    WP isa (.ite .b (.block []) (.loop (.block xorWordStep) .ae)) t fun u =>
      ∃ j, j≤n ∧ n-j<4 ∧ Cursors s K S D n j u := by
  refine WP.ite (decide (n<4)) (show isa.eval .b t = _ from flag) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · exact ⟨0,Nat.zero_le _,by simpa using of_decide_eq_true hb,init⟩
  have h4 : 4≤n := Nat.le_of_not_lt (of_decide_eq_false hb)
  refine WP.loop (M:=isa) (body:=.block xorWordStep) (c:=.ae)
    (fun k v => ∃ i, k=n-i ∧ i+4≤n ∧ Cursors s K S D n i v) ?_ (n-0) _
    ⟨0,rfl,h4,init⟩
  rintro k v ⟨i,rfl,room,cur⟩
  obtain ⟨u,run,cur',flag'⟩ := cursorWord h cur room
  refine WP.of_runBlock ⟨u,run,?_⟩
  by_cases done : n-(i+4)<4
  · exact Or.inl ⟨by simp [eval,flag',done],i+4,room,done,cur'⟩
  · exact Or.inr ⟨by simp [eval,flag',done],n-(i+4),by omega,i+4,rfl,by omega,cur'⟩

private theorem suffix_ok {s t : State} {K S D : BitVec 32} {n i : Nat} (h : XorPreG true s K S D n)
    (hi : i≤n) (nz : i<n) (cur : Cursors s K S D n i t) :
    WP isa (xorLoopG true) t (XorPostG true s K S D n) := by
  let atI := fun (p : BitVec 32) => p + BitVec.ofNat 32 i
  have lt := h.lt
  have add {p : BitVec 32} (hp : p.toNat+n≤2^32) : w64 (atI p) = w64 p+BitVec.ofNat 64 i :=
    w64_add (by omega)
  have fit {p : BitVec 32} (hp : p.toNat+n≤2^32) : (atI p).toNat+(n-i)≤2^32 := by
    rw [show (atI p).toNat = p.toNat+i from toNat_add32 (by omega)]; omega
  have sub {p : BitVec 32} (hp : p.toNat+n≤2^32) :
      Region.Sub ⟨w64 (atI p),n-i⟩ ⟨w64 p,n⟩ := by rw [add hp]; exact Offset.sub_base _ (by omega)
  have tail : XorPreG true t (atI K) (atI S) (atI D) (n-i) :=
    ⟨cur.key,cur.dst,cur.src,(fun ht => nomatch ht),cur.len,by omega,by omega,fit h.fK,fit h.fS,fit h.fD,
      by rw [cur.rd,cur.wr,add h.fK]; exact covers_off h.rd (by omega) (by omega),
      by rw [cur.rd,cur.wr,add h.fS]; exact covers_off h.rdS (by omega) (by omega),
      by rw [cur.wr,add h.fD]; exact covers_off h.wr (by omega) (by omega),
      (h.disj.sub_left (sub h.fK)).sub_right (sub h.fD),
      h.sd.imp (congrArg atI) (fun q => (q.sub_left (sub h.fS)).sub_right (sub h.fD))⟩
  refine WP.mono (xorLoopG_ok true t tail) fun u z => ?_
  have join (p : BitVec 32) : atI p+BitVec.ofNat 32 (n-i) = p+BitVec.ofNat 32 n := by
    unfold atI; rw [BitVec.add_assoc,← BitVec.ofNat_add,Nat.add_sub_of_le hi]
  refine ⟨?_,z.edx.trans (join K),z.edi.trans (join D),fun _ => (z.esi rfl).trans (join S),?_,z.rd.trans cur.rd,z.wr.trans cur.wr⟩
  · rw [z.mem,cur.mem,add h.fD,add h.fS,add h.fK]
    have same := xorChunk (K:=w64 K) (S:=w64 S) (D:=w64 D) (m:=s.mem) (i:=i) (k:=n-i)
      (by omega : i+(n-i)≤n) (by omega) h.disj (h.sd.imp (congrArg w64) id)
    simpa only [Nat.add_sub_of_le hi] using same
  · intro r a b c d e f
    exact (z.other r a b c d e f).trans (cur.other r a b c d e (f rfl))

private theorem wordXor_ok {s : State} {K S D : BitVec 32} {n : Nat} (h : XorPreG true s K S D n) :
    WP isa wordXor s (XorPostG true s K S D n) := by
  have lt := h.lt
  obtain ⟨a,run,cur,flag⟩ : ∃ a, runBlock isa [.alu .cmp .ecx (imm 4)] s = some a ∧
      Cursors s K S D n 0 a ∧ a.cf=some (decide (n<4)) := by
    refine ⟨_,by xrun [],?_,?_⟩
    · refine ⟨by simpa using h.edx,by simpa [xorSrc] using h.src,by simpa using h.edi,
        by simpa using h.ecx,by simp [xorBytes,bytesAt,writeBytes_nil],fun _ _ _ _ _ _ _ => rfl,rfl,rfl⟩
    · simp [h.ecx,toNat_ofNat32 lt]
  refine WP.seq (WP.of_runBlock ⟨a,run,WP.seq (WP.mono (words_ok h cur flag) ?_)⟩)
  rintro b ⟨i,le,_,c⟩
  obtain ⟨v,run',d,zf⟩ : ∃ v, runBlock isa [.alu .test .ecx (.reg .ecx)] b = some v ∧
      Cursors s K S D n i v ∧ v.zf=some (decide (n-i=0)) := by
    refine ⟨_,by xrun [],?_,?_⟩
    · exact ⟨c.key,c.src,c.dst,c.len,c.mem,c.other,c.rd,c.wr⟩
    · simp [c.len]
      exact VG.X86.Wp.ofNat_beq_zero (by omega)
  refine WP.seq (WP.of_runBlock ⟨v,run',WP.ite (decide (n-i=0)) (show isa.eval .e v = _ from zf)
    (fun yes => WP.block_nil ?_) (fun no => suffix_ok h le (by have := of_decide_eq_false no; omega) d)⟩)
  have eq : i=n := by have := of_decide_eq_true yes; omega
  subst i
  exact ⟨d.mem,d.key,d.dst,fun _ => d.src,fun r a b c e f g => d.other r a b c e f (g rfl),d.rd,d.wr⟩
theorem xorTailCode_ok (words : Bool) {s : State} {K S D : BitVec 32} {n : Nat}
    (h : XorPreG true s K S D n) : WP isa (xorTailCode words) s (XorPostG true s K S D n) := by
  cases words
  · exact xorLoopG_ok true s h
  · exact wordXor_ok h

end VG.Proof.AesGcm.X86
