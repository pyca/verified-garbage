module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Env

/-!
# AES-GCM's short path on x86-64: the text

Untrusted: everything here is checked by Lean. `xorText g` XORs the `rcx`
bytes at `rsi` with those at `rdx` (the keystream), in place, and if `g` also
writes the result at `rdi`: 16 bytes at a time through `xmm4`, then one at a
time (`xorText_ok`); the three buffers do not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

/-- Writes to disjoint regions commute. -/
theorem writeBytes_comm (m : Mem) (p q : Addr) (xs ys : List Byte)
    (h : (⟨p, xs.length⟩ : Region).Disjoint ⟨q, ys.length⟩) :
    writeBytes (writeBytes m p xs) q ys = writeBytes (writeBytes m q ys) p xs := by
  funext a
  simp only [writeBytes]
  by_cases h₁ : (a - p).toNat < xs.length <;> by_cases h₂ : (a - q).toNat < ys.length <;>
    simp only [h₁, h₂, ite_true, ite_false]
  exact absurd (show Region.Contains ⟨q, ys.length⟩ a 1 by simp only [Region.Contains]; omega_arith)
    (h a (by simp only [Region.Contains]; omega_arith))

/-- The bytes at `S` XORed with those at `K`. -/
def xb (m : Mem) (S K : Addr) (n : Nat) : List Byte := List.zipWith (· ^^^ ·) (bytesAt m S n) (bytesAt m K n)

theorem length_xb (m : Mem) (S K : Addr) (n : Nat) : (xb m S K n).length = n := by
  simp [xb, length_bytesAt]

theorem xb_add (m : Mem) (S K : Addr) (a b : Nat) :
    xb m S K (a + b) = xb m S K a ++ xb m (S + BitVec.ofNat 64 a) (K + BitVec.ofNat 64 a) b := by
  simp only [xb, bytesAt_add]
  rw [List.zipWith_append (by rw [length_bytesAt, length_bytesAt])]

theorem xb_succ (m : Mem) (S K : Addr) (i : Nat) :
    xb m S K (i + 1) = xb m S K i ++ [m (S + BitVec.ofNat 64 i) ^^^ m (K + BitVec.ofNat 64 i)] := by
  rw [xb_add]; simp [xb, bytesAt]

/-- What `xorText g` writes: `xs` at `S`, and if `g` at `D` too. -/
def xw (g : Bool) (m : Mem) (S D : Addr) (xs : List Byte) : Mem :=
  if g then writeBytes (writeBytes m S xs) D xs else writeBytes m S xs

/-- A 16-byte store of the XOR of two 16-byte values loaded. -/
theorem writeW_xor128 (m src : Mem) (a b c : Addr) :
    m.writeW a (src.readW b 128 ^^^ src.readW c 128) =
      writeBytes m a (List.zipWith (· ^^^ ·) (bytesAt src b 16) (bytesAt src c 16)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (128 / 8)) (BitVec.setWidth 128 (src.read b (128 / 8)) ^^^
      BitVec.setWidth 128 (src.read c (128 / 8)))) = src.read b 16 ^^^ src.read c 16 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read src b (List.mem_range.mp hj),
    Mem.extractLsb'_read src c (List.mem_range.mp hj)]

/-- The 16-byte loop's body. -/
abbrev xor16Body (g : Bool) : List Instr :=
  [.vmovdquLoad .l128 .xmm4 srcB, .vbinLoad .vpxor .l128 .xmm4 .xmm4 kB, .vmovdquStore .l128 srcB .xmm4] ++
    (if g then [.vmovdquStore .l128 dstB .xmm4] else []) ++ [.alu .add .r10 (imm 16), .alu .cmp .r10 (.reg .r8)]

theorem xor16Step_ok (g : Bool) (s : State) {S K D : Addr} {i k : Nat} (hs : s.gpr .rsi = S)
    (hk : s.gpr .rdx = K) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hk8 : s.gpr .r8 = BitVec.ofNat 64 k)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 16) (r₂ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 16)
    (w₁ : InRegions s.wr (S + BitVec.ofNat 64 i) 16) (w₂ : g → InRegions s.wr (D + BitVec.ofNat 64 i) 16) :
    ∃ s', runBlock isa (xor16Body g) s = some s' ∧
      s'.mem = xw g s.mem (S + BitVec.ofNat 64 i) (D + BitVec.ofNat 64 i)
        (xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) 16) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 16 ∧
      s'.zf = some (BitVec.ofNat 64 i + 16 - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdx hk hi
  have e₃ := ea_idx s .rdi hd hi
  cases g
  · refine ⟨_, by
      simp only [xor16Body, srcB, dstB, kB, imm, List.cons_append, List.nil_append, Bool.false_eq_true,
        ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load128,
        State.store128, State.ea, State.setV, State.lane, e₁, e₂, r₁, r₂, w₁, ite_true, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, xw, Bool.false_eq_true, ite_false, xb]
      exact writeW_xor128 _ _ _ _ _
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk8]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
    · intro r hr l hl
      simp only [List.mem_singleton] at hr
      simp only [zlane_setReg, zlane_arithFlags]
      simp only [State.zlane, State.lane, hr, ite_false]
  · have w₂' := w₂ rfl
    refine ⟨_, by
      simp only [xor16Body, srcB, dstB, kB, imm, List.cons_append, List.nil_append, ite_true,
        runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load128,
        State.store128, State.ea, State.setV, State.lane, e₁, e₂, e₃, r₁, r₂, w₁, w₂', ite_true,
        Option.map_some, Option.bind_some]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, xw, ite_true, xb]
      rw [show ∀ a b : BitVec 128, VBinOp.vpxor.sse.eval a b = a ^^^ b from fun _ _ => rfl,
        writeW_xor128, writeW_xor128]
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk8]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
    · intro r hr l hl
      simp only [List.mem_singleton] at hr
      simp only [zlane_setReg, zlane_arithFlags]
      simp only [State.zlane, State.lane, hr, ite_false]

/-- An 8-byte store of the XOR of two 8-byte values loaded. -/
theorem writeW_xor64 (m src : Mem) (a b c : Addr) :
    m.writeW a (src.readW b 64 ^^^ src.readW c 64) =
      writeBytes m a (List.zipWith (· ^^^ ·) (bytesAt src b 8) (bytesAt src c 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (64 / 8)) (BitVec.setWidth 64 (src.read b (64 / 8)) ^^^
      BitVec.setWidth 64 (src.read c (64 / 8)))) = src.read b 8 ^^^ src.read c 8 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read src b (List.mem_range.mp hj),
    Mem.extractLsb'_read src c (List.mem_range.mp hj)]

/-- A 4-byte store of the XOR of two 4-byte values loaded. -/
theorem writeW_xor32 (m src : Mem) (a b c : Addr) :
    m.writeW a (src.readW b 32 ^^^ src.readW c 32) =
      writeBytes m a (List.zipWith (· ^^^ ·) (bytesAt src b 4) (bytesAt src c 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (32 / 8)) (BitVec.setWidth 32 (src.read b (32 / 8)) ^^^
      BitVec.setWidth 32 (src.read c (32 / 8)))) = src.read b 4 ^^^ src.read c 4 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read src b (List.mem_range.mp hj),
    Mem.extractLsb'_read src c (List.mem_range.mp hj)]

/-- `xorWord g w`: eight (if `w`) or four bytes XORed. -/
theorem xorWord_ok (g w : Bool) (s : State) {S K D : Addr} {i : Nat} (hs : s.gpr .rsi = S)
    (hk : s.gpr .rdx = K) (hd : s.gpr .rdi = D) (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) (if w then 8 else 4))
    (r₂ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) (if w then 8 else 4))
    (w₁ : InRegions s.wr (S + BitVec.ofNat 64 i) (if w then 8 else 4))
    (w₂ : g → InRegions s.wr (D + BitVec.ofNat 64 i) (if w then 8 else 4)) :
    ∃ s', runBlock isa (xorWord g w) s = some s' ∧
      s'.mem = xw g s.mem (S + BitVec.ofNat 64 i) (D + BitVec.ofNat 64 i)
        (xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 (i + if w then 8 else 4) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdx hk hi
  have e₃ := ea_idx s .rdi hd hi
  have w₁' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) (if w then 8 else 4) := by
    obtain ⟨x, hx, hc⟩ := w₁; exact ⟨x, List.mem_append_right _ hx, hc⟩
  cases w <;> cases g <;> simp only [Bool.false_eq_true, ite_true, ite_false] at r₁ r₂ w₁ w₁' w₂ ⊢
  · refine ⟨_, by xrun [xorWord, srcB, kB, e₁, e₂, r₁, r₂, w₁], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, Bool.false_eq_true, ite_false, xb]
      rw [← writeW_xor32]; congr 1; simp
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · have w₂' := w₂ trivial
    refine ⟨_, by xrun [xorWord, srcB, kB, dstB, e₁, e₂, e₃, r₁, r₂, w₁, w₂'], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, ite_true, xb]
      rw [← writeW_xor32, ← writeW_xor32]; congr 1 <;> simp
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · refine ⟨_, by xrun [xorWord, srcB, kB, e₁, e₂, r₁, r₂, w₁], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, Bool.false_eq_true, ite_false, xb]
      rw [← writeW_xor64]
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · have w₂' := w₂ trivial
    refine ⟨_, by xrun [xorWord, srcB, kB, dstB, e₁, e₂, e₃, r₁, r₂, w₁, w₂'], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, ite_true, xb]
      rw [← writeW_xor64, ← writeW_xor64]
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by simp [bytesAt]

theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  have := writeBytes_snoc m a [] b (by decide)
  rw [List.nil_append, writeBytes_nil] at this
  rw [this]; simp

/-- The byte loop's body. -/
abbrev xor1Body (g : Bool) : List Instr :=
  ([.movzx8 .rax srcB, .movzx8 .r9 kB, .alu .xor .rax (.reg .r9), .store8 srcB .rax] : List Instr) ++
    (if g then ([.store8 dstB .rax] : List Instr) else ([] : List Instr)) ++ ([.alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)] : List Instr)

theorem xor1Step_ok (g : Bool) (s : State) {S K D : Addr} {i n : Nat} (hs : s.gpr .rsi = S)
    (hk : s.gpr .rdx = K) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (r₂ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (w₁ : InRegions s.wr (S + BitVec.ofNat 64 i) 1) (w₂ : g → InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (xor1Body g) s = some s' ∧
      s'.mem = xw g s.mem (S + BitVec.ofNat 64 i) (D + BitVec.ofNat 64 i)
        [s.mem (S + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)] ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ZKeep [] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdx hk hi
  have e₃ := ea_idx s .rdi hd hi
  have w₁' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w₁; exact ⟨x, List.mem_append_right _ hx, hc⟩
  cases g
  · refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, BitVec.reduceSignExtend, xor1Body, srcB, dstB, kB,
        imm, List.cons_append, List.nil_append, Bool.false_eq_true, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, ite_true, ite_false, e₁, e₂, r₁, r₂, w₁]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, setWidth8_xor, xw, Bool.false_eq_true, ite_false, writeW8_eq]
    · simp [gpr_setReg, hi]
    · simp [hi, hn]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  · have w₂' := w₂ rfl
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, BitVec.reduceSignExtend, xor1Body, srcB, dstB, kB,
        imm, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, ite_true, ite_false, e₁, e₂, e₃, r₁, r₂, w₁, w₂']
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, setWidth8_xor, xw, ite_true, writeW8_eq]
    · simp [gpr_setReg, hi]
    · simp [hi, hn]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]

/-- What `xorText g` needs: `n` bytes at `S` (read and written), at `K` (read)
and, if `g`, at `D` (written), apart. -/
structure XorPre (g : Bool) (s : State) (S K D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdx : s.gpr .rdx = K
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  lt : n < 2 ^ 63
  rS : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  rK : Covers [⟨K, n⟩] (s.rd ++ s.wr)
  wS : Covers [⟨S, n⟩] s.wr
  wD : g → Covers [⟨D, n⟩] s.wr
  dSK : (⟨S, n⟩ : Region).Disjoint ⟨K, n⟩
  dSD : g → (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩
  dKD : g → (⟨K, n⟩ : Region).Disjoint ⟨D, n⟩

/-- What `xorText g` leaves. -/
def XorPost (g : Bool) (s : State) (S K D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = xw g s.mem S D (xb s.mem S K n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    ZKeep [.xmm4] s s'

theorem xw_nil (g : Bool) (m : Mem) (S D : Addr) : xw g m S D [] = m := by
  cases g <;> simp [xw, writeBytes_nil]

theorem xw_frame (g : Bool) (m : Mem) (S D : Addr) (xs : List Byte) :
    Frame [⟨S, xs.length⟩, ⟨D, xs.length⟩] m (xw g m S D xs) := by
  cases g
  · exact (writeBytes_frame' m rfl).mono (by simp)
  · exact ((writeBytes_frame' m rfl).mono (by simp)).trans ((writeBytes_frame' _ rfl).mono (by simp))

/-- The bytes from `i` on of a buffer apart from `D`'s are as they were. -/
theorem xw_bytesAt {g : Bool} {m : Mem} {S D P : Addr} {xs : List Byte} {n i k : Nat} (hlen : xs.length = i)
    (hik : i + k ≤ n) (hn : n < 2 ^ 63)
    (hS : (⟨P + BitVec.ofNat 64 i, k⟩ : Region).Disjoint ⟨S, i⟩)
    (hD : g → (⟨P + BitVec.ofNat 64 i, k⟩ : Region).Disjoint ⟨D, i⟩) :
    bytesAt (xw g m S D xs) (P + BitVec.ofNat 64 i) k = bytesAt m (P + BitVec.ofNat 64 i) k := by
  cases g
  · exact bytesAt_frame (writeBytes_frame' m hlen) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS) (by omega_arith)
  · refine bytesAt_frame (rs := [⟨S, i⟩, ⟨D, i⟩]) (((writeBytes_frame' m hlen).mono (by simp)).trans
      ((writeBytes_frame' _ hlen).mono (by simp))) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hS
    · exact hD rfl

theorem xw_append (g : Bool) (m : Mem) {S D : Addr} {n : Nat} (xs ys : List Byte) (hn : n < 2 ^ 63)
    (hxy : xs.length + ys.length ≤ n) (hd : g → (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) :
    xw g (xw g m S D xs) (S + BitVec.ofNat 64 xs.length) (D + BitVec.ofNat 64 xs.length) ys =
      xw g m S D (xs ++ ys) := by
  cases g
  · simp only [xw, Bool.false_eq_true, ite_false]
    exact writeBytes_append _ _ _ _ (by omega_arith)
  · simp only [xw, ite_true]
    rw [writeBytes_comm (writeBytes m S xs) D (S + BitVec.ofNat 64 xs.length) xs ys
      (((hd rfl).symm.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base S (by omega_arith))),
      writeBytes_append _ _ _ _ (by omega_arith), writeBytes_append _ _ _ _ (by omega_arith)]

theorem xorText_ok (g : Bool) (s : State) {S K D : Addr} {n : Nat} (h : XorPre g s S K D n) :
    WP isa (xorText g) s (XorPost g s S K D n) := by
  have hn63 := h.lt
  refine WP.seq (WP.mono (copySetup_ok s h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  -- The bytes from `i` on, at `S` and at `K`, after the first `i` written.
  have rdS : ∀ {xs : List Byte} {i k : Nat}, xs.length = i → i + k ≤ n →
      bytesAt (xw g s.mem S D xs) (S + BitVec.ofNat 64 i) k = bytesAt s.mem (S + BitVec.ofNat 64 i) k :=
    fun hl hik => xw_bytesAt hl hik hn63 (Offset.disjoint_base S (Nat.le_refl _) (by omega_arith))
      fun hg => ((h.dSD hg).sub_left (Offset.sub_base S hik)).sub_right (Region.sub_prefix (by omega_arith))
  have rdK : ∀ {xs : List Byte} {i k : Nat}, xs.length = i → i + k ≤ n →
      bytesAt (xw g s.mem S D xs) (K + BitVec.ofNat 64 i) k = bytesAt s.mem (K + BitVec.ofNat 64 i) k :=
    fun hl hik => xw_bytesAt hl hik hn63
      ((h.dSK.symm.sub_left (Offset.sub_base K hik)).sub_right (Region.sub_prefix (by omega_arith)))
      fun hg => ((h.dKD hg).sub_left (Offset.sub_base K hik)).sub_right (Region.sub_prefix (by omega_arith))
  -- After the 16-byte loop: the first `16 ⌊n / 16⌋` bytes.
  let q := n / 16
  have mid : WP isa (.ite .e (.block []) (.loop (.block (xor16Body g)) .ne)) s₁ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 (16 * q) ∧ t.mem = xw g s.mem S D (xb s.mem S K (16 * q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4] s t := by
    refine WP.ite (decide (16 * q = 0)) (by simp only [eval, zf₁, q]) (fun hz => ?_) (fun hz => ?_)
    · have hq : 16 * q = 0 := of_decide_eq_true hz
      refine WP.block_nil ⟨by rw [r10₁, hq], by rw [m₁, hq]; simp [xb, bytesAt, xw_nil],
        fun r a b c d => g₁ r b d, rd₁, wr₁, z₁.mono (by simp)⟩
    · have hq : 0 < q := by have := of_decide_eq_false hz; omega_arith
      refine WP.loop (M := isa) (body := .block (xor16Body g)) (c := .ne)
        (fun (k : Nat) (t : State) => ∃ j, k = q - j ∧ j < q ∧ t.gpr .r10 = BitVec.ofNat 64 (16 * j) ∧
          t.mem = xw g s.mem S D (xb s.mem S K (16 * j)) ∧
          (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
          t.gpr .r8 = BitVec.ofNat 64 (16 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (q - 0) _
        ⟨0, rfl, hq, by rw [r10₁], by rw [m₁]; simp [xb, bytesAt, xw_nil], fun r a b c d => g₁ r b d,
          r8₁, rd₁, wr₁, z₁.mono (by simp)⟩
      rintro k t ⟨j, rfl, hj, r10, mem, g', r8, rd, wr, z⟩
      have hj16 : 16 * j + 16 ≤ n := by omega_arith
      have gg := fun r (hr : r ∈ [Reg.rsi, .rdx, .rdi]) => g' r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      obtain ⟨t', run', mem', r10', zf', g'', rd', wr', z'⟩ := xor16Step_ok g t
        (by rw [gg .rsi (by simp), h.rsi]) (by rw [gg .rdx (by simp), h.rdx]) (by rw [gg .rdi (by simp), h.rdi])
        r10 r8
        (by rw [rd, wr]; exact in_of_covers16 h.rS hj16 (by omega_arith))
        (by rw [rd, wr]; exact in_of_covers16 h.rK hj16 (by omega_arith))
        (by rw [wr]; exact in_of_covers16 h.wS hj16 (by omega_arith))
        (fun hg => by rw [wr]; exact in_of_covers16 (h.wD hg) hj16 (by omega_arith))
      refine WP.of_runBlock ⟨t', run', ?_⟩
      have hlen : (xb s.mem S K (16 * j)).length = 16 * j := length_xb _ _ _ _
      have hsrc : xb t.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16 =
          xb s.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16 := by
        simp only [xb]; rw [mem, rdS hlen hj16, rdK hlen hj16]
      have hmem : t'.mem = xw g s.mem S D (xb s.mem S K (16 * (j + 1))) := by
        rw [mem', hsrc, mem, show 16 * (j + 1) = 16 * j + 16 by omega_arith, xb_add]
        have := xw_append g s.mem (xb s.mem S K (16 * j))
          (xb s.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16) hn63
          (by rw [length_xb, length_xb]; omega_arith) h.dSD
        rw [hlen] at this
        exact this
      have hz : t'.zf = some (decide (j + 1 = q)) := by
        rw [zf', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, sub_beq (by omega_arith) (by omega_arith)]
        congr 1; simp only [decide_eq_decide]; omega_arith
      have gg' : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c d => by
        rw [g'' r d, g' r a b c d]
      have r10'' : t'.gpr .r10 = BitVec.ofNat 64 (16 * (j + 1)) := by
        rw [r10', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; congr 1
      by_cases he : j + 1 = q
      · left
        refine ⟨by simp [eval, hz, he], by rw [r10'', he], by rw [hmem, he], gg', by rw [rd', rd],
          by rw [wr', wr], z.trans z'⟩
      · right
        refine ⟨by simp [eval, hz, he], q - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, r10'', hmem, gg',
          by rw [g'' _ (by decide), r8], by rw [rd', rd], by rw [wr', wr], z.trans z'⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- The state after the first `i` bytes.
  let Mid : Nat → State → Prop := fun i t => t.gpr .r10 = BitVec.ofNat 64 i ∧
    t.mem = xw g s.mem S D (xb s.mem S K i) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    ZKeep [.xmm4] s t
  have regs : ∀ {t : State}, (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) →
      t.gpr .rsi = S ∧ t.gpr .rdx = K ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 n := fun g' =>
    ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rsi],
      by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rdx],
      by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rdi],
      by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rcx]⟩
  -- Eight or four bytes, through `rax`.
  have word : ∀ (w : Bool) {i : Nat} {t : State} {R : BitVec 64}, i + (if w then 8 else 4) ≤ n → Mid i t →
      t.gpr .r8 = R → WP isa (.block (xorWord g w)) t fun u => Mid (i + if w then 8 else 4) u ∧ u.gpr .r8 = R := by
    intro w i t R hik ⟨r10, mem, g', rd, wr, z⟩ hr8
    obtain ⟨hsi, hdx, hdi, -⟩ := regs g'
    have cov : ∀ {p : Addr} {rs : List Region}, Covers [⟨p, n⟩] rs →
        InRegions rs (p + BitVec.ofNat 64 i) (if w then 8 else 4) := fun hc =>
      hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hik (by omega_arith)⟩
    obtain ⟨t', run', mem', r10', g'', rd', wr', z'⟩ := xorWord_ok g w t hsi hdx hdi r10
      (by rw [rd, wr]; exact cov h.rS) (by rw [rd, wr]; exact cov h.rK) (by rw [wr]; exact cov h.wS)
      (fun hg => by rw [wr]; exact cov (h.wD hg))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen : (xb s.mem S K i).length = i := length_xb _ _ _ _
    have hsrc : xb t.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4) =
        xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4) := by
      simp only [xb]; rw [mem, rdS hlen hik, rdK hlen hik]
    have hmem : t'.mem = xw g s.mem S D (xb s.mem S K (i + if w then 8 else 4)) := by
      rw [mem', hsrc, mem, xb_add]
      have := xw_append g s.mem (xb s.mem S K i)
        (xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4)) hn63
        (by rw [length_xb, length_xb]; omega_arith) h.dSD
      rw [hlen] at this
      exact this
    exact ⟨⟨r10', hmem, fun r a b c d => by rw [g'' r a d, g' r a b c d], by rw [rd', rd], by rw [wr', wr],
      z.trans (z'.mono (by simp))⟩, by rw [g'' _ (by decide) (by decide), hr8]⟩
  -- The bytes from `i < n` on, one at a time.
  have bytes : ∀ {i : Nat} {t : State}, i < n → Mid i t → WP isa (Impl.AesGcm.X86_64.Short.xorBytes g) t (XorPost g s S K D n) := by
    intro i₀ t₀ hi₀ ⟨r10₀, m₀, g₀, rd₀, wr₀, z₀⟩
    refine WP.loop (M := isa) (body := .block (xor1Body g)) (c := .ne)
      (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
        t.mem = xw g s.mem S D (xb s.mem S K i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        ZKeep [.xmm4] s t) ?_ (n - i₀) _ ⟨i₀, rfl, hi₀, r10₀, m₀, g₀, rd₀, wr₀, z₀⟩
    rintro k t ⟨i, rfl, hi, r10, mem, g', rd, wr, z⟩
    obtain ⟨hsi, hdx, hdi, hcx'⟩ := regs g'
    obtain ⟨t', run', mem', r10', zf', g'', rd', wr', z'⟩ := xor1Step_ok g t hsi hdx hdi r10 hcx'
      (by rw [rd, wr]; exact in_of_covers h.rS hi (by omega_arith))
      (by rw [rd, wr]; exact in_of_covers h.rK hi (by omega_arith))
      (by rw [wr]; exact in_of_covers h.wS hi (by omega_arith))
      (fun hg => by rw [wr]; exact in_of_covers (h.wD hg) hi (by omega_arith))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen : (xb s.mem S K i).length = i := length_xb _ _ _ _
    have hS1 := rdS hlen (show i + 1 ≤ n by omega_arith)
    have hK1 := rdK hlen (show i + 1 ≤ n by omega_arith)
    rw [bytesAt_one, bytesAt_one] at hS1 hK1
    have hmem : t'.mem = xw g s.mem S D (xb s.mem S K (i + 1)) := by
      rw [mem', mem, List.cons.inj hS1 |>.1, List.cons.inj hK1 |>.1, xb_succ]
      have := xw_append g s.mem (xb s.mem S K i)
        [s.mem (S + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)] hn63 (by rw [hlen]; simp; omega_arith) h.dSD
      rw [hlen] at this
      exact this
    have hz : t'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    have gg' : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c d => by
      rw [g'' r a c d, g' r a b c d]
    have zk : ZKeep [.xmm4] s t' := z.trans (z'.mono (by simp))
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg', by rw [rd', rd], by rw [wr', wr], zk⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by rw [r10', succ_ofNat],
        hmem, gg', by rw [rd', rd], by rw [wr', wr], zk⟩
  -- `t`, the bytes left after the 16-byte loop, and the bits of `n` tested.
  have M₂ : Mid (16 * q) s₂ := ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩
  generalize ht : n % 16 = t
  have ht16 : t < 16 := by omega_arith
  have hn : n = 16 * q + t := by omega_arith
  have tst : ∀ (k : Nat), k < 16 → ∀ {i : Nat} {u : State}, Mid i u →
      WP isa (.block [.alu .test .rcx (imm k)]) u fun v => Mid i v ∧ v.zf = some (decide (t &&& k = 0)) := by
    intro k hk i u ⟨r10, m, g', rd, wr, z⟩
    have hcx : u.gpr .rcx = BitVec.ofNat 64 n := (regs g').2.2.2
    have hand : BitVec.ofNat 64 n &&& BitVec.ofNat 64 k = BitVec.ofNat 64 (t &&& k) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : n &&& k = t &&& k := by
        have e := Nat.and_mod_two_pow (a := n) (b := k) (n := 4)
        rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (show k < 2 ^ 4 by omega_arith)),
          Nat.mod_eq_of_lt (show k < 2 ^ 4 by omega_arith), show 2 ^ 4 = 16 from rfl, ht] at e
        exact e
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith), ← h1, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega_arith))]
    have hz : (BitVec.ofNat 64 (t &&& k) == 0) = decide (t &&& k = 0) := by
      have hlt : t &&& k < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_left (by omega_arith)
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        exact this
      · intro e; rw [e]; rfl
    apply WP.of_runBlock
    refine ⟨_, by xrun [hcx], ?_⟩
    refine ⟨⟨by simp only [gpr_arithFlags]; exact r10, by simp only [mem_arithFlags]; exact m,
      fun r a b c d => by simp [gpr_arithFlags, g' r a b c d],
      by simp only [rd_arithFlags]; exact rd, by simp only [wr_arithFlags]; exact wr, z.trans fun _ _ _ _ => rfl⟩, ?_⟩
    simp only [zf_arithFlags, imm_eq (show k < 2 ^ 31 by omega_arith), hand, hz]
  -- None left.
  refine WP.seq (WP.mono (tst 15 (by decide) M₂) fun s₃ ⟨M₃, zf₃⟩ => ?_)
  refine WP.ite (decide (t &&& 15 = 0)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : t = 0 := by
      have := of_decide_eq_true hz; revert this; revert ht16; generalize t = x; revert x; decide
    obtain ⟨-, m, g', rd, wr, z⟩ := M₃
    exact WP.block_nil ⟨by rw [m, show 16 * q = n by omega_arith], g', rd, wr, z⟩
  have hpos : 0 < t := by
    have := of_decide_eq_false hz; revert this; revert ht16; generalize t = x; revert x; decide
  -- Fewer than 4: one at a time.
  refine WP.seq (WP.mono (tst 12 (by decide) M₃) fun s₄ ⟨M₄, zf₄⟩ => ?_)
  refine WP.ite (decide (t &&& 12 = 0)) (by simp only [eval, zf₄]) (fun _ => bytes (by omega_arith) M₄) (fun hb => ?_)
  -- Eight bytes, if `t` has bit 8.
  refine WP.seq (WP.mono (tst 8 (by decide) M₄) fun s₅ ⟨M₅, zf₅⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u : State) => Mid (16 * q + (t &&& 8)) u)
    (WP.ite (decide (t &&& 8 = 0)) (by simp only [eval, zf₅]) (fun hb => ?_) (fun hb => ?_)) fun s₆ M₆ => ?_)
  · have h0 : t &&& 8 = 0 := of_decide_eq_true hb
    rw [h0, Nat.add_zero]; exact WP.block_nil M₅
  · have h8 : t &&& 8 = 8 := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    have h8le : 8 ≤ t := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    rw [h8]
    exact WP.mono (word true (R := s₅.gpr .r8) (by simp only [ite_true]; omega_arith) M₅ rfl) fun u hu => hu.1
  -- Four bytes, if `t` has bit 4.
  refine WP.seq (WP.mono (tst 4 (by decide) M₆) fun s₇ ⟨M₇, zf₇⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u : State) => Mid (16 * q + (t &&& 8) + (t &&& 4)) u)
    (WP.ite (decide (t &&& 4 = 0)) (by simp only [eval, zf₇]) (fun hb => ?_) (fun hb => ?_)) fun s₈ M₈ => ?_)
  · have h0 : t &&& 4 = 0 := of_decide_eq_true hb
    rw [h0, Nat.add_zero]; exact WP.block_nil M₇
  · have h4 : t &&& 4 = 4 := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    have hle : (t &&& 8) + 4 ≤ t := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    rw [h4]
    exact WP.mono (word false (R := s₇.gpr .r8) (by simp only [Bool.false_eq_true, ite_false]; omega_arith) M₇ rfl)
      fun u hu => hu.1
  -- The last ones, if any, one at a time.
  have hsum : (t &&& 8) + (t &&& 4) + (t &&& 3) = t := by revert ht16; generalize t = x; revert x; decide
  refine WP.seq (WP.mono (tst 3 (by decide) M₈) fun s₉ ⟨M₉, zf₉⟩ => ?_)
  refine WP.ite (decide (t &&& 3 = 0)) (by simp only [eval, zf₉]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : t &&& 3 = 0 := of_decide_eq_true hz
    obtain ⟨-, m, g', rd, wr, z⟩ := M₉
    exact WP.block_nil ⟨by rw [m, show 16 * q + (t &&& 8) + (t &&& 4) = n by omega_arith], g', rd, wr, z⟩
  · have h3 : t &&& 3 ≠ 0 := of_decide_eq_false hz
    exact bytes (by omega_arith) M₉

end VG.Proof.AesGcm.X86_64.Short
