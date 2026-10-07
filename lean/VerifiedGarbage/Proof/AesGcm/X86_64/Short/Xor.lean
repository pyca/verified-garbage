import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy

/-!
# AES-GCM's short path on x86-64: the text

Untrusted: everything here is checked by Lean. `xorText g` XORs the `rcx`
bytes at `rsi` with those at `rdx` (the keystream), in place, and if `g` also
writes the result at `rdi`: 16 bytes at a time through `xmm4`, then one at a
time (`xorText_ok`); the three buffers do not overlap.
-/

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
  exact absurd (show Region.Contains ⟨q, ys.length⟩ a 1 by simp only [Region.Contains]; omega)
    (h a (by simp only [Region.Contains]; omega))

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

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by simp [bytesAt]

theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  have := writeBytes_snoc m a [] b (by decide)
  rw [List.nil_append, writeBytes_nil] at this
  rw [this]; simp

/-- The byte loop's body. -/
abbrev xor1Body (g : Bool) : List Instr :=
  [.movzx8 .rax srcB, .movzx8 .r9 kB, .alu .xor .rax (.reg .r9), .store8 srcB .rax] ++
    (if g then [.store8 dstB .rax] else []) ++ [.alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

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
      simp only [List.mem_singleton] at hr; subst hr; exact hS) (by omega)
  · refine bytesAt_frame (rs := [⟨S, i⟩, ⟨D, i⟩]) (((writeBytes_frame' m hlen).mono (by simp)).trans
      ((writeBytes_frame' _ hlen).mono (by simp))) (fun r hr => ?_) (by omega)
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
    exact writeBytes_append _ _ _ _ (by omega)
  · simp only [xw, ite_true]
    rw [writeBytes_comm (writeBytes m S xs) D (S + BitVec.ofNat 64 xs.length) xs ys
      (((hd rfl).symm.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base S (by omega))),
      writeBytes_append _ _ _ _ (by omega), writeBytes_append _ _ _ _ (by omega)]

theorem xorText_ok (g : Bool) (s : State) {S K D : Addr} {n : Nat} (h : XorPre g s S K D n) :
    WP isa (xorText g) s (XorPost g s S K D n) := by
  have hn63 := h.lt
  refine WP.seq (WP.mono (copySetup_ok s h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  -- The bytes from `i` on, at `S` and at `K`, after the first `i` written.
  have rdS : ∀ {xs : List Byte} {i k : Nat}, xs.length = i → i + k ≤ n →
      bytesAt (xw g s.mem S D xs) (S + BitVec.ofNat 64 i) k = bytesAt s.mem (S + BitVec.ofNat 64 i) k :=
    fun hl hik => xw_bytesAt hl hik hn63 (Offset.disjoint_base S (Nat.le_refl _) (by omega))
      fun hg => ((h.dSD hg).sub_left (Offset.sub_base S hik)).sub_right (Region.sub_prefix (by omega))
  have rdK : ∀ {xs : List Byte} {i k : Nat}, xs.length = i → i + k ≤ n →
      bytesAt (xw g s.mem S D xs) (K + BitVec.ofNat 64 i) k = bytesAt s.mem (K + BitVec.ofNat 64 i) k :=
    fun hl hik => xw_bytesAt hl hik hn63
      ((h.dSK.symm.sub_left (Offset.sub_base K hik)).sub_right (Region.sub_prefix (by omega)))
      fun hg => ((h.dKD hg).sub_left (Offset.sub_base K hik)).sub_right (Region.sub_prefix (by omega))
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
    · have hq : 0 < q := by have := of_decide_eq_false hz; omega
      refine WP.loop (M := isa) (body := .block (xor16Body g)) (c := .ne)
        (fun (k : Nat) (t : State) => ∃ j, k = q - j ∧ j < q ∧ t.gpr .r10 = BitVec.ofNat 64 (16 * j) ∧
          t.mem = xw g s.mem S D (xb s.mem S K (16 * j)) ∧
          (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
          t.gpr .r8 = BitVec.ofNat 64 (16 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (q - 0) _
        ⟨0, rfl, hq, by rw [r10₁], by rw [m₁]; simp [xb, bytesAt, xw_nil], fun r a b c d => g₁ r b d,
          r8₁, rd₁, wr₁, z₁.mono (by simp)⟩
      rintro k t ⟨j, rfl, hj, r10, mem, g', r8, rd, wr, z⟩
      have hj16 : 16 * j + 16 ≤ n := by omega
      have gg := fun r (hr : r ∈ [Reg.rsi, .rdx, .rdi]) => g' r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      obtain ⟨t', run', mem', r10', zf', g'', rd', wr', z'⟩ := xor16Step_ok g t
        (by rw [gg .rsi (by simp), h.rsi]) (by rw [gg .rdx (by simp), h.rdx]) (by rw [gg .rdi (by simp), h.rdi])
        r10 r8
        (by rw [rd, wr]; exact in_of_covers16 h.rS hj16 (by omega))
        (by rw [rd, wr]; exact in_of_covers16 h.rK hj16 (by omega))
        (by rw [wr]; exact in_of_covers16 h.wS hj16 (by omega))
        (fun hg => by rw [wr]; exact in_of_covers16 (h.wD hg) hj16 (by omega))
      refine WP.of_runBlock ⟨t', run', ?_⟩
      have hlen : (xb s.mem S K (16 * j)).length = 16 * j := length_xb _ _ _ _
      have hsrc : xb t.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16 =
          xb s.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16 := by
        simp only [xb]; rw [mem, rdS hlen hj16, rdK hlen hj16]
      have hmem : t'.mem = xw g s.mem S D (xb s.mem S K (16 * (j + 1))) := by
        rw [mem', hsrc, mem, show 16 * (j + 1) = 16 * j + 16 by omega, xb_add]
        have := xw_append g s.mem (xb s.mem S K (16 * j))
          (xb s.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16) hn63
          (by rw [length_xb, length_xb]; omega) h.dSD
        rw [hlen] at this
        exact this
      have hz : t'.zf = some (decide (j + 1 = q)) := by
        rw [zf', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]
        congr 1; simp only [decide_eq_decide]; omega
      have gg' : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c d => by
        rw [g'' r d, g' r a b c d]
      have r10'' : t'.gpr .r10 = BitVec.ofNat 64 (16 * (j + 1)) := by
        rw [r10', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; congr 1
      by_cases he : j + 1 = q
      · left
        refine ⟨by simp [eval, hz, he], by rw [r10'', he], by rw [hmem, he], gg', by rw [rd', rd],
          by rw [wr', wr], z.trans z'⟩
      · right
        refine ⟨by simp [eval, hz, he], q - (j + 1), by omega, j + 1, rfl, by omega, r10'', hmem, gg',
          by rw [g'' _ (by decide), r8], by rw [rd', rd], by rw [wr', wr], z.trans z'⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- The last `n mod 16` bytes, one at a time.
  have hcx : s₂.gpr .rcx = BitVec.ofNat 64 n := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.rcx]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.zf = some (decide (16 * q = n)) ∧ t.gpr = s₂.gpr ∧
      t.mem = s₂.mem ∧ t.rd = s₂.rd ∧ t.wr = s₂.wr ∧ ZKeep [] s₂ t) ?_ fun s₃ ⟨zf₃, g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
  · apply WP.of_runBlock
    refine ⟨_, by xrun [r10₂, hcx], ?_⟩
    refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    simp only [zf_arithFlags]; rw [sub_beq (by omega) (by omega)]
  refine WP.ite (decide (16 * q = n)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have hq : 16 * q = n := of_decide_eq_true hz
    exact WP.block_nil ⟨by rw [m₃, m₂, hq], fun r a b c d => by rw [g₃, g₂ r a b c d], by rw [rd₃, rd₂],
      by rw [wr₃, wr₂], z₂.trans (z₃.mono (by simp))⟩
  · have hq : 16 * q < n := by have := of_decide_eq_false hz; omega
    refine WP.loop (M := isa) (body := .block (xor1Body g)) (c := .ne)
      (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
        t.mem = xw g s.mem S D (xb s.mem S K i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        ZKeep [.xmm4] s t) ?_ (n - 16 * q) _
      ⟨16 * q, rfl, hq, by rw [g₃, r10₂], by rw [m₃, m₂], fun r a b c d => by rw [g₃, g₂ r a b c d],
        by rw [rd₃, rd₂], by rw [wr₃, wr₂], z₂.trans (z₃.mono (by simp))⟩
    rintro k t ⟨i, rfl, hi, r10, mem, g', rd, wr, z⟩
    have gg := fun r (hr : r ∈ [Reg.rsi, .rdx, .rdi, .rcx]) => g' r
      (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
    obtain ⟨t', run', mem', r10', zf', g'', rd', wr', z'⟩ := xor1Step_ok g t
      (by rw [gg .rsi (by simp), h.rsi]) (by rw [gg .rdx (by simp), h.rdx]) (by rw [gg .rdi (by simp), h.rdi])
      r10 (by rw [gg .rcx (by simp), h.rcx])
      (by rw [rd, wr]; exact in_of_covers h.rS hi (by omega))
      (by rw [rd, wr]; exact in_of_covers h.rK hi (by omega))
      (by rw [wr]; exact in_of_covers h.wS hi (by omega))
      (fun hg => by rw [wr]; exact in_of_covers (h.wD hg) hi (by omega))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen : (xb s.mem S K i).length = i := length_xb _ _ _ _
    have hS1 := rdS hlen (show i + 1 ≤ n by omega)
    have hK1 := rdK hlen (show i + 1 ≤ n by omega)
    rw [bytesAt_one, bytesAt_one] at hS1 hK1
    have hmem : t'.mem = xw g s.mem S D (xb s.mem S K (i + 1)) := by
      rw [mem', mem, List.cons.inj hS1 |>.1, List.cons.inj hK1 |>.1, xb_succ]
      have := xw_append g s.mem (xb s.mem S K i)
        [s.mem (S + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)] hn63 (by rw [hlen]; simp; omega) h.dSD
      rw [hlen] at this
      exact this
    have hz : t'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg' : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c d => by
      rw [g'' r a c d, g' r a b c d]
    have zk : ZKeep [.xmm4] s t' := z.trans (z'.mono (by simp))
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg', by rw [rd', rd], by rw [wr', wr], zk⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
        hmem, gg', by rw [rd', rd], by rw [wr', wr], zk⟩

end VG.Proof.AesGcm.X86_64.Short
