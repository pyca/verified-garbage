module

public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Run
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Sm4Gcm.Arm.Loops`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `r3` bytes
from `r1` to `r2`, and `xorLoop` XORs `r3` bytes at `r1` into those at `r2`,
a byte at a time through advancing pointers, counting `r3` down to zero
(`copyLoop_ok`, `xorLoop_ok`); the buffers do not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega_arith) (by omega_arith)⟩

/-- What the loops need of the state: `n` (at least 1) bytes at the 32-bit
pointers `S` (read) and `D` (written). -/
structure LoopPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  r1 : s.gpr .r1 = S
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fitS : S.toNat + n ≤ 2 ^ 32
  fitD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨State.addr D, n⟩] s.wr
  disj : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr D, n⟩

/-- What the loops leave, but memory. -/
structure LoopOut (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  r1 : s'.gpr .r1 = S + BitVec.ofNat 32 n
  r2 : s'.gpr .r2 = D + BitVec.ofNat 32 n
  r3 : s'.gpr .r3 = 0
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem addr_i {P : BitVec 32} {n i : Nat} (hf : P.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    State.addr (P + BitVec.ofNat 32 i) = State.addr P + BitVec.ofNat 64 i := addr_add (by omega_arith)

theorem setWidth8_32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem dec32 {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - (i + 1)) := by
  rw [ofNat_sub32 (by omega_arith) (by omega_arith)]; congr 1

theorem z_dec {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - (i + 1)) == 0) = decide (i + 1 = n) := by
  rw [z_cmp0 (by omega_arith)]; congr 1; apply propext; omega_arith

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.ldrb .r12 .r1 0, .strb .r12 .r2 0, addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]

theorem copyStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 i)
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 i) (hn : s.gpr .r3 = BitVec.ofNat 32 (n - i))
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i)) (s.mem (State.addr (S + BitVec.ofNat 32 i))) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨_, by arun [hs, hd, hn, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, setWidth8_32]
  · simp [gpr_setReg, hs, add32_ofNat_assoc]
  · simp [gpr_setReg, hd, add32_ofNat_assoc]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)

theorem copyLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) n) ∧
      LoopOut s S D n s' := by
  have hn32 : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r1 = S + BitVec.ofNat 32 i ∧
      t.gpr .r2 = D + BitVec.ofNat 32 i ∧ t.gpr .r3 = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1, add_ofNat_zero], by rw [h.r2, add_ofNat_zero], by rw [h.r3]; rfl,
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r1, r2, r3, mem, g, rd, wr, sp⟩
  have aS := addr_i h.fitS hi
  have aD := addr_i h.fitD hi
  obtain ⟨t', run', mem', r1', r2', r3', z', g', rd', wr', sp'⟩ := copyStep_ok t r1 r2 r3
    (by rw [rd, wr, aS]; exact in_of_covers h.rd hi (by omega_arith))
    (by rw [wr, aD]; exact in_of_covers h.wr hi (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem (State.addr S) i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (i + 1)) := by
    rw [mem', mem, aS, aD, src_kept h.disj hi (by omega_arith) _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem _ (bytesAt s.mem _ i) _ (by rw [hlen]; omega_arith), hlen]
  have hz : t'.z = decide (i + 1 = n) := by rw [z', dec32 hi hn32, z_dec hi hn32]
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  have ev : isa.eval .ne t' = some !decide (i + 1 = n) := eval_ne' hz
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r1', he], by rw [r2', he], ?_,
      fun r h₀ h₁ h₂ h₃ h₄ => gg r h₁ h₂ h₃ h₄, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r3', dec32 hi hn32, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r1', r2',
      by rw [r3', dec32 hi hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.ldrb .r12 .r2 0, .ldrb .r0 .r1 0, .dp .eor .r12 .r12 (.reg .r0), .strb .r12 .r2 0,
    addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : BitVec 32)).setWidth 8 = a ^^^ b := by
  ext j hj; simp

theorem xorStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 i)
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 i) (hn : s.gpr .r3 = BitVec.ofNat 32 (n - i))
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa xorBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        (s.mem (State.addr (D + BitVec.ofNat 32 i)) ^^^ s.mem (State.addr (S + BitVec.ofNat 32 i))) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have w' : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1 := in_left w
  refine ⟨_, by arun [hs, hd, hn, add_ofNat_zero, r, w, w'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, setWidth8_xor]
  · simp [gpr_setReg, hs, add32_ofNat_assoc]
  · simp [gpr_setReg, hd, add32_ofNat_assoc]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · intro r h₀ h₁ h₂ h₃ h₄; simp [gpr_setReg, h₀, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    xorBytes m D S (i + 1) = xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [xorBytes, bytesAt_succ, List.zipWith_append, Cmac.bytesAt_length]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (xorBytes m D S n).length = n := by
  simp [xorBytes, Cmac.bytesAt_length]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 63) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith), Nat.lt_irrefl, ite_false]

theorem xorLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : LoopPre s S D n) :
    WP isa xorLoop s fun s' =>
      s'.mem = writeBytes s.mem (State.addr D) (xorBytes s.mem (State.addr D) (State.addr S) n) ∧
      LoopOut s S D n s' := by
  have hn32 : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r1 = S + BitVec.ofNat 32 i ∧
      t.gpr .r2 = D + BitVec.ofNat 32 i ∧ t.gpr .r3 = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (xorBytes s.mem (State.addr D) (State.addr S) i) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1, add_ofNat_zero], by rw [h.r2, add_ofNat_zero], by rw [h.r3]; rfl,
      by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r1, r2, r3, mem, g, rd, wr, sp⟩
  have aS := addr_i h.fitS hi
  have aD := addr_i h.fitD hi
  obtain ⟨t', run', mem', r1', r2', r3', z', g', rd', wr', sp'⟩ := xorStep_ok t r1 r2 r3
    (by rw [rd, wr, aS]; exact in_of_covers h.rd hi (by omega_arith))
    (by rw [wr, aD]; exact in_of_covers h.wr hi (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_xorBytes s.mem (State.addr D) (State.addr S) i
  have hmem : t'.mem = writeBytes s.mem (State.addr D) (xorBytes s.mem (State.addr D) (State.addr S) (i + 1)) := by
    rw [mem', mem, aS, aD, src_kept h.disj hi (by omega_arith) _ hlen, dst_kept hi (by omega_arith) _ hlen, xorBytes_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  have hz : t'.z = decide (i + 1 = n) := by rw [z', dec32 hi hn32, z_dec hi hn32]
  have gg : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ => by rw [g' r h₀ h₁ h₂ h₃ h₄, g r h₀ h₁ h₂ h₃ h₄]
  have ev : isa.eval .ne t' = some !decide (i + 1 = n) := eval_ne' hz
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r1', he], by rw [r2', he], ?_, gg,
      by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r3', dec32 hi hn32, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r1', r2',
      by rw [r3', dec32 hi hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.Ghash1`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.Arm.Blocks`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: small blocks shared by the pieces

Untrusted: everything here is checked by Lean. `cmp r, #0` (`cmp0_ok`), and
`minLen`: `r3 := min (16 - r6, r5)`, from the carry of a comparison
(`minLen_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm

/-- `cmp r, #0` sets `Z` iff `r` holds 0. -/
theorem cmp0_ok (s : State) (r : Reg) {n : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.cmp r (imm 0)] s = some s' ∧ s'.z = decide (n = 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z_subFlags, h]; rw [z_cmp hn (by decide)]
  all_goals rfl

/-- `cmp r, #k`. -/
theorem cmpk_ok (s : State) (r : Reg) {n k : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) :
    ∃ s', runBlock isa [.cmp r (imm k)] s = some s' ∧ s'.z = decide (n = k) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [he], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z_subFlags, h]; rw [z_cmp hn hk]
  all_goals rfl

/-- What a block that keeps everything but some registers leaves. -/
structure Keeps (s s' : State) : Prop where
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- `r3 := min (16 - r6, r5)`. -/
theorem minLen_ok (s : State) {o n : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 o)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (ho : o ≤ 16) (hn : n < 2 ^ 32) :
    WP isa minLen s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min (16 - o) n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov .r3 (imm 16), .dp .sub .r3 .r3 (.reg .r6), .cmp .r5 (.reg .r3),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r3 = BitVec.ofNat 32 (16 - o) ∧ s₁.z = !decide (16 - o ≤ n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6, ofNat_sub32 ho (by decide)]
    · simp only [z_subFlags, c_subFlags, gpr_setReg, z_setReg, c_setReg, ite_true, ite_false, reduceCtorEq,
        h5, h6, ofNat_sub32 ho (by decide), toNat32 hn, toNat32 (show 16 - o < 2 ^ 32 by omega_using [])]
      cases decide (16 - o ≤ n) <;> rfl
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hr3, hz, hg, hk⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (!decide (16 - o ≤ n)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · refine WP.run (Q := fun s' => s' = s₁.setReg .r3 (s₁.gpr .r5)) ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r h₁ h₂ => ?_, hk.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    · rw [gpr_setReg_self, hg .r5 (by decide) (by decide), h5]
      simp at ht; rw [Nat.min_eq_right (by omega_using [ht])]
    · simp only [gpr_setReg, h₁, ite_false]; exact hg r h₁ h₂
  · refine WP.block_nil ⟨?_, hg, hk⟩
    simp at hf; rw [hr3, Nat.min_eq_left (by omega_using [hf])]

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: GHASH over blocks of the state, `T` or the data

Untrusted: everything here is checked by Lean. `ghCall_ok` is the frame of a
call of `vg_ghash` from a state whose registers are its arguments (the hash
subkey at `ctx + 240`, the accumulator at `st + yo`, the working space at
`W + 512`), and `ghash1 yo b o` continues the accumulator over the block at
`P = b + o` (`ghash1_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the working space at `W + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (c w sp : BitVec 32) (Y : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  spk : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {c st w sp k7 k8 : BitVec 32} {Y : Addr} {ds : List Block}
    (h : GhOut s c w sp Y ds s') (he : Env c st w sp k7 k8 s) : Env c st w sp k7 k8 s' :=
  he.of_saved h.saved h.spk h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The arguments of a call, from a state whose registers are its arguments,
for `n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_mk {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P (w + BitVec.ofNat 32 512) n := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega_using [hyo])
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, by rw [hk]; exact L.sp8, by rw [L.cN (by decide)]; have := L.cw; omega_using [this],
    by rw [L.stN (by omega_using [hyo])]; have := L.sw; omega_using [hyo, this], hfit, by rw [L.wN (by decide)]; have := L.ww; omega_using [this],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [eH, eY, eS, hk]
  · exact L.ctx_st (by decide) (by omega_using [hyo])
  · exact L.ctx_w (by decide) (by decide)
  · exact hpy
  · exact L.st_w (by omega_using [hyo]) (.inr ⟨by decide, by decide⟩)
  · exact hpw
  · exact L.stk_ctx (by decide)
  · exact L.stk_st (by omega_using [hyo])
  · exact hpk
  · exact L.stk_w (by decide)
  · exact covers_cons (he.perm.ctxC (by decide)) hpr
  · exact covers_cons (he.perm.stC (by omega_using [hyo])) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments, for
`n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_ok [VG.Proof.Gcm.Arm.GhashLaw] {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa ghFrame s (GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) (blocksAt s.mem (State.addr P) n)) := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega_using [hyo])
  have eS := L.wA (d := 512) (by decide)
  have hc := ghCall_mk L hyo he h0 h1 h2 h3 h12 hfit hpy hpw hpk hpr
  refine WP.mono (gh_call hc) fun s' h => ⟨h.rd, h.wr, h.sp, h.saved, ?_, ?_⟩
  · have f := h.frame; rw [eY, eS, he.sp] at f; exact f
  · have o := h.out; rw [eH, eY] at o; exact o

/-- The arguments of `ghash1`. -/
theorem ghArgs_ok {c st w sp k7 k8 : BitVec 32} {s : State} (he : Env c st w sp k7 k8 s) (yo : Nat) (b : Reg) (o : Nat)
    (hb : b = .r10 ∨ b = .r11) (hyo : encodable (BitVec.ofNat 32 yo) = true)
    (ho : encodable (BitVec.ofNat 32 o) = true) :
    ∃ s', runBlock isa [addI .r0 .r9 hO, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1),
        addI .r12 .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s'.gpr .r2 = s.gpr b + BitVec.ofNat 32 o ∧ s'.gpr .r3 = BitVec.ofNat 32 1 ∧
      s'.gpr .r12 = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  rcases hb with rfl | rfl
  all_goals
    refine ⟨_, by arun [hyo, ho], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h9]
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok [VG.Proof.Gcm.Arm.GhashLaw] {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) (b : Reg) (o : Nat) (hb : b = .r10 ∨ b = .r11)
    (ho : encodable (BitVec.ofNat 32 o) = true) {P : BitVec 32}
    (hP : s.gpr b + BitVec.ofNat 32 o = P) (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16⟩) (hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 yo b o) s (GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) [blockAt s.mem (State.addr P)]) := by
  obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := ghArgs_ok he yo b o hb
    (by rcases hyo with rfl | rfl <;> decide) ho
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hk.sp hk.rd hk.wr
  refine WP.mono (ghCall_ok L hyo he₁ (P := P) (n := 1) h0 h1 (by rw [h2, hP]) h3 h12 (by omega_using [hfit])
    (by simpa using hpy) (by simpa using hpw) (by simpa using hpk)
    (by rw [hk.rd, hk.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans hk.rd, h.wr.trans hk.wr, h.spk.trans hk.sp,
    fun r hr hl => by
      rw [h.saved r hr hl]
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hl | exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide),
    hk.mem ▸ h.frame, by rw [h.out, blocksAt_one, hk.mem]⟩

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.Words`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: words and the lengths block

Untrusted: everything here is checked by Lean. `rev` is `byteRev32`; the
bytes of a block of two 64-bit values are their big-endian bytes
(`toBytes_append64`); and `8 x` of a 64-bit `x = hi:lo`, as the code computes
it with shifts (`shl3_words`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG
open VG.Spec.Gcm (be64 toBytes)

theorem rev_eq : VG.Arm.rev = byteRev32 := rfl

theorem toBytes_append64 (a c : BitVec 64) : toBytes (a ++ c) = be64 a.toNat ++ be64 c.toNat := by
  have ha := a.isLt; have hc := c.isLt
  have e : (a ++ c).toNat = a.toNat * 2 ^ 64 + c.toNat := Proof.Gcm.toNat_append a c
  simp only [toBytes, be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, e]
    omega_using []

/-- `8 x`, of `x = hi:lo`, in two words, as `lsl #3` and `orr` with `lsr #29`. -/
theorem shl3_words (hi lo : BitVec 32) :
    (((hi <<< 3) ||| (lo >>> 29)) ++ (lo <<< 3) : BitVec 64) = (hi ++ lo) <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  have h₁ := hi.isLt; have h₂ := lo.isLt
  simp only [Proof.Gcm.toNat_append, BitVec.toNat_shiftLeft, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hor : (hi.toNat * 2 ^ 3 % 2 ^ 32) ||| (lo.toNat / 2 ^ 29) = hi.toNat * 2 ^ 3 % 2 ^ 32 + lo.toNat / 2 ^ 29 := by
    have : lo.toNat / 2 ^ 29 < 2 ^ 3 := by omega_using []
    rw [show hi.toNat * 2 ^ 3 % 2 ^ 32 = 2 ^ 3 * (hi.toNat % 2 ^ 29) by omega_using [], Nat.mul_comm,
      ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt this]
  rw [hor]
  omega_using []

/-- `8 x` modulo 2⁶⁴, as a number. -/
theorem shl3_toNat (x : BitVec 64) : (x <<< 3).toNat = 8 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; congr 1; omega_using []

theorem toBytes_append4 (a b c d : BitVec 32) :
    toBytes (a ++ b ++ c ++ d) = be64 (a ++ b).toNat ++ be64 (c ++ d).toNat := by
  have e : a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) := by
    apply BitVec.eq_of_toNat_eq
    have := c.isLt; have := d.isLt
    simp only [Proof.Gcm.toNat_append]
    omega_using []
  rw [e, toBytes_append64]

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `r6`
buffered bytes with zeros in `T` and absorbs them (`flush_ok`); `lens yo`
stores the lengths block of `r5:r4` and `r7:r6` bytes in `T` and absorbs it
(`lens_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (st w sp : BitVec 32) (yo : Nat) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

theorem gh_tFrame {st w sp : BitVec 32} {yo : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] m m') :
    Frame (tFrame st w sp yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem store4_zero_bytes (m : Mem) (p : Addr) : bytesAt (store4 m p 0 0 0 0) p 16 = zeros 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_zero]; rfl

/-- The four words at `p`, as the code stores them at `b + o`, `b + o + 4`, … -/
theorem store4_eq (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    store4 m p w₀ w₁ w₂ w₃ = (((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8)
      w₂).writeW (p + BitVec.ofNat 64 12) w₃ := rfl

/-- Before `flush yo` (or `lens yo`): GHASH has absorbed `x`. -/
structure FlIn (c st w sp k7 k8 : BitVec 32) (H : Block) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `m₀`. -/
structure FlOut (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (tFrame st w sp yo) m₀ s.mem

/-- After the copy of the buffered bytes to `T`, padded with zeros. -/
structure FlMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (o : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  hT : bytesAt s.mem (State.addr w + BitVec.ofNat 64 96) 16 =
    bytesAt m₀ (State.addr st + BitVec.ofNat 64 32) o ++ zeros (16 - o)
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt m₀ (State.addr st + BitVec.ofNat 64 yo)
  frame : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The `o` buffered bytes copied to `T`, padded with zeros. -/
theorem flushCopy_ok {H : Block} {o : Nat} {s : State} (h : FlIn c st w sp k7 k8 H s)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 o) (ho : o < 16) (h0 : o ≠ 0) :
    WP isa (.seq (.block flushPre) copyLoop) s (FlMid c st w sp k7 k8 yo H o s.mem) := by
  have he := h.env
  have h10 := he.r10; have h11 := he.r11
  have w₀ := he.perm.wW (show 96 + 4 ≤ 768 by decide)
  have w₁ := he.perm.wW (show 100 + 4 ≤ 768 by decide)
  have w₂ := he.perm.wW (show 104 + 4 ≤ 768 by decide)
  have w₃ := he.perm.wW (show 108 + 4 ≤ 768 by decide)
  obtain ⟨s₂, run₂, hm₂, h1, h2, h3, hg₂, hk₂⟩ : ∃ s₂, runBlock isa flushPre s = some s₂ ∧
      s₂.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 32 ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 96 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 o ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp := by
    refine ⟨_, by simp only [flushPre]; arun [h10, h11, L.wA, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, store4_eq, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h6]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have eS := L.stA (d := 32) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have lp : LoopPre s₂ (st + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 96) o := by
    refine ⟨h1, h2, h3, by omega_arith, by omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith,
      by rw [L.wN (by decide)]; have := L.ww; omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂.1, hk₂.2.1, eS]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂.2.1, eT]; exact he.perm.wC (by omega_arith)
    · rw [eS, eT]; exact L.st_w (by omega_arith) (.inr ⟨by decide, by omega_arith⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eS, eT] at hm₃
  -- The memory so far.
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hB₂ : bytesAt s₂.mem (State.addr st + BitVec.ofNat 64 32) o = bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) o :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
      (by omega_arith)
  have hlen := length_bytesAt s₂.mem (State.addr st + BitVec.ofNat 64 32) o
  have fc : Frame [⟨State.addr w + BitVec.ofNat 64 96, o⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  have f₃ : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide) (by decide)])
      (lo.sp.trans hk₂.2.2) (lo.rd.trans hk₂.1) (lo.wr.trans hk₂.2.1), ?_, ?_, ?_, f₃⟩
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
  · rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hB₂]
    refine congrArg (HAppend.hAppend _) ?_
    have := store4_zero_bytes s.mem (State.addr w + BitVec.ofNat 64 96)
    rw [← hm₂, show (16 : Nat) = o + (16 - o) by omega_arith, bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega_arith, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · exact blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)

/-- The padded buffer absorbed. -/
theorem flushGh_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {m₀ : Mem} {s : State}
    (h : FlMid c st w sp k7 k8 yo H (x.length % 16) m₀ s) (h0 : x.length % 16 ≠ 0) :
    WP isa (ghash1 yo .r11 tO) s (FlOut c st w sp k7 k8 yo H x (x ++ zeros (padLen x.length)) m₀) := by
  have he := h.env
  have eT := L.wA (d := 96) (by decide)
  refine WP.mono (ghash1_ok L hyo he .r11 96 (.inr rfl) (by decide) (P := w + BitVec.ofNat 32 96)
    (by rw [he.r11]) (by rw [L.wN (by decide)]; have := L.ww; omega_arith) ?_ ?_ ?_ ?_) fun s₄ g => ?_
  · rw [eT]; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)
  · rw [eT]; exact covers_left (he.perm.wC (by decide))
  refine ⟨g.env he, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega_arith)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), h.hH]
  · intro ha
    refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s.mem (State.addr w + BitVec.ofNat 64 96) 16) h.hT ?_
    rw [g.out, h.hY, h.hH, eT]; rfl
  · refine (h.frame.sub fun r hr => ?_).trans (gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `flush yo`. -/
theorem flush_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {x : List Byte} {s : State} (h : FlIn c st w sp k7 k8 H s)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16)) :
    WP isa (flush yo) s (FlOut c st w sp k7 k8 yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r6 h6 (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (flushCopy_ok L hyo (o := x.length % 16) ⟨he₁, by rw [hm₁]; exact h.hH⟩
      (by rw [hg₁]; exact h6) hlt h0) fun s₃ hm => flushGh_ok L hyo hm h0)

end

/-- `[8 (hi:lo)]₆₄` into `W + o`, as two byte-reversed words. -/
theorem be64Store_ok {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {s : State} (he : Env c st w sp k7 k8 s)
    (lo hi : Reg) (hlo : lo ≠ .r0) (o : Nat) (ho : o + 8 ≤ 768) :
    ∃ s', runBlock isa (be64Store lo hi o) s = some s' ∧
      s'.mem = (s.mem.writeW (State.addr w + BitVec.ofNat 64 o) (byteRev32 ((s.gpr hi <<< 3) ||| (s.gpr lo >>> 29)))).writeW
        (State.addr w + BitVec.ofNat 64 o + BitVec.ofNat 64 4) (byteRev32 (s.gpr lo <<< 3)) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show o + 4 ≤ 768 by omega_arith)
  have w₁ := he.perm.wW (show o + 4 + 4 ≤ 768 by omega_arith)
  have e₁ := L.wA (d := o) (by omega_arith)
  have e₂ := L.wA (d := o + 4) (by omega_arith)
  have o₁ : o < 4096 := by omega_arith
  have o₂ : o + 4 < 4096 := by omega_arith
  refine ⟨_, by simp only [be64Store]; arun [h11, e₁, e₂, w₀, w₁, hlo, o₁, o₂], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, hlo, add_ofNat_assoc, rev_eq]
  · intro r a; simp [gpr_setReg, a]
  all_goals rfl

/-- `[8 (r5:r4)]₆₄ ‖ [8 (r7:r6)]₆₄`, the lengths block, stored in `T`. -/
theorem lensStore_ok {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {s : State} (he : Env c st w sp k7 k8 s) :
    WP isa (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) s fun s' =>
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 96)
        (byteRev32 ((s.gpr .r5 <<< 3) ||| (s.gpr .r4 >>> 29))) (byteRev32 (s.gpr .r4 <<< 3))
        (byteRev32 ((s.gpr .r7 <<< 3) ||| (s.gpr .r6 >>> 29))) (byteRev32 (s.gpr .r6 <<< 3)) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ := be64Store_ok L he .r4 .r5 (by decide) tO (by decide)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hsp₁ hrd₁ hwr₁
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂, hsp₂⟩ := be64Store_ok L he₁ .r6 .r7 (by decide) (tO + 8)
    (by decide)
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  refine ⟨?_, fun r hr => by rw [hg₂ r hr, hg₁ r hr], hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁⟩
  rw [hm₂, hm₁, hg₁ .r6 (by decide), hg₁ .r7 (by decide)]
  simp only [store4_eq, tO, add_ofNat_assoc]

theorem lensBlock_eq (a₀ a₁ c₀ c₁ : BitVec 32) :
    le4 (byteRev32 ((a₁ <<< 3) ||| (a₀ >>> 29))) ++ le4 (byteRev32 (a₀ <<< 3)) ++
        le4 (byteRev32 ((c₁ <<< 3) ||| (c₀ >>> 29))) ++ le4 (byteRev32 (c₀ <<< 3)) =
      lensBlock (a₁ ++ a₀).toNat (c₁ ++ c₀).toNat := by
  rw [Cmac.le4_rev4, toBytes_append4, shl3_words, shl3_words, shl3_toNat, shl3_toNat, Proof.Gcm.be64_mod,
    Proof.Gcm.be64_mod]
  rfl

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The lengths block of `r5:r4` and `r7:r6` bytes, absorbed. -/
theorem lens_ok [VG.Proof.Gcm.Arm.GhashLaw] {H : Block} {s : State} (he : Env c st w sp k7 k8 s)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) :
    WP isa (lens yo) s fun s' => Env c st w sp k7 k8 s' ∧
      blockAt s'.mem (State.addr c + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (State.addr st + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (State.addr st + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat)] ∧
      Frame (tFrame st w sp yo) s.mem s'.mem := by
  refine WP.seq (WP.mono (lensStore_ok L he) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_)
  have he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hsp₂ hrd₂ hwr₂
  have fT : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hT : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 96) 16 =
      lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat := by
    rw [hm₂, Cmac.bytesAt_store4, lensBlock_eq]
  have hY₂ : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) :=
    blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (State.addr c + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  have eT := L.wA (d := 96) (by decide)
  refine WP.mono (ghash1_ok L hyo he₂ .r11 96 (.inr rfl) (by decide) (P := w + BitVec.ofNat 32 96)
    (by rw [he₂.r11]) (by rw [L.wN (by decide)]; have := L.ww; omega_arith) ?_ ?_ ?_ ?_) fun s₃ g => ?_
  · rw [eT]; exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)
  · rw [eT]; exact covers_left (he₂.perm.wC (by decide))
  refine ⟨g.env he₂, ?_, ?_, ?_⟩
  · rw [blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega_arith)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), hH₂]
  · have hb : blockAt s₂.mem (State.addr w + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat) := by
      rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, eT, hb]
  · refine (fT.sub fun r hr => ?_).trans (gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

end

end VG.Proof.Sm4Gcm.Arm
