module

import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: copying a slice

Untrusted: everything here is checked by Lean. `copyBlocks` copies `k ≥ 1`
blocks from `x12` to `x11`, 16 bytes at a time through `v0`
(`copyBlocks_wp`), and `copySlice` the `n` bytes at `x12` to `x11`: its
whole blocks so, then its last `n mod 16` bytes eight, four and one at a
time (`copyW`, `copyW_ok`), leaving `x11` past them (`copySlice_wp`). The
bytes copied
and the bytes written do not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)
open VG.Proof.AesGcm.AArch64 (LoopPre WordAt copyW_ok eval_zero eval_nonzero succ_ofNat loopRegs covers_prefix covers_off)

/-- The registers the copy of a slice writes. -/
abbrev copyRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

/-- What the copy of a slice keeps: the other registers, the stack pointer
and the permissions. -/
structure Keeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ copyRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h₁ : Keeps s t) (h₂ : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

abbrev blockBody : List Instr :=
  [.ldrq .v0 .x12 0, .strq .v0 .x11 0, .addImm .x .x12 .x12 16, .addImm .x .x11 .x11 16,
    .subImm .x .x14 .x14 1]

theorem blockStep_ok (s : State) {A B : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x11 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) A 16) (w : InRegions s.wr B 16) :
    ∃ s', runBlock isa blockBody s = some s' ∧ s'.mem = s.mem.write B 16 (s.mem.read A 16) ∧
      s'.gpr .x12 = s.gpr .x12 + 16 ∧ s'.gpr .x11 = s.gpr .x11 + 16 ∧ s'.gpr .x14 = s.gpr .x14 - 1 ∧
      s'.gpr .x13 = s.gpr .x13 ∧ Keeps s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, blockBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, gpr_setV, mem_setV, rd_setV, wr_setV, v_setV_self,
      Option.bind_some, Option.map_some, BitVec.setWidth_eq, ha, hb, r, w]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    ⟨fun r h => ?_, rfl, rfl, rfl⟩⟩
  · simp only [mem_write, v_setV_self]
  · simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, -, h₄, -⟩ := h
    simp [gpr_write, h₁, h₂, h₄]

/-- What the block loop needs: `k ≥ 1` blocks at `S` to copy to `D`, apart. -/
structure BlocksPre (s : State) (S D : Addr) (k : Nat) : Prop where
  x12 : s.gpr .x12 = S
  x11 : s.gpr .x11 = D
  x14 : s.gpr .x14 = BitVec.ofNat 64 k
  pos : 1 ≤ k
  lt : 16 * k < 2 ^ 64
  rd : Covers [⟨S, 16 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * k⟩] s.wr
  disj : (⟨S, 16 * k⟩ : Region).Disjoint ⟨D, 16 * k⟩

/-- The bytes at `S + j`, not among the `j` bytes written at `D`, are what
they were. -/
theorem read_kept {m : Mem} {S D : Addr} {j n L : Nat} (hd : (⟨S, L⟩ : Region).Disjoint ⟨D, L⟩)
    (hj : j + n ≤ L) (hL : L < 2 ^ 64) :
    (writeBytes m D (bytesAt m S j)).read (S + BitVec.ofNat 64 j) n = m.read (S + BitVec.ofNat 64 j) n := by
  refine Mem.read_congr fun k hk => ?_
  refine (writeBytes_frame m D (bytesAt m S j) (R := ⟨D, j⟩)
    (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Offset.add_add] at hcon
  exact hd _ (Offset.contains_base S (show j + k + 1 ≤ L by omega) (by omega))
    (Region.sub_prefix (show j ≤ L by omega) _ hcon)

/-- The 16 bytes of a read, as a list. -/
theorem read16_bytes (m : Mem) (a : Addr) :
    (List.range 16).map (fun j => (m.read a 16).extractLsb' (8 * j) 8) = bytesAt m a 16 := by
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  exact Mem.extractLsb'_read m a hj

theorem copyBlocks_wp (s : State) {S D : Addr} {k : Nat} (h : BlocksPre s S D k) :
    WP isa copyBlocks s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S (16 * k)) ∧
      s'.gpr .x12 = S + BitVec.ofNat 64 (16 * k) ∧ s'.gpr .x11 = D + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .x13 = s.gpr .x13 ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa) (body := .block blockBody) (c := .nonzero .x .x14)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ t.gpr .x12 = S + BitVec.ofNat 64 (16 * i) ∧
      t.gpr .x11 = D + BitVec.ofNat 64 (16 * i) ∧ t.gpr .x14 = BitVec.ofNat 64 (k - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S (16 * i)) ∧ t.gpr .x13 = s.gpr .x13 ∧ Keeps s t) ?_ (k - 0) _
    ⟨0, rfl, h.pos, by rw [h.x12]; simp, by rw [h.x11]; simp, by rw [h.x14, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], rfl, Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, x12, x11, x14, mem, x13, kp⟩
  have hin : 16 * i + 16 ≤ 16 * k := by omega
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 16 * k⟩] rs) :
      InRegions rs (P + BitVec.ofNat 64 (16 * i)) 16 :=
    hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hin (by omega)⟩
  obtain ⟨t', run', mem', x12', x11', x14', x13', kp'⟩ := blockStep_ok t
    (A := S + BitVec.ofNat 64 (16 * i)) (B := D + BitVec.ofNat 64 (16 * i)) (by rw [x12, BitVec.add_zero])
    (by rw [x11, BitVec.add_zero]) (by rw [kp.rd, kp.wr]; exact cov _ _ h.rd)
    (by rw [kp.wr]; exact cov _ _ h.wr)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (16 * (i + 1))) := by
    rw [mem', mem, read_kept h.disj hin (by omega), write_eq_writeBytes, read16_bytes,
      show 16 * (i + 1) = 16 * i + 16 by omega, bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), Proof.Cmac.bytesAt_length]
  have hstep (P : Addr) : P + BitVec.ofNat 64 (16 * i) + 16 = P + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
      Nat.mul_succ]
  have x14'' : t'.gpr .x14 = BitVec.ofNat 64 (k - (i + 1)) := by
    rw [x14', x14, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x14) (a := k - (i + 1)) x14'' (by omega)
  by_cases he : i + 1 = k
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x12', x12, hstep, he], by rw [x11', x11, hstep, he],
      x13'.trans x13, kp.trans kp'⟩
  · right
    refine ⟨by rw [ev]; simp; omega, k - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, hstep], by rw [x11', x11, hstep], x14'', hmem, x13'.trans x13, kp.trans kp'⟩

/-- What the copy of a slice needs: `n` bytes at `S` to copy to `D`, apart. -/
structure SlicePre (s : State) (S D : Addr) (n : Nat) : Prop where
  x12 : s.gpr .x12 = S
  x11 : s.gpr .x11 = D
  x13 : s.gpr .x13 = BitVec.ofNat 64 n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

theorem ofNat_lsr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem ofNat_and15 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 15 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem blocksArg_ok (s : State) :
    ∃ s', runBlock isa blocksArg s = some s' ∧ s'.gpr .x14 = s.gpr .x13 >>> 4 ∧
      (∀ r, r ≠ .x14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x .x14 (s.read .x .x13 >>> 4), by simp only [blocksArg, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, Size.bits],
    by simp [gpr_write, State.read], fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

theorem bytesArg_ok (s : State) :
    ∃ s', runBlock isa bytesArg s = some s' ∧ s'.gpr .x13 = s.gpr .x13 &&& BitVec.ofNat 64 15 ∧
      (∀ r, r ≠ .x13 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr :=
  ⟨(s.write .x .x15 (BitVec.setWidth 64 (15 : BitVec 16) <<< 0)).write .x .x13
      ((s.write .x .x15 (BitVec.setWidth 64 (15 : BitVec 16) <<< 0)).read .x .x13 &&&
        (s.write .x .x15 (BitVec.setWidth 64 (15 : BitVec 16) <<< 0)).read .x .x15),
    by simp only [bytesArg, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, Nat.reduceMul,
      ite_true, Size.bits],
    by simp [gpr_write, State.read], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩

/-- `copySlice16`: the `n` bytes at `S` to `D`, and `x11` past them. -/
theorem copySlice16_wp (s : State) {S D : Addr} {n : Nat} (h : SlicePre s S D n) :
    WP isa copySlice16 s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .x11 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hn := h.lt
  have hqr : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
  obtain ⟨s₁, run₁, x14₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := blocksArg_ok s
  have x14₁' : s₁.gpr .x14 = BitVec.ofNat 64 (n / 16) := by rw [x14₁, h.x13, ofNat_lsr4 hn]
  have kp₁ : Keeps s s₁ := ⟨fun r hr => g₁ r (by intro e; subst e; simp [copyRegs] at hr), sp₁, rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The whole blocks.
  have hblk : WP isa (.ite (.zero .x .x14) (.block []) copyBlocks) s₁ fun s₂ =>
      s₂.mem = writeBytes s.mem D (bytesAt s.mem S (16 * (n / 16))) ∧
      s₂.gpr .x12 = S + BitVec.ofNat 64 (16 * (n / 16)) ∧ s₂.gpr .x11 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
      s₂.gpr .x13 = BitVec.ofNat 64 n ∧ Keeps s s₂ := by
    refine WP.ite (decide (n / 16 = 0)) (eval_zero x14₁' (by omega)) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 16 = 0 := by simpa using ht
      refine WP.block_nil ⟨?_, ?_, ?_, ?_, kp₁⟩
      · rw [m₁, h0, Nat.mul_zero]; simp [bytesAt, writeBytes_nil]
      · rw [g₁ _ (by decide), h.x12, h0]; simp
      · rw [g₁ _ (by decide), h.x11, h0]; simp
      · rw [g₁ _ (by decide), h.x13]
    · have h0 : n / 16 ≠ 0 := by simpa using hf
      have hb : BlocksPre s₁ S D (n / 16) :=
        ⟨by rw [g₁ _ (by decide), h.x12], by rw [g₁ _ (by decide), h.x11], x14₁', by omega, by omega,
          by rw [rd₁, wr₁]; exact covers_prefix h.rd (by omega),
          by rw [wr₁]; exact covers_prefix h.wr (by omega),
          (h.disj.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))⟩
      refine WP.mono (copyBlocks_wp s₁ hb) fun s₂ ⟨m₂, x12₂, x11₂, x13₂, kp₂⟩ => ⟨?_, x12₂, x11₂, ?_, kp₁.trans kp₂⟩
      · rw [m₂, m₁]
      · rw [x13₂, g₁ _ (by decide), h.x13]
  refine WP.seq (WP.mono hblk fun s₂ ⟨m₂, x12₂, x11₂, x13₂, kp₂⟩ => ?_)
  -- The last `n mod 16` bytes.
  obtain ⟨s₃, run₃, x13₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := bytesArg_ok s₂
  have x13₃' : s₃.gpr .x13 = BitVec.ofNat 64 (n % 16) := by rw [x13₃, x13₂, ofNat_and15 hn]
  have kp₃ : Keeps s s₃ := kp₂.trans ⟨fun r hr => g₃ r (by intro e; subst e; simp [copyRegs] at hr)
    (by intro e; subst e; simp [copyRegs] at hr), sp₃, rd₃, wr₃⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hS : (⟨S + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ : Region).Sub ⟨S, n⟩ := Offset.sub_base _ (by omega)
  have hD : (⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ : Region).Sub ⟨D, n⟩ := Offset.sub_base _ (by omega)
  have hlen : (bytesAt s.mem S (16 * (n / 16))).length = 16 * (n / 16) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes still to copy are what they were.
  have hrest : bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [m₃, m₂]
    refine Proof.AesGcm.AArch64.bytesAt_frame (writeBytes_frame s.mem D _ (R := ⟨D, 16 * (n / 16)⟩)
      (by rw [hlen]; exact Region.contains_self _ _)) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.disj.sub_left hS).sub_right (Region.sub_prefix (by omega))
  have hend : D + BitVec.ofNat 64 (16 * (n / 16)) + BitVec.ofNat 64 (n % 16) = D + BitVec.ofNat 64 n := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hqr]
  have hall : writeBytes (writeBytes s.mem D (bytesAt s.mem S (16 * (n / 16)))) (D + BitVec.ofNat 64 (16 * (n / 16)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) = writeBytes s.mem D (bytesAt s.mem S n) := by
    have e := writeBytes_append s.mem D (bytesAt s.mem S (16 * (n / 16)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
      (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)
    rw [hlen] at e
    rw [e, ← bytesAt_append, hqr]
  refine WP.ite (decide (n % 16 = 0)) (eval_zero x13₃' (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, ?_, kp₃⟩
    · rw [m₃, m₂, ← hall, h0]; simp [bytesAt, writeBytes_nil]
    · rw [g₃ _ (by decide) (by decide), x11₂, ← hend, h0]; simp
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    have lp : LoopPre s₃ (S + BitVec.ofNat 64 (16 * (n / 16))) (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      ⟨by omega, by rw [rd₃, wr₃, kp₂.rd, kp₂.wr]; exact covers_off h.rd (by omega) hn,
        by rw [wr₃, kp₂.wr]; exact covers_off h.wr (by omega) hn, (h.disj.sub_left hS).sub_right hD⟩
    have W₀ : WordAt s₃ (S + BitVec.ofNat 64 (16 * (n / 16))) (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) 0
        (D + BitVec.ofNat 64 (16 * (n / 16))) (bytesAt s₃.mem (S + BitVec.ofNat 64 (16 * (n / 16))) 0) s₃ :=
      ⟨Nat.zero_le _, by rw [g₃ _ (by decide) (by decide), x12₂]; simp,
        by rw [g₃ _ (by decide) (by decide), x11₂]; simp, by rw [x13₃', Nat.sub_zero],
        by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
    refine WP.mono (copyW_ok lp W₀) fun s₄ ⟨m₄, g₄, sp₄, rd₄, wr₄, x11₄⟩ =>
        ⟨?_, by rw [x11₄, hend], kp₃.trans ⟨g₄, sp₄, rd₄, wr₄⟩⟩
    rw [m₄, hrest, m₃, m₂, hall]

/-! ## 64 bytes at a time -/

/-- One 16-byte copy at offset `o` from both pointers, through `vr`. -/
theorem pair_wp (t : State) (vr : VReg) {o : Nat} (ho : o % 16 = 0 ∧ o < 4096 * 16)
    (r : InRegions (t.rd ++ t.wr) (t.gpr .x12 + BitVec.ofNat 64 o) 16)
    (w : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 o) 16) :
    WP isa (.block [.ldrq vr .x12 o, .strq vr .x11 o]) t fun t' =>
      t'.mem = t.mem.write (t.gpr .x11 + BitVec.ofNat 64 o) 16 (t.mem.read (t.gpr .x12 + BitVec.ofNat 64 o) 16) ∧
      (∀ r, t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits,
      State.read, gpr_setV, mem_setV, rd_setV, wr_setV, v_setV_self, Option.bind_some, Option.map_some,
      BitVec.setWidth_eq, ho, and_self, ite_true, r, w, Nat.reduceMul]
    rfl, ?_⟩
  exact ⟨by simp only [mem_write, v_setV_self], fun _ => rfl, rfl, rfl, rfl⟩

/-- The copy so far extended by the 16 bytes after its first `j`. -/
theorem extend16 {m : Mem} {S D : Addr} {j L : Nat} (hd : (⟨S, L⟩ : Region).Disjoint ⟨D, L⟩)
    (hj : j + 16 ≤ L) (hL : L < 2 ^ 64) :
    (writeBytes m D (bytesAt m S j)).write (D + BitVec.ofNat 64 j) 16
        ((writeBytes m D (bytesAt m S j)).read (S + BitVec.ofNat 64 j) 16) =
      writeBytes m D (bytesAt m S (j + 16)) := by
  rw [read_kept hd hj hL, write_eq_writeBytes, read16_bytes, bytesAt_append,
    ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), Proof.Cmac.bytesAt_length]

/-- What the chunk loop needs: `k ≥ 1` chunks of 64 bytes at `S` to copy to `D`, apart. -/
structure ChunksPre (s : State) (S D : Addr) (k : Nat) : Prop where
  x12 : s.gpr .x12 = S
  x11 : s.gpr .x11 = D
  x14 : s.gpr .x14 = BitVec.ofNat 64 k
  pos : 1 ≤ k
  lt : 64 * k < 2 ^ 64
  rd : Covers [⟨S, 64 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 64 * k⟩] s.wr
  disj : (⟨S, 64 * k⟩ : Region).Disjoint ⟨D, 64 * k⟩

theorem add_ofNat_ofNat (P : Addr) (a b : Nat) :
    P + BitVec.ofNat 64 a + BitVec.ofNat 64 b = P + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The pointers past the chunk, and one chunk fewer. -/
theorem chunkTail_ok (s : State) :
    ∃ s', runBlock isa [.addImm .x .x12 .x12 64, .addImm .x .x11 .x11 64, .subImm .x .x14 .x14 1] s = some s' ∧
      s'.mem = s.mem ∧ s'.gpr .x12 = s.gpr .x12 + 64 ∧ s'.gpr .x11 = s.gpr .x11 + 64 ∧
      s'.gpr .x14 = s.gpr .x14 - 1 ∧ s'.gpr .x13 = s.gpr .x13 ∧ Keeps s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits]
    rfl, ?_⟩
  refine ⟨rfl, by simp [gpr_write, State.read], by simp [gpr_write, State.read], by simp [gpr_write, State.read],
    by simp [gpr_write], ⟨fun r h => ?_, rfl, rfl, rfl⟩⟩
  simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h₁, h₂, -, h₄, -⟩ := h
  simp [gpr_write, h₁, h₂, h₄]

theorem copyChunks_wp (s : State) {S D : Addr} {k : Nat} (h : ChunksPre s S D k) :
    WP isa copyChunks s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S (64 * k)) ∧
      s'.gpr .x12 = S + BitVec.ofNat 64 (64 * k) ∧ s'.gpr .x11 = D + BitVec.ofNat 64 (64 * k) ∧
      s'.gpr .x13 = s.gpr .x13 ∧ Keeps s s' := by
  have hL := h.lt
  refine WP.loop (M := isa) (c := .nonzero .x .x14)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ t.gpr .x12 = S + BitVec.ofNat 64 (64 * i) ∧
      t.gpr .x11 = D + BitVec.ofNat 64 (64 * i) ∧ t.gpr .x14 = BitVec.ofNat 64 (k - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S (64 * i)) ∧ t.gpr .x13 = s.gpr .x13 ∧ Keeps s t) ?_ (k - 0) _
    ⟨0, rfl, h.pos, by rw [h.x12]; simp, by rw [h.x11]; simp, by rw [h.x14, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], rfl, Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, x12, x11, x14, mem, x13, kp⟩
  have hin : 64 * i + 64 ≤ 64 * k := by omega
  have disj : (⟨S, 64 * k⟩ : Region).Disjoint ⟨D, 64 * k⟩ := h.disj
  -- The `o`-th 16 bytes of the chunk, whose sources and destinations are in the regions.
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 64 * k⟩] rs) (o : Nat) (ho : o + 16 ≤ 64) :
      InRegions rs (P + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 o) 16 := by
    rw [add_ofNat_ofNat]
    exact hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P (by omega) (by omega)⟩
  -- One pair, from a state where the first `64 i + o` bytes are copied.
  have step (u : State) (vr : VReg) (o : Nat) (ho : o % 16 = 0 ∧ o < 4096 * 16) (ho' : o + 16 ≤ 64)
      (u12 : u.gpr .x12 = S + BitVec.ofNat 64 (64 * i)) (u11 : u.gpr .x11 = D + BitVec.ofNat 64 (64 * i))
      (um : u.mem = writeBytes s.mem D (bytesAt s.mem S (64 * i + o))) (urw : u.rd = t.rd ∧ u.wr = t.wr) :
      WP isa (.block [.ldrq vr .x12 o, .strq vr .x11 o]) u fun u' =>
        u'.mem = writeBytes s.mem D (bytesAt s.mem S (64 * i + o + 16)) ∧ (∀ r, u'.gpr r = u.gpr r) ∧
          u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
    refine WP.mono (pair_wp u vr ho (by rw [urw.1, urw.2, u12, kp.rd, kp.wr]; exact cov _ _ h.rd o ho')
      (by rw [urw.2, u11, kp.wr]; exact cov _ _ h.wr o ho')) fun u' ⟨m', g', sp', rd', wr'⟩ => ⟨?_, g', sp', rd', wr'⟩
    rw [m', u12, u11, um, add_ofNat_ofNat, add_ofNat_ofNat]
    exact extend16 disj (by omega) hL
  have hstep (P : Addr) : P + BitVec.ofNat 64 (64 * i) + 64 = P + BitVec.ofNat 64 (64 * (i + 1)) := by
    rw [BitVec.add_assoc, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add,
      Nat.mul_succ]
  show WP isa (.block ([.ldrq .v0 .x12 0, .strq .v0 .x11 0] ++ [.ldrq .v1 .x12 16, .strq .v1 .x11 16] ++
    [.ldrq .v2 .x12 32, .strq .v2 .x11 32] ++ [.ldrq .v3 .x12 48, .strq .v3 .x11 48] ++
    [.addImm .x .x12 .x12 64, .addImm .x .x11 .x11 64, .subImm .x .x14 .x14 1])) t _
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append ?_)))
  refine WP.mono (step t .v0 0 (by decide) (by decide) x12 x11 (by rw [mem, Nat.add_zero]) ⟨rfl, rfl⟩)
    fun u₁ ⟨m₁, g₁, sp₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (step u₁ .v1 16 (by decide) (by decide) (by rw [g₁, x12]) (by rw [g₁, x11])
    (by rw [m₁, show 64 * i + 0 + 16 = 64 * i + 16 by omega]) ⟨rd₁, wr₁⟩)
    fun u₂ ⟨m₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (step u₂ .v2 32 (by decide) (by decide) (by rw [g₂, g₁, x12]) (by rw [g₂, g₁, x11])
    (by rw [m₂, show 64 * i + 16 + 16 = 64 * i + 32 by omega])
    ⟨rd₂.trans rd₁, wr₂.trans wr₁⟩) fun u₃ ⟨m₃, g₃, sp₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (step u₃ .v3 48 (by decide) (by decide) (by rw [g₃, g₂, g₁, x12]) (by rw [g₃, g₂, g₁, x11])
    (by rw [m₃, show 64 * i + 32 + 16 = 64 * i + 48 by omega])
    ⟨rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁)⟩) fun u₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  have hg (r : Reg) : u₄.gpr r = t.gpr r := by rw [g₄, g₃, g₂, g₁]
  obtain ⟨t', run', mem', x12', x11', x14', x13', kp'⟩ := chunkTail_ok u₄
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have m₅ : t'.mem = writeBytes s.mem D (bytesAt s.mem S (64 * (i + 1))) := by
    rw [mem', m₄, show 64 * i + 48 + 16 = 64 * (i + 1) by omega]
  have x14'' : t'.gpr .x14 = BitVec.ofNat 64 (k - (i + 1)) := by
    rw [x14', hg, x14, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x14) (a := k - (i + 1)) x14'' (by omega)
  have kp₄ : Keeps s u₄ := kp.trans ⟨fun r _ => hg r, sp₄.trans (sp₃.trans (sp₂.trans sp₁)),
    rd₄.trans (rd₃.trans (rd₂.trans rd₁)), wr₄.trans (wr₃.trans (wr₂.trans wr₁))⟩
  by_cases he : i + 1 = k
  · left
    refine ⟨by rw [ev]; simp [he], by rw [m₅, he], by rw [x12', hg, x12, hstep, he],
      by rw [x11', hg, x11, hstep, he], by rw [x13', hg, x13], kp₄.trans kp'⟩
  · right
    refine ⟨by rw [ev]; simp; omega, k - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', hg, x12, hstep], by rw [x11', hg, x11, hstep], x14'', m₅, by rw [x13', hg, x13],
      kp₄.trans kp'⟩

theorem ofNat_lsr6 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem ofNat_and63 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (n % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 63 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega),
    show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem chunksArg_ok (s : State) :
    ∃ s', runBlock isa chunksArg s = some s' ∧ s'.gpr .x14 = s.gpr .x13 >>> 6 ∧
      (∀ r, r ≠ .x14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x .x14 (s.read .x .x13 >>> 6), by simp only [chunksArg, runBlock_cons, runStep_some, runBlock_nil,
      exec, Nat.reduceLT, ite_true, Size.bits],
    by simp [gpr_write, State.read], fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

theorem restArg_ok (s : State) :
    ∃ s', runBlock isa restArg s = some s' ∧ s'.gpr .x13 = s.gpr .x13 &&& BitVec.ofNat 64 63 ∧
      (∀ r, r ≠ .x13 → r ≠ .x15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr :=
  ⟨(s.write .x .x15 (BitVec.setWidth 64 (63 : BitVec 16) <<< 0)).write .x .x13
      ((s.write .x .x15 (BitVec.setWidth 64 (63 : BitVec 16) <<< 0)).read .x .x13 &&&
        (s.write .x .x15 (BitVec.setWidth 64 (63 : BitVec 16) <<< 0)).read .x .x15),
    by simp only [restArg, runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, Nat.reduceMul,
      ite_true, Size.bits],
    by simp [gpr_write, State.read], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩

/-- `copySlice64`: the `n` bytes at `S` to `D`, and `x11` past them. -/
theorem copySlice64_wp (s : State) {S D : Addr} {n : Nat} (h : SlicePre s S D n) :
    WP isa copySlice64 s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .x11 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hn := h.lt
  have hqr : 64 * (n / 64) + n % 64 = n := Nat.div_add_mod n 64
  obtain ⟨s₁, run₁, x14₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := chunksArg_ok s
  have x14₁' : s₁.gpr .x14 = BitVec.ofNat 64 (n / 64) := by rw [x14₁, h.x13, ofNat_lsr6 hn]
  have kp₁ : Keeps s s₁ := ⟨fun r hr => g₁ r (by intro e; subst e; simp [copyRegs] at hr), sp₁, rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The whole chunks.
  have hchk : WP isa (.ite (.zero .x .x14) (.block []) copyChunks) s₁ fun s₂ =>
      s₂.mem = writeBytes s.mem D (bytesAt s.mem S (64 * (n / 64))) ∧
      s₂.gpr .x12 = S + BitVec.ofNat 64 (64 * (n / 64)) ∧ s₂.gpr .x11 = D + BitVec.ofNat 64 (64 * (n / 64)) ∧
      s₂.gpr .x13 = BitVec.ofNat 64 n ∧ Keeps s s₂ := by
    refine WP.ite (decide (n / 64 = 0)) (eval_zero x14₁' (by omega)) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 64 = 0 := by simpa using ht
      refine WP.block_nil ⟨?_, ?_, ?_, ?_, kp₁⟩
      · rw [m₁, h0, Nat.mul_zero]; simp [bytesAt, writeBytes_nil]
      · rw [g₁ _ (by decide), h.x12, h0]; simp
      · rw [g₁ _ (by decide), h.x11, h0]; simp
      · rw [g₁ _ (by decide), h.x13]
    · have h0 : n / 64 ≠ 0 := by simpa using hf
      have hb : ChunksPre s₁ S D (n / 64) :=
        ⟨by rw [g₁ _ (by decide), h.x12], by rw [g₁ _ (by decide), h.x11], x14₁', by omega, by omega,
          by rw [rd₁, wr₁]; exact covers_prefix h.rd (by omega),
          by rw [wr₁]; exact covers_prefix h.wr (by omega),
          (h.disj.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))⟩
      refine WP.mono (copyChunks_wp s₁ hb) fun s₂ ⟨m₂, x12₂, x11₂, x13₂, kp₂⟩ => ⟨?_, x12₂, x11₂, ?_, kp₁.trans kp₂⟩
      · rw [m₂, m₁]
      · rw [x13₂, g₁ _ (by decide), h.x13]
  refine WP.seq (WP.mono hchk fun s₂ ⟨m₂, x12₂, x11₂, x13₂, kp₂⟩ => ?_)
  -- The last `n mod 64` bytes.
  obtain ⟨s₃, run₃, x13₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := restArg_ok s₂
  have x13₃' : s₃.gpr .x13 = BitVec.ofNat 64 (n % 64) := by rw [x13₃, x13₂, ofNat_and63 hn]
  have kp₃ : Keeps s s₃ := kp₂.trans ⟨fun r hr => g₃ r (by intro e; subst e; simp [copyRegs] at hr)
    (by intro e; subst e; simp [copyRegs] at hr), sp₃, rd₃, wr₃⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hS : (⟨S + BitVec.ofNat 64 (64 * (n / 64)), n % 64⟩ : Region).Sub ⟨S, n⟩ := Offset.sub_base _ (by omega)
  have hD : (⟨D + BitVec.ofNat 64 (64 * (n / 64)), n % 64⟩ : Region).Sub ⟨D, n⟩ := Offset.sub_base _ (by omega)
  have hlen : (bytesAt s.mem S (64 * (n / 64))).length = 64 * (n / 64) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes still to copy are what they were.
  have hrest : bytesAt s₃.mem (S + BitVec.ofNat 64 (64 * (n / 64))) (n % 64) =
      bytesAt s.mem (S + BitVec.ofNat 64 (64 * (n / 64))) (n % 64) := by
    rw [m₃, m₂]
    refine Proof.AesGcm.AArch64.bytesAt_frame (writeBytes_frame s.mem D _ (R := ⟨D, 64 * (n / 64)⟩)
      (by rw [hlen]; exact Region.contains_self _ _)) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.disj.sub_left hS).sub_right (Region.sub_prefix (by omega))
  have hend : D + BitVec.ofNat 64 (64 * (n / 64)) + BitVec.ofNat 64 (n % 64) = D + BitVec.ofNat 64 n := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hqr]
  have hall : writeBytes (writeBytes s.mem D (bytesAt s.mem S (64 * (n / 64)))) (D + BitVec.ofNat 64 (64 * (n / 64)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (64 * (n / 64))) (n % 64)) = writeBytes s.mem D (bytesAt s.mem S n) := by
    have e := writeBytes_append s.mem D (bytesAt s.mem S (64 * (n / 64)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (64 * (n / 64))) (n % 64))
      (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)
    rw [hlen] at e
    rw [e, ← bytesAt_append, hqr]
  have sp : SlicePre s₃ (S + BitVec.ofNat 64 (64 * (n / 64))) (D + BitVec.ofNat 64 (64 * (n / 64))) (n % 64) :=
    ⟨by rw [g₃ _ (by decide) (by decide), x12₂], by rw [g₃ _ (by decide) (by decide), x11₂], x13₃', by omega,
      by rw [rd₃, wr₃, kp₂.rd, kp₂.wr]; exact covers_off h.rd (by omega) hn,
      by rw [wr₃, kp₂.wr]; exact covers_off h.wr (by omega) hn, (h.disj.sub_left hS).sub_right hD⟩
  refine WP.mono (copySlice16_wp s₃ sp) fun s₄ ⟨m₄, x11₄, kp₄⟩ => ⟨?_, by rw [x11₄, hend], kp₃.trans kp₄⟩
  rw [m₄, hrest, m₃, m₂, hall]

/-! ## Aligning where the slice goes -/

/-- Writing `ys` over a write of no more bytes at the same address. -/
theorem writeBytes_over (m : Mem) (q : Addr) {xs ys : List Byte} (h : xs.length ≤ ys.length) :
    writeBytes (writeBytes m q xs) q ys = writeBytes m q ys := by
  funext a
  simp only [writeBytes]
  split
  · rfl
  · rename_i hy
    simp only [show ¬ (a - q).toNat < xs.length by omega, ite_false]

/-- The 16 bytes of the head, then the rest from `h` on, written over them:
the `n` bytes. -/
theorem head_rest {m : Mem} {S D : Addr} {h n : Nat} (hh : h ≤ 16) (hn : 16 ≤ n) (hL : n < 2 ^ 64) :
    writeBytes (writeBytes m D (bytesAt m S 16)) (D + BitVec.ofNat 64 h) (bytesAt m (S + BitVec.ofNat 64 h) (n - h)) =
      writeBytes m D (bytesAt m S n) := by
  have e₁ : bytesAt m S 16 = bytesAt m S h ++ bytesAt m (S + BitVec.ofNat 64 h) (16 - h) := by
    rw [← bytesAt_append, Nat.add_sub_cancel' hh]
  have e₂ : bytesAt m S n = bytesAt m S h ++ bytesAt m (S + BitVec.ofNat 64 h) (n - h) := by
    rw [← bytesAt_append, Nat.add_sub_cancel' (by omega)]
  have lh : (bytesAt m S h).length = h := Proof.Cmac.bytesAt_length _ _ _
  rw [e₁, e₂, ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), lh,
    writeBytes_over _ _ (by simp [Proof.Cmac.bytesAt_length]; omega),
    ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), lh]

theorem sub_and15 (D : Addr) :
    (16 : BitVec 64) - (D &&& 15) = BitVec.ofNat 64 (16 - D.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have ha : (D &&& 15).toNat = D.toNat % 16 := by
    rw [show (15 : BitVec 64) = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl, BitVec.toNat_and,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), Nat.and_two_pow_sub_one_eq_mod]
  have hm := Nat.mod_lt D.toNat (show 0 < 16 by decide)
  rw [BitVec.toNat_sub, ha, show (16 : BitVec 64).toNat = 16 from rfl, BitVec.toNat_ofNat]
  omega

theorem alignHead_ok (s : State) {S D : Addr} (h12 : s.gpr .x12 = S) (h11 : s.gpr .x11 = D)
    (r : InRegions (s.rd ++ s.wr) S 16) (w : InRegions s.wr D 16) :
    ∃ s', runBlock isa alignHead s = some s' ∧ s'.mem = s.mem.write D 16 (s.mem.read S 16) ∧
      s'.gpr .x12 = S + BitVec.ofNat 64 (16 - D.toNat % 16) ∧
      s'.gpr .x11 = D + BitVec.ofNat 64 (16 - D.toNat % 16) ∧
      s'.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 (16 - D.toNat % 16) ∧ Keeps s s' := by
  have r' : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 0) 16 := by rw [h12, BitVec.add_zero]; exact r
  have w' : InRegions s.wr (s.gpr .x11 + BitVec.ofNat 64 0) 16 := by rw [h11, BitVec.add_zero]; exact w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, alignHead,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, gpr_setV, mem_setV, rd_setV, wr_setV, v_setV_self,
      Option.bind_some, Option.map_some, BitVec.setWidth_eq, r', w']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ⟨fun r h => ?_, rfl, rfl, rfl⟩⟩
  · simp only [mem_write, v_setV_self, h12, h11, BitVec.add_zero]
  · simp [gpr_write, State.read, h11, h12]; exact sub_and15 D
  · simp [gpr_write, State.read, h11]; exact sub_and15 D
  · simp [gpr_write, State.read, h11]; exact sub_and15 D
  · simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅]

/-- `copySlice`: the `n` bytes at `S` to `D`, and `x11` past them. -/
theorem copySlice_wp (s : State) {S D : Addr} {n : Nat} (h : SlicePre s S D n) :
    WP isa copySlice s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .x11 = D + BitVec.ofNat 64 n ∧ Keeps s s' := by
  have hn := h.lt
  obtain ⟨s₁, run₁, x14₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := blocksArg_ok s
  have x14₁' : s₁.gpr .x14 = BitVec.ofNat 64 (n / 16) := by rw [x14₁, h.x13, ofNat_lsr4 hn]
  have kp₁ : Keeps s s₁ := ⟨fun r hr => g₁ r (by intro e; subst e; simp [copyRegs] at hr), sp₁, rd₁, wr₁⟩
  have sp₁' : SlicePre s₁ S D n := ⟨by rw [g₁ _ (by decide), h.x12], by rw [g₁ _ (by decide), h.x11],
    by rw [g₁ _ (by decide), h.x13], hn, by rw [rd₁, wr₁]; exact h.rd, by rw [wr₁]; exact h.wr, h.disj⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n / 16 = 0)) (eval_zero x14₁' (by omega)) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (copySlice16_wp s₁ sp₁') fun s₂ ⟨m₂, x11₂, kp₂⟩ => ⟨?_, x11₂, kp₁.trans kp₂⟩
    rw [m₂, m₁]
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    have h16 : 16 ≤ n := by omega
    have hd := Nat.mod_lt D.toNat (show 0 < 16 by decide)
    have hh1 : 16 - D.toNat % 16 ≤ 16 := by omega
    obtain ⟨s₂, run₂, m₂, x12₂, x11₂, x13₂, kp₂⟩ := alignHead_ok s₁ sp₁'.x12 sp₁'.x11
      (covers_prefix sp₁'.rd (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
      (covers_prefix sp₁'.wr (by omega) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hS : (⟨S + BitVec.ofNat 64 (16 - D.toNat % 16), n - (16 - D.toNat % 16)⟩ : Region).Sub ⟨S, n⟩ :=
      Offset.sub_base _ (by omega)
    have hD : (⟨D + BitVec.ofNat 64 (16 - D.toNat % 16), n - (16 - D.toNat % 16)⟩ : Region).Sub ⟨D, n⟩ :=
      Offset.sub_base _ (by omega)
    have sp₂ : SlicePre s₂ (S + BitVec.ofNat 64 (16 - D.toNat % 16)) (D + BitVec.ofNat 64 (16 - D.toNat % 16))
        (n - (16 - D.toNat % 16)) :=
      ⟨x12₂, x11₂, by rw [x13₂, sp₁'.x13, Offset.ofNat_sub_ofNat (by omega)], by omega,
        by rw [kp₂.rd, kp₂.wr]; exact covers_off sp₁'.rd (by omega) hn,
        by rw [kp₂.wr]; exact covers_off sp₁'.wr (by omega) hn, (h.disj.sub_left hS).sub_right hD⟩
    refine WP.mono (copySlice64_wp s₂ sp₂) fun s₃ ⟨m₃, x11₃, kp₃⟩ => ⟨?_, ?_, kp₁.trans (kp₂.trans kp₃)⟩
    · -- The rest's bytes are what they were: the head wrote only at `D`.
      have hrest : bytesAt s₂.mem (S + BitVec.ofNat 64 (16 - D.toNat % 16)) (n - (16 - D.toNat % 16)) =
          bytesAt s.mem (S + BitVec.ofNat 64 (16 - D.toNat % 16)) (n - (16 - D.toNat % 16)) := by
        rw [m₂, m₁, write_eq_writeBytes]
        refine Proof.AesGcm.AArch64.bytesAt_frame (writeBytes_frame s.mem D _ (R := ⟨D, 16⟩)
          (by simp only [List.length_map, List.length_range]; exact Region.contains_self _ _)) (fun r hr => ?_)
          (by omega)
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.disj.sub_left hS).sub_right (Region.sub_prefix (by omega))
      rw [m₃, hrest, m₂, m₁, write_eq_writeBytes, read16_bytes]
      exact head_rest hh1 h16 hn
    · rw [x11₃, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]

end VG.Proof.AesGcm.AArch64.Gather
