import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
import VerifiedGarbage.Proof.Cmac.Stream

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: copying a slice

Untrusted: everything here is checked by Lean. `copyBlocks` copies `k ≥ 1`
blocks from `x12` to `x11`, 16 bytes at a time through `v0`
(`copyBlocks_wp`), and `copySlice` the `n` bytes at `x12` to `x11`: its
whole blocks so, then its last `n mod 16` bytes one at a time (`copyLoop`,
`copyLoop_ok`), leaving `x11` past them (`copySlice_wp`). The bytes copied
and the bytes written do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok eval_zero eval_nonzero succ_ofNat loopRegs covers_prefix covers_off)

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

/-- `copySlice`: the `n` bytes at `S` to `D`, and `x11` past them. -/
theorem copySlice_wp (s : State) {S D : Addr} {n : Nat} (h : SlicePre s S D n) :
    WP isa copySlice s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
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
    refine WP.mono (copyLoop_ok s₃ (by rw [g₃ _ (by decide) (by decide), x12₂])
      (by rw [g₃ _ (by decide) (by decide), x11₂]) x13₃' (by omega) lp) fun s₄ ⟨m₄, _, x11₄, g₄, sp₄, rd₄, wr₄⟩ =>
        ⟨?_, by rw [x11₄, hend], kp₃.trans ⟨g₄, sp₄, rd₄, wr₄⟩⟩
    rw [m₄, hrest, m₃, m₂, hall]

end VG.Proof.AesGcm.AArch64.Gather
