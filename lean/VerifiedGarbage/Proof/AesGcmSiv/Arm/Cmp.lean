import VerifiedGarbage.Proof.AesGcmSiv.Arm.Crypt
import VerifiedGarbage.Proof.AesGcm.Arm.Compare

/-!
# AES-GCM-SIV on ARMv7: comparing the tags and masking the data

Untrusted: everything here is checked by Lean. `cmp` sets `r0` to 1 if the
tags at `W` and `W + 176` are equal and 0 if not, without a branch, as
AES-GCM's `cmpTail` does (`Proof.AesGcm.Arm.cmp_value`) (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − r0`: it keeps the data if `r0` is 1
and zeroes it if `r0` is 0 (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.Arm (add_ofNat_assoc add_ofNat_zero eval_eq' eval_ne' z_cmp ofNat_sub32 ofNat_add32
  mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags
  wr_subFlags length_bytesAt in_of_covers cmp_value words_eq_iff bytes_words)

theorem cmp_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.gpr .r0 = (if bytesAt t.mem (State.addr p.W) 16 =
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 176) 16 then 1 else 0) ∧
      Others [.r0, .r1, .r2] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ : InRegions (t.rd ++ t.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  have q₀ := E.perm.wR (show 176 + 4 ≤ 3760 by decide)
  have q₁ := E.perm.wR (show 180 + 4 ≤ 3760 by decide)
  have q₂ := E.perm.wR (show 184 + 4 ≤ 3760 by decide)
  have q₃ := E.perm.wR (show 188 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [cmp, xorW]; srun [E.r11, add_ofNat_zero, L.wA, r₀, r₁, r₂, r₃, q₀, q₁, q₂, q₃], ?_,
    by others_tac, by rfl, by rfl, by rfl, by rfl⟩
  simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  rw [cmp_value, bytes_words, bytes_words]
  simp only [add_ofNat_assoc, add_ofNat_zero, Nat.reduceAdd]
  congr 1
  exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm

/-! ## The mask -/

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, Impl.AesGcm.Arm.addI .r4 .r4 1,
    .subs .r5 .r5 (Impl.AesGcm.Arm.imm 1)]

theorem byte_and (a : Byte) (k : BitVec 32) : (a.setWidth 32 &&& k).setWidth 8 = a &&& k.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 32 by omega, hi, decide_true, Bool.true_and]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept' {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : BitVec 32} {n : Nat} (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    (hn1 : 1 ≤ n) (hn : n < 2 ^ 32) (hf : D.toNat + n ≤ 2 ^ 32) (hw : Covers [⟨State.addr D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem (State.addr D) (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) n) ∧
      Others [.r4, .r5, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r4 = D + BitVec.ofNat 32 i ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) i) ∧
      Others [.r4, .r5, .r12] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, by omega, by rw [h4, add_ofNat_zero], by rw [h5, Nat.sub_zero],
      by simp [maskBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r4, r5, mem, g, sp, rd, wr⟩
  have ea : State.addr (D + BitVec.ofNat 32 i) = State.addr D + BitVec.ofNat 64 i := addr_add (by omega)
  have w₁ : InRegions t.wr (State.addr D + BitVec.ofNat 64 i) 1 := by rw [wr]; exact in_of_covers hw hi (by omega)
  have w₂ : InRegions (t.rd ++ t.wr) (State.addr D + BitVec.ofNat 64 i) 1 := Proof.AesGcm.Arm.in_left w₁
  have h1 : t.gpr .r1 = s.gpr .r1 := g _ (by decide)
  obtain ⟨t', run', mem', r4', r5', z', g', sp', rd', wr'⟩ : ∃ t', runBlock isa maskBody t = some t' ∧
      t'.mem = t.mem.writeW (State.addr D + BitVec.ofNat 64 i)
        (t.mem (State.addr D + BitVec.ofNat 64 i) &&& (s.gpr .r1).setWidth 8) ∧
      t'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ t'.gpr .r5 = BitVec.ofNat 32 (n - (i + 1)) ∧
      t'.z = decide (n - (i + 1) = 0) ∧ Others [.r4, .r5, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
    refine ⟨_, by srun [r4, r5, add_ofNat_zero, ea, w₁, w₂], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, byte_and, h1]
    · simp [gpr_setReg, r4, Proof.AesGcm.Arm.add32_ofNat_assoc]
    · simp only [gpr_setReg, gpr_subFlags, ite_true, r5]
      rw [ofNat_sub32 (by omega) (by omega)]; rfl
    · simp only [z_setReg, z_subFlags]
      rw [z_cmp (by omega) (by decide)]
      congr 1; apply propext; omega
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) i).length = i := by
    simp [maskBytes, length_bytesAt]
  have hmem : t'.mem = writeBytes s.mem (State.addr D) (maskBytes s.mem (State.addr D) ((s.gpr .r1).setWidth 8) (i + 1)) := by
    rw [mem', mem, dst_kept' (by omega) _ hlen]
    simp only [maskBytes]
    rw [Proof.AesGcm.Arm.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem _ _ _ (by rw [List.length_map, length_bytesAt]; omega),
      List.length_map, length_bytesAt]
  have ev := eval_ne' z'
  have gg : Others [.r4, .r5, .r12] s t' := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega, r4', r5', hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#32 - BitVec.ofNat 32 1 : BitVec 32).setWidth 8) = xs := by
  rw [show (0#32 - BitVec.ofNat 32 1 : BitVec 32).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#32 - BitVec.ofNat 32 0 : BitVec 32).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#32 - BitVec.ofNat 32 0 : BitVec 32).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `r0` is whether `c` holds. -/
structure MaskPost (p : Prm) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env p t'
  r0 : t'.gpr .r0 = t.gpr .r0
  frame : Frame [⟨State.addr p.D, p.n⟩] t.mem t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = if c then bytesAt t.mem (State.addr p.D) p.n else Spec.GcmSiv.zeros p.n

theorem mask_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) {c : Prop} [Decidable c]
    (hok : t.gpr .r0 = BitVec.ofNat 32 (if c then 1 else 0)) :
    WP isa mask t (MaskPost p c t) := by
  have hn := L.n_lt
  have a₄ := E.perm.argR' L (k := 4) (by decide)
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain ⟨t₁, run₁, r1₁, r4₁, r5₁, z₁, ho₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      [.ldrSp .r4 4, .ldrSp .r5 8, .mov .r1 (Impl.AesGcm.Arm.imm 0), .dp .sub .r1 .r1 (.reg .r0),
        .cmp .r5 (Impl.AesGcm.Arm.imm 0)] t = some t₁ ∧
      t₁.gpr .r1 = 0#32 - t.gpr .r0 ∧ t₁.gpr .r4 = p.D ∧ t₁.gpr .r5 = BitVec.ofNat 32 p.n ∧
      t₁.z = decide (p.n = 0) ∧ Others [.r1, .r4, .r5] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
    refine ⟨_, by srun [E.sp, a₄, a₈, A.a4, A.a8], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
      rw [z_cmp hn (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have r0₁ : t₁.gpr .r0 = t.gpr .r0 := ho₁ _ (by decide)
  refine WP.ite (decide (p.n = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n = 0 := by simpa using ht
    refine WP.block_nil ⟨E₁, r0₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    rw [h0]; split <;> simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : p.n ≠ 0 := by simpa using hf
    refine WP.mono (maskLoop_ok t₁ r4₁ r5₁ (by omega) hn L.dw E₁.perm.d) fun t₂ ⟨hm₂, ho₂, sp₂, rd₂, wr₂⟩ => ?_
    have hl : (maskBytes t₁.mem (State.addr p.D) ((t₁.gpr .r1).setWidth 8) p.n).length = p.n := by
      simp [maskBytes, length_bytesAt]
    refine ⟨E₁.of_others ho₂ sp₂ rd₂ wr₂, by rw [ho₂ _ (by decide), r0₁],
      by rw [hm₂, ← hm₁]; exact Proof.AesGcm.Arm.writeBytes_frame' _ hl, ?_⟩
    have e := Proof.AesGcm.Arm.bytesAt_writeBytes_self t₁.mem (State.addr p.D)
      (maskBytes t₁.mem (State.addr p.D) ((t₁.gpr .r1).setWidth 8) p.n) (by omega)
    rw [hl] at e
    rw [hm₂, e, r1₁, hok, hm₁]
    simp only [maskBytes]
    split
    · exact map_and_ff _
    · rw [map_and_zero, length_bytesAt]

end VG.Proof.AesGcmSiv.Arm
