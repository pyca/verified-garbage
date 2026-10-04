import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp

/-!
# AES-GCM-SIV on AArch64: comparing the tags and masking (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` leaves in `x27`
whether the received tag at `W` equals the computed one at `W + 224`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − x27`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.AArch64 (add_ofNat_assoc ofNat_sub eval_zero eval_nonzero Others in_of_covers
  length_bytesAt succ_ofNat read_one)

/-- `x27` from the words of the tags: 1 if they are equal, 0 if not. -/
theorem ok_val (d : BitVec 64) :
    (BitVec.setWidth 64 (1#16) <<< 0 : BitVec 64) - BitVec.ofNat 64 (if d = 0 then 0 else 1) =
      BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  by_cases h : d = 0 <;> simp only [h, ↓reduceIte] <;> decide

theorem cmp_ok {p : Prm} {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.gpr .x27 = BitVec.ofNat 64 (if bytesAt t.mem p.W 16 = bytesAt t.mem (p.W + BitVec.ofNat 64 224) 16
        then 1 else 0) ∧
      Others [.x9, .x10, .x11, .x12, .x27] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ : InRegions (t.rd ++ t.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have r₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have u₀ := E.perm.wR (show 224 + 8 ≤ 3808 by decide)
  have u₈ := E.perm.wR (show 232 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [cmp]; grun [E.x19, BitVec.add_zero, r₀, r₈, u₀, u₈, gpr_addWithCarry, c_addWithCarry,
    mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry, c_write], ?_,
    fun r hr => ?_, (by rfl), (by rfl), (by rfl), (by rfl)⟩
  · have key := Proof.AesGcm.AArch64.words_eq t.mem p.W (p.W + BitVec.ofNat 64 224)
    rw [add_ofNat_assoc] at key
    simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
      Size.bits, Nat.reduceAdd, show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv,
      Nat.reduceMul]
    refine (congrArg (HSub.hSub (BitVec.setWidth 64 (1#16) <<< 0 : BitVec 64))
      (Proof.AesGcm.AArch64.carry_val _)).trans ((ok_val _).trans ?_)
    simp only [Mem.readW, BitVec.setWidth_eq] at key
    simp only [key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, gpr_addWithCarry, hr]

/-! ## The mask -/

abbrev maskBody : List Instr :=
  [.ldrb .x14 .x12 0, .logic .and .w .x14 .x14 .x11, .strb .x14 .x12 0, Impl.AesGcm.AArch64.ptr .x12 .x12 1,
    .subImm .x .x13 .x13 1]

theorem byte_and (a : BitVec (8 * 1)) (k : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) &&& BitVec.setWidth 32 k))) =
      a &&& k.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, show i < 64 by omega, show i < 32 by omega,
    hi, decide_true, Bool.true_and]

theorem maskStep_ok (s : State) {A : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A) (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A &&& (s.gpr .x11).setWidth 8) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      Others [.x12, .x13, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := Proof.AesGcm.AArch64.in_left (rd := s.rd) w
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      Impl.AesGcm.AArch64.ptr, ha, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, byte_and, read_one,
    Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept' {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .x12 = D) (hn : s.gpr .x13 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hnl : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) (.nonzero .x .x13)) s fun s' =>
      s'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) n) ∧
      Others [.x12, .x13, .x14] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) i) ∧
      Others [.x12, .x13, .x14] s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, by omega, by rw [hd]; simp, by rw [hn, Nat.sub_zero], by simp [maskBytes, bytesAt, writeBytes_nil],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x13', g', sp', rd', wr'⟩ := maskStep_ok t (A := D + BitVec.ofNat 64 i)
    (by rw [x12, BitVec.add_zero]) (by rw [wr]; exact in_of_covers hw hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (maskBytes s.mem D ((s.gpr .x11).setWidth 8) i).length = i := by
    simp [maskBytes, length_bytesAt]
  have h11 : t.gpr .x11 = s.gpr .x11 := g _ (by decide)
  have hmem : t'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .x11).setWidth 8) (i + 1)) := by
    rw [mem', mem, dst_kept' (by omega) _ hlen, h11]
    simp only [maskBytes]
    rw [Proof.AesGcm.AArch64.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem D _ _ (by rw [List.length_map, length_bytesAt]; omega),
      List.length_map, length_bytesAt]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : Others [.x12, .x13, .x14] s t' := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, succ_ofNat], x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#64 - BitVec.ofNat 64 1 : BitVec 64).setWidth 8) = xs := by
  rw [show (0#64 - BitVec.ofNat 64 1 : BitVec 64).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#64 - BitVec.ofNat 64 0 : BitVec 64).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#64 - BitVec.ofNat 64 0 : BitVec 64).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `x27` is whether `c` holds. -/
structure MaskPost (p : Prm) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env p t'
  x27 : t'.gpr .x27 = t.gpr .x27
  frame : Frame [⟨p.D, p.n⟩] t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = if c then bytesAt t.mem p.D p.n else Spec.GcmSiv.zeros p.n

theorem mask_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {c : Prop} [Decidable c]
    (hok : t.gpr .x27 = BitVec.ofNat 64 (if c then 1 else 0)) :
    WP isa mask t (MaskPost p c t) := by
  have hn := L.n_lt
  obtain ⟨t₁, run₁, x11₁, x12₁, x13₁, ho₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      [Impl.AesGcm.AArch64.imm .x9 0, .sub .x .x11 .x9 .x27, Impl.AesGcm.AArch64.mov .x12 .x25,
        Impl.AesGcm.AArch64.mov .x13 .x26] t = some t₁ ∧
      t₁.gpr .x11 = 0#64 - t.gpr .x27 ∧ t₁.gpr .x12 = p.D ∧ t₁.gpr .x13 = BitVec.ofNat 64 p.n ∧
      Others [.x9, .x11, .x12, .x13] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write]
    · simp [gpr_write, E.x25]
    · simp [gpr_write, E.x26]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have x27₁ : t₁.gpr .x27 = t.gpr .x27 := ho₁ _ (by decide)
  refine WP.ite (decide (p.n = 0)) (eval_zero x13₁ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n = 0 := by simpa using ht
    refine WP.block_nil ⟨E₁, x27₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    rw [h0]; split <;> simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : p.n ≠ 0 := by simpa using hf
    refine WP.mono (maskLoop_ok t₁ x12₁ x13₁ (by omega) hn E₁.perm.d) fun t₂ ⟨hm₂, ho₂, sp₂, rd₂, wr₂⟩ => ?_
    have hl : (maskBytes t₁.mem p.D ((t₁.gpr .x11).setWidth 8) p.n).length = p.n := by
      simp [maskBytes, length_bytesAt]
    refine ⟨E₁.keep (fun r hr => ho₂ r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
      by rw [ho₂ _ (by decide), x27₁], by rw [hm₂, ← hm₁]; exact Proof.AesGcm.AArch64.writeBytes_frame' _ hl, ?_⟩
    have e := Proof.AesGcm.AArch64.bytesAt_writeBytes_self t₁.mem p.D
      (maskBytes t₁.mem p.D ((t₁.gpr .x11).setWidth 8) p.n) (by omega)
    rw [hl] at e
    rw [hm₂, e, x11₁, hok, hm₁]
    simp only [maskBytes]
    split
    · exact map_and_ff _
    · rw [map_and_zero, length_bytesAt]

end VG.Proof.AesGcmSiv.AArch64
