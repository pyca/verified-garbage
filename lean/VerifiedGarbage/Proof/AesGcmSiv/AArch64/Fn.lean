import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp

/-!
# AES-GCM-SIV on AArch64: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

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

/-!
## The arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`)
and what the state may access (`args_of_seal`, `args_of_open`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, keeps the arguments in `x19`–`x26` and `tag` at `W + 216`
(`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (saved)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left SavedAt savedR save_ok savedMem_frame savedAt_save in_off
  Others)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .x0
  W := stackArg s 0
  N := s.gpr .x2
  A := s.gpr .x3
  D := s.gpr .x5
  T := s.gpr .x7
  SP := s.sp
  R := (s.gpr .x1).toNat
  al := (s.gpr .x4).toNat
  n := (s.gpr .x6).toNat

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, _, b1, b2, b3, b4, b5, b6, _, hR⟩ := h
  exact ⟨b1, b6, b2, b3, b4, d2, d1, d4, d3, d6, d5, d9, b5, d8, d7, hR, BitVec.isLt _, BitVec.isLt _⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨s.gpr .x2, 12⟩] (s.rd ++ s.wr)) (hA : Covers [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 0, 3808⟩] s.wr)
    (hT : Covers [⟨s.gpr .x7, 16⟩] (s.rd ++ s.wr)) : Perm (prmOf s) s :=
  ⟨hk, hN, hA, hD, hW, hT⟩

/-- `seal`'s layout and permissions, its tag to write, and its stack argument
to read. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [⟨s.gpr .x7, 16⟩] s.wr ∧ Covers [args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩, args s],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨s.gpr .x7, 16⟩, ⟨stackArg s 0, 3808⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (covers_left (mwr _ (by simp))), mwr _ (by simp), mrd _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag to read, and its
stack argument to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x7, 16⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨stackArg s 0, 3808⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)), mrd _ (by simp)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the entry writes: the save area and `tag`'s address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 96⟩

/-- `tag`'s address, at `W + 216`. -/
abbrev TagSlot (p : Prm) (m : Mem) : Prop := m.readW (p.W + BitVec.ofNat 64 216) 64 = p.T

/-- `entry`. -/
theorem entry_ok {s : State} (P : Perm (prmOf s) s) (hA : Covers [args s] (s.rd ++ s.wr)) :
    WP isa (.block entry) s fun s₁ => Env (prmOf s) s₁ ∧ SavedAt s₁.mem (prmOf s).W s ∧
      Frame [entryR (prmOf s).W] s.mem s₁.mem ∧ TagSlot (prmOf s) s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.block_append (WP.block_append (WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s₀ hs₀ => ?_))
  subst hs₀
  have hW₀ : (s.write .x .x9 (s.mem.readW s.sp 64)).gpr .x9 = (prmOf s).W := by
    simp [gpr_write, prmOf, stackArg, stackArgAddr]
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok _ .x9 hW₀ (by simpa only [wr_write] using P.w2560)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hWv : (prmOf s).W = s.mem.readW s.sp 64 := by simp [prmOf, stackArg, stackArgAddr, Mem.readW]
  have w216 : InRegions s₁.wr (s.mem.readW s.sp 64 + BitVec.ofNat 64 216) 8 := by
    rw [wr₁, ← hWv]; simpa only [wr_write] using in_off P.w (show 216 + 8 ≤ 3808 by decide) (by decide)
  refine WP.run ⟨_, by grun [g₁, BitVec.add_zero, w216], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  have hs : ∀ r ∈ saved, (s.write .x .x9 (s.mem.readW s.sp 64)).gpr r.1 = s.gpr r.1 := by
    intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have sv : SavedAt s₁.mem (prmOf s).W s := by
    rw [m₁]; exact fun p hp => (savedAt_save _ _ _ p hp).trans (hs p hp)
  have fS : Frame [entryR (prmOf s).W] s.mem s₁.mem := by
    rw [m₁]; simp only [mem_write]
    exact (savedMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have c216 : (entryR (prmOf s).W).Contains ((prmOf s).W + BitVec.ofNat 64 216) (64 / 8) := by
    rw [show (prmOf s).W + BitVec.ofNat 64 216 = ((prmOf s).W + BitVec.ofNat 64 128) + BitVec.ofNat 64 88 from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by decide) (by decide)
  have e : ∀ (m : Mem) (a : Addr) (v : BitVec 64), m.write a 8 v = m.writeW a v := fun m a v => by
    simp [Mem.writeW]
  rw [← hWv] at *
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [sp_write]; rw [sp₁]; rfl,
    P.of_eq (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)⟩, ?_, ?_, ?_, ?_, ?_⟩
  iterate 8 (simp [gpr_write, g₁, prmOf, ofNat_toNat64, stackArg, stackArgAddr, Mem.readW])
  · simp only [mem_write, e]
    exact sv.frame ((Frame.refl [(⟨(prmOf s).W + BitVec.ofNat 64 216, 8⟩ : Region)] _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · simp only [mem_write, e]
    exact fS.writeW (List.mem_singleton_self _) _ c216
  · simp only [mem_write, e, TagSlot, Mem.readW_writeW_self64]
    simp [gpr_write, g₁, prmOf]
  · simp only [rd_write]; exact rd₁
  · simp only [wr_write]; exact wr₁

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hT : TagSlot p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.W 16 = bytesAt s.mem p.T 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have t₀ : InRegions (s.rd ++ s.wr) p.T 8 := by simpa using in_off (d := 0) (n := 8) E.perm.t (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) E.perm.t (by decide) (by decide)
  have w₀ : InRegions s.wr p.W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 8 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  have hs : Mem.Sep (p.T + BitVec.ofNat 64 8) (64 / 8) p.W (64 / 8) :=
    L.t_w.sep (Offset.contains_base p.T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base p.W (d := 0) (n := 8) (k := 3808) (by decide) (by decide))
  refine ⟨_, by simp only [recv]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hT : TagSlot p s.mem)
    (hTw : Covers [⟨p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.T 16 = bytesAt s.mem p.W 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have t₀ : InRegions s.wr p.T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  have hs : Mem.Sep (p.W + BitVec.ofNat 64 8) (64 / 8) p.T (64 / 8) :=
    L.t_w.symm.sep (Offset.contains_base p.W (d := 8) (n := 8) (k := 3808) (by decide) (by decide))
      (by simpa using Offset.contains_base p.T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by simp only [tagOut]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, or the key schedule. -/
macro "disj_tac" L:term : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.k_w' $L ?_) <;> decide
    | (with_reducible refine Lay.n_w' $L ?_) <;> decide
    | (with_reducible refine Lay.a_w' $L ?_) <;> decide
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | (with_reducible refine Lay.t_w' $L ?_) <;> decide
    | with_reducible exact Lay.t_d $L
    | with_reducible exact (Lay.t_d $L).symm
    | with_reducible exact (Lay.d_w $L).symm))

end VG.Proof.AesGcmSiv.AArch64

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.AArch64.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- A run, which keeps the permissions. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨t, s', e, hq, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

/-- `tag`'s address in `W`, after code that misses it. -/
theorem TagSlot.frame {p : Prm} {m m' : Mem} (h : TagSlot p m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p.W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r) : TagSlot p m' := by
  unfold TagSlot at *
  rw [hf.readW (r := ⟨p.W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) hd (by decide), h]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (h : sealPre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨L, P, hTw, hA⟩ := args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₁ ⟨E₁, sv₁, f₁, sl₁, rd₁, wr₁⟩ => ?_)
  -- The keys.
  refine WP.seq (WP.mono (WP.rdwr (keys_ok v L E₁)) fun s₂ ⟨Ky, _, kw⟩ => ?_)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  -- The copy of the tag, and `restore`.
  have sl₅ : TagSlot (prmOf s) s₅.mem :=
    (((sl₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L)
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, kw, wr₁]
  obtain ⟨s₆, run₆, fT, hT₆, -, ho₆, sp₆, rd₆, wr₆⟩ := tagOut_ok L Cr.env sl₅ (by rw [w₅]; exact hTw)
  have E₆ : Env (prmOf s) s₆ := Cr.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (((((sv₁.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame (by disj_tac L)).frame
      Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 88 ≤ 3808 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok (s₀ := s) E₆.x19 E₆.sp E₆.w2560R sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R) (Spec.GcmSiv.keyLen (prmOf s).R)
      (bytesAt s.mem (prmOf s).N 12) (bytesAt s.mem (prmOf s).D (prmOf s).n) (bytesAt s.mem (prmOf s).A (prmOf s).al) =
    (bytesAt s'.mem (prmOf s).D (prmOf s).n, bytesAt s'.mem (prmOf s).T 16)
  rw [hm, hT₆, bytesAt_keep fT (by disj_tac L) (by omega)]
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₂ : bytesAt s₂.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₂ : bytesAt s₂.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have d₄ : bytesAt s₄.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega), bytesAt_keep Po.frame (by disj_tac L) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  have t₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [L.w0] at t₅
  have tg := Tg.out
  rw [L.w0] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.AArch64

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 224`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl SavedAt savedR exit_ok Others)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (h : openPre s) :
    WP isa («open» v.callees) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  obtain ⟨L, P, hA⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  refine WP.seq (WP.mono (entry_ok P hA) fun s₀ ⟨E₀, sv₀, f₀, sl₀, _, _⟩ => ?_)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, -, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L E₀ sl₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env (prmOf s) s₁ := E₀.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fR' : Frame [⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by rw [L.w0]; exact fR
  have sv₁ : SavedAt s₁.mem (prmOf s).W s := sv₀.frame fR' (by disj_tac L)
  have f₁ : Frame [entryR (prmOf s).W, ⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(prmOf s).W + BitVec.ofNat 64 0, 16⟩, by simp, fun _ h => h⟩)
  have hT₁ : bytesAt s₁.mem (prmOf s).W 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [hR₁, bytesAt_keep f₀ (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  have a₃ : bytesAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem ((prmOf s).W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.AArch64.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem ((prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.AArch64.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  -- Its tag at `W + 224`.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 224) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, x27₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env (prmOf s) s₆ := Tg.env.keep (fun r hr => ho₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ x27₆) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  refine WP.block_append (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok (s₀ := s) (Mk.env.write (by decide) _).x19 (Mk.env.write (by decide) _).sp
    (Mk.env.write (by decide) _).w2560R (by simp only [mem_write]; exact sv₇)) fun s' ⟨ga, hm, hx0, _⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (prmOf s).K (prmOf s).R = Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₃ : bytesAt s₃.mem (prmOf s).N 12 = bytesAt s.mem (prmOf s).N 12 := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by decide), bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₃' : bytesAt s₃.mem (prmOf s).A (prmOf s).al = bytesAt s.mem (prmOf s).A (prmOf s).al := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (prmOf s).D (prmOf s).n = bytesAt s.mem (prmOf s).D (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have tag₂ : bytesAt s₂.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), L.w0, hT₁]
  have tag₅ : bytesAt s₅.mem ((prmOf s).W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (prmOf s).T 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide), bytesAt_keep Po.frame (by disj_tac L) (by decide),
      bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [L.w0] at tag₂ tag₅
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem ((prmOf s).W + BitVec.ofNat 64 240) (prmOf s).R := by
    rw [ciph_keep Po.frame (by disj_tac L) hRb, ciph_cryR L Cr.frame]
  have d₆ : bytesAt s₆.mem (prmOf s).D (prmOf s).n = bytesAt s₃.mem (prmOf s).D (prmOf s).n := by
    rw [hm₆, bytesAt_keep Tg.frame (by disj_tac L) (by omega), bytesAt_keep Po.frame (by disj_tac L) (by omega)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  have ax : s'.gpr .x0 = s₆.gpr .x27 := by
    rw [hx0]; simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero]; exact Mk.x27
  rw [x27₆, tg, tag₅] at ax
  show openPost (openResult s) s' (prmOf s).D (prmOf s).n
  have hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
            (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
          bytesAt s.mem (prmOf s).T 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (prmOf s).K (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (prmOf s).N 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
        (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) =
      bytesAt s.mem (prmOf s).T 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (prmOf s).T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (prmOf s).N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (prmOf s).T 16))
          (bytesAt s.mem (prmOf s).D (prmOf s).n)) (bytesAt s.mem (prmOf s).A (prmOf s).al)) := Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm]; simp only [mem_write]; rw [md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.AArch64
