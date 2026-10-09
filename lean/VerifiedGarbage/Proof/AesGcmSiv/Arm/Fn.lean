import VerifiedGarbage.Proof.AesGcmSiv.Arm.Crypt
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesGcm.Arm.Args

/-!
# AES-GCM-SIV on ARMv7: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

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

/-!
## The arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`),
what the state may access (`args_of_seal`, `args_of_open`) and the stack
arguments (`args_of`). `recv` and `tagOut` copy the tag, whose address they
read from the stack (`recv_ok`, `tagOut_ok`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, and keeps the arguments in `r7`–`r11` (`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (arg args bel covers_of_mem covers_left covers_prefix SavedAt savedR argAddr_zero stackArg_eq
  in_off add_ofNat_zero mem_store)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .r0
  W := arg s 4
  N := s.gpr .r2
  A := s.gpr .r3
  D := arg s 1
  T := arg s 3
  SP := s.sp
  R := (s.gpr .r1).toNat
  al := (arg s 0).toNat
  n := (arg s 2).toNat

theorem args_eq (s : State) : args s 5 = argR s.sp := by
  simp only [args, argAddr_zero]

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  sig_split h
  rename_i sd sw nd nw ad aw td tw dw da wa bs bn ba bd bt bw fK fN fA fD fT fW sp8 spf
  have hR := h
  clear h
  rw [args_eq] at da wa
  exact ⟨fK, fW, fN, fA, fD, BitVec.isLt _, BitVec.isLt _, sp8, spf, fT, sw, sd, nw, nd, aw, ad, dw, tw, td, da, wa,
    bs, bn, ba, bd, bw, hR⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), 12⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨State.addr (arg s 1), (arg s 2).toNat⟩] s.wr) (hW : Covers [⟨State.addr (arg s 4), 3760⟩] s.wr)
    (ha : Covers [args s 5] (s.rd ++ s.wr)) (hT : Covers [⟨State.addr (arg s 3), 16⟩] (s.rd ++ s.wr))
    (hw : ∀ r ∈ s.wr, (args s 5).Disjoint r) : Perm (prmOf s) s := by
  rw [args_eq] at ha hw
  exact ⟨hk, hN, hA, hD, hW, ha, hw, hT⟩

/-- `seal`'s layout and permissions, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [⟨State.addr (arg s 3), 16⟩] s.wr := by
  obtain ⟨hrd, hwr, ta, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 3), 16⟩,
      ⟨State.addr (arg s 4), 3760⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (covers_left (mwr _ (by simp))) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact da.symm
      · exact ta.symm
      · exact wa.symm), mwr _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) : Lay (prmOf s) ∧ Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), 12⟩,
      ⟨State.addr (s.gpr .r3), (arg s 0).toNat⟩, ⟨State.addr (arg s 3), 16⟩, args s 5], Covers [r] (s.rd ++ s.wr) :=
    fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region), ⟨State.addr (arg s 4), 3760⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  obtain ⟨-, -, -, -, -, -, -, -, -, da, wa, -⟩ := id hl
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (fun r hr => by
      rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact da.symm
      · exact wa.symm)⟩

theorem args_of (s : State) : Args (prmOf s) s.mem :=
  ⟨by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq], by simp [prmOf, arg, stackArg_eq],
    by simp [prmOf, arg, stackArg_eq]⟩

/-- What the entry leaves. -/
structure Entered (s s₁ : State) : Prop where
  env : Env (prmOf s) s₁
  saved : SavedAt s₁.mem (prmOf s).W s
  frame : Frame [savedR (prmOf s).W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {s : State} (L : Lay (prmOf s)) (P : Perm (prmOf s) s) : WP isa (.block entry) s (Entered s) := by
  have hw := L.ww
  have ha : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4 := P.argR' L (k := 16) (by decide)
  have e16 : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = (prmOf s).W := by simp [prmOf, arg, stackArg_eq]
  refine Proof.AesGcm.Arm.entry_ok (off := 16) (by decide) ha (by rw [e16]; omega)
    (by rw [e16]; exact P.w2560) fun s₁ g16 g rd wr sp sv fr => ?_
  rw [e16] at g16 sv fr
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by simp only [sp_setReg]; rw [sp]; rfl,
    P.of_eq (by simp only [rd_setReg]; exact rd) (by simp only [wr_setReg]; exact wr)⟩, by simpa [mem_setReg] using sv,
    by simpa [mem_setReg] using fr, by simp only [rd_setReg]; exact rd, by simp only [wr_setReg]; exact wr⟩
  all_goals simp [gpr_setReg, g, g16, prmOf]

/-! ## The tag's copies -/

/-- `tag`'s address, read from the stack. -/
theorem tagArg {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 12)) 32 = p.T ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 12)) 4 := by
  rw [E.sp]; exact ⟨A.a12, E.perm.argR' L (k := 12) (by decide)⟩

/-- A 16-byte block copied by words, all loaded first. -/
theorem bytesAt_copy4 (m : Mem) (S T : Addr) :
    bytesAt (Proof.Cmac.store4 m T (m.readW S 32) (m.readW (S + BitVec.ofNat 64 4) 32)
      (m.readW (S + BitVec.ofNat 64 8) 32) (m.readW (S + BitVec.ofNat 64 12) 32)) T 16 = bytesAt m S 16 := by
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨State.addr p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.T) 16 ∧
      Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := tagArg L E A
  have tw := L.tw
  have eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega)
  have t₀ : InRegions (s.rd ++ s.wr) (State.addr p.T) 4 := by
    simpa using in_off (d := 0) (n := 4) E.perm.t (by decide) (by decide)
  have t₁ := in_off (d := 4) (n := 4) E.perm.t (by decide) (by decide)
  have t₂ := in_off (d := 8) (n := 4) E.perm.t (by decide) (by decide)
  have t₃ := in_off (d := 12) (n := 4) E.perm.t (by decide) (by decide)
  have w₀ : InRegions s.wr (State.addr p.W) 4 := by simpa using E.perm.wW (show 0 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 4 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 8 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [recv]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact bytesAt_copy4 _ _ _

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨State.addr p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr p.T) 16 = bytesAt s.mem (State.addr p.W) 16 ∧
      Others [.r0, .r1, .r2, .r3, .r12] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hT, hTa⟩ := tagArg L E A
  have tw := L.tw
  have eT : ∀ k, k < 16 → State.addr (p.T + BitVec.ofNat 32 k) = State.addr p.T + BitVec.ofNat 64 k :=
    fun k hk => addr_add (by omega)
  have t₀ : InRegions s.wr (State.addr p.T) 4 := by simpa using in_off (d := 0) (n := 4) hTw (by decide) (by decide)
  have t₁ := in_off (d := 4) (n := 4) hTw (by decide) (by decide)
  have t₂ := in_off (d := 8) (n := 4) hTw (by decide) (by decide)
  have t₃ := in_off (d := 12) (n := 4) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [tagOut]; srun [E.r11, add_ofNat_zero, L.wA, hT, hTa, eT, t₀, t₁, t₂, t₃, w₀, w₁, w₂, w₃],
    ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store]
    exact Proof.Cmac.frame_store4 _ _ _ _ _
  · simp only [mem_setReg, mem_store]
    exact bytesAt_copy4 _ _ _

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, the stack below `SP`, or the key schedule. -/
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
    | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.args_w' $L ?_) <;> decide
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | (with_reducible refine Lay.t_w' $L ?_) <;> decide
    | with_reducible exact Lay.t_d $L
    | with_reducible exact (Lay.t_d $L).symm
    | with_reducible exact (Lay.d_w $L).symm
    | with_reducible exact (Lay.bk $L).symm
    | with_reducible exact (Lay.bn $L).symm
    | with_reducible exact (Lay.ba $L).symm
    | with_reducible exact (Lay.bd $L).symm
    | with_reducible exact Lay.args_below $L
    | with_reducible exact (Lay.d_args $L).symm))

end VG.Proof.AesGcmSiv.Arm

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, and
the restore compute `encryptWith` (RFC 8452 §4) of the arguments
(`seal_wp`), given that the tag input computed with GHASH is the RFC's
(`Proof.GcmSiv.Words.tagInputG`, related to it in `Verified.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR restore_ok)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

theorem bytesAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨P, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' P n = bytesAt m P n :=
  Proof.AesGcm.Arm.bytesAt_frame hf hd hn

theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr} {R : Nat}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) (hR : 16 * (R + 1) ≤ 240) :
    Spec.GcmSiv.ctxCiph m' K R = Spec.GcmSiv.ctxCiph m K R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_keep hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : Prm} (L : Lay p) {s₀ t : State} (E : Env p t) (hsp : p.SP = s₀.sp)
    (hs : SavedAt t.mem p.W s₀) :
    WP isa (.block Impl.AesGcm.Arm.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .r0 = t.gpr .r0 :=
  WP.mono (restore_ok E.r11 (by have := L.ww; omega) (covers_left (covers_prefix E.perm.w (by decide))) hs
    (by rw [E.sp, hsp])) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩
where
  covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := Proof.AesGcm.Arm.covers_left h
  covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
      Covers [⟨p, n⟩] rs := Proof.AesGcm.Arm.covers_prefix h hn

/-- A run, which keeps the permissions. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, hq⟩ := h
  exact ⟨t, s', e, hq, (Exec.rdwr e).1, (Exec.rdwr e).2.1⟩

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (hti : TagInputEq) {s : State} (h : sealPre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' := by
  obtain ⟨L, P, hTw⟩ := args_of_seal h
  have hRb := L.rounds_le
  have hn := L.n_lt
  have A₀ := args_of s
  refine WP.seq (WP.mono (WP.rdwr (entry_ok L P)) fun s₁ ⟨En, _, w₁⟩ => ?_)
  have A₁ : Args (prmOf s) s₁.mem := A₀.frame L En.frame (by disj_tac L)
  -- The keys.
  refine WP.seq (WP.mono (WP.rdwr (keys_ok L En.env)) fun s₂ ⟨Ky, _, w₂⟩ => ?_)
  have A₂ : Args (prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok L Ky.env A₂ Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have A₃ : Args (prmOf s) s₃.mem := A₂.frame L Po.frame (by disj_tac L)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  have A₄ : Args (prmOf s) s₄.mem := A₃.frame L Tg.frame (by disj_tac L)
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok L Tg.env A₄) fun s₅ Cr => ?_)
  have A₅ : Args (prmOf s) s₅.mem := A₄.frame L Cr.frame (by disj_tac L)
  -- The copy of the tag, and `restore`.
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, w₂, w₁]
  obtain ⟨s₆, run₆, fT, hT₆, ho₆, sp₆, rd₆, wr₆⟩ := tagOut_ok L Cr.env A₅ (by rw [w₅]; exact hTw)
  have E₆ : Env (prmOf s) s₆ := Cr.env.of_others ho₆ sp₆ rd₆ wr₆
  have sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (((((En.saved.frame Ky.frame (by disj_tac L)).frame Po.frame (by disj_tac L)).frame Tg.frame
      (by disj_tac L)).frame Cr.frame (by disj_tac L))).frame fT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.t_w' (show 128 + 36 ≤ 3760 by decide)).symm
  refine WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  refine WP.mono (exit_ok L E₆ rfl sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
      (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12)
      (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al) =
    (bytesAt s'.mem (State.addr (prmOf s).D) (prmOf s).n, bytesAt s'.mem (State.addr (prmOf s).T) 16)
  rw [hm, hT₆, bytesAt_keep fT (by disj_tac L) (by omega)]
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (prmOf s).K) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R :=
    ciph_keep En.frame (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 :=
    bytesAt_keep En.frame (by disj_tac L) (by decide)
  have n₂ : bytesAt s₂.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₂ : bytesAt s₂.mem (State.addr (prmOf s).A) (prmOf s).al = bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep En.frame (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep En.frame (by disj_tac L) (by omega)]
  have d₄ : bytesAt s₄.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by omega), bytesAt_keep Po.frame (by disj_tac L) (by omega), d₂]
  have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R :=
    ciph_keep Po.frame (by disj_tac L) hRb
  have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R := by
    rw [ciph_keep Tg.frame (by disj_tac L) hRb, key₃]
  have t₅ : bytesAt s₅.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.Arm

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 176`, the comparison, the mask and the restore
compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR)

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

theorem ite_ofNat (c : Prop) [Decidable c] :
    (if c then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (if c then 1 else 0) := by
  split <;> rfl

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (hti : TagInputEq) {s : State} (h : openPre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' := by
  obtain ⟨L, P⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  have A₀ := args_of s
  refine WP.seq (WP.mono (entry_ok L P) fun s₀ En₀ => ?_)
  have A₀' : Args (prmOf s) s₀.mem := A₀.frame L En₀.frame (by disj_tac L)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L En₀.env A₀'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have fR' : Frame [⟨State.addr (prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by
    rw [BitVec.add_zero]; exact fR
  have E₁ : Env (prmOf s) s₁ := En₀.env.of_others ho₁ sp₁ rd₁ wr₁
  have sv₁ : SavedAt s₁.mem (prmOf s).W s := En₀.saved.frame fR' (by disj_tac L)
  have f₁ : Frame [savedR (prmOf s).W, ⟨State.addr (prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (En₀.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have A₁ : Args (prmOf s) s₁.mem := A₀'.frame L fR' (by disj_tac L)
  have hT₁ : bytesAt s₁.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [BitVec.add_zero, hR₁, bytesAt_keep En₀.frame (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok L E₁) fun s₂ Ky => ?_)
  have A₂ : Args (prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok L Ky.env A₂) fun s₃ Cr => ?_)
  have A₃ : Args (prmOf s) s₃.mem := A₂.frame L Cr.frame (by disj_tac L)
  have a₃ : bytesAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16 =
      bytesAt s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok L Cr.env A₃ hG₃ hY₃) fun s₄ Po => ?_)
  have A₄ : Args (prmOf s) s₄.mem := A₃.frame L Po.frame (by disj_tac L)
  -- Its tag at `W + 176`.
  refine WP.seq (WP.mono (tag_ok L Po.env (o := 176) (by decide)) fun s₅ Tg => ?_)
  have A₅ : Args (prmOf s) s₅.mem := A₄.frame L Tg.frame (by disj_tac L)
  -- The comparison.
  obtain ⟨s₆, run₆, r0₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env (prmOf s) s₆ := Tg.env.of_others ho₆ sp₆ rd₆ wr₆
  rw [ite_ofNat] at r0₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ (hm₆ ▸ A₅) r0₆) fun s₇ Mk => ?_)
  -- The restore.
  have sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok L Mk.env rfl sv₇) fun s' ⟨ga, hm, hr0⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (prmOf s).K) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 :=
    bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₃ : bytesAt s₃.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by decide), bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₃' : bytesAt s₃.mem (State.addr (prmOf s).A) (prmOf s).al =
      bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have tag₂ : bytesAt s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), hT₁]
  have tag₅ : bytesAt s₅.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide), bytesAt_keep Po.frame (by disj_tac L) (by decide),
      bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R := by
    rw [ciph_keep Po.frame (by disj_tac L) hRb, ciph_cryR L Cr.frame]
  have d₆ : bytesAt s₆.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s₃.mem (State.addr (prmOf s).D) (prmOf s).n := by
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
  have ax : s'.gpr .r0 = s₆.gpr .r0 := by rw [hr0, Mk.r0]
  rw [r0₆, tg, tag₅] at ax
  show openPost (openResult s) s' (State.addr (prmOf s).D) (prmOf s).n
  have hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
            (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) =
          bytesAt s.mem (State.addr (prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
          (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
        (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) =
      bytesAt s.mem (State.addr (prmOf s).T) 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (State.addr (prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (State.addr (prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
          (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) :=
      Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.Arm
