module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy

/-!
# Deterministic ECDSA on AArch64: a candidate

RFC 6979's step h.2: `T`, the concatenation of `V = HMAC_K(V)` until it has
at least `Q` bytes (`genT` with `blocks` of them, `blocks_eq`), at `T` in
the frame, with its length so far in the frame: each step (`step_ok`) is
`V = HMAC_K(V)`, `V`'s 64 bytes copied after the `D` bytes of `T` so far,
`T`'s length `D` more, and `x12 ≠ 0` iff it is still below `Q`. The loop of
them (`loopT_ok`) leaves `T`; the candidate `k`, read by `core` at `T`, is
its leftmost `Q` bytes, shifted right by `sh` bits if `wide` (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-! ## `T`, as RFC 6979 computes it -/

theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (i : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (i + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K i V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K i V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K i V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | i + 1, V => by
    rw [Spec.Ecdsa.Rfc6979.genT, genT_succ H K i]
    simp [Spec.Ecdsa.Rfc6979.genT]

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (i : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V).1.length = i * P.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | i + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K i, show Spec.Hmac.hmac P.ok.SH.H K _ = P.mac K _ from rfl,
      P.mac_length, Nat.succ_mul]

/-- The number of `V`s in a candidate: the fewest whose `D` bytes each make
at least `Q`, as many as RFC 6979's `blocks` makes `qlen` bits. -/
theorem blocks_eq (P : RfcHash) {n : Nat} (h₁ : (n - 1) * P.H.D < P.Q) (h₂ : P.Q ≤ n * P.H.D) :
    Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = n := by
  have hl := P.R.nBits_len
  have hD := P.sizes.2.2.2.2.2.2.1
  rw [Spec.Ecdsa.Rfc6979.blocks]
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at h₂; have := P.wsizes; omega
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h₁
  have e₁ : (m + 1) * (8 * P.H.D) = 8 * (m * P.H.D) + 8 * P.H.D := by
    rw [Nat.succ_mul, Nat.mul_left_comm]
  have e₂ : (m + 1 + 1) * (8 * P.H.D) = 8 * (m * P.H.D) + 8 * P.H.D + 8 * P.H.D := by
    rw [Nat.succ_mul, e₁]
  have e₃ : (m + 1) * P.H.D = m * P.H.D + P.H.D := Nat.succ_mul _ _
  rw [e₃] at h₂
  have hl1 : Spec.Ecdsa.nBits P.R.E.C ≤ 8 * P.Q := hl.2.1
  have hl2 : 8 * P.Q < Spec.Ecdsa.nBits P.R.E.C + 8 := hl.1
  refine Nat.div_eq_of_lt_le ?_ ?_
  · rw [e₁]
    generalize m * P.H.D = X at *
    generalize Spec.Ecdsa.nBits P.R.E.C = N at *
    omega
  · rw [e₂]
    generalize m * P.H.D = X at *
    generalize Spec.Ecdsa.nBits P.R.E.C = N at *
    omega

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The frame's `T` and its length -/

/-- `T`'s length so far, and its bytes. -/
abbrev tlOf {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : BitVec 64 :=
  m.readW (L.B + BitVec.ofNat 64 224) 64
abbrev tOf {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (n : Nat) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 360) n

/-- `T`'s length, zero. -/
theorem candInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.candInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 224, 8⟩] t.mem t'.mem ∧ tlOf L t'.mem = 0 := by
  have w := hc.inFrW (d := 224) (n := 8) (by omega) (by omega)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  apply WP.of_runBlock
  simp only [Cfg.candInit, fTl, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits by decide, show (0 : Nat) < 4096 by decide, ite_true, addr, Size.bytes,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, Option.bind_some, State.store, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq, ite_false, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, RegUpd.rd_write, hc.sp, BitVec.add_zero, Offset.add_add, Nat.reduceAdd, w,
    write8, Option.some.injEq, exists_eq_left']
  refine ⟨by atriv, by atriv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    ?_⟩
  simp only [tlOf, Mem.readW_writeW_self64]
  decide

/-- `D` in `x8`, and `T`'s length in `x9`. -/
theorem candLd_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.candLd) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .x8 = BitVec.ofNat 64 P.I.hashLen ∧ u.gpr .x9 = tlOf L t.mem :=
  by
  rw [Cfg.candLd, ← List.singleton_append, WP.block_append_iff]
  exact WP.mono (ldDl_ok hL hc (d := .x8) (by decide)) fun u₁ h₁ =>
    WP.mono (ldSlot_ok hL h₁.ctx (d := .x9) (by decide) (o := fTl) (by decide) (v := tlOf L t.mem)
      (by rw [h₁.mem]; rfl)) fun u₂ h₂ => ⟨h₂.ctx, h₂.mem.trans h₁.mem, by rw [h₂.keep _ (by decide), h₁.val], h₂.val⟩

/-- `(a - q) >>> 63` is nonzero iff `a < q`, for both below `2^63`. -/
theorem lt_flag (a q : Nat) (ha : a < 2 ^ 63) (hq : q < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 q) >>> 63 != 0) = decide (a < q) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega)]
  by_cases h : a < q
  · rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    simp [h]
  · rw [show 2 ^ 64 - q + a = (a - q) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega)]
    simp [h]

/-- The tail of a step: `T`'s length `D` more, stored, and the flag. -/
theorem flagT_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h15 : u.gpr .x15 = L.B + BitVec.ofNat 64 16)
    {a D : Nat} (h9 : u.gpr .x9 = BitVec.ofNat 64 a) (h8 : u.gpr .x8 = BitVec.ofNat 64 D) (ha : a + D < 2 ^ 63) :
    WP isa (.block ([.add .x .x9 .x9 .x8, .str .x .x9 .x15 fTl, .movz .x .x11 (BitVec.ofNat 16 P.Q) 0,
      .sub .x .x12 .x9 .x11, .lsr .x .x12 .x12 63] : List Instr)) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 224, 8⟩] u.mem u'.mem ∧ tlOf L u'.mem = BitVec.ofNat 64 (a + D) ∧
      isa.eval (.nonzero .x .x12) u' = some (decide (a + D < P.Q)) := by
  have hQ := P.wsizes
  have w := hc.inFrW (d := 224) (n := 8) (by omega) (by omega)
  refine WP.mono (Ctx.of_keep (Q := fun u' => u'.mem.readW (L.B + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 (a + D) ∧
      isa.eval (.nonzero .x .x12) u' = some (decide (a + D < P.Q))) hL hc
    (ws := [⟨L.B + BitVec.ofNat 64 224, 8⟩]) ?_ (by rfl)
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega))
    fun u' ⟨hc', hf, hv, he⟩ => ⟨hc', hf, hv, he⟩
  apply WP.of_runBlock
  simp only [fTl, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    show 16 * 0 < Size.x.bits by decide, show 63 < Size.x.bits by decide, ite_true, addr, Size.bytes,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, Option.bind_some, State.store,
    RegUpd.gpr_write, reduceCtorEq, ite_false, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.rd_write,
    h15, h9, h8, Offset.add_add, Nat.reduceAdd, w, write8, Option.some.injEq, exists_eq_left']
  refine ⟨by atriv, by atriv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    ?_, ?_⟩
  · rw [Mem.readW_writeW_self64, BitVec.ofNat_add_ofNat]
  · refine (eval_nonzero _).trans ?_
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.ofNat_add_ofNat,
      show BitVec.setWidth 64 (BitVec.ofNat 16 P.Q) <<< 0 = BitVec.ofNat 64 P.Q from movz_val (by omega)]
    exact congrArg some (lt_flag _ _ ha (by omega))

/-! ## One step, and the loop -/

/-- What a candidate changes: `scratch`, the stack below the frame, `K`, `V`,
`T`'s length and `T`. -/
abbrev CW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region :=
  [L.SCR, ⟨L.B, 144⟩, ⟨L.B + BitVec.ofNat 64 224, 8⟩, ⟨L.B + BitVec.ofNat 64 360, 136⟩]

theorem kvw_cw : ∀ r ∈ KVW L, ∃ r' ∈ CW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp, sub_refl _⟩

/-- Before step `i + 1` of `T`, from `V₀` with the key `K`. -/
structure TInv (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (g : Reg → BitVec 64) (m₀ : Mem) (K V₀ : List Byte)
    (t : State) (i : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V₀).2
  tl : tlOf L u.mem = BitVec.ofNat 64 (i * P.H.D)
  tb : tOf L u.mem (i * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V₀).1
  lt : i * P.H.D < P.Q

/-- After the last step, the `n`th, of `T`. -/
structure TOut (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (g : Reg → BitVec 64) (m₀ : Mem) (K V₀ : List Byte)
    (t : State) (n : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K n V₀).2
  tb : tOf L u.mem (n * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K n V₀).1
  lo : (n - 1) * P.H.D < P.Q
  hi : P.Q ≤ n * P.H.D

/-- `V`'s 64 bytes to `T`'s `a`th byte, through `x13`. -/
theorem copyT_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a : Nat} (ha : a < 72)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 a) :
    WP isa (.block (([.addSp .x15 0, .addSp .x13 fT, .add .x .x13 .x13 .x9] : List Instr) ++
      Cfg.copyN 8 .x15 fV .x13 0)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x15 → u'.gpr r = u.gpr r) ∧ u'.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧
      Frame [⟨L.B + BitVec.ofNat 64 (360 + a), 64⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (360 + a)) 64 =
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 80) 64 := by
  have nB := hL.nB
  rw [WP.block_append_iff, show ([.addSp .x15 0, .addSp .x13 fT, .add .x .x13 .x13 .x9] : List Instr) =
    [.addSp .x15 0] ++ [.addSp .x13 fT] ++ [.add .x .x13 .x13 .x9] from rfl, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .x15) (by decide) (o := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .x13) (by decide) (o := fT) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (addR_ok hL h₂.ctx (d := .x13) (n := .x13) (m := .x9) (by decide)) fun u₃ h₃ => ?_
  have h13 : u₃.gpr .x13 = L.B + BitVec.ofNat 64 (360 + a) := by
    rw [h₃.val, h₂.val, h₂.keep _ (by decide), h₁.keep _ (by decide), h9, Offset.add_add]; rfl
  have h15 : u₃.gpr .x15 = L.B + BitVec.ofNat 64 16 := by
    rw [h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  have hc₃ := h₃.ctx
  refine WP.mono_syms (copyN_ok (src := .x15) (dst := .x13) (S := L.B + BitVec.ofNat 64 16)
    (D := L.B + BitVec.ofNat 64 (360 + a)) (so := fV) (d := 0) (K := 8) (by decide) (by decide)
    (by simp only [fV, Offset.add_add]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
    (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ 8 (Nat.le_refl _) u₃ h15 h13
    (fun j hj => by rw [Offset.add_add]; exact hc₃.inFr (by simp only [fV]; omega) (by simp only [fV]; omega))
    (fun j hj => by rw [Offset.add_add]; exact hc₃.inFrW (by omega) (by omega)))
    fun u₄ ⟨hrd, hwr, hsp, hg, hf, hb⟩ hsy => ?_
  rw [add_ofNat_zero] at hf hb
  rw [Offset.add_add] at hb
  have hm : u₃.mem = u.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  refine ⟨hc₃.keep hL hrd hwr hsp (fun r hr _ => hg r (ne_cs hr (by decide))) hf (hsy := hsy)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega)),
    fun r h11 h13' h15' => by rw [hg r h11, h₃.keep r h13', h₂.keep r h13', h₁.keep r h15'],
    by rw [hg _ (by decide), h15], hm ▸ hf, by rw [hb, hm]; rfl⟩

/-- Step `i + 1` of `T`: `V = HMAC_K(V)`, after `T`'s first `i D` bytes. -/
theorem step_ok (hL : L.Ok) (hk : CoreOk P L) {K V₀ : List Byte} {t : State} {i : Nat} {u : State}
    (hi : TInv P L g m₀ K V₀ t i u) :
    WP isa (cfgOf P).candStep u fun u' =>
      (isa.eval (.nonzero .x .x12) u' = some true ∧ TInv P L g m₀ K V₀ t (i + 1) u') ∨
      (isa.eval (.nonzero .x .x12) u' = some false ∧ TOut P L g m₀ K V₀ t (i + 1) u') := by
  have nB := hL.nB
  have hs := P.sizes
  have hw := P.wsizes
  have hlt := hi.lt
  refine WP.seq (WP.mono (hmacV_ok hL rfl hk.2 hi.ctx) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  have kT : ∀ {m m' : Mem}, Frame (KVW L) m m' → ∀ {o n : Nat}, 224 ≤ o → o + n ≤ 512 →
      Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) n :=
    fun hf o n h₁ h₂ => bytesAt_frame hf (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by omega)
  have htl₁ : tlOf L u₁.mem = BitVec.ofNat 64 (i * P.H.D) :=
    (hf₁.readW (r := ⟨L.B + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)).trans hi.tl
  have htb₁ : tOf L u₁.mem (i * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V₀).1 :=
    (kT hf₁ (by omega) (by omega)).trans hi.tb
  refine WP.seq (WP.mono (candLd_ok hL hc₁) fun u₂ ⟨hc₂, hm₂, h8, h9⟩ => ?_)
  rw [Cfg.candCopy, WP.block_append_iff]
  refine WP.mono (copyT_ok hL hc₂ (a := i * P.H.D) (by omega) (by rw [h9, htl₁]))
    fun u₃ ⟨hc₃, hg₃, h15, hf₃, hb₃⟩ => ?_
  refine WP.mono (flagT_ok (P := P) hL hc₃ h15 (a := i * P.H.D) (D := P.I.hashLen)
    (by rw [hg₃ _ (by decide) (by decide) (by decide), h9, htl₁])
    (by rw [hg₃ _ (by decide) (by decide) (by decide), h8]) (by show _ + P.H.D < _; omega))
    fun u₄ ⟨hc₄, hf₄, htl₄, he₄⟩ => ?_
  have e1 : (i + 1) * P.H.D = i * P.H.D + P.H.D := Nat.succ_mul _ _
  have hm₁ : u₂.mem = u₁.mem := hm₂
  -- The candidate's bytes so far.
  have hT₄ : tOf L u₄.mem ((i + 1) * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K (i + 1) V₀).1 := by
    have htb' : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 360) (i * P.H.D) =
        (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V₀).1 := htb₁
    rw [e1, tOf, Proof.Hmac.Common.bytesAt_add, Offset.add_add, genT_succ]
    dsimp only
    rw [bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      hm₁, htb', bytesAt_take _ _ (k := 64) (by omega), hb₃, ← bytesAt_take _ _ (by omega), hm₁]
    refine congrArg (_ ++ ·) ?_
    rw [← hi.v, ← hi.k]
    exact hv₁
  have hfr : Frame (CW L) t.mem u₄.mem := by
    refine ((hi.frame.trans (hf₁.sub fun r hr => kvw_cw r hr)).trans ((hm₁ ▸ hf₃).sub fun r hr => ?_)).trans
      (hf₄.sub fun r hr => ?_)
    all_goals simp only [List.mem_singleton] at hr; subst hr
    all_goals first
      | exact ⟨⟨L.B + BitVec.ofNat 64 360, 136⟩, by simp, Offset.sub (e := 360) (k := 136) _ (by omega) (by omega)⟩
      | exact ⟨⟨L.B + BitVec.ofNat 64 224, 8⟩, by simp, sub_refl _⟩
  have hK₄ : kOf P L u₄.mem = K := by
    show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 16) P.H.D = K
    rw [bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega), hm₁]
    exact hk₁.trans hi.k
  have hV₄ : vOf P L u₄.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K (i + 1) V₀).2 := by
    show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 80) P.H.D = _
    rw [bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega), hm₁]
    refine hv₁.trans ?_
    rw [hi.k, hi.v, genT_succ]
  have htl : tlOf L u₄.mem = BitVec.ofNat 64 ((i + 1) * P.H.D) := by rw [htl₄, e1]
  by_cases hgo : (i + 1) * P.H.D < P.Q
  · refine .inl ⟨by rw [he₄]; simp only [show i * P.H.D + P.I.hashLen < P.Q by
        show i * P.H.D + P.H.D < P.Q; omega, decide_true], hc₄, hfr, hK₄, hV₄, htl, hT₄, hgo⟩
  · refine .inr ⟨by rw [he₄]; simp only [show ¬ (i * P.H.D + P.I.hashLen < P.Q) by
        show ¬ (i * P.H.D + P.H.D < P.Q); omega, decide_false], hc₄, hfr, hK₄, hV₄, hT₄,
      by rw [Nat.add_sub_cancel]; exact hlt, by omega⟩

/-- The loop of steps: `T`, from `V₀`, until it has at least `Q` bytes. -/
theorem loopT_ok (hL : L.Ok) (hk : CoreOk P L) {K V₀ : List Byte} {t u : State}
    (hi : TInv P L g m₀ K V₀ t 0 u) :
    WP isa (.loop (cfgOf P).candStep (.nonzero .x .x12)) u fun u' => ∃ n, TOut P L g m₀ K V₀ t n u' := by
  have hD := P.sizes.2.2.2.2.2.2.1
  have hQ := P.wsizes
  refine WP.loop (M := isa) (fun n s => ∃ i, i + n = 4 ∧ TInv P L g m₀ K V₀ t i s) ?_ 4 u ⟨0, rfl, hi⟩
  rintro n s ⟨i, hn, hs⟩
  refine WP.mono (step_ok hL hk hs) fun s' h => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · have := hx.lt
    have h3 : i + 1 ≤ 3 := by
      by_contra h
      have : 4 * P.H.D ≤ (i + 1) * P.H.D := Nat.mul_le_mul_right _ (by omega)
      omega
    exact .inr ⟨he, n - 1, by omega, i + 1, by omega, hx⟩
  · exact .inl ⟨he, _, hx⟩

/-- `T`'s length, kept by HMAC's writes. -/
theorem tl_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : tlOf L m' = tlOf L m := by
  have nB := hL.nB
  exact hf.readW (r := ⟨L.B + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)

/-- `T`'s length, zero: before step 1 of `T`, from `V` with the key `K`. -/
theorem candInit_inv (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.candInit) t (TInv P L g m₀ (kOf P L t.mem) (vOf P L t.mem) t 0) := by
  have nB := hL.nB
  have hQ := P.wsizes
  have hD := P.sizes.2.2.2.2.2.2.1
  have hD' := P.sizes.2.2.2.2.2.2.2.1
  exact WP.mono (candInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, htl₀⟩ =>
    ⟨hc₀, hf₀.sub fun r hr => ⟨r, by simp at hr; subst hr; simp, sub_refl _⟩,
      bytesAt_frame (p := L.B + BitVec.ofNat 64 16) (n := P.H.D) hf₀ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      bytesAt_frame (p := L.B + BitVec.ofNat 64 80) (n := P.H.D) hf₀ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega),
      by rw [htl₀, Nat.zero_mul]; rfl, by simp [Spec.Ecdsa.Rfc6979.genT, tOf, Spec.Sha256.bytesAt], by simp; omega⟩

/-- The candidate: `T`, from `V = HMAC_K(V)` until it has `Q` bytes, and
`k`, its leftmost `Q` bytes (shifted right by `sh` bits if `wide`), at `T`,
whose number is `bits2int` of `T`. -/
theorem cand_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem)
        (Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D) (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem)
          (Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D) (vOf P L t.mem)).1 := by
  have nB := hL.nB
  have hQ := P.wsizes
  have hD := P.sizes.2.2.2.2.2.2.1
  have hD' := P.sizes.2.2.2.2.2.2.2.1
  have hl := P.R.nBits_len
  refine WP.seq (WP.mono (candInit_inv hL hc) fun u₀ hi => ?_)
  -- The candidate's number, from `T`'s leftmost `Q` bytes.
  have key : ∀ {n : Nat} {u : State}, TOut P L g m₀ (kOf P L t.mem) (vOf P L t.mem) t n u →
      Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = n ∧
      Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) n (vOf P L t.mem)).1 =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) >>> P.R.sh := fun {n u} ho => by
    refine ⟨blocks_eq P ho.lo ho.hi, ?_⟩
    have hlen := genT_length P (kOf P L t.mem) n (vOf P L t.mem)
    rw [Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
      (by rw [hlen]; exact ho.hi), ← ho.tb, tOf, ← bytesAt_take _ _ ho.hi, hl.2.2]
  cases hW : P.R.wide
  · have hw' : (cfgOf P).wide = false := hW
    simp only [hw', Bool.false_eq_true, ite_false]
    refine WP.mono (loopT_ok hL hk hi) fun u ⟨n, ho⟩ => ⟨ho.ctx, ho.frame, ho.k, ?_, ?_⟩
    · rw [(key ho).1]; exact ho.v
    · have hsh : P.R.sh = 0 := by
        have := (P.R.sizesA hW).2.2.1; rw [hl.2.2]; show 8 * P.R.E.C.len - _ = 0; omega
      rw [(key ho).1, (key ho).2, hsh, Nat.shiftRight_zero]
  · have hw' : (cfgOf P).wide = true := hW
    simp only [hw', ite_true]
    have hsh := sh7 hW
    refine WP.seq (WP.mono (loopT_ok hL hk hi) fun u ⟨n, ho⟩ => ?_)
    refine WP.mono (conv_ok (P := P) hL hW ho.ctx (o := fT) (s := (cfgOf P).sh) (by decide) (by decide)
      (by decide) (by show 1 ≤ P.R.sh; omega) (by show P.R.sh < 64; omega)) fun u' ⟨hc', hf', hb'⟩ => ?_
    simp only [fT, Nat.reduceAdd] at hf' hb'
    refine ⟨hc', ho.frame.trans (hf'.sub fun r hr => ?_), ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 360, 136⟩, by simp, Offset.sub (e := 360) (k := 136) _ (by omega) (by omega)⟩
    · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
      rw [bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega) (by omega)
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      exact ho.k
    · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 80) P.H.D = _
      rw [bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega) (by omega)
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), (key ho).1]
      exact ho.v
    · rw [(key ho).1, (key ho).2, hb', ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
        have := ofBytes_lt (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 360) P.Q)
        rwa [length_bytesAt] at this))]
      rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64
