module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.Hmac.Common
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on 32-bit ARM: the candidate

`T`, the concatenation of the `blocks` successive `V = HMAC_K(V)` of RFC
6979's step h.2 (`genT`), as many as make the scalars' `Q` bytes: the code
takes a step for each `i` below `steps` (enough for SHA-1's 20 bytes), if
`i D < Q` (`more_ok`): `V = HMAC_K(V)`, then `V`'s 64 bytes copied to `T`'s
place at `i D` (`keepV_ok`). After `i` of them `T`'s place begins with the
first `min(i, c)` `V`s, `c = ⌈Q / D⌉ = blocks` (`steps_ok`). The candidate is
`T`'s first `Q` bytes, shifted right by `sh` bits (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_movw wp_mul wp_cmp op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## RFC 6979's `T`, a `V` at a time -/

theorem genT_succ' (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (j : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (j + 1) V = ((Spec.Ecdsa.Rfc6979.genT H K j V).1 ++
      Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K j V).2, Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K j V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | j + 1, V => by
    rw [Spec.Ecdsa.Rfc6979.genT, genT_succ' H K j, Spec.Ecdsa.Rfc6979.genT]
    simp only [List.append_assoc]

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (j : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V).1.length = j * P.F.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | j + 1, V => by
    rw [genT_succ', List.length_append, genT_length P K j, P.mac_length]
    rw [Nat.succ_mul]

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.F.H.D - 1) / P.F.H.D

/-- `i D < Q` exactly for the `i` below `c`, of which there are at most `steps`. -/
theorem c_facts (P : RfcHash) :
    (∀ i, i * P.F.H.D < P.Q ↔ i < P.nV) ∧ P.nV ≤ (cfgOf P).steps ∧ 1 ≤ P.nV ∧ P.Q ≤ P.nV * P.F.H.D ∧
      P.nV * P.F.H.D < P.Q + P.F.H.D := by
  have hQ := P.wsizes
  have hs : (cfgOf P).steps = (P.Q + 19) / 20 := rfl
  rw [hs]
  rcases P.hDB with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
    simp only [RfcHash.nV, h] <;> refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- RFC 6979's `blocks`, for the curve's `n`. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := by
  have hn := P.R.nBits_len
  have hD := P.sizes
  obtain ⟨-, -, -, h₁, h₂⟩ := c_facts P
  rw [Spec.Ecdsa.Rfc6979.blocks]
  have hQ : P.Q = P.R.E.C.len := rfl
  have e₁ : P.nV * (8 * P.F.H.D) = 8 * (P.nV * P.F.H.D) := Nat.mul_left_comm _ _ _
  have e₂ : (P.nV + 1) * (8 * P.F.H.D) = 8 * (P.nV * P.F.H.D) + 8 * P.F.H.D := by rw [Nat.succ_mul, e₁]
  generalize P.nV * P.F.H.D = X at h₁ h₂ e₁ e₂
  refine Nat.div_eq_of_lt_le ?_ ?_
  · rw [e₁]; omega
  · rw [e₂]; omega

/-! ## The blocks of a step -/

theorem mul_val {D i : Nat} (_hD : D < 256) (hi : i < 256) :
    BitVec.ofNat 32 D * (BitVec.ofNat 16 i).setWidth 32 = BitVec.ofNat 32 (D * i) := by
  rw [movw_val (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  exact (Nat.mul_mod _ _ _).symm

/-- `i D` is small. -/
theorem iD_le (P : RfcHash) {i : Nat} (hi : i < 4) : P.F.H.D * i ≤ 192 := by
  have := P.sizes
  exact Nat.le_trans (Nat.mul_le_mul (show P.F.H.D ≤ 64 by omega) (show i ≤ 3 by omega)) (by decide)

/-- `r1 = i D`. -/
theorem iD_ok (hq : HOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat} (hi : i < 4) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u', Ctx L g m₀ u' → u'.mem = u.mem → u'.gpr .r1 = BitVec.ofNat 32 (P.F.H.D * i) →
      (∀ r, r ≠ .r0 → r ≠ .r1 → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (Cfg.iD i ++ is)) u Q := by
  have hD := P.sizes
  simp only [Cfg.iD, List.append_assoc]
  refine dOut_ok hq hc (d := .r1) (by decide) fun u₁ c₁ m₁ v₁ k₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun u₂ v₂ => wp_mul fun u₃ v₃ => ?_
  refine k u₃ ((c₁.upd v₂ (by decide)).upd v₃ (by decide)) (by rw [v₃.mem, v₂.mem, m₁]) ?_
    fun r h0 h1 => by rw [v₃.other _ h1, v₂.other _ h0, k₁ _ h1]
  rw [v₃.gpr, v₂.other _ (by decide), v₁, v₂.gpr, mul_val (by omega) (by omega)]

theorem Ctx.fupd {u u' : State} (hc : Ctx L g m₀ u) (h : VG.Proof.X25519.Arm.Fupd u u') : Ctx L g m₀ u' :=
  ⟨by rw [h.rd]; exact hc.rd, by rw [h.wr]; exact hc.wr, by rw [h.sp]; exact hc.sp, by rw [h.gpr]; exact hc.r4,
    by rw [h.gpr]; exact hc.r5, by rw [h.gpr]; exact hc.r6, by rw [h.gpr]; exact hc.r8, by rw [h.gpr]; exact hc.r11,
    fun p hp => by rw [h.mem]; exact hc.saved p hp, by rw [h.mem]; exact hc.frame⟩

/-- `Z` set iff `i D < Q`. -/
theorem more_ok (hq : HOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat} (hi : i < 4) :
    WP isa (.block ((cfgOf P).more i)) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → u'.gpr r = u.gpr r) ∧
      isa.eval .eq u' = some (decide (i * P.F.H.D < P.Q)) := by
  have hD := P.sizes
  have hQ := P.wsizes
  have hDi := iD_le P hi
  have hQe : encodable (BitVec.ofNat 32 P.Q) = true := by
    have : P.Q ≤ 66 := hQ.2.2.2.2.2.1
    revert this; generalize P.Q = q; revert q; decide
  simp only [Cfg.more, show (cfgOf P).len = P.Q from rfl]
  refine iD_ok hq hc hi fun u₁ c₁ m₁ v₁ k₁ => ?_
  refine wp_subsC (op2_imm hQe) fun u₂ v₂ c₂ => wp_movC (op2_imm (by decide)) fun u₃ v₃ c₃ => ?_
  refine wp_adc (op2_imm (by decide)) fun u₄ v₄ => wp_cmp (op2_imm (by decide)) fun u₅ v₅ z₅ => WP.block_nil ?_
  have c₄ := ((c₁.upd v₂ (by decide)).upd v₃ (by decide)).upd v₄ (by decide)
  refine ⟨c₄.fupd v₅, by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, m₁], fun r h0 h1 => ?_, ?_⟩
  · rw [v₅.gpr, v₄.other _ h1, v₃.other _ h1, v₂.other _ h1, k₁ r h0 h1]
  · show some u₅.z = _
    rw [z₅, v₄.gpr, v₃.gpr, c₃, c₂, v₁, toNat_ofNat_lt (by anums), toNat_ofNat_lt (by anums)]
    congr 1
    by_cases h : P.Q ≤ P.F.H.D * i
    · rw [decide_eq_true h, decide_eq_false (by rw [Nat.mul_comm]; omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by rw [Nat.mul_comm]; omega)]; rfl

theorem iD_mod (P : RfcHash) (i : Nat) : P.F.H.D * i % 4 = 0 := by
  have := P.sizes
  rw [Nat.mul_mod, show P.F.H.D % 4 = 0 by omega, Nat.zero_mul, Nat.zero_mod]

/-- `V`'s 64 bytes to `T`'s place at `i D`, for `i D < Q`. -/
theorem keepV_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat} (hi : i < 4)
    (hiQ : P.F.H.D * i < P.Q) :
    WP isa (.block (Cfg.keepV i)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (220 + P.F.H.D * i), 64⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (220 + P.F.H.D * i)) 64 =
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 88) 64 := by
  have hQ := P.wsizes
  have h4 := iD_mod P i
  have hDi : P.F.H.D * i ≤ 64 := by omega
  have hb := hL.B_fit
  have hfp := fp_fit hL
  simp only [Cfg.keepV, List.append_assoc]
  refine iD_ok hq hc hi fun u₁ c₁ m₁ v₁ k₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun u₂ v₂ => ?_
  have c₂ := c₁.upd v₂ (by decide)
  have h1 : u₂.gpr .r1 = L.fp + BitVec.ofNat 32 (P.F.H.D * i) := by
    rw [v₂.gpr, dpVal, v₁, c₁.r8, BitVec.add_comm]
  have eD : State.addr (L.fp + BitVec.ofNat 32 (P.F.H.D * i)) + BitVec.ofNat 64 fT =
      L.B + BitVec.ofNat 64 (220 + P.F.H.D * i) := by
    rw [hL.fpA (by omega), Offset.add_add, show 24 + P.F.H.D * i + fT = 220 + P.F.H.D * i by simp only [fT]; omega]
  have eS : State.addr L.fp + BitVec.ofNat 64 fV = L.B + BitVec.ofNat 64 88 := by rw [fpB hL]; rfl
  have hn : (L.fp + BitVec.ofNat 32 (P.F.H.D * i)).toNat = L.fp.toNat + P.F.H.D * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show P.F.H.D * i < 2 ^ 32 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine WP.mono (copyN_ok (src := .r8) (dst := .r1) (S := L.fp) (K := 16) (so := fV) (d := fT) (by decide) (by decide)
    (by rw [eS, eD]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
    (by simp only [fV]; omega) (by rw [hn]; simp only [fT]; omega) (by decide) (by decide) 16 (Nat.le_refl _) u₂
    c₂.r8 h1 (fun j hj => by rw [fpB hL]; exact c₂.inFr (by simp only [fV]; omega) (by simp only [fV]; omega))
    (fun j hj => by rw [← Offset.add_add, eD, Offset.add_add]; exact c₂.inFrW (by omega) (by omega)))
    fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hf₃, hb₃⟩ => ?_
  rw [eD] at hf₃ hb₃
  rw [eS] at hb₃
  refine ⟨c₂.keep hL hrd₃ hwr₃ hsp₃ (fun r hr => hg₃ r (by revert hr r; decide)) hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)),
    fun r h0 h1 => by rw [hg₃ r h0, v₂.other _ h1, k₁ r h0 h1], by rw [show u₂.mem = u.mem by rw [v₂.mem, m₁]] at hf₃; exact hf₃, ?_⟩
  rw [hb₃, v₂.mem, m₁]

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and `V`, and `T`. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 220, 132⟩]

theorem kvw_cw : ∀ r ∈ KVW L, ∃ r' ∈ CW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp, sub_refl _⟩

/-- After `i` steps of the candidate, from `t`: `K` as it was, `V` the last of the first
`min(i, c)` `V`s, which `T` begins with. -/
structure StepInv (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (i : Nat)
    (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame (CW L) t.mem u.mem
  k : kOf P L u.mem = kOf P L t.mem
  v : vOfP P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) (min i P.nV) (vOfP P L t.mem)).2
  tb : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 220) (min i P.nV * P.F.H.D) =
    (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) (min i P.nV) (vOfP P L t.mem)).1

/-- Step `i`, for `i D < Q`. -/
theorem step_ok (hL : L.Ok) (hq : HOk P L) {t u : State} {i : Nat} (hi : i < 4) (hiQ : i * P.F.H.D < P.Q)
    (h : StepInv P L g m₀ t i u) :
    WP isa ((cfgOf P).step i) u (StepInv P L g m₀ t (i + 1)) := by
  have hc := (c_facts P).1
  have hmi : min i P.nV = i := Nat.min_eq_left (by have := (hc i).mp hiQ; omega)
  have hmi' : min (i + 1) P.nV = i + 1 := Nat.min_eq_left (by have := (hc i).mp hiQ; omega)
  have hD := P.sizes
  have hb := hL.B_fit
  have hQ := P.wsizes
  have h4 := iD_mod P i
  have hiQ' : P.F.H.D * i < P.Q := by rw [Nat.mul_comm]; exact hiQ
  have hDi : P.F.H.D * i ≤ 64 := by omega
  have hiD : i * P.F.H.D = P.F.H.D * i := Nat.mul_comm _ _
  refine WP.seq (WP.mono (hmacV_ok hL hq h.ctx) fun u₁ ⟨hc₁, h9₁, hf₁, hk₁, hv₁⟩ => ?_)
  refine WP.mono (keepV_ok hL hq hc₁ hi hiQ') fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hv := h.v
  have htb := h.tb
  rw [hmi] at hv htb
  have hT : (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) i (vOfP P L t.mem)).1.length = i * P.F.H.D :=
    genT_length P _ _ _
  refine ⟨hc₂, by rw [hg₂ _ (by decide) (by decide), h9₁, h.r9], ?_, ?_, ?_, ?_⟩
  · refine (h.frame.trans (hf₁.sub kvw_cw)).trans (hf₂.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨L.B + BitVec.ofNat 64 220, 132⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
  · rw [show kOf P L u₂.mem = kOf P L u₁.mem from bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), hk₁, h.k]
  · rw [show vOfP P L u₂.mem = vOfP P L u₁.mem from bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega), hv₁, h.k, hv, hmi',
      genT_succ']
  · rw [hmi', genT_succ', Nat.succ_mul, Proof.Hmac.Common.bytesAt_add, Offset.add_add, hiD]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [← htb, hiD]
      refine (bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (Nat.le_refl _)) (by omega) (by omega)) (by omega)).trans
        (bytesAt_frame hf₁ (fun r hr => ?_) (by omega))
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)
    · rw [bytesAt_take _ _ (show P.F.H.D ≤ 64 by omega),
        hb₂, ← bytesAt_take _ _ (show P.F.H.D ≤ 64 by omega)]
      show vOfP P L u₁.mem = _
      rw [hv₁, h.k, hv]

/-- Past the last `V`: nothing changes. -/
theorem StepInv.skip {t u : State} {i : Nat} (h : StepInv P L g m₀ t i u) (hi : P.nV ≤ i) :
    StepInv P L g m₀ t (i + 1) u := by
  have e : min (i + 1) P.nV = min i P.nV := by omega
  exact ⟨h.ctx, h.r9, h.frame, h.k, e ▸ h.v, e ▸ h.tb⟩

/-- `more i` keeps the invariant. -/
theorem StepInv.more {t u u' : State} {i : Nat} (h : StepInv P L g m₀ t i u) (hc : Ctx L g m₀ u')
    (hm : u'.mem = u.mem) (h9 : u'.gpr .r9 = u.gpr .r9) : StepInv P L g m₀ t i u' :=
  ⟨hc, h9.trans h.r9, hm ▸ h.frame, hm ▸ h.k, hm ▸ h.v, hm ▸ h.tb⟩

/-- The steps from `i` on, `n` of them. -/
theorem moreSteps_ok (hL : L.Ok) (hq : HOk P L) {t : State} :
    ∀ n i, i + n ≤ 4 → ∀ u, StepInv P L g m₀ t i u →
      WP isa ((cfgOf P).moreSteps (List.range' i n)) u (StepInv P L g m₀ t (i + n))
  | 0, i, _, u, h => WP.block_nil h
  | n + 1, i, hn, u, h => by
    rw [List.range'_succ]
    refine WP.seq (WP.mono (more_ok hq h.ctx (i := i) (by omega)) fun u₁ ⟨c₁, m₁, g₁, e₁⟩ => ?_)
    have h₁ := h.more c₁ m₁ (g₁ _ (by decide) (by decide))
    refine WP.seq (WP.ite _ e₁ (fun hb => ?_) (fun hb => ?_))
    · refine WP.mono (step_ok hL hq (by omega) (of_decide_eq_true hb) h₁) fun u₂ h₂ => ?_
      rw [show i + (n + 1) = i + 1 + n by omega]
      exact moreSteps_ok hL hq n (i + 1) (by omega) u₂ h₂
    · have hi := of_decide_eq_false hb
      have : P.nV ≤ i := by have := ((c_facts P).1 i).not.mp hi; omega
      refine WP.block_nil ?_
      rw [show i + (n + 1) = i + 1 + n by omega]
      exact moreSteps_ok hL hq n (i + 1) (by omega) u₁ (h₁.skip this)

theorem range_drop_one (n : Nat) : (List.range n).drop 1 = List.range' 1 (n - 1) := by
  rw [List.range_eq_range', List.drop_range']

/-- The candidate: `V`, the last of the `c` successive `V`s, and `k`, whose
number is `bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧ Frame (CW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOfP P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOfP P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOfP P L t.mem)).1 := by
  obtain ⟨hcf, hst, h1, hQc, -⟩ := c_facts P
  have hQ := P.wsizes
  have hD := P.sizes
  have hfT : fT = 196 := rfl
  have hb := hL.B_fit
  have hs4 : (cfgOf P).steps ≤ 4 := by show (P.Q + 19) / 20 ≤ 4; omega
  have h0 : StepInv P L g m₀ t 0 t :=
    ⟨hc, rfl, Frame.refl _ _, rfl, by simp [Spec.Ecdsa.Rfc6979.genT],
      by simp [Spec.Ecdsa.Rfc6979.genT, Spec.Sha256.bytesAt]⟩
  refine WP.seq (WP.mono (step_ok hL hq (i := 0) (by omega) (by omega) h0) fun u₁ h₁ => ?_)
  rw [range_drop_one]
  refine WP.seq (WP.mono (moreSteps_ok hL hq ((cfgOf P).steps - 1) 1 (by omega) u₁ h₁) fun u₂ h₂ => ?_)
  have hmin : min (1 + ((cfgOf P).steps - 1)) P.nV = P.nV := Nat.min_eq_right (by omega)
  have hv := h₂.v
  have htb := h₂.tb
  rw [hmin] at hv htb
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOfP P L t.mem)
  -- `T`'s first `Q` bytes.
  have hk : Spec.Sha256.bytesAt u₂.mem (kAddr L) P.Q =
      (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOfP P L t.mem)).1.take P.Q := by
    rw [bytesAt_take _ _ hQc, ← htb]
  cases hw : P.R.wide
  · have hsh : (cfgOf P).sh = 0 := (sh_zero P).mpr hw
    have e8 : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hw).2.2.1
    simp only [hsh, ite_true]
    refine WP.block_nil ⟨h₂.ctx, h₂.r9, h₂.frame, h₂.k, hv, ?_⟩
    rw [hk, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeQ e8 (by rw [hTl]; exact hQc)]
  · have hsh : (cfgOf P).sh = 7 := by
      show P.R.sh = 7; have := P.R.nBits_len; have := P.R.sizesW hw; omega
    simp only [show (cfgOf P).sh ≠ 0 by omega, ite_false]
    rw [hsh]
    obtain ⟨-, hQ66, hnb⟩ := P.R.sizesW hw
    refine WP.mono (conv_ok hL hw h₂.ctx (o := fT) (s := 7) (by decide) (by decide) (by decide) (by decide))
      fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ⟨hc₃, by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        h₂.r9], ?_, ?_, ?_, ?_⟩
    · refine h₂.frame.trans (hf₃.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 220, 132⟩, by simp, Offset.sub _ (by decide) (by simp only [fT]; omega)⟩
    · rw [← h₂.k]
      refine bytesAt_frame hf₃ (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr (by omega) (by omega)
      · exact Offset.disjoint _ (.inl (by simp only [fT]; omega)) (by omega) (by simp only [fT]; omega)
    · rw [← hv]
      refine bytesAt_frame hf₃ (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr (by omega) (by omega)
      · exact Offset.disjoint _ (.inl (by simp only [fT]; omega)) (by omega) (by simp only [fT]; omega)
    · have hl := P.R.nBits_len
      have hQq : P.Q = P.R.E.C.len := rfl
      rw [show kAddr L = L.B + BitVec.ofNat 64 (24 + fT) from rfl, hb₃, ← show kAddr L = L.B + BitVec.ofNat 64 (24 + fT) from rfl,
        hk, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by omega) (by rw [hTl]; exact hQc),
        ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := ofBytes_lt ((Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOfP P L t.mem)).1.take P.Q)
          rwa [List.length_take, Nat.min_eq_left (by rw [hTl]; exact hQc)] at this)),
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by omega]

end VG.Proof.Ecdsa.Rfc6979.Arm
