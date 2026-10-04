import VerifiedGarbage.Proof.AesSiv.Arm.Env
import VerifiedGarbage.Proof.AesSiv.Key
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-!
# AES-SIV on ARMv7: `vg_aes_siv_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
`r4`–`r6`, `r11` and `lr` in the scratch buffer, expands `K1` into the
context with `vg_aes_expand_key`, derives its subkeys after the schedule
with `vg_cmac_aes_subkeys`, expands `K2` after them and restores the
registers (`init_wp`): the context is then that of the key
(`Proof.AesSiv.keyRepr_of`). The code between the calls is constant time
by the taint analysis, and the calls by their own proofs (`init_ct`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.CmacAes.Stream.Arm (EArgs EPost SArgs SPost ek_call sub_call ek_rel sub_rel blw8)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsr wp_mov wp_add)

/-- `vg_aes_siv_init(key = r0, key_len = r1, ctx = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ctx : Region := ⟨State.addr (s.gpr .r2), 512⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2560⟩
    let blw : Region := ⟨State.addr s.sp - 8, 8⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      blw.Disjoint key ∧ blw.Disjoint ctx ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 512 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 32 ∨ (s.gpr .r1).toNat = 48 ∨ (s.gpr .r1).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem (State.addr (s.gpr .r2))
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (Kp Ct S : BitVec 32) (KL : Nat) : Prop where
  r0 : s₀.gpr .r0 = Kp
  r1 : (s₀.gpr .r1).toNat = KL
  r2 : s₀.gpr .r2 = Ct
  r3 : s₀.gpr .r3 = S
  rd : s₀.rd = [⟨State.addr Kp, KL⟩]
  wr : s₀.wr = [⟨State.addr Ct, 512⟩, ⟨State.addr S, 2560⟩]
  k_c : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr Ct, 512⟩
  k_s : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 2560⟩
  c_s : (⟨State.addr Ct, 512⟩ : Region).Disjoint ⟨State.addr S, 2560⟩
  b_k : (blw8 s₀).Disjoint ⟨State.addr Kp, KL⟩
  b_c : (blw8 s₀).Disjoint ⟨State.addr Ct, 512⟩
  b_s : (blw8 s₀).Disjoint ⟨State.addr S, 2560⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fC : Ct.toNat + 512 ≤ 2 ^ 32
  fS : S.toNat + 2560 ≤ 2 ^ 32
  sp : 8 ≤ s₀.sp.toNat
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) :
    IPre s₀ (s₀.gpr .r0) (s₀.gpr .r2) (s₀.gpr .r3) (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n⟩

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 32 KL >>> 1 = BitVec.ofNat 32 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 32 (KL / 2) >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem initSaved_slots : Spill.Slots 2176 2196 initSaved := by decide

theorem initPost_eq : initPost =
    (([(.r4, 2176), (.r5, 2180), (.r6, 2184), (.lr, 2192)] : List (Reg × Nat)) ++
      ([(.r11, 2188)] : List (Reg × Nat))).map
      (fun p => Instr.ldr p.1 .r11 p.2) := rfl

section
variable {s₀ : State} {Kp Ct S : BitVec 32} {KL : Nat}

theorem IPre.rounds (hp : IPre s₀ Kp Ct S KL) : KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half (hp : IPre s₀ Kp Ct S KL) : KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.aC (hp : IPre s₀ Kp Ct S KL) {d : Nat} (hd : d < 512) :
    State.addr (Ct + BitVec.ofNat 32 d) = State.addr Ct + BitVec.ofNat 64 d := addr_add (by have := hp.fC; omega)

theorem IPre.aK (hp : IPre s₀ Kp Ct S KL) :
    State.addr (Kp + BitVec.ofNat 32 (KL / 2)) = State.addr Kp + BitVec.ofNat 64 (KL / 2) :=
  addr_add (by have := hp.fK; have := hp.klen; omega)

theorem IPre.sC (_hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 512) :
    Region.Sub ⟨State.addr Ct + BitVec.ofNat 64 d, n⟩ ⟨State.addr Ct, 512⟩ := Offset.sub_base _ h

theorem IPre.sS (_hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 2560) :
    Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, n⟩ ⟨State.addr S, 2560⟩ := Offset.sub_base _ h

theorem IPre.sK (_hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ KL) :
    Region.Sub ⟨State.addr Kp + BitVec.ofNat 64 d, n⟩ ⟨State.addr Kp, KL⟩ := Offset.sub_base _ h

/-- A region of the context, writable. -/
theorem IPre.wC (hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 512) :
    ∃ r' ∈ s₀.wr, ∃ off, State.addr Ct + BitVec.ofNat 64 d = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨⟨State.addr Ct, 512⟩, by rw [hp.wr]; simp, d, rfl, h⟩

/-- A region of the scratch buffer, writable. -/
theorem IPre.wS (hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 2560) :
    ∃ r' ∈ s₀.wr, ∃ off, State.addr S + BitVec.ofNat 64 d = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨⟨State.addr S, 2560⟩, by rw [hp.wr]; simp, d, rfl, h⟩

/-- The arguments of a call of `vg_aes_expand_key`: half the key from byte
`a`, into the context from byte `c`. -/
theorem IPre.eargs (hp : IPre s₀ Kp Ct S KL) {s : State} {a c : Nat} (ha : a = 0 ∨ a = KL / 2)
    (hc : c = 0 ∨ c = 272) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h0 : s.gpr .r0 = Kp + BitVec.ofNat 32 a) (h1 : s.gpr .r1 = BitVec.ofNat 32 (KL / 2))
    (h2 : s.gpr .r2 = Ct + BitVec.ofNat 32 c) (h3 : s.gpr .r3 = S) :
    EArgs s (Kp + BitVec.ofNat 32 a) (Ct + BitVec.ofNat 32 c) S (KL / 2) := by
  have hK := hp.fK
  have hC := hp.fC
  have hl := hp.klen
  have eK : State.addr (Kp + BitVec.ofNat 32 a) = State.addr Kp + BitVec.ofNat 64 a := by
    rcases ha with rfl | rfl
    · simp
    · exact hp.aK
  have eC : State.addr (Ct + BitVec.ofNat 32 c) = State.addr Ct + BitVec.ofNat 64 c := hp.aC (by omega)
  have sK : Region.Sub ⟨State.addr (Kp + BitVec.ofNat 32 a), KL / 2⟩ ⟨State.addr Kp, KL⟩ := by
    rw [eK]; exact hp.sK (by omega)
  have sC : Region.Sub ⟨State.addr (Ct + BitVec.ofNat 32 c), 240⟩ ⟨State.addr Ct, 512⟩ := by
    rw [eC]; exact hp.sC (by omega)
  exact
    { r0 := h0, r1 := h1, r2 := h2, r3 := h3
      klen := hp.half
      kw := (hp.k_c.sub_left sK).sub_right sC
      ks := (hp.k_s.sub_left sK).sub_right (Region.sub_prefix (by decide))
      ws := (hp.c_s.sub_left sC).sub_right (Region.sub_prefix (by decide))
      fK := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rcases ha with rfl | rfl <;> simp <;> omega
      fW := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rcases hc with rfl | rfl <;> simp <;> omega
      fS := by have := hp.fS; omega
      reads := by
        rw [hrd, hwr, hp.rd]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr Kp, KL⟩, by simp, a, eK, by show a + KL / 2 ≤ KL; rcases ha with rfl | rfl <;> omega⟩
      writes := by
        rw [hwr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', hr', off, e, l⟩ := hp.wC (d := c) (n := 240) (by omega)
          exact ⟨r', hr', off, by rw [eC]; exact e, l⟩
        · obtain ⟨r', hr', off, e, l⟩ := hp.wS (d := 0) (n := 512) (by decide)
          exact ⟨r', hr', off, by rw [← e]; simp, l⟩ }

/-- The arguments of the call of `vg_cmac_aes_subkeys`. -/
theorem IPre.sargs (hp : IPre s₀ Kp Ct S KL) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.sp = s₀.sp) (h0 : s.gpr .r0 = Ct) (h1 : s.gpr .r1 = BitVec.ofNat 32 (KL / 8 + 6))
    (h2 : s.gpr .r2 = Ct + BitVec.ofNat 32 240) (h3 : s.gpr .r3 = S) :
    SArgs s Ct (Ct + BitVec.ofNat 32 240) S (KL / 8 + 6) := by
  have hC := hp.fC
  have eC : State.addr (Ct + BitVec.ofNat 32 240) = State.addr Ct + BitVec.ofNat 64 240 := hp.aC (by decide)
  have sC : Region.Sub ⟨State.addr (Ct + BitVec.ofNat 32 240), 32⟩ ⟨State.addr Ct, 512⟩ := by
    rw [eC]; exact hp.sC (by decide)
  have bl : blw8 s = blw8 s₀ := by rw [blw8, blw8, hsp]
  exact
    { r0 := h0, r1 := h1, r2 := h2, r3 := h3
      rounds := hp.rounds
      hsp := by rw [hsp]; exact hp.sp
      wk := by rw [eC]; exact Offset.base_disjoint _ (by decide) (by omega)
      ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      ks := (hp.c_s.sub_left sC).sub_right (Region.sub_prefix (by decide))
      bw := by rw [bl]; exact hp.b_c.sub_right (Region.sub_prefix (by decide))
      bk := by rw [bl]; exact hp.b_c.sub_right sC
      bs := by rw [bl]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
      fW := by omega
      fK := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
      fS := by have := hp.fS; omega
      reads := by
        rw [hrd, hwr, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr Ct, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      writes := by
        rw [hwr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', hr', off, e, l⟩ := hp.wC (d := 240) (n := 32) (by decide)
          exact ⟨r', hr', off, by rw [eC]; exact e, l⟩
        · obtain ⟨r', hr', off, e, l⟩ := hp.wS (d := 0) (n := 2176) (by decide)
          exact ⟨r', hr', off, by rw [← e]; simp, l⟩ }

end

/-! ## The code between the calls -/

/-- What every piece of `init` keeps: the key, the half length, the context
and the scratch buffer in `r4`, `r5`, `r6` and `r11`, the other callee-saved
registers (but `lr`), the stack pointer and the regions. -/
structure IKeep (s₀ : State) (Kp Ct S : BitVec 32) (KL : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = Kp
  r5 : s.gpr .r5 = BitVec.ofNat 32 (KL / 2)
  r6 : s.gpr .r6 = Ct
  r11 : s.gpr .r11 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r11 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- After a call, which keeps the callee-saved registers. -/
theorem IKeep.call {s₀ s s' : State} {Kp Ct S : BitVec 32} {KL : Nat} (h : IKeep s₀ Kp Ct S KL s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : IKeep s₀ Kp Ct S KL s' :=
  ⟨by rw [hg _ (by simp [preserved]) (by decide), h.r4], by rw [hg _ (by simp [preserved]) (by decide), h.r5],
    by rw [hg _ (by simp [preserved]) (by decide), h.r6], by rw [hg _ (by simp [preserved]) (by decide), h.r11],
    fun r hr a b c d e => by rw [hg r hr e, h.keep r hr a b c d e], by rw [hsp, h.sp], by rw [hrd, h.rd],
    by rw [hwr, h.wr]⟩

/-- The memory after saving the registers. -/
abbrev iMem (s₀ : State) (S : BitVec 32) : Mem := Spill.saveMem s₀.mem (State.addr S) s₀.gpr initSaved

theorem initPre_wp {s₀ : State} {Kp Ct S : BitVec 32} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    WP isa (.block initPre) s₀ fun s => IKeep s₀ Kp Ct S KL s ∧ s.mem = iMem s₀ S ∧
      EArgs s Kp Ct S (KL / 2) := by
  have hS := hp.fS
  refine Spill.save_slots_ok initSaved_slots (by rw [hp.r3]; omega) (fun d h₁ h₂ => ?_) ?_
  · rw [hp.r3, hp.wr]
    exact ⟨⟨State.addr S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    WP.block_nil ?_
  have hKL : s₀.gpr .r1 = BitVec.ofNat 32 KL :=
    BitVec.eq_of_toNat_eq (by
      rw [hp.r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hp.klen with h | h | h <;> omega)])
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have r5 : s₅.gpr .r5 = BitVec.ofNat 32 (KL / 2) := by
    simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]
    rw [hKL]; exact half_bv hp.klen
  refine ⟨⟨?_, r5, ?_, ?_, fun r hr a b c d e => ?_, sp₅, rd₅, wr₅⟩,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hp.r3], ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, hp.r0]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, hp.r2]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, hp.r3]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  · have e := hp.eargs (s := s₅) (a := 0) (c := 0) (.inl rfl) (.inl rfl) rd₅ wr₅
      (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, hp.r0, BitVec.add_zero])
      (by rw [u₅.gpr, ← u₅.other _ (by decide), r5])
      (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, hp.r2, BitVec.add_zero])
      (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, hp.r3])
    simpa only [BitVec.add_zero] using e

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : BitVec 32} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IKeep s₀ Kp Ct S KL s) :
    WP isa (.block initMid₁) s fun s' => IKeep s₀ Kp Ct S KL s' ∧ s'.mem = s.mem ∧
      SArgs s' Ct (Ct + BitVec.ofNat 32 240) S (KL / 8 + 6) := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, sp₅, rd₅, wr₅⟩,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], hp.sargs rd₅ wr₅ sp₅ ?_ ?_ ?_ ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r4]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r5]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other, h.r11]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | (simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
       exact h.keep _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h.r6]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.gpr, u₁.other, h.r5]
    exact rounds_bv hp.klen
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, h.r11]

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : BitVec 32} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IKeep s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' => IKeep s₀ Kp Ct S KL s' ∧ s'.mem = s.mem ∧
      EArgs s' (Kp + BitVec.ofNat 32 (KL / 2)) (Ct + BitVec.ofNat 32 272) S (KL / 2) := by
  refine wp_add (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₄ : s₄.sp = s₀.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr a b c d e => ?_, sp₄, rd₄, wr₄⟩,
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    hp.eargs (.inr rfl) (.inr rfl) rd₄ wr₄ ?_ ?_ ?_ ?_⟩
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r4]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r5]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, h.r11]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | exact absurd rfl e
    | (simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other]
       exact h.keep _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.gpr, h.r4, h.r5]
  · simp (disch := decide) only [u₄.other, u₃.other, u₂.gpr, u₁.other, h.r5]
  · simp (disch := decide) only [u₄.other, u₃.gpr, u₂.other, u₁.other, h.r6]
  · simp (disch := decide) only [u₄.gpr, u₃.other, u₂.other, u₁.other, h.r11]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r0 = Kp at hp
  generalize s₀.gpr .r2 = Ct at hp
  generalize s₀.gpr .r3 = S at hp
  generalize (s₀.gpr .r1).toNat = KL at hp
  have hS := hp.fS
  have hC := hp.fC
  have hK := hp.fK
  have hl := hp.klen
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ ⟨k₁, m₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (ek_call e₁) fun s₂ h₂ => ?_)
  have k₂ := k₁.call h₂.saved h₂.sp h₂.rd h₂.wr
  refine WP.seq (WP.mono (initMid₁_wp hp k₂) fun s₃ ⟨k₃, m₃, a₃⟩ => ?_)
  refine WP.seq (WP.mono (sub_call a₃) fun s₄ h₄ => ?_)
  have k₄ := k₃.call h₄.saved h₄.sp h₄.rd h₄.wr
  refine WP.seq (WP.mono (initMid₂_wp hp k₄) fun s₅ ⟨k₅, m₅, a₅⟩ => ?_)
  refine WP.seq (WP.mono (ek_call a₅) fun s₆ h₆ => ?_)
  have k₆ := k₅.call h₆.saved h₆.sp h₆.rd h₆.wr
  have e240 := hp.aC (d := 240) (by decide)
  have e272 := hp.aC (d := 272) (by decide)
  have bl₃ : blw8 s₃ = blw8 s₀ := by rw [blw8, blw8, k₃.sp]
  -- The memory, call by call.
  have f₁ : Frame [⟨State.addr S + BitVec.ofNat 64 2176, 20⟩] s₀.mem s₁.mem := by
    rw [m₁]; exact Spill.saveMem_frame_slots initSaved_slots _ _ _
  have f₂ : Frame [⟨State.addr Ct, 240⟩, ⟨State.addr S, 512⟩] s₁.mem s₂.mem := by
    have := h₂.frame; simpa using this
  have f₄ : Frame [⟨State.addr Ct + BitVec.ofNat 64 240, 32⟩, ⟨State.addr S, 2176⟩, blw8 s₀] s₂.mem s₄.mem := by
    have := h₄.frame; rw [e240, bl₃, m₃] at this; exact this
  have f₆ : Frame [⟨State.addr Ct + BitVec.ofNat 64 272, 240⟩, ⟨State.addr S, 512⟩] s₄.mem s₆.mem := by
    have := h₆.frame; rw [e272, m₅] at this; exact this
  -- The saved registers.
  have dSv : ∀ r ∈ [(⟨State.addr Ct, 240⟩ : Region), ⟨State.addr S, 512⟩,
      ⟨State.addr Ct + BitVec.ofNat 64 240, 32⟩, ⟨State.addr S, 2176⟩, blw8 s₀,
      ⟨State.addr Ct + BitVec.ofNat 64 272, 240⟩],
      (⟨State.addr S + BitVec.ofNat 64 2176, 2196 - 2176⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 2176, 2196 - 2176⟩ ⟨State.addr S, 2560⟩ :=
      hp.sS (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact (hp.b_s.sub_right sub).symm
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved s₁.mem (State.addr S) s₀.gpr initSaved := by
    rw [m₁]; exact Spill.saveMem_saved _ _ _ _ initSaved_slots
  have sv₆ : Spill.Saved s₆.mem (State.addr S) s₀.gpr initSaved :=
    ((sv₁.frame initSaved_slots f₂ fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)).frame
      initSaved_slots f₄ fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      initSaved_slots f₆ fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  rw [initPost_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_slots_ok (lo := 2176) (hi := 2196) (by decide) (by decide) (g := s₀.gpr)
    (by rw [k₆.r11]; omega)
    (fun d h₁ h₂ => by
      rw [k₆.r11, k₆.rd, k₆.wr, hp.rd, hp.wr]
      exact ⟨⟨State.addr S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [k₆.r11]; exact fun p hp' => sv₆ p hp')
    fun s₇ hl₇ ho₇ m₇ _ _ sp₇ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [sp₇, k₆.sp]⟩, ?_⟩
  · have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl₇ (.r4, 2176) (by decide)
    · exact hl₇ (.r5, 2180) (by decide)
    · exact hl₇ (.r6, 2184) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ho₇ _ (by decide)]; exact k₆.keep _ hr' (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hl₇ (.r11, 2188) (by decide)
    · exact hl₇ (.lr, 2192) (by decide)
  · show Spec.Siv.KeyRepr s₇.mem (State.addr (s₀.gpr .r2))
      (Spec.Aes.bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
    rw [hp.r2, hp.r0, hp.r1, m₇]
    -- The key, outside everything the code writes.
    have dK {a n : Nat} (ha : a + n ≤ KL) : ∀ r ∈ [(⟨State.addr Ct, 240⟩ : Region), ⟨State.addr S, 512⟩,
        ⟨State.addr Ct + BitVec.ofNat 64 240, 32⟩, ⟨State.addr S, 2176⟩, blw8 s₀,
        ⟨State.addr S + BitVec.ofNat 64 2176, 20⟩],
        (⟨State.addr Kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
      have sub := hp.sK ha
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_c.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_c.sub_left sub).sub_right (hp.sC (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.b_k.sub_right sub).symm
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
    have key {a : Nat} (ha : a + KL / 2 ≤ KL) :
        Spec.Aes.bytesAt s₅.mem (State.addr Kp + BitVec.ofNat 64 a) (KL / 2) =
          Spec.Aes.bytesAt s₀.mem (State.addr Kp + BitVec.ofNat 64 a) (KL / 2) := by
      rw [m₅, Proof.Cmac.bytesAt_frame f₄ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega),
        Proof.Cmac.bytesAt_frame f₂ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
          (by omega),
        Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK ha r (by simp only [List.mem_singleton] at hr; subst hr; simp))
          (by omega)]
    have key₁ : Spec.Aes.bytesAt s₁.mem (State.addr Kp) (KL / 2) = Spec.Aes.bytesAt s₀.mem (State.addr Kp) (KL / 2) := by
      have := Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK (a := 0) (n := KL / 2) (by omega) r
        (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)
      rwa [BitVec.add_zero] at this
    have hRb : 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
    have sch : Spec.Aes.bytesAt s₂.mem (State.addr Ct) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (State.addr Kp) (KL / 2)) := by
      have := h₂.out; rw [key₁] at this; exact this
    refine Proof.AesSiv.keyRepr_of hp.klen ?_ ?_ ?_
    · rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.base_disjoint _ (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint _ (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
          · exact (hp.b_c.sub_right (Region.sub_prefix (by omega))).symm)
          (by omega), sch]
    · rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact (hp.c_s.sub_left (hp.sC (by decide))).sub_right (Region.sub_prefix (by decide))) (by decide),
        ← e240, h₄.out, m₃,
        show 16 * (KL / 8 + 6 + 1) = 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) by
          simp only [Spec.Aes.rounds]; omega, sch]
    · have := h₆.out
      rw [e272, hp.aK, key (a := KL / 2) (by omega)] at this
      exact this

end VG.Proof.AesSiv.Arm
