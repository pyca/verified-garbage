import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.AesSiv.Key
import VerifiedGarbage.Impl.AesSiv.AArch64

/-!
# AES-SIV on AArch64: `vg_aes_siv_init`

The code saves `x19`–`x22` and `x30` in the working space, expands `K1` into
the context, derives its subkeys after the schedule, expands `K2` after them
and restores the registers: the context is then that of the key
(`Spec.Siv.KeyRepr`, `keyRepr_of`). The code between the calls is constant
time by the taint analysis, and the calls by their own proofs (`ek_rel`,
`sub_rel`). A call (`bl`) stores nothing in memory, so no stack is used.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (EArgs EPost SArgs SPost ek_call sub_call ek_rel sub_rel toNat_ofNat
  toNat_add_lt ofNat_toNat_eq)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- `vg_aes_siv_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ctx : Region := ⟨s.gpr .x2, 512⟩
    let scr : Region := ⟨s.gpr .x3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 32 ∨ (s.gpr .x1).toNat = 48 ∨ (s.gpr .x1).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem (s.gpr .x2) (Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`
and the working space `S`. -/
structure IPre (s₀ : State) (Kp Ct S : Addr) (KL : Nat) : Prop where
  x0 : s₀.gpr .x0 = Kp
  x1 : (s₀.gpr .x1).toNat = KL
  x2 : s₀.gpr .x2 = Ct
  x3 : s₀.gpr .x3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨Ct, 512⟩, ⟨S, 2560⟩]
  k_c : (⟨Kp, KL⟩ : Region).Disjoint ⟨Ct, 512⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  c_s : (⟨Ct, 512⟩ : Region).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wC : Ct.toNat + 512 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64

theorem IPre.of {s₀ : State} (h : initAArch64.pre s₀) :
    IPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 1 = BitVec.ofNat 64 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 (KL / 2) >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

section
variable {s₀ : State} {Kp Ct S : Addr} {KL : Nat}

theorem IPre.rounds (hp : IPre s₀ Kp Ct S KL) : KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half (hp : IPre s₀ Kp Ct S KL) : KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.sS (_hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 2560) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2560⟩ :=
  Offset.sub_base S (by omega)

theorem IPre.sC (_hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 512) :
    Region.Sub ⟨Ct + BitVec.ofNat 64 d, n⟩ ⟨Ct, 512⟩ :=
  Offset.sub_base Ct (by omega)

theorem IPre.sK (_hp : IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ KL) :
    Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ :=
  Offset.sub_base Kp (by omega)

/-- The arguments of a call of `vg_aes_expand_key_scratch` on half the key, from
offset `a` (0 or `KL / 2`), into the context at offset `c`. -/
theorem IPre.eargs (hp : IPre s₀ Kp Ct S KL) {s : State} {a c : Nat}
    (ha : a + KL / 2 ≤ KL) (hc : c + 240 ≤ 512)
    (x0 : s.gpr .x0 = Kp + BitVec.ofNat 64 a) (x1 : s.gpr .x1 = BitVec.ofNat 64 (KL / 2))
    (x2 : s.gpr .x2 = Ct + BitVec.ofNat 64 c) (x3 : s.gpr .x3 = S)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    EArgs s (Kp + BitVec.ofNat 64 a) (Ct + BitVec.ofNat 64 c) S (KL / 2) where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  klen := hp.half
  kw := (hp.k_c.sub_left (hp.sK ha)).sub_right (hp.sC hc)
  ks := (hp.k_s.sub_left (hp.sK ha)).sub_right (Region.sub_prefix (by decide))
  ws := (hp.c_s.sub_left (hp.sC hc)).sub_right (Region.sub_prefix (by decide))
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨Kp, KL⟩, by simp, a, rfl, by simp; omega⟩
    · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega⟩
    · exact ⟨⟨S, 2560⟩, by simp, 0, by simp, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega⟩
    · exact ⟨⟨S, 2560⟩, by simp, 0, by simp, by simp⟩

/-- The arguments of the call of `vg_cmac_aes_subkeys`. -/
theorem IPre.sargs (hp : IPre s₀ Kp Ct S KL) {s : State}
    (x0 : s.gpr .x0 = Ct) (x1 : s.gpr .x1 = BitVec.ofNat 64 (KL / 8 + 6))
    (x2 : s.gpr .x2 = Ct + BitVec.ofNat 64 240) (x3 : s.gpr .x3 = S)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  rounds := hp.rounds
  wk := Offset.base_disjoint Ct (by decide) (by have := hp.wC; omega)
  ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  ks := (hp.c_s.sub_left (hp.sC (by decide))).sub_right (Region.sub_prefix (by decide))
  wrapK := by rw [toNat_add_lt Ct hp.wC (by decide)]; have := hp.wC; omega
  wrapS := by have := hp.wS; omega
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 0, by simp, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 0, by simp, by simp⟩

end

/-! ## The saved registers -/

theorem initSaved_fits : Spill.Fits initSaved := by decide

theorem initSaved_bound : ∀ p ∈ initSaved, 2176 ≤ p.2 ∧ p.2 + 8 ≤ 2216 := by decide

theorem initRestored_sub : ∀ p ∈ initRestored, p ∈ initSaved := by decide

theorem initRestored_restorable : Spill.Restorable .x22 initRestored := by decide

theorem initRestored_fst : ∀ r ∈ preserved, r ∈ initRestored.map Prod.fst ∨ r ∉ initSaved.map Prod.fst := by
  decide

/-! ## Before the first call -/

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp Ct S (KL / 2)
  x19 : s.gpr .x19 = Kp
  x20 : s.gpr .x20 = BitVec.ofNat 64 (KL / 2)
  x21 : s.gpr .x21 = Ct
  x22 : s.gpr .x22 = S
  other : ∀ r ∈ preserved, r ∉ initSaved.map Prod.fst → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ Kp Ct S KL) := by
  have hKL : s₀.gpr .x1 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.x1
  have hw := hp.wS
  rw [show initPre = Spill.saveCode .x3 initSaved ++
    [mov .x19 .x0, .lsr .x .x20 .x1 1, mov .x21 .x2, mov .x22 .x3, mov .x1 .x20] from rfl]
  refine Spill.save_ok (fun p hp' => (initSaved_fits.1 p hp')) (fun p hp' => by
    have := initSaved_bound p hp'
    rw [hp.x3, hp.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) ?_
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write, hp.x0], by simp [gpr_write, hKL, half_bv hp.klen], by simp [gpr_write, hp.x2],
    by simp [gpr_write, hp.x3], fun r hr hn => ?_, rfl, by simp [mem_write, hp.x3], rfl, rfl⟩
  · rw [← k0 Kp, ← k0 Ct]
    exact hp.eargs (a := 0) (c := 0) (by omega) (by decide) (by simp [gpr_write, hp.x0])
      (by simp [gpr_write, hKL, half_bv hp.klen]) (by simp [gpr_write, hp.x2]) (by simp [gpr_write, hp.x3])
      rfl rfl
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [initSaved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]

/-! ## Between the calls -/

theorem initMid₁_ok {s : State} {Ct S : Addr} {H : Nat} (h20 : s.gpr .x20 = BitVec.ofNat 64 H)
    (h21 : s.gpr .x21 = Ct) (h22 : s.gpr .x22 = S) :
    ∃ s', runBlock isa initMid₁ s = some s' ∧ s'.gpr .x0 = Ct ∧
      s'.gpr .x1 = BitVec.ofNat 64 H >>> 2 + BitVec.ofNat 64 6 ∧ s'.gpr .x2 = Ct + BitVec.ofNat 64 240 ∧
      s'.gpr .x3 = S ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, initMid₁, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, h21], by simp [gpr_write, h20], by simp [gpr_write, h21],
    by simp [gpr_write, h22], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem initMid₂_ok {s : State} {Kp Ct S : Addr} {H : Nat} (h19 : s.gpr .x19 = Kp)
    (h20 : s.gpr .x20 = BitVec.ofNat 64 H) (h21 : s.gpr .x21 = Ct) (h22 : s.gpr .x22 = S) :
    ∃ s', runBlock isa initMid₂ s = some s' ∧ s'.gpr .x0 = Kp + BitVec.ofNat 64 H ∧
      s'.gpr .x1 = BitVec.ofNat 64 H ∧ s'.gpr .x2 = Ct + BitVec.ofNat 64 272 ∧ s'.gpr .x3 = S ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, initMid₂, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, h19, h20], by simp [gpr_write, h20], by simp [gpr_write, h21],
    by simp [gpr_write, h22], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- What each call leaves for the code after it: the registers that hold
the arguments of the next one. -/
structure IAfter (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = Kp
  x20 : s.gpr .x20 = BitVec.ofNat 64 (KL / 2)
  x21 : s.gpr .x21 = Ct
  x22 : s.gpr .x22 = S
  other : ∀ r ∈ preserved, r ∉ initSaved.map Prod.fst → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem not_x30 {r : Reg} (h : r ∉ initSaved.map Prod.fst) : r ≠ .x30 := by rintro rfl; exact h (by decide)

theorem IAfter.keep {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : IAfter s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : IAfter s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide) (by decide), h.x19], by rw [hs _ (by decide) (by decide), h.x20],
    by rw [hs _ (by decide) (by decide), h.x21], by rw [hs _ (by decide) (by decide), h.x22],
    fun r hr hn => by rw [hs r hr (not_x30 hn), h.other r hr hn],
    by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.after {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : IMid₁ s₀ Kp Ct S KL s) :
    IAfter s₀ Kp Ct S KL s :=
  ⟨h.x19, h.x20, h.x21, h.x22, h.other, h.sp, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₁) s fun s' =>
      SArgs s' Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ IAfter s₀ Kp Ct S KL s' ∧ s'.mem = s.mem := by
  obtain ⟨s', run, x0, x1, x2, x3, g, sp, m, rd, wr⟩ := initMid₁_ok h.x20 h.x21 h.x22
  have h' := h.keep (fun r hr _ => g r hr) sp rd wr
  exact WP.of_runBlock ⟨s', run, hp.sargs x0 (by rw [x1, rounds_bv hp.klen]) x2 x3 h'.rd h'.wr, h', m⟩

/-- The arguments of the second call of `vg_aes_expand_key_scratch`, and the
registers the code after it uses. -/
abbrev IEk (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop :=
  EArgs s (Kp + BitVec.ofNat 64 (KL / 2)) (Ct + BitVec.ofNat 64 272) S (KL / 2) ∧ IAfter s₀ Kp Ct S KL s

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL)
    (h : IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' => IEk s₀ Kp Ct S KL s' ∧ s'.mem = s.mem := by
  obtain ⟨s', run, x0, x1, x2, x3, g, sp, m, rd, wr⟩ := initMid₂_ok h.x19 h.x20 h.x21 h.x22
  have h' := h.keep (fun r hr _ => g r hr) sp rd wr
  exact WP.of_runBlock ⟨s', run, ⟨hp.eargs (by omega) (by decide) x0 x1 x2 x3 h'.rd h'.wr, h'⟩, m⟩

/-! ## The whole function -/

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initAArch64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => GprAbi s₀ s' ∧ initAArch64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .x0 = Kp at hp
  generalize s₀.gpr .x2 = Ct at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x1).toNat = KL at hp
  have hwC := hp.wC
  have hwS := hp.wS
  have hwK := hp.wK
  have hH := hp.half
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after.keep h₂.saved h₂.sp h₂.rd h₂.wr
  refine WP.seq (WP.mono (initMid₁_wp hp a₂) fun s₃ ⟨h₃, a₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (sub_call v _ h₃) fun s₄ h₄ => ?_)
  have a₄ := a₃.keep h₄.saved h₄.sp h₄.rd h₄.wr
  refine WP.seq (WP.mono (initMid₂_wp hp a₄) fun s₅ ⟨⟨h₅, a₅⟩, m₅⟩ => ?_)
  refine WP.seq (WP.mono (ek_call v h₅) fun s₆ h₆ => ?_)
  have a₆ := a₅.keep h₆.saved h₆.sp h₆.rd h₆.wr
  -- The memory, call by call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 40⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_frame initSaved_bound (by decide) _ _ _
  have f₂ : Frame [⟨Ct, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have f₆ : Frame [⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S, 512⟩] s₅.mem s₆.mem := h₆.frame
  -- The saved registers.
  have dSv {d : Nat} (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2560) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S, 512⟩,
      ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨Ct + BitVec.ofNat 64 272, 240⟩]) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2560⟩ := hp.sS hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left sub
  have sv₁ : Spill.Saved S s₀.gpr initSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved initSaved_fits _ _ _
  have sv₆ : Spill.Saved S s₀.gpr initSaved s₆.mem := by
    have b := initSaved_bound
    refine ((sv₁.frame f₂ fun p hp' r hr => dSv (b p hp').1 (by have := b p hp'; omega) r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)).frame
      (m' := s₄.mem) (by rw [← m₃]; exact f₄) fun p hp' r hr => dSv (b p hp').1 (by have := b p hp'; omega) r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)).frame
      (by rw [← m₅]; exact f₆) fun p hp' r hr => dSv (b p hp').1 (by have := b p hp'; omega) r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  have inR : ∀ p ∈ initRestored, InRegions (s₆.rd ++ s₆.wr) (S + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    have := initSaved_bound p (initRestored_sub p hp')
    rw [a₆.rd, a₆.wr, hp.wr]
    exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (Spill.restore_wp a₆.x22 (fun p hp' => initSaved_fits.1 p (initRestored_sub p hp'))
    initRestored_restorable inR (fun p hp' => sv₆ p (initRestored_sub p hp'))) fun s₇ h₇ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [h₇.sp, a₆.sp]⟩, ?_⟩
  · rcases initRestored_fst r hr with hm | hm
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm
      exact h₇.gpr p hp'
    · rw [h₇.other r fun h => hm (by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h; exact List.mem_map_of_mem (initRestored_sub p hp')),
        a₆.other r hr hm]
  · show Spec.Siv.KeyRepr s₇.mem (s₀.gpr .x2) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat)
    rw [hp.x2, hp.x0, hp.x1, h₇.mem]
    -- The key, outside everything the code writes.
    have dK {a n : Nat} (ha : a + n ≤ KL) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, ⟨S, 512⟩,
        ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, ⟨S + BitVec.ofNat 64 2176, 40⟩]) :
        (⟨Kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
      have sub := hp.sK ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_c.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_c.sub_left sub).sub_right (hp.sC (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right (hp.sS (by decide))
    have key {a : Nat} (ha : a + KL / 2 ≤ KL) :
        Spec.Aes.bytesAt s₅.mem (Kp + BitVec.ofNat 64 a) (KL / 2) =
          Spec.Aes.bytesAt s₀.mem (Kp + BitVec.ofNat 64 a) (KL / 2) := by
      rw [m₅, Proof.Cmac.bytesAt_frame f₄ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
          (by omega), m₃,
        Proof.Cmac.bytesAt_frame f₂ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
          (by omega),
        Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK ha r (by simp only [List.mem_singleton] at hr; subst hr; simp))
          (by omega)]
    have key₁ : Spec.Aes.bytesAt s₁.mem Kp (KL / 2) = Spec.Aes.bytesAt s₀.mem Kp (KL / 2) := by
      have := Proof.Cmac.bytesAt_frame f₁ (fun r hr => dK (a := 0) (n := KL / 2) (by omega) r
        (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega)
      rwa [k0] at this
    have key₂ := key (a := KL / 2) (by omega)
    have sch : Spec.Aes.bytesAt s₂.mem Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp (KL / 2)) := by
      rw [h₂.out, key₁]
    have hRb : 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
    refine Proof.AesSiv.keyRepr_of hp.klen ?_ ?_ ?_
    · rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.base_disjoint Ct (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega), m₅,
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.base_disjoint Ct (by omega) (by omega)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega), m₃, sch]
    · rw [Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint Ct (by omega) (by omega) (by omega)
          · exact (hp.c_s.sub_left (hp.sC (by decide))).sub_right (Region.sub_prefix (by decide))) (by decide),
        m₅, h₄.out, m₃,
        show 16 * (KL / 8 + 6 + 1) = 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) by
          simp only [Spec.Aes.rounds]; omega, sch]
    · rw [h₆.out, key₂]

/-! ## Constant time -/

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initAArch64.pre s₀) (h0' : initAArch64.pre s₀')
    (hq : initAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat := by
    rw [q0, q1, q2, q3]; exact IPre.of h0'
  generalize s₀.gpr .x0 = Kp at hp hp'
  generalize s₀.gpr .x2 = Ct at hp hp'
  generalize s₀.gpr .x3 = S at hp hp'
  generalize (s₀.gpr .x1).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22]) (.block initMid₁)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22]) (.block initMid₂)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.x22]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have agree (a b : State) (h : IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) :
      taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22]) a b := by
    refine agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.x19, h.2.x19]
    · rw [h.1.x20, h.2.x20]
    · rw [h.1.x21, h.2.x21]
    · rw [h.1.x22, h.2.x22]
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q4 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := IMid₁ s₀ Kp Ct S KL) (F₂ := IMid₁ s₀' Kp Ct S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  have e₁ := (ek_rel v (P := fun a b => IMid₁ s₀ Kp Ct S KL a ∧ IMid₁ s₀' Kp Ct S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, q4]⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL) fun a b h =>
      ⟨WP.mono (ek_call v h.1.args) fun _ h₂ => h.1.after.keep h₂.saved h₂.sp h₂.rd h₂.wr,
        WP.mono (ek_call v h.2.args) fun _ h₂ => h.2.after.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  have m₁ := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    agree hB).wp
    (F₁ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ IAfter s₀ Kp Ct S KL s)
    (F₂ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ IAfter s₀' Kp Ct S KL s)
    fun a b h => ⟨WP.mono (initMid₁_wp hp h.1) fun _ p => ⟨p.1, p.2.1⟩,
      WP.mono (initMid₁_wp hp' h.2) fun _ p => ⟨p.1, p.2.1⟩⟩
  have sk := (sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (SArgs a Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ IAfter s₀ Kp Ct S KL a) ∧
      SArgs b Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ IAfter s₀' Kp Ct S KL b)
    fun a b h => ⟨h.1.1, h.2.1, by rw [h.1.2.sp, h.2.2.sp, q4]⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (sub_call v _ h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.sp h₂.rd h₂.wr,
      WP.mono (sub_call v _ h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  have m₂ := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    agree hC).wp
    (F₁ := IEk s₀ Kp Ct S KL) (F₂ := IEk s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (initMid₂_wp hp h.1) fun _ p => p.1, WP.mono (initMid₂_wp hp' h.2) fun _ p => p.1⟩
  have e₂ := (ek_rel v (P := fun a b => IEk s₀ Kp Ct S KL a ∧ IEk s₀' Kp Ct S KL b)
    fun a b h => ⟨h.1.1, h.2.1, by rw [h.1.2.sp, h.2.2.sp, q4]⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (ek_call v h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.sp h₂.rd h₂.wr,
      WP.mono (ek_call v h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  have p := RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x22, h.2.x22]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initAArch64.pre initAArch64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.AArch64
