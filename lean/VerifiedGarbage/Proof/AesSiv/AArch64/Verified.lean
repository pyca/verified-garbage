import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Impl.AesSiv.AArch64
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesSiv.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Init`. -/
section

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
    VG.Proof.AesSiv.AArch64.IPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat :=
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

theorem IPre.rounds (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) : KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) : KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.sS (_hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 2560) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2560⟩ :=
  Offset.sub_base S (by omega)

theorem IPre.sC (_hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ 512) :
    Region.Sub ⟨Ct + BitVec.ofNat 64 d, n⟩ ⟨Ct, 512⟩ :=
  Offset.sub_base Ct (by omega)

theorem IPre.sK (_hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) {d n : Nat} (h : d + n ≤ KL) :
    Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ :=
  Offset.sub_base Kp (by omega)

/-- The arguments of a call of `vg_aes_expand_key_scratch` on half the key, from
offset `a` (0 or `KL / 2`), into the context at offset `c`. -/
theorem IPre.eargs (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) {s : State} {a c : Nat}
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
theorem IPre.sargs (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) {s : State}
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

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL) :
    WP isa (.block VG.Impl.AesSiv.AArch64.initPre) s₀ (VG.Proof.AesSiv.AArch64.IMid₁ s₀ Kp Ct S KL) := by
  have hKL : s₀.gpr .x1 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.x1
  have hw := hp.wS
  rw [show VG.Impl.AesSiv.AArch64.initPre = Spill.saveCode .x3 initSaved ++
    [mov .x19 .x0, .lsr .x .x20 .x1 1, mov .x21 .x2, mov .x22 .x3, mov .x1 .x20] from rfl]
  refine Spill.save_ok (fun p hp' => (initSaved_fits.1 p hp')) (fun p hp' => by
    have := VG.Proof.AesSiv.AArch64.initSaved_bound p hp'
    rw [hp.x3, hp.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) ?_
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write, hp.x0], by simp [gpr_write, hKL, VG.Proof.AesSiv.AArch64.half_bv hp.klen], by simp [gpr_write, hp.x2],
    by simp [gpr_write, hp.x3], fun r hr hn => ?_, rfl, by simp [mem_write, hp.x3], rfl, rfl⟩
  · rw [← k0 Kp, ← k0 Ct]
    exact hp.eargs (a := 0) (c := 0) (by omega) (by decide) (by simp [gpr_write, hp.x0])
      (by simp [gpr_write, hKL, VG.Proof.AesSiv.AArch64.half_bv hp.klen]) (by simp [gpr_write, hp.x2]) (by simp [gpr_write, hp.x3])
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

theorem IAfter.keep {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide) (by decide), h.x19], by rw [hs _ (by decide) (by decide), h.x20],
    by rw [hs _ (by decide) (by decide), h.x21], by rw [hs _ (by decide) (by decide), h.x22],
    fun r hr hn => by rw [hs r hr (VG.Proof.AesSiv.AArch64.not_x30 hn), h.other r hr hn],
    by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.after {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : VG.Proof.AesSiv.AArch64.IMid₁ s₀ Kp Ct S KL s) :
    VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s :=
  ⟨h.x19, h.x20, h.x21, h.x22, h.other, h.sp, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL)
    (h : VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₁) s fun s' =>
      SArgs s' Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s' ∧ s'.mem = s.mem := by
  obtain ⟨s', run, x0, x1, x2, x3, g, sp, m, rd, wr⟩ := VG.Proof.AesSiv.AArch64.initMid₁_ok h.x20 h.x21 h.x22
  have h' := h.keep (fun r hr _ => g r hr) sp rd wr
  exact WP.of_runBlock ⟨s', run, hp.sargs x0 (by rw [x1, VG.Proof.AesSiv.AArch64.rounds_bv hp.klen]) x2 x3 h'.rd h'.wr, h', m⟩

/-- The arguments of the second call of `vg_aes_expand_key_scratch`, and the
registers the code after it uses. -/
abbrev IEk (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop :=
  EArgs s (Kp + BitVec.ofNat 64 (KL / 2)) (Ct + BitVec.ofNat 64 272) S (KL / 2) ∧ VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (hp : VG.Proof.AesSiv.AArch64.IPre s₀ Kp Ct S KL)
    (h : VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' => VG.Proof.AesSiv.AArch64.IEk s₀ Kp Ct S KL s' ∧ s'.mem = s.mem := by
  obtain ⟨s', run, x0, x1, x2, x3, g, sp, m, rd, wr⟩ := VG.Proof.AesSiv.AArch64.initMid₂_ok h.x19 h.x20 h.x21 h.x22
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
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after.keep h₂.saved h₂.sp h₂.rd h₂.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.initMid₁_wp hp a₂) fun s₃ ⟨h₃, a₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (sub_call v _ h₃) fun s₄ h₄ => ?_)
  have a₄ := a₃.keep h₄.saved h₄.sp h₄.rd h₄.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.initMid₂_wp hp a₄) fun s₅ ⟨⟨h₅, a₅⟩, m₅⟩ => ?_)
  refine WP.seq (WP.mono (ek_call v h₅) fun s₆ h₆ => ?_)
  have a₆ := a₅.keep h₆.saved h₆.sp h₆.rd h₆.wr
  -- The memory, call by call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 40⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_frame VG.Proof.AesSiv.AArch64.initSaved_bound (by decide) _ _ _
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
    rw [h₁.mem]; exact Spill.saveMem_saved VG.Proof.AesSiv.AArch64.initSaved_fits _ _ _
  have sv₆ : Spill.Saved S s₀.gpr initSaved s₆.mem := by
    have b := VG.Proof.AesSiv.AArch64.initSaved_bound
    refine ((sv₁.frame f₂ fun p hp' r hr => dSv (b p hp').1 (by have := b p hp'; omega) r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)).frame
      (m' := s₄.mem) (by rw [← m₃]; exact f₄) fun p hp' r hr => dSv (b p hp').1 (by have := b p hp'; omega) r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)).frame
      (by rw [← m₅]; exact f₆) fun p hp' r hr => dSv (b p hp').1 (by have := b p hp'; omega) r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  have inR : ∀ p ∈ initRestored, InRegions (s₆.rd ++ s₆.wr) (S + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    have := VG.Proof.AesSiv.AArch64.initSaved_bound p (VG.Proof.AesSiv.AArch64.initRestored_sub p hp')
    rw [a₆.rd, a₆.wr, hp.wr]
    exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (Spill.restore_wp a₆.x22 (fun p hp' => initSaved_fits.1 p (VG.Proof.AesSiv.AArch64.initRestored_sub p hp'))
    VG.Proof.AesSiv.AArch64.initRestored_restorable inR (fun p hp' => sv₆ p (VG.Proof.AesSiv.AArch64.initRestored_sub p hp'))) fun s₇ h₇ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [h₇.sp, a₆.sp]⟩, ?_⟩
  · rcases VG.Proof.AesSiv.AArch64.initRestored_fst r hr with hm | hm
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm
      exact h₇.gpr p hp'
    · rw [h₇.other r fun h => hm (by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h; exact List.mem_map_of_mem (VG.Proof.AesSiv.AArch64.initRestored_sub p hp')),
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
  have hp' : VG.Proof.AesSiv.AArch64.IPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat := by
    rw [q0, q1, q2, q3]; exact IPre.of h0'
  generalize s₀.gpr .x0 = Kp at hp hp'
  generalize s₀.gpr .x2 = Ct at hp hp'
  generalize s₀.gpr .x3 = S at hp hp'
  generalize (s₀.gpr .x1).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block VG.Impl.AesSiv.AArch64.initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22]) (.block initMid₁)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22]) (.block initMid₂)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.x22]) (.block VG.Impl.AesSiv.AArch64.initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have agree (a b : State) (h : VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL b) :
      taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22]) a b := by
    refine VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.x19, h.2.x19]
    · rw [h.1.x20, h.2.x20]
    · rw [h.1.x21, h.2.x21]
    · rw [h.1.x22, h.2.x22]
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine VG.Proof.CmacAes.AArch64.agree_of q4 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.AesSiv.AArch64.IMid₁ s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.AArch64.IMid₁ s₀' Kp Ct S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.AesSiv.AArch64.initPre_wp hp, VG.Proof.AesSiv.AArch64.initPre_wp hp'⟩
  have e₁ := (ek_rel v (P := fun a b => VG.Proof.AesSiv.AArch64.IMid₁ s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.AArch64.IMid₁ s₀' Kp Ct S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, q4]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL) fun a b h =>
      ⟨WP.mono (ek_call v h.1.args) fun _ h₂ => h.1.after.keep h₂.saved h₂.sp h₂.rd h₂.wr,
        WP.mono (ek_call v h.2.args) fun _ h₂ => h.2.after.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  have m₁ := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL b) _
    agree hB).wp
    (F₁ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL s)
    (F₂ := fun (s : State) => SArgs s Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL s)
    fun a b h => ⟨WP.mono (VG.Proof.AesSiv.AArch64.initMid₁_wp hp h.1) fun _ p => ⟨p.1, p.2.1⟩,
      WP.mono (VG.Proof.AesSiv.AArch64.initMid₁_wp hp' h.2) fun _ p => ⟨p.1, p.2.1⟩⟩
  have sk := (sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (SArgs a Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL a) ∧
      SArgs b Ct (Ct + BitVec.ofNat 64 240) S (KL / 8 + 6) ∧ VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL b)
    fun a b h => ⟨h.1.1, h.2.1, by rw [h.1.2.sp, h.2.2.sp, q4]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (sub_call v _ h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.sp h₂.rd h₂.wr,
      WP.mono (sub_call v _ h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  have m₂ := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL b) _
    agree hC).wp
    (F₁ := VG.Proof.AesSiv.AArch64.IEk s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.AArch64.IEk s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (VG.Proof.AesSiv.AArch64.initMid₂_wp hp h.1) fun _ p => p.1, WP.mono (VG.Proof.AesSiv.AArch64.initMid₂_wp hp' h.2) fun _ p => p.1⟩
  have e₂ := (ek_rel v (P := fun a b => VG.Proof.AesSiv.AArch64.IEk s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.AArch64.IEk s₀' Kp Ct S KL b)
    fun a b h => ⟨h.1.1, h.2.1, by rw [h.1.2.sp, h.2.2.sp, q4]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL) (F₂ := VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (ek_call v h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.sp h₂.rd h₂.wr,
      WP.mono (ek_call v h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  have p := RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.IAfter s₀ Kp Ct S KL a ∧ VG.Proof.AesSiv.AArch64.IAfter s₀' Kp Ct S KL b) _
    (fun a b h => VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x22, h.2.x22]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initAArch64.pre initAArch64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesSiv.AArch64.init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Env`. -/
section

/-!
# AES-SIV on AArch64: the regions of `encrypt` and `decrypt`

The functions' S2V and CTR work on the key context `C`, the rounds `R`, `D`
(16 bytes, at `W + 2560`), a string `P` (`L` bytes: a component of
associated data, or the data) and the working space `W` (2560 bytes). They
call `vg_cmac_aes_update` and `vg_cmac_aes_finalize` with the context as the
key, a CMAC state in the working space, the string or the working space as
the message, and the working space at `W + 256` as theirs (`Env.uargs`,
`Env.fargs`); and `vg_aes_ctr32` with `K2`'s schedule and blocks of the
working space (`Env.cargs`). `Env` names what their contracts say about the
regions, whichever of them are writable; `Regs` the registers that hold the
arguments while the code runs.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.CmacAes.Stream.AArch64 (UArgs FArgs toNat_add_lt)
open VG.Proof.CmacAes.AArch64 (CallPre k0)

/-- The regions of the arguments. -/
structure Env (s₀ : State) (C D P W : Addr) (R L : Nat) : Prop where
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hD : D = W + BitVec.ofNat 64 dOff
  ctxIn : (⟨C, 512⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dIn : (⟨D, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dataIn : (⟨P, L⟩ : Region) ∈ s₀.rd ++ s₀.wr
  workIn : (⟨W, 2560⟩ : Region) ∈ s₀.wr
  c_w : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2560⟩
  d_p : (⟨D, 16⟩ : Region).Disjoint ⟨P, L⟩
  d_w : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  p_w : (⟨P, L⟩ : Region).Disjoint ⟨W, 2560⟩
  wC : C.toNat + 512 ≤ 2 ^ 64
  wD : D.toNat + 16 ≤ 2 ^ 64
  wP : P.toNat + L ≤ 2 ^ 64
  wW : W.toNat + 2560 ≤ 2 ^ 64
  lt : L < 2 ^ 64

/-- The registers that hold the arguments while the code runs: the working
space in `x19`, the context in `x20`, the rounds in `x21`, and the string in
`x22` (`x23` bytes). -/
structure Regs (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x22 : s.gpr .x22 = P
  x23 : s.gpr .x23 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Regs.keep {s₀ s s' : State} {C D P W : Addr} {R L : Nat} (h : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s)
    (hs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' :=
  ⟨by rw [hs _ (by decide) (by decide), h.x19], by rw [hs _ (by decide) (by decide), h.x20],
    by rw [hs _ (by decide) (by decide), h.x21], by rw [hs _ (by decide) (by decide), h.x22],
    by rw [hs _ (by decide) (by decide), h.x23], by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

/-- A property every register of a literal list has, for a register of it. -/
theorem dec_mem {l : List Reg} {p : Reg → Prop} [DecidablePred p] (h : l.all (fun r => decide (p r)) = true)
    {r : Reg} (hr : r ∈ l) : p r :=
  of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- A register of a literal list without `x`. -/
theorem dec_ne {l : List Reg} {x : Reg} (h : l.contains x = false) {r : Reg} (hr : r ∈ l) : r ≠ x := by
  rintro rfl; simp_all

/-- `Regs.keep` after code that writes none of `x19`–`x23`. -/
theorem Regs.keep' {s₀ s s' : State} {C D P W : Addr} {R L : Nat} (h : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s)
    (hs : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' :=
  ⟨by rw [hs _ (by decide), h.x19], by rw [hs _ (by decide), h.x20], by rw [hs _ (by decide), h.x21],
    by rw [hs _ (by decide), h.x22], by rw [hs _ (by decide), h.x23], by rw [hsp, h.sp], by rw [hrd, h.rd],
    by rw [hwr, h.wr]⟩

/-- A region at an offset of one of `rs`. -/
theorem cov_off {rs : List Region} {r : Region} (hr : r ∈ rs) {off n : Nat} (h : off + n ≤ r.len) :
    Covers [⟨r.base + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨r, hr, off, rfl, h⟩

theorem cov_base {rs : List Region} {r : Region} (hr : r ∈ rs) {n : Nat} (h : n ≤ r.len) :
    Covers [⟨r.base, n⟩] rs := by
  have := VG.Proof.AesSiv.AArch64.cov_off hr (off := 0) (n := n) (by omega)
  rwa [k0] at this

/-- The PRF and the cipher of a key context outside a frame's regions. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.Cmac.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.Cmac.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

/-- The registers the taint analysis needs public around the calls. -/
theorem regs_agree {s₀ s₀' a b : State} {C D P W : Addr} {R L : Nat} (hq : s₀.sp = s₀'.sp)
    (ha : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a) (hb : VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b) :
    taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) a b := by
  refine Proof.CmacAes.AArch64.agree_of (by rw [ha.sp, hb.sp, hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [ha.x19, hb.x19]
  · rw [ha.x20, hb.x20]
  · rw [ha.x21, hb.x21]
  · rw [ha.x22, hb.x22]
  · rw [ha.x23, hb.x23]

/-- `xor2` is the block XOR of the CMAC proofs. -/
theorem xor2_eq (pb qb cb : Reg) (pd qd cd : Nat) :
    xor2 pb qb cb pd qd cd = Proof.CmacAes.AArch64.xor2 pb qb cb pd qd cd := rfl

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

theorem z0 : BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0 := by decide

/-- `copy16 src dst`: the block at `B + src` copied to `B + dst`, a word at a time. -/
theorem copy16_ok {s : State} {B : Addr} (hb : s.gpr .x19 = B) {src dst : Nat}
    (hs : src % 8 = 0 ∧ src + 8 < 32768) (hd : dst % 8 = 0 ∧ dst + 8 < 32768)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (B + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (B + BitVec.ofNat 64 (dst + 8)) 8) :
    ∃ s', runBlock isa (copy16 src dst) s = some s' ∧
      s'.mem = Proof.CmacAes.Stream.AArch64.copyMem s.mem (B + BitVec.ofNat 64 dst) (B + BitVec.ofNat 64 src) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, and_self, copy16, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write,
      Option.bind_some, Option.map_some, hb, hs.1, hd.1, BitVec.setWidth_eq,
      show src < 32768 by omega, show src + 8 < 32768 from hs.2, show dst < 32768 by omega,
      show dst + 8 < 32768 from hd.2, Nat.add_mod_right, r₀, r₁, w₀, w₁, and_self]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ => by simp [gpr_write, h₁], rfl, rfl, rfl⟩
  simp only [Proof.CmacAes.Stream.AArch64.copyMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, Offset.add_add]

namespace Env

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem sW (_h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base W hd

theorem sC (_h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 512) :
    Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base C hd

theorem sP (_h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ L) :
    Region.Sub ⟨P + BitVec.ofNat 64 d, n⟩ ⟨P, L⟩ :=
  Offset.sub_base P hd

theorem inW (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ 2560) :
    InRegions s.wr (W + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, h.workIn, Offset.contains_base W hd (by have := h.wW; omega)⟩

theorem inRW (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]
  obtain ⟨r, hr, hc⟩ := h.inW (s := s₀) rfl hd
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inRC (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.ctxIn, Offset.contains_base C hd (by have := h.wC; omega)⟩

theorem inRP (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ L) : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dataIn, Offset.contains_base P hd (by have := h.wP; have := h.lt; omega)⟩

theorem inWP (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hwr : s.wr = s₀.wr)
    {d n : Nat} (hd : d + n ≤ L) : InRegions s.wr (P + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact ⟨_, hPw, Offset.contains_base P hd (by have := h.wP; have := h.lt; omega)⟩

theorem inRD (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hrd, hwr]; exact ⟨_, h.dIn, Offset.contains_base D hd (by have := h.wD; omega)⟩

/-- A message for the CMAC functions: `n` bytes at `Q`, which miss the state at
`W + o` and the working space of the functions called. -/
structure Src (s₀ : State) (W : Addr) (o : Nat) (Q : Addr) (n : Nat) : Prop where
  qo : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩
  qs : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩
  wrap : Q.toNat + n ≤ 2 ^ 64
  cov : Covers [⟨Q, n⟩] (s₀.rd ++ s₀.wr)

/-- Data bytes as the message. -/
theorem srcData (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {o a n : Nat} (ho : o + 16 ≤ 2560) (ha : a + n ≤ L) :
    VG.Proof.AesSiv.AArch64.Env.Src s₀ W o (P + BitVec.ofNat 64 a) n where
  qo := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW ho)
  qs := (h.p_w.sub_left (h.sP ha)).sub_right (h.sW (by decide))
  wrap := by
    have := h.wP
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := (P + BitVec.ofNat 64 a).isLt; omega
    · rw [toNat_add_lt P this (by omega)]; omega
  cov := VG.Proof.AesSiv.AArch64.cov_off h.dataIn ha

theorem srcData₀ (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {o n : Nat} (ho : o + 16 ≤ 2560) (hn : n ≤ L) :
    VG.Proof.AesSiv.AArch64.Env.Src s₀ W o P n := by
  have := h.srcData (o := o) (a := 0) (n := n) ho (by omega)
  rwa [k0] at this

/-- Bytes of the working space below `W + 256`, apart from the state, as the message. -/
theorem srcWork (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {o t n : Nat} (ho : o + 16 ≤ 256) (ht : t + n ≤ 256)
    (hs : t + n ≤ o ∨ o + 16 ≤ t) : VG.Proof.AesSiv.AArch64.Env.Src s₀ W o (W + BitVec.ofNat 64 t) n where
  qo := Offset.disjoint W hs (by omega) (by omega)
  qs := Offset.disjoint W (by omega) (by omega) (by omega)
  wrap := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  cov := Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp; omega))

/-- The arguments of `vg_cmac_aes_finalize`: the context as the key, the
state at `St` (in the working space below `W + 256`, or `D`), the message at
`Q`, and the working space at `W + 256`. -/
theorem fargs' (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {St : Addr} (hSt : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩)
    (hcs : (⟨C, 512⟩ : Region).Disjoint ⟨St, 16⟩) (hwSt : St.toNat + 16 ≤ 2 ^ 64)
    (hcov : Covers [⟨St, 16⟩] s₀.wr) {Q : Addr} {n : Nat}
    (hq : (⟨Q, n⟩ : Region).Disjoint ⟨St, 16⟩) (hqs : (⟨Q, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 2176⟩)
    (hqw : Q.toNat + n ≤ 2 ^ 64) (hqc : Covers [⟨Q, n⟩] (s₀.rd ++ s₀.wr)) (hn : n ≤ 16)
    (x0 : s.gpr .x0 = C) (x1 : s.gpr .x1 = BitVec.ofNat 64 R) (x2 : s.gpr .x2 = St)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 n) (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256) :
    FArgs s C St Q (W + BitVec.ofNat 64 256) n R where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := h.rounds
  len := hn
  kst := hcs.sub_left (Region.sub_prefix (by decide))
  ks := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  pst := hq
  ps := hqs
  sts := hSt
  wrapK := by have := h.wC; omega
  wrapSt := hwSt
  wrapP := hqw
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    exact Covers.append_left (Covers.cons (VG.Proof.AesSiv.AArch64.cov_base h.ctxIn (by simp)) (Covers.cons hqc Covers.nil))
      (Covers.cons (Covers.right hcov) (Covers.cons (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons hcov (Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp)) Covers.nil)

/-- `fargs'` with the state at `W + o`. -/
theorem fargs (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesSiv.AArch64.Env.Src s₀ W o Q n) (hn : n ≤ 16)
    (x0 : s.gpr .x0 = C) (x1 : s.gpr .x1 = BitVec.ofNat 64 R) (x2 : s.gpr .x2 = W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 n) (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256) :
    FArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) n R :=
  h.fargs' hrd hwr (Offset.disjoint W (by omega) (by omega) (by omega))
    ((h.c_w.sub_right (h.sW (by omega))))
    (by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega) (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp; omega))
    hq.qo hq.qs hq.wrap hq.cov hn x0 x1 x2 x3 x4 x5

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + o`, `n` blocks at `Q`, and the working space at `W + 256`. -/
theorem uargs (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {o : Nat} (ho : o + 16 ≤ 256) {Q : Addr} {n : Nat}
    (hq : VG.Proof.AesSiv.AArch64.Env.Src s₀ W o Q (16 * n)) (hn : 16 * n < 2 ^ 64)
    (x0 : s.gpr .x0 = C) (x1 : s.gpr .x1 = BitVec.ofNat 64 R) (x2 : s.gpr .x2 = W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 n) (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256) :
    UArgs s C (W + BitVec.ofNat 64 o) Q (W + BitVec.ofNat 64 256) R n where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := h.rounds
  hn := hn
  wc := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by omega))
  ws := (h.c_w.sub_left (Region.sub_prefix (by decide))).sub_right (h.sW (by decide))
  dc := hq.qo
  ds := hq.qs
  cs := Offset.disjoint W (by omega) (by omega) (by omega)
  wrapC := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  wrapD := hq.wrap
  wrapS := by rw [toNat_add_lt W h.wW (by omega)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    exact Covers.append_left (Covers.cons (VG.Proof.AesSiv.AArch64.cov_base h.ctxIn (by simp)) (Covers.cons hq.cov Covers.nil))
      (Covers.cons (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp; omega)))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp))) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp; omega)) (Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp)) Covers.nil)

/-- The arguments of `vg_aes_ctr32` on one block: `K2`'s schedule, the counter
block at `W + 96`, the keystream block at `W + 80` (zero), and the working
space at `W + 256`. -/
theorem cargs (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (x0 : s.gpr .x0 = C + BitVec.ofNat 64 272) (x1 : s.gpr .x1 = BitVec.ofNat 64 R)
    (x2 : s.gpr .x2 = W + BitVec.ofNat 64 96) (x3 : s.gpr .x3 = W + BitVec.ofNat 64 80) (x4 : s.gpr .x4 = 1)
    (x5 : s.gpr .x5 = W + BitVec.ofNat 64 256)
    (hz : Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16) :
    CallPre s (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256)
      R where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := h.rounds
  wc := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  wd := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  ws := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  cd := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  cs := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  ds := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  wrap := by rw [toNat_add_lt W h.wW (show 80 < 2560 by decide)]; have := h.wW; omega
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.ctxIn (by simp)) Covers.nil)
      (Covers.cons (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp)))
        (Covers.cons (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp)))
          (Covers.cons (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp))) Covers.nil)))
  writes := by
    rw [hwr]
    exact Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp)) (Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp))
      (Covers.cons (VG.Proof.AesSiv.AArch64.cov_off h.workIn (by simp)) Covers.nil))
  zero := hz

/-- The 16 bytes at `W + d` zeroed. -/
theorem zero16_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hwr : s.wr = s₀.wr) {d : Nat}
    (hd : d + 16 ≤ 2560) (h8 : d % 8 = 0) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 d) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₀ := h.inW hwr (d := d) (n := 8) (by omega)
  have w₁ := h.inW hwr (d := d + 8) (n := 8) (by omega)
  have h8' : (d + 8) % 8 = 0 := by omega
  have l₀ : d < 32768 := by omega
  have l₁ : d + 8 < 32768 := by omega
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, and_self, zero16, runBlock_cons,
      runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write,
      wr_write, Option.bind_some, BitVec.setWidth_eq, h19, h8, h8', l₀, l₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl⟩
  simp only [Proof.Cmac.zero2, Mem.writeW, BitVec.setWidth_eq, Offset.add_add, VG.Proof.AesSiv.AArch64.z0, Nat.reduceDiv]

end Env

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Call`. -/
section

/-!
# AES-SIV on AArch64: calling `vg_cmac_aes_finalize` with any subkeys

`vg_cmac_aes_finalize`'s contract gives the CMAC of the message only when the
subkeys in its `key` are those of the key schedule's cipher. Its code needs
no such thing: it computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key`
holds, for the chaining value `C` at `state` and the last block `Mₙ` of
§6.2 step 4 (`finalize_raw_wp`). AES-SIV's contracts compute with the
subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use this
(`finr_call`), with `WP.call` from this correctness of the same code.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (FPre finPre_wp ctr_call finalizeAArch64 mn restoreF_ok wr_in finalize_keepsV
  callEntry_x0 callEntry_x1 callEntry_x2 callEntry_x3 callEntry_x4 toNat_rounds)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs finalize_noFrames toNat_ofNat)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawAArch64 : Contract isa where
  pre := finalizeAArch64.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 =
      Spec.Cmac.aesWith (s.gpr .x1).toNat (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
        (Spec.Cmac.xor (mn s.mem (s.gpr .x0) (s.gpr .x3) (s.gpr .x4).toNat)
          (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16))
  pub := finalizeAArch64.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa (Impl.CmacAes.AArch64.finalize v.callee) s₀
      fun s' => GprAbi s₀ s' ∧ finalizeRawAArch64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .x0 = W at hp
  generalize hSt : s₀.gpr .x2 = St at hp
  generalize hP : s₀.gpr .x3 = P at hp
  generalize s₀.gpr .x5 = S at hp
  generalize hL : (s₀.gpr .x4).toNat = L at hp
  generalize hR' : (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), h₁.x19]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, mem₃⟩ := restoreF_ok s₂ x19₂
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2072) (n := 8) (by decide)))
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2064) (n := 8) (by decide)))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hp.st_scr.symm.sub_left (FPre.scrD (by omega)))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2064 (by decide) (by decide), h₁.slot19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2072 (by decide) (by decide), h₁.slot30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · show Spec.Aes.bytesAt s₃.mem (s₀.gpr .x2) 16 = _
    rw [hW, hSt, hP, hL, hR', mem₃, h₂.out, sch, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawAArch64.pre s) :
    ∃ t s', Exec isa (Impl.CmacAes.AArch64.finalize v.callee) s t s' ∧ abiPreserved s s' ∧
      finalizeRawAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesSiv.AArch64.finalize_raw_wp v hs) (finalize_keepsV v)

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem St 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
      (Spec.Cmac.xor (mn s.mem K P L) (Spec.Aes.bytesAt s.mem St 16))

theorem finr_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) s (VG.Proof.AesSiv.AArch64.FRPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := VG.Proof.AesSiv.AArch64.finalizeRawAArch64) (VG.Proof.AesSiv.AArch64.finalize_raw_correct v) h.pre h.reads h.writes ?_
    (finalize_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [VG.Proof.AesSiv.AArch64.finalizeRawAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hL] at hpost
  exact hpost

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.CmacOf`. -/
section

/-!
# AES-SIV on AArch64: the CMAC of a string (`cmacOf`)

`cmacOf` computes the CMAC of the string with the context's PRF into the
state at `W + 128`: the code zeroes the state, computes `16 nb`, the bytes of
the whole blocks before the last 1 to 16 (`Spec.Cmac.chainedLen`), into
`x28`, chains the `nb` blocks with `vg_cmac_aes_update` and finalizes the
rest with `vg_cmac_aes_finalize` (`Siv.cmacWith_chained`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 mn agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs UPost FArgs upd_call upd_rel fin_rel toNat_ofNat eval_zero mz0 mz15
  nb16_bv)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The length of the whole blocks -/

theorem chainedLen_le (L : Nat) : Spec.Cmac.chainedLen 16 L ≤ L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (L : Nat) : L - Spec.Cmac.chainedLen 16 L ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (L : Nat) : 16 * (Spec.Cmac.chainedLen 16 L / 16) = Spec.Cmac.chainedLen 16 L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_pos {L : Nat} (h : 0 < L) : Spec.Cmac.chainedLen 16 L = 16 * ((L - 1) / 16) := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem lsr4 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 4 = BitVec.ofNat 64 (c / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- The other registers `encrypt` and `decrypt` keep: the descriptors, the
number left, and the data and its length. -/
def Hold (s s' : State) : Prop := ∀ r ∈ [Reg.x24, .x25, .x26, .x27], s'.gpr r = s.gpr r

theorem Hold.refl (s : State) : VG.Proof.AesSiv.AArch64.Hold s s := fun _ _ => rfl

theorem Hold.trans {a b c : State} (h₁ : VG.Proof.AesSiv.AArch64.Hold a b) (h₂ : VG.Proof.AesSiv.AArch64.Hold b c) : VG.Proof.AesSiv.AArch64.Hold a c :=
  fun r hr => by rw [h₂ r hr, h₁ r hr]

theorem Hold.of {s s' : State} (h : ∀ r ∈ preserved, r ≠ .x28 → r ≠ .x30 → s'.gpr r = s.gpr r) : VG.Proof.AesSiv.AArch64.Hold s s' :=
  fun r hr => h r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr)

/-! ## Before the update -/

theorem cmacArgs_ok {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {c : Nat} (hc : c < 2 ^ 64)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa [.lsr .x .x4 .x28 4, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 stOff, mov .x3 .x22,
        .addImm .x .x5 .x19 csOff] s = some s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.gpr .x0 = C ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧ s'.gpr .x2 = W + BitVec.ofNat 64 128 ∧
      s'.gpr .x3 = P ∧ s'.gpr .x4 = BitVec.ofNat 64 (c / 16) ∧ s'.gpr .x5 = W + BitVec.ofNat 64 256 ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, stOff, csOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, by simp [gpr_write, hr.x20], by simp [gpr_write, hr.x21],
    by simp [gpr_write, hr.x19], by simp [gpr_write, hr.x22], by simp [gpr_write, h28, VG.Proof.AesSiv.AArch64.lsr4 hc],
    by simp [gpr_write, hr.x19], rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem sub_and15 (x : BitVec 64) : x - (x &&& 15) = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have h : (x &&& 15).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have := x.isLt
  rw [BitVec.toNat_sub, h, BitVec.toNat_ofNat]
  omega

theorem cmacPre_wp (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) :
    WP isa (cmacPre stOff) s fun s' => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧ VG.Proof.AesSiv.AArch64.Hold s s' ∧
      UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      s'.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) ∧
      s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 128) := by
  have hcl := VG.Proof.AesSiv.AArch64.chainedLen_le L
  have hlt := h.lt
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := stOff) (by decide) (by decide)
  rw [cmacPre, show zero16 stOff ++ [.movz .x .x28 0 0] = zero16 stOff ++ ([.movz .x .x28 0 0] : List Instr)
    from rfl]
  refine WP.seq (WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₁.write .x .x28 0, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, ite_true,
      mz0], ?_⟩⟩))
  -- The state after the first block.
  have hr₁ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L (s₁.write .x .x28 0) :=
    hr.keep' (fun r hr' => by
      rw [gpr_write_of_ne _ _ _ (by rintro rfl; revert hr'; decide), g₁ r (by rintro rfl; revert hr'; decide)])
      (by rw [sp_write, sp₁]) (by rw [rd_write, rd₁]) (by rw [wr_write, wr₁])
  have k₁ : ∀ r ∈ preserved, r ≠ .x28 → (s₁.write .x .x28 0).gpr r = s.gpr r := fun r hr' h28 => by
    rw [gpr_write_of_ne _ _ _ h28, g₁ r (by rintro rfl; revert hr'; decide)]
  have last (s₂ : State) (hr₂ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₂)
      (k₂ : ∀ r ∈ preserved, r ≠ .x28 → s₂.gpr r = s.gpr r)
      (x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (m₂ : s₂.mem = s₁.mem) :
      WP isa (.block [.lsr .x .x4 .x28 4, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 stOff, mov .x3 .x22,
        .addImm .x .x5 .x19 csOff]) s₂ fun s' => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧ VG.Proof.AesSiv.AArch64.Hold s s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
        s'.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) ∧
        s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 128) := by
    obtain ⟨s', run, g, x0, x1, x2, x3, x4, x5, sp, m, rd, wr⟩ := VG.Proof.AesSiv.AArch64.cmacArgs_ok hr₂ (by omega) x28₂
    have hr' := hr₂.keep' (fun r hr => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr)) sp rd wr
    refine WP.of_runBlock ⟨s', run, hr', Hold.of fun r hr'' h28 _ => by rw [g r hr'', k₂ r hr'' h28],
      h.uargs hr'.rd hr'.wr (by decide) (by rw [VG.Proof.AesSiv.AArch64.chainedLen_div]; exact h.srcData₀ (by decide) hcl)
        (by rw [VG.Proof.AesSiv.AArch64.chainedLen_div]; omega) x0 x1 x2 x3 x4 x5, by rw [g _ (by decide), x28₂], by rw [m, m₂, m₁]⟩
  have ev := eval_zero (s := s₁.write .x .x28 0) hlt hr₁.x23
  by_cases hL0 : L = 0
  · refine WP.seq (WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h))
    exact last _ hr₁ k₁ (by rw [gpr_write_self, hL0]; rfl) (mem_write _ _ _ _)
  · refine WP.seq (WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_)
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine last _ (hr₁.keep' (fun r hr' => ?_) rfl rfl rfl) (fun r hr' h28 => ?_) ?_ (by simp [mem_write])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
    · rw [← k₁ r hr' h28]
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, mz15]
      rw [VG.Proof.AesSiv.AArch64.chainedLen_pos (by omega), g₁ _ (by decide), hr.x23, VG.Proof.AesSiv.AArch64.sub_and15]
      have : (BitVec.ofNat 64 L - 1#64).toNat = L - 1 := by
        rw [BitVec.toNat_sub, toNat_ofNat hlt]; simp; omega
      rw [this]

/-! ## Between the calls -/

theorem cmacMid_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {c : Nat}
    (hc : c ≤ L) (h28 : s.gpr .x28 = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa (cmacMid stOff) s = some s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.gpr .x0 = C ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧ s'.gpr .x2 = W + BitVec.ofNat 64 128 ∧
      s'.gpr .x3 = P + BitVec.ofNat 64 c ∧ s'.gpr .x4 = BitVec.ofNat 64 (L - c) ∧
      s'.gpr .x5 = W + BitVec.ofNat 64 256 ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, cmacMid, mov, stOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, by simp [gpr_write, hr.x20], by simp [gpr_write, hr.x21],
    by simp [gpr_write, hr.x19], by simp [gpr_write, hr.x22, h28],
    by simp [gpr_write, hr.x23, h28, VG.Proof.AesSiv.AArch64.ofNat_sub hc hlt], by simp [gpr_write, hr.x19], rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-! ## The whole -/

/-- What `cmacOf` leaves: the CMAC of the string with the context's PRF in the
state at `W + 128`. -/
structure CPost (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s'
  hold : VG.Proof.AesSiv.AArch64.Hold s s'
  frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 128) 16 =
    Spec.Siv.ctxMac s.mem C R (Spec.Aes.bytesAt s.mem P L)

theorem cmacOf_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State}
    (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) :
    WP isa (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) s (VG.Proof.AesSiv.AArch64.CPost s₀ C D P W R L s) := by
  have hcl := VG.Proof.AesSiv.AArch64.chainedLen_le L
  have hrest := VG.Proof.AesSiv.AArch64.chainedLen_rest L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.cmacPre_wp h hr) fun s₁ ⟨hr₁, k₁, hu₁, x28₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call v _ hu₁) fun s₂ h₂ => ?_)
  have hr₂ := hr₁.keep h₂.saved h₂.sp h₂.rd h₂.wr
  have x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
    rw [h₂.saved _ (by decide) (by decide), x28₁]
  obtain ⟨s₃, run₃, g₃, x0₃, x1₃, x2₃, x3₃, x4₃, x5₃, sp₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.AArch64.cmacMid_ok h hr₂ hcl x28₂
  have hr₃ := hr₂.keep' (fun r hr => g₃ r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr)) sp₃ rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ (h.fargs hr₃.rd hr₃.wr (by decide)
    (h.srcData (o := 128) (by decide) (show Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) ≤ L by
      omega)) hrest x0₃ x1₃ x2₃ x3₃ x4₃ x5₃)) fun s₄ h₄ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have f₁ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  have frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s₄.mem :=
    (f₁.trans f₂).trans (by rw [← m₃]; exact f₄)
  refine ⟨hr₃.keep h₄.saved h₄.sp h₄.rd h₄.wr,
    k₁.trans (Hold.of fun r hr h28 h30 => by rw [h₄.saved r hr h30, g₃ r hr, h₂.saved r hr h30]), frame, ?_⟩
  -- The bytes the calls read are those at the start.
  have dRead {Q : Addr} {n : Nat} (hd : ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region),
      ⟨W + BitVec.ofNat 64 256, 2176⟩], (⟨Q, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
      Spec.Aes.bytesAt s₁.mem Q n = Spec.Aes.bytesAt s.mem Q n ∧
        Spec.Aes.bytesAt s₃.mem Q n = Spec.Aes.bytesAt s.mem Q n := by
    have e₁ := Proof.Cmac.bytesAt_frame f₁ hd hn
    refine ⟨e₁, ?_⟩
    rw [m₃, Proof.Cmac.bytesAt_frame f₂ hd hn, e₁]
  have hlt := h.lt
  have dC {d n : Nat} (hd : d + n ≤ 512) := dRead (Q := C + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))) (by omega)
  have dP {d n : Nat} (hd : d + n ≤ L) := dRead (Q := P + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := (dC (d := 240) (n := 16) (by decide)).2
  have k2 := (dC (d := 256) (n := 16) (by decide)).2
  have pre := (dP (d := 0) (n := Spec.Cmac.chainedLen 16 L) (by omega)).1
  have rest := (dP (d := Spec.Cmac.chainedLen 16 L) (n := L - Spec.Cmac.chainedLen 16 L) (by omega)).2
  rw [k0] at sch pre
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 128) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  have hS : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : L = Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) := by omega
  rw [h₄.out, mn, sch.2, k1, k2, rest, m₃, h₂.out, Proof.Cmac.Stream.blocksAt_eq, VG.Proof.AesSiv.AArch64.chainedLen_div, sch.1, hz, pre,
    Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS]
  have tk : (Spec.Aes.bytesAt s.mem P L).take (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem P (Spec.Cmac.chainedLen 16 L) := by
    have := Proof.AesSiv.take_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L)
      (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  have dr : (Spec.Aes.bytesAt s.mem P L).drop (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (L - Spec.Cmac.chainedLen 16 L) := by
    have := Proof.AesSiv.drop_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L)
      (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  rw [tk, dr]
  rw [Proof.Cmac.xor_comm]
  rfl

/-! ## Constant time -/

/-- The registers before and after the update, with `16 nb` in `x28`. -/
abbrev RX (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop :=
  VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s ∧ s.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)

theorem regs_agree28 {s₀ s₀' a b : State} {C D P W : Addr} {R L : Nat} (hq : s₀.sp = s₀'.sp)
    (ha : VG.Proof.AesSiv.AArch64.RX s₀ C D P W R L a) (hb : VG.Proof.AesSiv.AArch64.RX s₀' C D P W R L b) :
    taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x28]) a b := by
  refine VG.Proof.CmacAes.AArch64.agree_of (by rw [ha.1.sp, hb.1.sp, hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.1.x19, hb.1.x19]
  · rw [ha.1.x20, hb.1.x20]
  · rw [ha.1.x21, hb.1.x21]
  · rw [ha.1.x22, hb.1.x22]
  · rw [ha.1.x23, hb.1.x23]
  · rw [ha.2, hb.2]

theorem cmacOf_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b)
      (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff)
      fun a b => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b := by
  have hcl := VG.Proof.AesSiv.AArch64.chainedLen_le L
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) (cmacPre stOff)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x28])
      (.block (cmacMid stOff)) hc).isSome = true := ⟨_, by taint_decide⟩
  have pre_wp {σ s : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hr : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L s) :
      WP isa (cmacPre stOff) s fun s' => VG.Proof.AesSiv.AArch64.RX σ C D P W R L s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) :=
    WP.mono (VG.Proof.AesSiv.AArch64.cmacPre_wp hσ hr) fun _ ⟨a, _, b, c, _⟩ => ⟨⟨a, c⟩, b⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.AArch64.RX s₀ C D P W R L s ∧
      UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    (F₂ := fun (s : State) => VG.Proof.AesSiv.AArch64.RX s₀' C D P W R L s ∧
      UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    fun a b hab => ⟨pre_wp h hab.1, pre_wp h' hab.2⟩
  have u := (upd_rel v v.callee.name
    (P := fun a b => (VG.Proof.AesSiv.AArch64.RX s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16)) ∧
      VG.Proof.AesSiv.AArch64.RX s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.1.sp, hab.2.1.1.sp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.RX s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.RX s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (upd_call v _ hab.1.2) fun _ h₂ =>
        ⟨hab.1.1.1.keep h₂.saved h₂.sp h₂.rd h₂.wr, by rw [h₂.saved _ (by decide) (by decide), hab.1.1.2]⟩,
      WP.mono (upd_call v _ hab.2.2) fun _ h₂ =>
        ⟨hab.2.1.1.keep h₂.saved h₂.sp h₂.rd h₂.wr, by rw [h₂.saved _ (by decide) (by decide), hab.2.1.2]⟩⟩
  have mid_wp {σ s : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hr : VG.Proof.AesSiv.AArch64.RX σ C D P W R L s) :
      WP isa (.block (cmacMid stOff)) s fun s' => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L s' ∧
        FArgs s' C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
          (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R := by
    obtain ⟨s', run, g, x0, x1, x2, x3, x4, x5, sp, _, rd, wr⟩ := VG.Proof.AesSiv.AArch64.cmacMid_ok hσ hr.1 hcl hr.2
    have hr' := hr.1.keep' (fun r hr => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr)) sp rd wr
    exact WP.of_runBlock ⟨s', run, hr', hσ.fargs hr'.rd hr'.wr (by decide)
      (hσ.srcData (o := 128) (by decide) (by omega)) (VG.Proof.AesSiv.AArch64.chainedLen_rest L) x0 x1 x2 x3 x4 x5⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.RX s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.RX s₀' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree28 hq hab.1 hab.2) hB).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s ∧
      FArgs s C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    (F₂ := fun (s : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L s ∧
      FArgs s C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    fun a b hab => ⟨mid_wp h hab.1, mid_wp h' hab.2⟩
  have f := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun a b => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R) ∧
      VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ hab.1.2) fun _ h₂ => hab.1.1.keep h₂.saved h₂.sp h₂.rd h₂.wr,
      WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ hab.2.2) fun _ h₂ => hab.2.1.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((u.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq (f.mono (fun _ _ h => h) fun _ _ h => h.2)))

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.S2vAd`. -/
section

/-!
# AES-SIV on AArch64: a step of S2V over the associated data

After the CMAC of a component into the working space (`cmacOf_wp`), the code
doubles `D` (at `W + 2560`) in place and XORs the CMAC into it, so `D` is
then `dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_wp`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.CmacAes.AArch64 (k0 dblMem dbl_ok dblMem_bytes dblMem_frame xor2_ok)

variable {D W : Addr}

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it, then the
descriptor pointer advanced by 16 and the count decremented. -/
theorem adStep_wp {s : State} (h19 : s.gpr .x19 = W) (hD : D = W + BitVec.ofNat 64 dOff)
    (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, 2560⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩) (wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + 2560 ≤ 2 ^ 64) :
    WP isa (.block adStep) s fun s' =>
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x24 → r ≠ .x25 → s'.gpr r = s.gpr r) ∧
      s'.gpr .x24 = s.gpr .x24 + BitVec.ofNat 64 16 ∧ s'.gpr .x25 = s.gpr .x25 - BitVec.ofNat 64 1 ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Spec.Aes.bytesAt s'.mem D 16 =
        Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16))
          (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 128) 16) ∧
      Frame [⟨D, 16⟩] s.mem s'.mem := by
  subst hD
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (W + BitVec.ofNat 64 dOff + BitVec.ofNat 64 d) 8 :=
    ⟨_, hDw, Offset.contains_base _ hd (by omega)⟩
  have inD' (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (W + BitVec.ofNat 64 (dOff + d)) 8 := by
    rw [← Offset.add_add]; exact inD d hd
  have inW (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, hWw, Offset.contains_base W hd (by omega)⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  rw [adStep, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := dbl_ok s h19 (src := dOff) (dst := dOff) (by decide) (by decide)
    (rr (inD' 0 (by decide))) (rr (inD' 8 (by decide))) (inD' 0 (by decide)) (inD' 8 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have h19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h19]
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := xor2_ok s₁ .x19 .x19 .x19 dOff stOff dOff
    (P := W + BitVec.ofNat 64 dOff) (Q := W + BitVec.ofNat 64 stOff) (C := W + BitVec.ofNat 64 dOff)
    (by decide) (by decide) (by decide) (by rw [h19₁]) (by rw [h19₁, Offset.add_add])
    (by rw [h19₁]) (by rw [h19₁, Offset.add_add]) (by rw [h19₁]) (by rw [h19₁, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [rd₁, wr₁]; exact rr (inD' 0 (by decide))) (by rw [rd₁, wr₁, Offset.add_add]; exact rr (inD' 8 (by decide)))
    (by rw [rd₁, wr₁]; exact rr (inW 128 (by decide)))
    (by rw [rd₁, wr₁, Offset.add_add]; exact rr (inW 136 (by decide)))
    (by rw [wr₁]; exact inD' 0 (by decide)) (by rw [wr₁, Offset.add_add]; exact inD' 8 (by decide))
  refine WP.of_runBlock ⟨s₂, by rw [← VG.Proof.AesSiv.AArch64.xor2_eq] at run₂; exact run₂, ?_⟩
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  have dW {d n : Nat} (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 dOff, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W hd)
  refine ⟨fun r a b c d e f => by
      simp only [gpr_write, e, f, ite_false]
      rw [g₂ r a b, g₁ r a b c d], by simp [gpr_write, g₂ .x24 (by decide) (by decide),
      g₁ .x24 (by decide) (by decide) (by decide) (by decide)],
    by simp [gpr_write, g₂ .x25 (by decide) (by decide), g₁ .x25 (by decide) (by decide) (by decide) (by decide)],
    by simp only [sp_write, sp₂, sp₁], by simp only [rd_write, rd₂, rd₁], by simp only [wr_write, wr₂, wr₁], ?_, ?_⟩
  · have s₁ : (⟨W + BitVec.ofNat 64 dOff, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 dOff + BitVec.ofNat 64 8, 8⟩ := by
      rw [Offset.add_add]
      exact Offset.disjoint W (d := dOff) (n := 8) (e := dOff + 8) (k := 8) (by decide) (by decide) (by decide)
    have s₂ : (⟨W + BitVec.ofNat 64 dOff, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 136, 8⟩ :=
      (dW (d := 136) (n := 8) (by decide) _ (List.mem_singleton_self _)).symm.sub_left
      (Region.sub_prefix (by decide))
    simp only [mem_write]
    rw [m₂, Proof.Cmac.xor2Mem_bytes _ s₁ (by rw [Offset.add_add]; exact s₂),
      m₁, dblMem_bytes, Proof.Cmac.bytesAt_frame (dblMem_frame _ _ _ _) (dW (d := stOff) (n := 16) (by decide))
        (by decide), Spec.Siv.dbl, Siv.xor_eq]
    all_goals rfl
  · simp only [mem_write]
    rw [m₂]
    exact (m₁ ▸ dblMem_frame s.mem W dOff dOff).trans (Proof.Cmac.xor2Mem_frame _ _ _ _)

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.FinishShort`. -/
section

/-!
# AES-SIV on AArch64: finishing S2V with a string shorter than a block

For a last string `P` of `L < 16` bytes, `shortTail` builds
`pad(P) ⊕ dbl(D)` at `W + 32`: it zeroes the block, copies `P` into it,
appends `0x80`, copies `D` to `W + 144`, doubles it there and XORs it into
the block. `shortMac` finalizes that one complete block from a zero state at
`W + out`, which is then the CMAC of `dbl(D) xor pad(P)`
(`Siv.s2vFinish_short`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 mn dblMem dbl_ok dblMem_bytes dblMem_frame xor2_ok pad_ok)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs Copied copy_ok copyMem copyMem_frame copyMem_bytes toNat_ofNat mz16)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The data and its length, which `finish` keeps. -/
def Hold2 (s s' : State) : Prop := s'.gpr .x26 = s.gpr .x26 ∧ s'.gpr .x27 = s.gpr .x27

theorem Hold2.trans {a b c : State} (h₁ : VG.Proof.AesSiv.AArch64.Hold2 a b) (h₂ : VG.Proof.AesSiv.AArch64.Hold2 b c) : VG.Proof.AesSiv.AArch64.Hold2 a c :=
  ⟨by rw [h₂.1, h₁.1], by rw [h₂.2, h₁.2]⟩

theorem Hold2.of {s s' : State} (h : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x28 → r ≠ .x30 → s'.gpr r = s.gpr r) :
    VG.Proof.AesSiv.AArch64.Hold2 s s' :=
  ⟨h _ (by decide) (by decide) (by decide) (by decide), h _ (by decide) (by decide) (by decide) (by decide)⟩

theorem Hold.hold2 {s s' : State} (h : VG.Proof.AesSiv.AArch64.Hold s s') : VG.Proof.AesSiv.AArch64.Hold2 s s' := ⟨h _ (by decide), h _ (by decide)⟩

/-! ## The tail -/

theorem shortB1_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) :
    ∃ s₁, runBlock isa (zero16 tailOff ++ ([.addImm .x .x6 .x19 tailOff, mov .x7 .x22, mov .x8 .x23] : List Instr))
      s = some s₁ ∧ VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₁ ∧ (∀ r ∈ preserved, s₁.gpr r = s.gpr r) ∧
      s₁.gpr .x6 = W + BitVec.ofNat 64 32 ∧ s₁.gpr .x7 = P ∧ s₁.gpr .x8 = BitVec.ofNat 64 L ∧
      s₁.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 32) := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := tailOff) (by decide) (by decide)
  have x19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), hr.x19]
  refine ⟨_, by
    rw [VG.Proof.AesSiv.AArch64.runBlock_append, run₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, tailOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : (((s₁.write .x .x6 (s₁.gpr .x19 + BitVec.ofNat 64 32)).write .x .x7
      (s₁.gpr .x22 + BitVec.ofNat 64 0)).write .x .x8 (s₁.gpr .x23 + BitVec.ofNat 64 0)).gpr r = s.gpr r := by
    rw [← g₁ r (by rintro rfl; revert hr'; decide)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  refine ⟨hr.keep' (fun r hr' => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) sp₁ rd₁ wr₁, g, by simp [gpr_write, x19₁],
    by simp [gpr_write, g₁ _ (by decide : Reg.x22 ≠ .x9), hr.x22],
    by simp [gpr_write, g₁ _ (by decide : Reg.x23 ≠ .x9), hr.x23], by simp [mem_write, m₁]⟩

/-- The regions `shortTail` writes. -/
abbrev tailRegions (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩]

theorem shortTail_wp (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) (hL : L < 16) :
    WP isa shortTail s fun s' => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      Frame (VG.Proof.AesSiv.AArch64.tailRegions W) s.mem s'.mem ∧
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) := by
  have hwW := h.wW
  have hwD := h.wD
  have hD := h.hD
  obtain ⟨s₁, run₁, hr₁, g₁, x6₁, x7₁, x8₁, m₁⟩ := VG.Proof.AesSiv.AArch64.shortB1_ok h hr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dPT : (⟨P, L⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, L⟩ := h.p_w.sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₁ (by omega) x7₁ x6₁ x8₁
    (fun i hi => h.inRP hr₁.rd hr₁.wr (by omega))
    (fun i hi => by rw [hr₁.wr, Offset.add_add]; exact h.inW rfl (by omega)) dPT) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr' : r ∈ preserved) : s₂.gpr r = s₁.gpr r :=
    h₂.other r (by rintro rfl; revert hr'; decide) (by rintro rfl; revert hr'; decide)
      (by rintro rfl; revert hr'; decide) (by rintro rfl; revert hr'; decide)
  have hr₂ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₂ := hr₁.keep' (fun r hr' => g₂ r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) h₂.sp h₂.rd h₂.wr
  rw [show ([.add .x .x6 .x19 .x23, .addImm .x .x6 .x6 tailOff, .movz .x .x9 0x80 0, .strb .x9 .x6 0] ++
      copy16 dOff dbOff ++ Impl.CmacAes.AArch64.dbl dbOff dbOff ++ xor2 .x19 .x19 .x19 tailOff dbOff tailOff :
        List Instr) = ([.add .x .x6 .x19 .x23, .addImm .x .x6 .x6 tailOff] : List Instr) ++
      (([.movz .x .x9 0x80 0, .strb .x9 .x6 0] : List Instr) ++ (copy16 dOff dbOff ++
        (Impl.CmacAes.AArch64.dbl dbOff dbOff ++ xor2 .x19 .x19 .x19 tailOff dbOff tailOff))) by simp,
    WP.block_append_iff]
  have x19₂ : s₂.gpr .x19 = W := hr₂.x19
  -- The address of the byte after the string.
  refine WP.of_runBlock ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, tailOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  generalize hs₃ : ((s₂.write .x .x6 (s₂.gpr .x19 + s₂.gpr .x23)).write .x .x6
    (s₂.gpr .x19 + s₂.gpr .x23 + BitVec.ofNat 64 32)) = s₃
  have g₃ (r : Reg) (hr' : r ≠ .x6) : s₃.gpr r = s₂.gpr r := by rw [← hs₃]; simp [gpr_write, hr']
  have x6₃ : s₃.gpr .x6 + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L := by
    rw [← hs₃]
    simp only [gpr_write, ite_true, BitVec.setWidth_eq, x19₂, hr₂.x23, BitVec.add_zero]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L), ← BitVec.add_assoc]
  have m₃ : s₃.mem = s₂.mem := by rw [← hs₃]; rfl
  have sp₃ : s₃.sp = s₂.sp := by rw [← hs₃]; rfl
  have rd₃ : s₃.rd = s₂.rd := by rw [← hs₃]; rfl
  have wr₃ : s₃.wr = s₂.wr := by rw [← hs₃]; rfl
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := pad_ok s₃ x6₃
    (by rw [wr₃, hr₂.wr, Offset.add_add]; exact h.inW rfl (by omega))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have x19₄ : s₄.gpr .x19 = W := by rw [g₄ _ (by decide), g₃ _ (by decide), x19₂]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, hr₂.rd]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, hr₂.wr]
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 (dOff + d)) 8 := by
    rw [← Offset.add_add, ← hD]; exact h.inRD rd₄' wr₄' hd
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.AArch64.copy16_ok x19₄ (src := dOff) (dst := dbOff) (by decide) (by decide)
    (by simpa using inD 0 (by decide)) (inD 8 (by decide)) (h.inW wr₄' (by decide)) (h.inW wr₄' (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [WP.block_append_iff]
  have x19₅ : s₅.gpr .x19 = W := by rw [g₅ _ (by decide), x19₄]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  obtain ⟨s₆, run₆, m₆, g₆, sp₆, rd₆, wr₆⟩ := dbl_ok s₅ x19₅ (src := dbOff) (dst := dbOff) (by decide) (by decide)
    (h.inRW rd₅' wr₅' (by decide)) (h.inRW rd₅' wr₅' (by decide)) (h.inW wr₅' (by decide))
    (h.inW wr₅' (by decide))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have x19₆ : s₆.gpr .x19 = W := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), x19₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅']
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅']
  obtain ⟨s₇, run₇, m₇, g₇, sp₇, rd₇, wr₇⟩ := xor2_ok s₆ .x19 .x19 .x19 tailOff dbOff tailOff
    (P := W + BitVec.ofNat 64 32) (Q := W + BitVec.ofNat 64 144) (C := W + BitVec.ofNat 64 32)
    (by decide) (by decide) (by decide) (by rw [x19₆]) (by rw [x19₆, Offset.add_add])
    (by rw [x19₆]) (by rw [x19₆, Offset.add_add]) (by rw [x19₆]) (by rw [x19₆, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (h.inRW rd₆' wr₆' (by decide)) (by rw [Offset.add_add]; exact h.inRW rd₆' wr₆' (by decide))
    (h.inRW rd₆' wr₆' (by decide)) (by rw [Offset.add_add]; exact h.inRW rd₆' wr₆' (by decide))
    (h.inW wr₆' (by decide)) (by rw [Offset.add_add]; exact h.inW wr₆' (by decide))
  refine WP.of_runBlock ⟨s₇, by rw [VG.Proof.AesSiv.AArch64.xor2_eq]; exact run₇, ?_⟩
  -- The registers.
  have g (r : Reg) (hr' : r ∈ preserved) : s₇.gpr r = s.gpr r := by
    have n6 : r ≠ .x6 := by rintro rfl; revert hr'; decide
    have n9 : r ≠ .x9 := by rintro rfl; revert hr'; decide
    have n10 : r ≠ .x10 := by rintro rfl; revert hr'; decide
    have n11 : r ≠ .x11 := by rintro rfl; revert hr'; decide
    have n12 : r ≠ .x12 := by rintro rfl; revert hr'; decide
    rw [g₇ r n9 n10, g₆ r n9 n10 n11 n12, g₅ r n9, g₄ r n9, g₃ r n6, g₂ r hr', g₁ r hr']
  refine ⟨hr.keep' (fun r hr' => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) (by rw [sp₇, sp₆, sp₅, sp₄, sp₃, h₂.sp, hr₁.sp, hr.sp])
    (by rw [rd₇, rd₆', hr.rd]) (by rw [wr₇, wr₆', hr.wr]), g, ?_, ?_⟩
  -- The memory, step by step.
  · have hlen : (Spec.Aes.bytesAt s₁.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have c32 (d n : Nat) (hd : d + n ≤ 16) :
        (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 d) n :=
      Offset.contains_base _ hd (by omega)
    have f₁ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
    have f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₁.mem s₂.mem := by
      rw [h₂.mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; simpa using c32 0 L (by omega))
    have f₄ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
      rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c32 L 1 (by omega))
    have f₅ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₄.mem s₅.mem := by rw [m₅]; exact copyMem_frame _ _ _
    have f₆ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₅.mem s₆.mem := by rw [m₆]; exact dblMem_frame _ _ _ _
    have f₇ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₆.mem s₇.mem := by
      rw [m₇]; exact Proof.Cmac.xor2Mem_frame _ _ _ _
    have sub (rs : List Region) (hs : ∀ r ∈ rs, r ∈ VG.Proof.AesSiv.AArch64.tailRegions W) :
        ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesSiv.AArch64.tailRegions W, Region.Sub r r' :=
      fun r hr => ⟨r, hs r hr, fun _ h => h⟩
    rw [m₃] at f₄
    exact ((((((f₁.sub (sub _ (by simp))).trans (f₂.sub (sub _ (by simp)))).trans (f₄.sub (sub _ (by simp)))).trans
      (f₅.sub (sub _ (by simp)))).trans (f₆.sub (sub _ (by simp)))).trans (f₇.sub (sub _ (by simp))))
  · have hlen : (Spec.Aes.bytesAt s₁.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
        (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
      Offset.disjoint W hs (by omega) (by omega)
    have e8 (d : Nat) : W + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (d + 8) :=
      Offset.add_add _ _ _
    have one (X Y : Region) (hd : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd
    rw [m₇, Proof.Cmac.xor2Mem_bytes _ (by rw [e8]; exact dWW 32 8 40 8 (by omega) (by omega) (by omega))
      (by rw [e8]; exact dWW 32 8 152 8 (by omega) (by omega) (by omega))]
    have t₆ : Spec.Aes.bytesAt s₆.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 := by
      rw [m₆, Proof.Cmac.bytesAt_frame (dblMem_frame _ _ _ _) (one _ _ (dWW 32 16 144 16 (by omega) (by omega)
        (by omega))) (by decide), m₅, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _)
        (one _ _ (dWW 32 16 144 16 (by omega) (by omega) (by omega))) (by decide)]
    have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      rw [m₁]; exact Proof.Cmac.zero2_bytes _ _
    have pad := Proof.Cmac.padded_bytes s₁.mem (W + BitVec.ofNat 64 32) (Spec.Aes.bytesAt s₁.mem P L)
      (by rw [hlen]; exact hL) hz
    rw [hlen] at pad
    have hP : Spec.Aes.bytesAt s₁.mem P L = Spec.Aes.bytesAt s.mem P L := by
      rw [m₁]; exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
        (one _ _ (h.p_w.sub_right (h.sW (by decide)))) (by have := h.lt; omega)
    have dD : (⟨D, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, 16⟩ := h.d_w.sub_right (h.sW (by decide))
    have c₄ : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) 1 :=
      Offset.contains_base (W + BitVec.ofNat 64 32) (d := L) (n := 1) (k := 16) (by omega) (by omega)
    have c₂ : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32)
        (Spec.Aes.bytesAt s₁.mem P L).length := by
      rw [hlen]
      have := Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L) (k := 16) (by omega) (by omega)
      simpa using this
    have q₆ : Spec.Aes.bytesAt s₆.mem (W + BitVec.ofNat 64 144) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s.mem D 16) := by
      rw [m₆, dblMem_bytes, m₅, copyMem_bytes _ (by rw [← hD]; exact (h.d_w.sub_right (h.sW (by decide))).symm),
        ← hD, m₄, Proof.Cmac.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₄)
          (one _ _ dD) (by decide), m₃, h₂.mem,
        Proof.Cmac.bytesAt_frame (writeBytes_frame _ _ _ c₂) (one _ _ dD) (by decide),
        m₁, Proof.Cmac.zero2, Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (one _ _ dD) (by decide)]
    rw [t₆, m₄, m₃, h₂.mem, pad, hP, q₆, Spec.Siv.pad, Proof.Cmac.bytesAt_length,
      show 16 - L - 1 = 15 - L by omega]
    rfl

/-! ## The whole short case -/

/-- The regions `finish` writes: the output, the tail, `dbl(D)` and the
working space of the functions called. -/
abbrev finRegions (W : Addr) (out : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 32, 32⟩, ⟨W + BitVec.ofNat 64 144, 16⟩,
    ⟨W + BitVec.ofNat 64 256, 2176⟩]

/-- What `finish` leaves: S2V's end, from `D` and the data, at `W + out`. -/
structure FinPost (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s'
  hold : VG.Proof.AesSiv.AArch64.Hold2 s s'
  frame : Frame (VG.Proof.AesSiv.AArch64.finRegions W out) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)

theorem macPre_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (shortArgs out) s = some s' ∧ VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R ∧
      s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 out) := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := out) (by omega) (by omega)
  have x19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), hr.x19]
  have hout' : out < 4096 := by omega
  refine ⟨_, by
    rw [shortArgs, VG.Proof.AesSiv.AArch64.runBlock_append, run₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, mov, tailOff, csOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout']
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : ((((((s₁.write .x .x0 (s₁.gpr .x20 + BitVec.ofNat 64 0)).write .x .x1
      (s₁.gpr .x21 + BitVec.ofNat 64 0)).write .x .x2 (s₁.gpr .x19 + BitVec.ofNat 64 out)).write .x .x3
      (s₁.gpr .x19 + BitVec.ofNat 64 32)).write .x .x4 (BitVec.setWidth 64 (16 : BitVec 16) <<< (16 * 0))).write
      .x .x5 (s₁.gpr .x19 + BitVec.ofNat 64 256)).gpr r = s.gpr r := by
    rw [← g₁ r (by rintro rfl; revert hr'; decide)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have hr' := hr.keep' (fun r hr' => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) sp₁ rd₁ wr₁
  refine ⟨hr', g, h.fargs hr'.rd hr'.wr (by omega) (h.srcWork (by omega) (by decide) (by omega)) (by decide)
    (by simp [gpr_write, g₁ _ (by decide : Reg.x20 ≠ .x9), hr.x20])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x21 ≠ .x9), hr.x21])
    (by simp [gpr_write, x19₁]) (by simp [gpr_write, x19₁]) (by simp [gpr_write])
    (by simp [gpr_write, x19₁]), by simp [mem_write, m₁]⟩

theorem finishShort_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State}
    (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq shortTail (shortMac v.ctr.callee v.ctr.suffix out)) s (VG.Proof.AesSiv.AArch64.FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.shortTail_wp h hr hL) fun s₁ ⟨hr₁, g₁, f₁, t₁⟩ => ?_)
  obtain ⟨s₂, run₂, hr₂, g₂, fa₂, m₂⟩ := VG.Proof.AesSiv.AArch64.macPre_ok h hr₁ hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ fa₂) fun s₃ h₃ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s₂.mem s₃.mem := h₃.frame
  have f₁' : Frame (VG.Proof.AesSiv.AArch64.finRegions W out) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have f₂₃ : Frame (VG.Proof.AesSiv.AArch64.finRegions W out) s₁.mem s₃.mem :=
    (f₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp,
      fun _ h => h⟩)
  refine ⟨hr₂.keep h₃.saved h₃.sp h₃.rd h₃.wr,
    Hold2.of fun r hr _ _ h30 => by rw [h₃.saved r hr h30, g₂ r hr, g₁ r hr], f₁'.trans f₂₃, ?_⟩
  -- What the call reads, from the start.
  have fs : Frame (VG.Proof.AesSiv.AArch64.finRegions W out) s.mem s₂.mem :=
    f₁'.trans (f₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame fs (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have tl : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 :=
    Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact Proof.Cmac.zero2_bytes _ _
  have hlen : (Spec.Aes.bytesAt s.mem P L).length < 16 := by rw [Proof.Cmac.bytesAt_length]; exact hL
  have lk1 : (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have lk2 : (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have lm : (Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16))
      (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L))).length = 16 := by
    rw [Siv.length_xor, Siv.length_pad hlen, Spec.Siv.dbl, Proof.Cmac.dbl_length (Proof.Cmac.bytesAt_length _ _ _)]
    rfl
  have split := Siv.cmacWith_split (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (msg := [])
    (last := Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)))
    rfl (by omega) (Or.inl rfl)
  rw [List.nil_append] at split
  have ht : Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) =
      Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) := by
    rw [Siv.xor_eq, Siv.xor_eq, Proof.Cmac.xor_comm]
  rw [h₃.out, mn, sch, k1, k2, tl, t₁, hz, Siv.s2vFinish_short _ _ hlen, Spec.Siv.ctxMac, split,
    Proof.AesSiv.chain_blocks_nil, Proof.AesSiv.xor_zeros (Proof.AesSiv.length_lastBlock lk1 lk2 (by rw [ht]; omega)),
    Proof.Cmac.xor_comm (Spec.Cmac.zeros 16),
    Proof.AesSiv.xor_zeros (Proof.AesSiv.length_lastBlock (Proof.Cmac.bytesAt_length _ _ _)
      (Proof.Cmac.bytesAt_length _ _ _) (by omega)), ht]
  rfl

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.FinishLong`. -/
section

/-!
# AES-SIV on AArch64: finishing S2V with a string of a block or more

For a last string `P` of `L ≥ 16` bytes (`kOf`, `jOf`, `Proof/AesSiv/Long.lean`):
`longTail` computes `16 k` into `x28`, copies the last `T = L − 16 k` bytes
of `P` to the tail at `W + 32` and XORs `D` into its last 16 bytes, so the
tail is `P[16k..] xorend D` (`xorend_mem`); `longMac` chains the `k` blocks
of `P`, computes `j` into `x25`, chains the first `j` blocks of the tail,
and finalizes the rest of the tail (`long_spec`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (kOf jOf kOf_lt kOf_ge kOf_tail jOf_rest jOf_le xorend_mem long_spec)
open VG.Proof.CmacAes.AArch64 (k0 mn xor2_ok)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs FArgs Copied copy_ok toNat_ofNat toNat_add_lt upd_call
  bytesAt_writeBytes_self eval_zero mz0 mz16)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem mz1 : BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 0) = BitVec.ofNat 64 1 := by decide

/-- `(L − 1) >> 4`, the whole blocks before the last 1 to 16 bytes. -/
theorem nb_bv {L : Nat} (h : 0 < L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 1) >>> 4 = BitVec.ofNat 64 ((L - 1) / 16) := by
  rw [VG.Proof.AesSiv.AArch64.ofNat_sub (by omega) hL, VG.Proof.AesSiv.AArch64.lsr4 (by omega)]

/-- `16 k`, as the code computes it for `L ≥ 17`: `((L − 1) >> 4) − 1`, shifted left by 4. -/
theorem kOf_bv {L : Nat} (h : 17 ≤ L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 ((L - 1) / 16) - BitVec.ofNat 64 1) <<< 4 = BitVec.ofNat 64 (16 * kOf L) := by
  rw [kOf_ge (by omega), VG.Proof.AesSiv.AArch64.ofNat_sub (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show (L - 1) / 16 - 1 < 2 ^ 64 by omega)]
  omega

theorem lsl4 {j : Nat} (h : j ≤ 1) : BitVec.ofNat 64 j <<< 4 = BitVec.ofNat 64 (16 * j) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> decide

/-! ## The tail -/

/-- `16 k` in `x28`. -/
theorem kBlock_wp {s : State} (h23 : s.gpr .x23 = BitVec.ofNat 64 L) (hL16 : 16 ≤ L) (hL : L < 2 ^ 64) :
    WP isa kBlock s fun s' =>
      s'.gpr .x28 = BitVec.ofNat 64 (16 * kOf L) ∧ (∀ r, r ≠ .x9 → r ≠ .x28 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [kBlock]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : ((s.write .x .x9 (s.gpr .x23 - BitVec.ofNat 64 1)).write .x .x9
      ((s.gpr .x23 - BitVec.ofNat 64 1) >>> 4)).write .x .x28
      (BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0)) = t
  have x9 : t.gpr .x9 = BitVec.ofNat 64 ((L - 1) / 16) := by
    rw [← ht]; simp [gpr_write, h23, VG.Proof.AesSiv.AArch64.nb_bv (show 0 < L by omega) hL]
  have x9t := x9
  have gt : ∀ r, r ≠ .x9 → r ≠ .x28 → t.gpr r = s.gpr r := fun r a b => by rw [← ht]; simp [gpr_write, a, b]
  have x28t : t.gpr .x28 = 0 := by rw [← ht]; simp [gpr_write]
  have ev := eval_zero (s := t) (r := .x9) (x := (L - 1) / 16) (by omega) x9t
  by_cases h17 : L < 17
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [x28t, kOf_lt h17]; rfl, gt, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl,
      by rw [← ht]; rfl⟩
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨by simp [gpr_write, x9t, VG.Proof.AesSiv.AArch64.kOf_bv (by omega) hL], fun r a b => by simp [gpr_write, a, b, gt r a b],
      by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl⟩

/-- What `longTail` leaves: `16 k` in `x28`, and the tail `P[16k..] xorend D`
at `W + 32`. -/
structure LTail (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s'
  keep : ∀ r ∈ preserved, r ≠ .x28 → s'.gpr r = s.gpr r
  x28 : s'.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)
  frame : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s.mem s'.mem
  tail : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) (L - 16 * kOf L) =
    Spec.Siv.xorend (Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L))
      (Spec.Aes.bytesAt s.mem D 16)

theorem longTail_wp (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) (hL16 : 16 ≤ L) :
    WP isa longTail s (VG.Proof.AesSiv.AArch64.LTail s₀ C D P W R L s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hD := h.hD
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.kBlock_wp hr.x23 hL16 hlt) fun s₁ ⟨x28₁, g₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  have hr₁ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₁ :=
    hr.keep' (fun r hr' => g₁ r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr') (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr')) sp₁ rd₁ wr₁
  -- The arguments of the copy.
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, tailArgs, tailOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize hs₂ : ((s₁.write .x .x6 (s₁.gpr .x19 + BitVec.ofNat 64 32)).write .x .x7
      (s₁.gpr .x22 + s₁.gpr .x28)).write .x .x8 (s₁.gpr .x23 - s₁.gpr .x28) = s₂
  have g₂ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) : s₂.gpr r = s₁.gpr r := by
    rw [← hs₂]; simp [gpr_write, a, b, c]
  have x6₂ : s₂.gpr .x6 = W + BitVec.ofNat 64 32 := by rw [← hs₂]; simp [gpr_write, hr₁.x19]
  have x7₂ : s₂.gpr .x7 = P + BitVec.ofNat 64 (16 * kOf L) := by rw [← hs₂]; simp [gpr_write, hr₁.x22, x28₁]
  have x8₂ : s₂.gpr .x8 = BitVec.ofNat 64 (L - 16 * kOf L) := by
    rw [← hs₂]; simp [gpr_write, hr₁.x23, x28₁, VG.Proof.AesSiv.AArch64.ofNat_sub (show 16 * kOf L ≤ L by omega) hlt]
  have m₂ : s₂.mem = s₁.mem := by rw [← hs₂]; rfl
  have sp₂ : s₂.sp = s₁.sp := by rw [← hs₂]; rfl
  have rd₂ : s₂.rd = s₀.rd := by rw [← hs₂, rd_write, rd_write, rd_write, hr₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [← hs₂, wr_write, wr_write, wr_write, hr₁.wr]
  have dPT : (⟨P + BitVec.ofNat 64 (16 * kOf L), L - 16 * kOf L⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ :=
    (h.p_w.sub_left (h.sP (by omega))).sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₂ (by omega) x7₂ x6₂ x8₂
    (fun i hi => by rw [Offset.add_add]; exact h.inRP rd₂ wr₂ (by omega))
    (fun i hi => by rw [Offset.add_add]; exact h.inW wr₂ (by omega)) dPT) fun s₃ h₃ => ?_)
  have g₃ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) : s₃.gpr r = s₁.gpr r := by
    rw [h₃.other r a b c d, g₂ r a b c]
  have hlen : (Spec.Aes.bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)).length =
      L - 16 * kOf L := Proof.Cmac.bytesAt_length _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₂.mem s₃.mem := by
    rw [h₃.mem]; exact writeBytes_frame _ _ _ (by
      rw [hlen]; simpa using Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L - 16 * kOf L) (k := 32)
        (by omega) (by decide))
  -- `D` into the last block of the tail.
  rw [tailXor, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  generalize hs₄ : (s₃.write .x .x6 (s₃.gpr .x23 - s₃.gpr .x28)).write .x .x6
      (s₃.gpr .x19 + (s₃.gpr .x23 - s₃.gpr .x28)) = s₄
  have x6₄ : s₄.gpr .x6 = W + BitVec.ofNat 64 (L - 16 * kOf L) := by
    rw [← hs₄]
    simp [gpr_write, g₃ .x19 (by decide) (by decide) (by decide) (by decide),
      g₃ .x23 (by decide) (by decide) (by decide) (by decide), g₃ .x28 (by decide) (by decide) (by decide) (by decide),
      hr₁.x19, hr₁.x23, x28₁, VG.Proof.AesSiv.AArch64.ofNat_sub (show 16 * kOf L ≤ L by omega) hlt]
  have g₄ (r : Reg) (a : r ≠ .x6) : s₄.gpr r = s₃.gpr r := by rw [← hs₄]; simp [gpr_write, a]
  have rd₄ : s₄.rd = s₀.rd := by rw [← hs₄, rd_write, rd_write, h₃.rd, rd₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [← hs₄, wr_write, wr_write, h₃.wr, wr₂]
  have eT : W + BitVec.ofNat 64 (L - 16 * kOf L) + BitVec.ofNat 64 16 =
      W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) := by
    rw [Offset.add_add, Offset.add_add, show L - 16 * kOf L + 16 = 32 + (L - 16 * kOf L - 16) by omega]
  have eT8 : W + BitVec.ofNat 64 (L - 16 * kOf L) + BitVec.ofNat 64 (16 + 8) =
      W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) + BitVec.ofNat 64 8 := by
    rw [Offset.add_add, Offset.add_add, Offset.add_add]
    exact congrArg (fun n => W + BitVec.ofNat 64 n) (by omega)
  have iW (d : Nat) (hd : d + 8 ≤ 64) : InRegions s₄.wr (W + BitVec.ofNat 64 d) 8 := h.inW wr₄ (by omega)
  have iRW (d : Nat) (hd : d + 8 ≤ 64) : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 d) 8 :=
    h.inRW rd₄ wr₄ (by omega)
  have eA : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) =
      W + BitVec.ofNat 64 (L - 16 * kOf L + 16) := by
    rw [Offset.add_add, show 32 + (L - 16 * kOf L - 16) = L - 16 * kOf L + 16 by omega]
  have eA8 : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16) + BitVec.ofNat 64 8 =
      W + BitVec.ofNat 64 (L - 16 * kOf L + 24) := by
    rw [eA, Offset.add_add]
  have x19₄ : s₄.gpr .x19 = W := by
    rw [g₄ _ (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide), hr₁.x19]
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := xor2_ok s₄ .x6 .x19 .x6 16 dOff 16
    (P := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16)) (Q := D)
    (C := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (L - 16 * kOf L - 16))
    (by decide) (by decide) (by decide) (by rw [x6₄, eT]) (by rw [x6₄, eT8])
    (by rw [x19₄, hD]) (by rw [x19₄, hD, Offset.add_add]) (by rw [x6₄, eT]) (by rw [x6₄, eT8])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [eA]; exact iRW _ (by omega)) (by rw [eA8]; exact iRW _ (by omega))
    (by have := h.inRD rd₄ wr₄ (d := 0) (n := 8) (by decide); rwa [k0] at this)
    (h.inRD rd₄ wr₄ (by decide))
    (by rw [eA]; exact iW _ (by omega)) (by rw [eA8]; exact iW _ (by omega))
  refine WP.of_runBlock ⟨s₅, by rw [VG.Proof.AesSiv.AArch64.xor2_eq]; exact run₅, ?_⟩
  have f₅ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact (Proof.Cmac.xor2Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, List.mem_singleton_self _,
        Offset.sub_base (W + BitVec.ofNat 64 32) (d := L - 16 * kOf L - 16) (n := 16) (k := 32) (by omega)⟩
  have keep (r : Reg) (hr' : r ∈ preserved) (h28 : r ≠ .x28) : s₅.gpr r = s.gpr r := by
    have a : r ≠ .x6 := by rintro rfl; revert hr'; decide
    have b : r ≠ .x7 := by rintro rfl; revert hr'; decide
    have c : r ≠ .x8 := by rintro rfl; revert hr'; decide
    have d : r ≠ .x9 := by rintro rfl; revert hr'; decide
    have e : r ≠ .x10 := by rintro rfl; revert hr'; decide
    rw [g₅ r d e, g₄ r a, g₃ r a b c d, g₁ r d h28]
  refine ⟨hr.keep' (fun r hr' => keep r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr') (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr'))
      (by rw [sp₅, ← hs₄]; simp only [sp_write]; rw [h₃.sp, sp₂, sp₁]) (by rw [rd₅, rd₄, hr.rd])
      (by rw [wr₅, wr₄, hr.wr]), keep,
    by rw [g₅ _ (by decide) (by decide), g₄ _ (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      x28₁], ?_, ?_⟩
  · have m₄ : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
    rw [← m₁, ← m₂]
    exact f₃.trans (by rw [← m₄]; exact f₅)
  · have tD : (⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ : Region).Disjoint ⟨D, 16⟩ :=
      (h.d_w.sub_right (h.sW (by omega))).symm
    have dD (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 32, 32⟩ : Region)]) : (⟨D, 16⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))
    have m₄ : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
    have ws := bytesAt_writeBytes_self s₂.mem (W + BitVec.ofNat 64 32)
      (xs := Spec.Aes.bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)) (by rw [hlen]; omega)
    rw [hlen] at ws
    rw [m₅, xorend_mem _ hT.1 (by rw [toNat_add_lt W hwW (show 32 < 2560 by decide)]; omega) tD, m₄,
      Proof.Cmac.bytesAt_frame f₃ dD (by decide), h₃.mem, ws, m₂, m₁]

/-! ## The calls -/

/-- The arguments of the update over the `k` blocks of `P`. -/
theorem m1_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L) (h28 : s.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)) :
    ∃ s', runBlock isa (longArgs₁ out) s = some s' ∧ VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      UArgs s' C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧
      s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 out) := by
  have hT := kOf_tail hL16
  have hlt := h.lt
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := out) (by omega) (by omega)
  have hout' : out < 4096 := by omega
  refine ⟨_, by
    rw [longArgs₁, VG.Proof.AesSiv.AArch64.runBlock_append, run₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, csOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout']
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : ((((((s₁.write .x .x4 (s₁.gpr .x28 >>> 4)).write .x .x0
      (s₁.gpr .x20 + BitVec.ofNat 64 0)).write .x .x1 (s₁.gpr .x21 + BitVec.ofNat 64 0)).write .x .x2
      (s₁.gpr .x19 + BitVec.ofNat 64 out)).write .x .x3 (s₁.gpr .x22 + BitVec.ofNat 64 0)).write .x .x5
      (s₁.gpr .x19 + BitVec.ofNat 64 256)).gpr r = s.gpr r := by
    rw [← g₁ r (by rintro rfl; revert hr'; decide)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have hr' := hr.keep' (fun r hr' => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) sp₁ rd₁ wr₁
  have x19 : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), hr.x19]
  refine ⟨hr', g, h.uargs hr'.rd hr'.wr (by omega) (h.srcData₀ (by omega) (by omega)) (by omega)
    (by simp [gpr_write, g₁ _ (by decide : Reg.x20 ≠ .x9), hr.x20])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x21 ≠ .x9), hr.x21]) (by simp [gpr_write, x19])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x22 ≠ .x9), hr.x22])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x28 ≠ .x9), h28, VG.Proof.AesSiv.AArch64.lsr4 (show 16 * kOf L < 2 ^ 64 by omega)])
    (by simp [gpr_write, x19]), by simp [mem_write, m₁]⟩

/-- `j` in `x25`. -/
theorem jBlock_wp {s : State} (h23 : s.gpr .x23 = BitVec.ofNat 64 L) (hL16 : 16 ≤ L) (hL : L < 2 ^ 64) :
    WP isa jBlock s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (jOf L) ∧ (∀ r, r ≠ .x9 → r ≠ .x25 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [jBlock]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : ((s.write .x .x9 (s.gpr .x23 - BitVec.ofNat 64 1)).write .x .x9
      ((s.gpr .x23 - BitVec.ofNat 64 1) >>> 4)).write .x .x25
      (BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0)) = t
  have x9t : t.gpr .x9 = BitVec.ofNat 64 ((L - 1) / 16) := by
    rw [← ht]; simp [gpr_write, h23, VG.Proof.AesSiv.AArch64.nb_bv (show 0 < L by omega) hL]
  have gt : ∀ r, r ≠ .x9 → r ≠ .x25 → t.gpr r = s.gpr r := fun r a b => by rw [← ht]; simp [gpr_write, a, b]
  have x25t : t.gpr .x25 = 0 := by rw [← ht]; simp [gpr_write]
  have ev := eval_zero (s := t) (r := .x9) (x := (L - 1) / 16) (by omega) x9t
  by_cases h17 : L < 17
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [x25t]; simp [jOf, h17], gt, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl,
      by rw [← ht]; rfl⟩
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ]
      rfl, ?_⟩
    refine ⟨by simp [gpr_write, jOf, h17], fun r a b => by simp [gpr_write, b, gt r a b],
      by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl⟩

/-- The arguments of the update over the first `j` blocks of the tail. -/
theorem m3_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (h25 : s.gpr .x25 = BitVec.ofNat 64 (jOf L)) :
    ∃ s', runBlock isa (longArgs₂ out) s = some s' ∧ VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      UArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) := by
  have hj := jOf_le L
  have hout' : out < 4096 := by omega
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, longArgs₂, mov, tailOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout']
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : ((((((s.write .x .x4 (s.gpr .x25 + BitVec.ofNat 64 0)).write .x .x0
      (s.gpr .x20 + BitVec.ofNat 64 0)).write .x .x1 (s.gpr .x21 + BitVec.ofNat 64 0)).write .x .x2
      (s.gpr .x19 + BitVec.ofNat 64 out)).write .x .x3 (s.gpr .x19 + BitVec.ofNat 64 32)).write .x .x5
      (s.gpr .x19 + BitVec.ofNat 64 256)).gpr r = s.gpr r := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have hr' := hr.keep' (fun r hr' => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) rfl rfl rfl
  exact ⟨hr', g, rfl, h.uargs hr'.rd hr'.wr (by omega)
    (h.srcWork (o := out) (t := 32) (n := 16 * jOf L) (by omega) (by omega) (by omega)) (by omega)
    (by simp [gpr_write, hr.x20]) (by simp [gpr_write, hr.x21]) (by simp [gpr_write, hr.x19])
    (by simp [gpr_write, hr.x19]) (by simp [gpr_write, h25]) (by simp [gpr_write, hr.x19])⟩

/-- The arguments of the finalization of the rest of the tail. -/
theorem m4_run (s : State) {out : Nat} (hout : out < 4096) :
    ∃ s', runBlock isa (longArgs₃ out) s = some s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.gpr .x0 = s.gpr .x20 ∧ s'.gpr .x1 = s.gpr .x21 ∧ s'.gpr .x2 = s.gpr .x19 + BitVec.ofNat 64 out ∧
      s'.gpr .x3 = s.gpr .x19 + BitVec.ofNat 64 32 + s.gpr .x25 <<< 4 ∧
      s'.gpr .x4 = s.gpr .x23 - s.gpr .x28 - s.gpr .x25 <<< 4 ∧ s'.gpr .x5 = s.gpr .x19 + BitVec.ofNat 64 256 ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, longArgs₃, mov, tailOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem m4_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L) (h28 : s.gpr .x28 = BitVec.ofNat 64 (16 * kOf L))
    (h25 : s.gpr .x25 = BitVec.ofNat 64 (jOf L)) :
    ∃ s', runBlock isa (longArgs₃ out) s = some s' ∧ VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R := by
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  have hlt := h.lt
  obtain ⟨s', run, g, x0, x1, x2, x3, x4, x5, sp, m, rd, wr⟩ := VG.Proof.AesSiv.AArch64.m4_run s (out := out) (by omega)
  have hr' := hr.keep' (fun r hr' => g r (VG.Proof.AesSiv.AArch64.dec_mem (by decide) hr')) sp rd wr
  refine ⟨s', run, hr', g, m, h.fargs hr'.rd hr'.wr (by omega)
    (h.srcWork (o := out) (t := 32 + 16 * jOf L) (n := L - 16 * kOf L - 16 * jOf L) (by omega) (by omega)
      (by omega)) (by omega) (by rw [x0, hr.x20]) (by rw [x1, hr.x21]) (by rw [x2, hr.x19])
    (by rw [x3, hr.x19, h25, VG.Proof.AesSiv.AArch64.lsl4 hj1, Offset.add_add]) ?_ (by rw [x5, hr.x19])⟩
  rw [x4, hr.x23, h28, h25, VG.Proof.AesSiv.AArch64.lsl4 hj1, VG.Proof.AesSiv.AArch64.ofNat_sub (show 16 * kOf L ≤ L by omega) hlt,
    VG.Proof.AesSiv.AArch64.ofNat_sub (show 16 * jOf L ≤ L - 16 * kOf L by omega) (by omega)]

/-! ## The whole long case -/

/-- The regions `longMac` writes. -/
abbrev macRegions (W : Addr) (out : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩]

/-- What `longMac` leaves: CMAC's last step on the tail's last bytes, after the
`k` blocks of `P` and the first `j` blocks of the tail, all as they were. -/
structure LMac (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s'
  hold : VG.Proof.AesSiv.AArch64.Hold2 s s'
  frame : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16)
          (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16)
          (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (L - 16 * kOf L - 16 * jOf L)))
        (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1))))
          (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))) (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem P (16 * kOf L))))
          (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 32) (16 * jOf L)))))

theorem longMac_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s₁ : State}
    (hr₁ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₁) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112)
    (h28 : s₁.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)) :
    WP isa (longMac v.callee v.ctr.callee v.ctr.suffix out) s₁ (VG.Proof.AesSiv.AArch64.LMac s₀ C D P W R L out s₁) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₂, run₂, hr₂, g₂, u₂, m₂⟩ := VG.Proof.AesSiv.AArch64.m1_ok h hr₁ hout hL16 h28
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₂) fun s₃ h₃ => ?_)
  have hr₃ := hr₂.keep h₃.saved h₃.sp h₃.rd h₃.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.jBlock_wp hr₃.x23 hL16 hlt) fun s₄ ⟨x25₄, g₄, sp₄, m₄, rd₄, wr₄⟩ => ?_)
  have hr₄ := hr₃.keep' (fun r hr' => g₄ r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr') (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr')) sp₄ rd₄ wr₄
  obtain ⟨s₅, run₅, hr₅, g₅, m₅, u₅⟩ := VG.Proof.AesSiv.AArch64.m3_ok h hr₄ hout x25₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₅) fun s₆ h₆ => ?_)
  have hr₆ := hr₅.keep h₆.saved h₆.sp h₆.rd h₆.wr
  have x28₆ : s₆.gpr .x28 = BitVec.ofNat 64 (16 * kOf L) := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide), g₄ _ (by decide) (by decide),
      h₃.saved _ (by decide) (by decide), g₂ _ (by decide), h28]
  have x25₆ : s₆.gpr .x25 = BitVec.ofNat 64 (jOf L) := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide), x25₄]
  obtain ⟨s₇, run₇, hr₇, g₇, m₇, fa₇⟩ := VG.Proof.AesSiv.AArch64.m4_ok h hr₆ hout hL16 x28₆ x25₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ fa₇) fun s₈ h₈ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₂.mem s₃.mem := h₃.frame
  have f₆ : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₅.mem s₆.mem := h₆.frame
  have f₈ : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₇.mem s₈.mem := h₈.frame
  have F₂ : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₁.mem s₂.mem := f₂.mono (by simp)
  have g₂₅ : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₁.mem s₅.mem := by
    rw [m₅, m₄]; exact F₂.trans f₃
  have g₂₇ : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₁.mem s₇.mem := by rw [m₇]; exact g₂₅.trans f₆
  refine ⟨hr₇.keep h₈.saved h₈.sp h₈.rd h₈.wr, Hold2.of fun r hr h25 h28 h30 => ?_, g₂₇.trans f₈, ?_⟩
  · have n9 : r ≠ .x9 := by rintro rfl; revert hr; decide
    rw [h₈.saved r hr h30, g₇ r hr, h₆.saved r hr h30, g₅ r hr, g₄ r n9 h25, h₃.saved r hr h30, g₂ r hr]
  have dC {m : Mem} (hm : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₁.mem m) {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt m (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame hm (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))) (by omega)
  have dP {m : Mem} (hm : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₁.mem m) {d n : Nat} (hd : d + n ≤ L) :
      Spec.Aes.bytesAt m (P + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (P + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame hm (fun r hr => by
      have hc := h.p_w.sub_left (h.sP hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))) (by omega)
  have dT {m : Mem} (hm : Frame (VG.Proof.AesSiv.AArch64.macRegions W out) s₁.mem m) {d n : Nat} (hd : 32 ≤ d) (hd' : d + n ≤ 64) :
      Spec.Aes.bytesAt m (W + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)) (by omega)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact Proof.Cmac.zero2_bytes _ _
  have sch₂ := dC F₂ (d := 0) (n := 16 * (R + 1)) (by omega)
  have sch₅ := dC g₂₅ (d := 0) (n := 16 * (R + 1)) (by omega)
  have sch₇ := dC g₂₇ (d := 0) (n := 16 * (R + 1)) (by omega)
  rw [k0] at sch₂ sch₅ sch₇
  have k1 := dC g₂₇ (d := 240) (n := 16) (by decide)
  have k2 := dC g₂₇ (d := 256) (n := 16) (by decide)
  have pk := dP F₂ (d := 0) (n := 16 * kOf L) (by omega)
  rw [k0] at pk
  have t₅ := dT g₂₅ (d := 32) (n := 16 * jOf L) (by decide) (by omega)
  have t₇ := dT g₂₇ (d := 32 + 16 * jOf L) (n := L - 16 * kOf L - 16 * jOf L) (by omega) (by omega)
  rw [h₈.out, mn, sch₇, k1, k2, t₇, m₇, h₆.out, Proof.Cmac.Stream.blocksAt_eq, sch₅, t₅, m₅, m₄, h₃.out,
    Proof.Cmac.Stream.blocksAt_eq, sch₂, pk, hz]

theorem finishLong_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State}
    (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq longTail (longMac v.callee v.ctr.callee v.ctr.suffix out)) s (VG.Proof.AesSiv.AArch64.FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.longTail_wp h hr hL16) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.AesSiv.AArch64.longMac_wp v h h₁.regs hL16 hout h₁.x28) fun s₂ h₂ => ?_
  have f₁ : Frame (VG.Proof.AesSiv.AArch64.finRegions W out) s.mem s₁.mem := h₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have f₂ : Frame (VG.Proof.AesSiv.AArch64.finRegions W out) s₁.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨h₂.regs, (Hold2.of fun r hr _ h28 _ => h₁.keep r hr h28).trans h₂.hold, f₁.trans f₂, ?_⟩
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have pk : Spec.Aes.bytesAt s₁.mem P (16 * kOf L) = Spec.Aes.bytesAt s.mem P (16 * kOf L) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.p_w.sub_left (Region.sub_prefix (by omega))).sub_right (h.sW (by decide))) (by omega)
  -- The tail, as the calls read it.
  have hTsplit : L - 16 * kOf L = 16 * jOf L + (L - 16 * kOf L - 16 * jOf L) := by omega
  have tk := Proof.AesSiv.take_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * jOf L)
    (b := L - 16 * kOf L - 16 * jOf L)
  have dr := Proof.AesSiv.drop_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * jOf L)
    (b := L - 16 * kOf L - 16 * jOf L)
  rw [← hTsplit, h₁.tail] at tk dr
  rw [Offset.add_add] at dr
  have hLsplit : L = 16 * kOf L + (L - 16 * kOf L) := by omega
  have pt := Proof.AesSiv.take_bytesAt s.mem P (a := 16 * kOf L) (b := L - 16 * kOf L)
  have pd := Proof.AesSiv.drop_bytesAt s.mem P (a := 16 * kOf L) (b := L - 16 * kOf L)
  rw [← hLsplit] at pt pd
  have hlP : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hs := long_spec (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)
    (Proof.Cmac.bytesAt_length _ _ _) (by rw [hlP]; exact hL16)
  rw [hlP, pt, pd] at hs
  rw [h₂.out, sch, k1, k2, ← dr, ← tk, pk, Spec.Siv.ctxMac, ← hs]
  rfl

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Finish`. -/
section

/-!
# AES-SIV on AArch64: finishing S2V (`finish`)

`finish` branches on `L >> 4` to the short case (`finishShort_wp`) or the
long one (`finishLong_wp`), which leave S2V's end at `W + out`. Every
branch and loop in it is on `L`, and the arguments of its calls are the same
in two runs with the same pointers and lengths (`finish_rel`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.AesSiv (kOf jOf kOf_tail jOf_rest jOf_le)
open VG.Proof.CmacAes.AArch64 (agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs FArgs toNat_ofNat upd_call upd_rel fin_rel eval_zero)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem lsrL_ok {s : State} (h23 : s.gpr .x23 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.lsr .x .x9 .x23 4] s = some s' ∧ s'.gpr .x9 = BitVec.ofNat 64 (L / 16) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, BitVec.setWidth_eq]
    rfl, ?_⟩
  exact ⟨by simp [gpr_write, h23, VG.Proof.AesSiv.AArch64.lsr4 hL], fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

theorem FinPost.of_mem {s₁ s s' : State} {out : Nat} (hm : s₁.mem = s.mem) (hg : VG.Proof.AesSiv.AArch64.Hold2 s s₁)
    (h : VG.Proof.AesSiv.AArch64.FinPost s₀ C D P W R L out s₁ s') : VG.Proof.AesSiv.AArch64.FinPost s₀ C D P W R L out s s' :=
  ⟨h.regs, hg.trans h.hold, hm ▸ h.frame, hm ▸ h.out⟩

theorem finish_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State}
    (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.ctr.callee v.ctr.suffix out) s (VG.Proof.AesSiv.AArch64.FinPost s₀ C D P W R L out s) := by
  obtain ⟨s₁, run₁, x9₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.AArch64.lsrL_ok hr.x23 h.lt
  have hr₁ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₁ := hr.keep' (fun r hr' => g₁ r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr')) sp₁ rd₁ wr₁
  have hg₁ : VG.Proof.AesSiv.AArch64.Hold2 s s₁ := ⟨g₁ _ (by decide), g₁ _ (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ev := eval_zero (s := s₁) (r := .x9) (x := L / 16) (by have := h.lt; omega) x9₁
  by_cases hL : L < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    exact WP.mono (VG.Proof.AesSiv.AArch64.finishShort_wp v h hr₁ hL hout) fun _ p => p.of_mem m₁ hg₁
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) (fun _ => ?_)
    exact WP.mono (VG.Proof.AesSiv.AArch64.finishLong_wp v h hr₁ (by omega) hout) fun _ p => p.of_mem m₁ hg₁

/-! ## Constant time -/

/-- The pair of runs, with the same arguments. -/
abbrev RR (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b

/-- `regs_agree`, with other registers whose values both runs know. -/
theorem regs_agree' {s₀ s₀' a b : State} (hq : s₀.sp = s₀'.sp) (ha : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a)
    (hb : VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b) {rs : List Reg} (hrs : ∀ r ∈ rs, a.gpr r = b.gpr r) :
    taint.Agree (Taint.ofRegs (([.x19, .x20, .x21, .x22, .x23] : List Reg) ++ rs)) a b := by
  refine VG.Proof.CmacAes.AArch64.agree_of (by rw [ha.sp, hb.sp, hq]) fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ha.x19, hb.x19]
    · rw [ha.x20, hb.x20]
    · rw [ha.x21, hb.x21]
    · rw [ha.x22, hb.x22]
    · rw [ha.x23, hb.x23]
  · exact hrs r hr

theorem short_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) (.seq shortTail (shortMac v.ctr.callee v.ctr.suffix out))
      (VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) shortTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hB' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block (shortArgs o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ := hB' out hout
  have t₁ := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.AArch64.shortTail_wp h hab.1 hL) fun _ p => p.1, WP.mono (VG.Proof.AesSiv.AArch64.shortTail_wp h' hab.2 hL) fun _ p => p.1⟩
  have mpre {σ x : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) :
      WP isa (.block (shortArgs out)) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R := by
    obtain ⟨y, run, hy, _, fa, _⟩ := VG.Proof.AesSiv.AArch64.macPre_ok hσ hx hout
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have t₂ := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1 hab.2)
    hB).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨mpre h hab.1, mpre h' hab.2⟩
  have t₃ := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun a b => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R) ∧
      VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R)
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.sp p.rd p.wr,
      WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.sp p.rd p.wr⟩
  exact (t₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((t₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (t₃.mono (fun _ _ h => h) fun _ _ h => h.2))

theorem long_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) (.seq longTail (longMac v.callee v.ctr.callee v.ctr.suffix out))
      (VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) := by
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  obtain ⟨_, hT₀⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) longTail
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM1' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs ([.x19, .x20, .x21, .x22, .x23] ++
      [.x28])) (.block (longArgs₁ o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM1⟩ := hM1' out hout
  obtain ⟨_, hJb⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) jBlock
      hc).isSome = true := ⟨_, by taint_decide⟩
  have hM2' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs ([.x19, .x20, .x21, .x22, .x23] ++
      [.x25])) (.block (longArgs₂ o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM2⟩ := hM2' out hout
  have hM3' : ∀ o : Nat, o = 0 ∨ o = 112 → ∃ hc, (taint.check (Taint.ofRegs ([.x19, .x20, .x21, .x22, .x23] ++
      [.x25, .x28])) (.block (longArgs₃ o)) hc).isSome = true := by
    rintro o (rfl | rfl)
    · exact ⟨_, by taint_decide⟩
    · exact ⟨_, by taint_decide⟩
  obtain ⟨_, hM3⟩ := hM3' out hout
  -- What each run keeps between the pieces.
  let K := fun (x : State) => x.gpr .x28 = BitVec.ofNat 64 (16 * kOf L)
  let J := fun (x : State) => x.gpr .x25 = BitVec.ofNat 64 (jOf L)
  have wT {σ x : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) :
      WP isa longTail x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧ K y :=
    WP.mono (VG.Proof.AesSiv.AArch64.longTail_wp hσ hx hL16) fun _ p => ⟨p.regs, p.x28⟩
  have wM1 {σ x : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) (hk : K x) :
      WP isa (.block (longArgs₁ out)) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K y := by
    obtain ⟨y, run, hy, g, u, _⟩ := VG.Proof.AesSiv.AArch64.m1_ok hσ hx hout hL16 hk
    exact WP.of_runBlock ⟨y, run, hy, u, by show y.gpr .x28 = _; rw [g _ (by decide)]; exact hk⟩
  have wU1 {σ x : State} (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L)) (hk : K x) :
      WP isa (callUpdate v.callee) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧ K y :=
    WP.mono (upd_call v _ hu) fun y p => ⟨hx.keep p.saved p.sp p.rd p.wr,
      by show y.gpr .x28 = _; rw [p.saved _ (by decide) (by decide)]; exact hk⟩
  have wJ {σ x : State} (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) (hk : K x) :
      WP isa jBlock x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧ K y ∧ J y :=
    WP.mono (VG.Proof.AesSiv.AArch64.jBlock_wp hx.x23 hL16 hlt) fun y ⟨x25, g, sp, _, rd, wr⟩ =>
      ⟨hx.keep' (fun r hr => g r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr)) sp rd wr,
        by show y.gpr .x28 = _; rw [g _ (by decide) (by decide)]; exact hk, x25⟩
  have wM2 {σ x : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) (hk : K x) (hj : J x) :
      WP isa (.block (longArgs₂ out)) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧
        UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧
        K y ∧ J y := by
    obtain ⟨y, run, hy, g, _, u⟩ := VG.Proof.AesSiv.AArch64.m3_ok hσ hx hout hj
    exact WP.of_runBlock ⟨y, run, hy, u, by show y.gpr .x28 = _; rw [g _ (by decide)]; exact hk,
      by show y.gpr .x25 = _; rw [g _ (by decide)]; exact hj⟩
  have wU2 {σ x : State} (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x)
      (hu : UArgs x C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L))
      (hk : K x) (hj : J x) :
      WP isa (callUpdate v.callee) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧ K y ∧ J y :=
    WP.mono (upd_call v _ hu) fun y p => ⟨hx.keep p.saved p.sp p.rd p.wr,
      by show y.gpr .x28 = _; rw [p.saved _ (by decide) (by decide)]; exact hk,
      by show y.gpr .x25 = _; rw [p.saved _ (by decide) (by decide)]; exact hj⟩
  have wM3 {σ x : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) (hk : K x) (hj : J x) :
      WP isa (.block (longArgs₃ out)) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧
        FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
          (L - 16 * kOf L - 16 * jOf L) R := by
    obtain ⟨y, run, hy, _, _, fa⟩ := VG.Proof.AesSiv.AArch64.m4_ok hσ hx hout hL16 hk hj
    exact WP.of_runBlock ⟨y, run, hy, fa⟩
  have kk {a b : State} (ha : K a) (hb : K b) : a.gpr .x28 = b.gpr .x28 := by rw [ha, hb]
  have jj {a b : State} (ha : J a) (hb : J b) : a.gpr .x25 = b.gpr .x25 := by rw [ha, hb]
  -- The relations, segment by segment.
  have rT := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1 hab.2)
    hT₀).wp (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧ K y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧ K y)
    fun a b hab => ⟨wT h hab.1, wT h' hab.2⟩
  have rM1 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ K a) ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ K b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact kk hab.1.2 hab.2.2) hM1).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K y)
    fun a b hab => ⟨wM1 h hab.1.1 hab.1.2, wM1 h' hab.2.1 hab.2.2⟩
  have rU1 := (upd_rel v v.callee.name
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K a) ∧
      VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ UArgs b C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧ K b)
    fun a b hab => ⟨hab.1.2.1, hab.2.2.1, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧ K y) (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧ K y)
    fun a b hab => ⟨wU1 hab.1.1 hab.1.2.1 hab.1.2.2, wU1 hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rJ := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ K a) ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ K b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1.1 hab.2.1) hJb).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧ K y ∧ J y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧ K y ∧ J y)
    fun a b hab => ⟨wJ hab.1.1 hab.1.2, wJ hab.2.1 hab.2.2⟩
  have rM2 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ K a ∧ J a) ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ K b ∧ J b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact jj hab.1.2.2 hab.2.2.2) hM2).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K y ∧ J y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧
      UArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K y ∧ J y)
    fun a b hab => ⟨wM2 h hab.1.1 hab.1.2.1 hab.1.2.2, wM2 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rU2 := (upd_rel v v.callee.name
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K a ∧ J a) ∧
      VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧ K b ∧ J b)
    fun a b hab => ⟨hab.1.2.1, hab.2.2.1, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧ K y ∧ J y)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧ K y ∧ J y)
    fun a b hab => ⟨wU2 hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2, wU2 hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩
  have rM3 := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ K a ∧ J a) ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ K b ∧ J b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact jj hab.1.2.2 hab.2.2.2
      · exact kk hab.1.2.1 hab.2.2.1) hM3).wp
    (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧
      FArgs y C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨wM3 h hab.1.1 hab.1.2.1 hab.1.2.2, wM3 h' hab.2.1 hab.2.2.1 hab.2.2.2⟩
  have rF := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun (a b : State) => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R) ∧ VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R)
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ hab.1.2) fun _ p => hab.1.1.keep p.saved p.sp p.rd p.wr,
      WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ hab.2.2) fun _ p => hab.2.1.keep p.saved p.sp p.rd p.wr⟩
  exact (rT.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rM1.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rU1.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rJ.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rM2.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((rU2.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((rM3.mono (fun _ _ h => h) fun _ _ h => h.2).seq (rF.mono (fun _ _ h => h) fun _ _ h => h.2)))))))

theorem finish_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) {out : Nat} (hout : out = 0 ∨ out = 112) :
    RelCT isa (VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) (finish v.callee v.ctr.callee v.ctr.suffix out) (VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block [.lsr .x .x9 .x23 4]) hc).isSome = true := ⟨_, by taint_decide⟩
  have w {σ x : State} (hx : VG.Proof.AesSiv.AArch64.Regs σ C D P W R L x) :
      WP isa (.block [.lsr .x .x9 .x23 4]) x fun y => VG.Proof.AesSiv.AArch64.Regs σ C D P W R L y ∧
        y.gpr .x9 = BitVec.ofNat 64 (L / 16) := by
    obtain ⟨y, run, x9, g, sp, _, rd, wr⟩ := VG.Proof.AesSiv.AArch64.lsrL_ok hx.x23 h.lt
    exact WP.of_runBlock ⟨y, run, hx.keep' (fun r hr => g r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr)) sp rd wr, x9⟩
  have a := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.AArch64.RR s₀ s₀' C D P W R L) _ (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1 hab.2)
    hA).wp (F₁ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L y ∧ y.gpr .x9 = BitVec.ofNat 64 (L / 16))
    (F₂ := fun (y : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L y ∧ y.gpr .x9 = BitVec.ofNat 64 (L / 16))
    fun a b hab => ⟨w hab.1, w hab.2⟩
  have ev {y : State} (hy : y.gpr .x9 = BitVec.ofNat 64 (L / 16)) :=
    eval_zero (s := y) (r := .x9) (x := L / 16) (by have := h.lt; omega) hy
  refine (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq (RelCT.ite (fun a b hab => by
    rw [ev hab.1.2, ev hab.2.2]) ?_ ?_)
  · by_cases hL : L < 16
    · exact (VG.Proof.AesSiv.AArch64.short_rel v h h' hq hL hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [ev hab.1.1.2] at e; simp at e; omega
  · by_cases hL : L < 16
    · exact RelCT.of_false fun a b hab => by
        have e := hab.2; rw [ev hab.1.1.2] at e; simp at e; omega
    · exact (VG.Proof.AesSiv.AArch64.long_rel v h h' hq (by omega) hout).mono (fun _ _ p => ⟨p.1.1.1, p.1.2.1⟩) fun _ _ p => p

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Ctr`. -/
section

/-!
# AES-SIV on AArch64: CTR (`ctr`)

Each block: the counter `Q + i` (two byte-reversed words at `W + 64`) is
copied to the counter block at `W + 96`, `vg_aes_ctr32` writes its cipher to
the zeroed keystream block at `W + 80`, its first `min(16, left)` bytes are
XORed into the data a byte at a time (`xorBytes_wp`), and the counter is
incremented as a 128-bit integer (`inc_words`). After block `i` the data is
CTR's output on its first `16 (i + 1)` bytes (`ctrPart_step`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (ctrPart ctrPart_zero ctrPart_all ctrPart_step length_ctrPart be128_add take_bytesAt)
open VG.Proof.CmacAes.AArch64 (k0 CallPre CallPost ctr_call ctr_rel read_one succ_ofNat ofNat_ne_zero
  le8_rev)
open VG.Proof.CmacAes.Stream.AArch64 (copyMem copyMem_frame copyMem_bytes toNat_ofNat toNat_add_lt eval_zero
  eval_nonzero mz0 mz1 mz16)
open VG.Proof.Gcm.AArch64 (rev64_rev64)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## XORing a keystream block into the data -/

/-- The loop body of `xorBytes`. -/
abbrev xorBody : List Instr :=
  [.ldrb .x9 .x6 0, .ldrb .x10 .x7 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x6 0,
    .addImm .x .x6 .x6 1, .addImm .x .x7 .x7 1, .subImm .x .x8 .x8 1]

theorem byte_xor (a b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a) ^^^
      BitVec.setWidth 64 (BitVec.setWidth 32 b))) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem xorStep_ok (s : State) {A B : Addr} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x7 + BitVec.ofNat 64 0 = B) (ra : InRegions (s.rd ++ s.wr) A 1)
    (rb : InRegions (s.rd ++ s.wr) B 1) (wa : InRegions s.wr A 1) :
    ∃ s', runBlock isa VG.Proof.AesSiv.AArch64.xorBody s = some s' ∧ s'.mem = s.mem.writeW A ((s.mem A ^^^ s.mem B : Byte)) ∧
      s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x7 = s.gpr .x7 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.AesSiv.AArch64.xorBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, ra, rb, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_write, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, VG.Proof.AesSiv.AArch64.byte_xor, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- What `xorBytes` leaves. -/
structure Xored (s : State) (Q : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem Q xs
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem xorBytes_wp (s : State) {Q K : Addr} {n : Nat} (hn : 0 < n) (hn16 : n ≤ 16) (h6 : s.gpr .x6 = Q)
    (h7 : s.gpr .x7 = K) (h8 : s.gpr .x8 = BitVec.ofNat 64 n)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1)
    (hrk : ∀ i < n, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (Q + BitVec.ofNat 64 i) 1)
    (hdis : (⟨Q, n⟩ : Region).Disjoint ⟨K, n⟩) (hwq : Q.toNat + n ≤ 2 ^ 64) :
    WP isa xorBytes s
      (VG.Proof.AesSiv.AArch64.Xored s Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q n) (Spec.Aes.bytesAt s.mem K n))) := by
  refine WP.loop (M := isa) (body := .block VG.Proof.AesSiv.AArch64.xorBody) (c := .nonzero .x .x8)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .x6 = Q + BitVec.ofNat 64 j ∧
      t.gpr .x7 = K + BitVec.ofNat 64 j ∧ t.gpr .x8 = BitVec.ofNat 64 (n - j) ∧
      t.mem = writeBytes s.mem Q (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn, by rw [h6]; simp, by rw [h7]; simp, by rw [h8, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, Spec.Cmac.xor, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hj, x6, x7, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x6', x7', x8', g', sp', rd', wr'⟩ := VG.Proof.AesSiv.AArch64.xorStep_ok t (A := Q + BitVec.ofNat 64 j)
    (B := K + BitVec.ofNat 64 j) (by rw [x6, BitVec.add_zero]) (by rw [x7, BitVec.add_zero])
    (by rw [rd, wr]; exact hr j hj) (by rw [rd, wr]; exact hrk j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q j) (Spec.Aes.bytesAt s.mem K j)).length = j := by
    simp [Proof.Cmac.length_xor, Spec.Aes.bytesAt]
  have fr : Frame [⟨Q, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; exact Region.contains_self _ _)
  have hq : t.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat Q (show j < 2 ^ 64 by omega)] at hcon; omega
  have hkk : t.mem (K + BitVec.ofNat 64 j) = s.mem (K + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdis _ (Region.sub_prefix (by omega) _ hcon) (Offset.contains_base K (by omega) (by omega))
  have hmem : t'.mem = writeBytes s.mem Q
      (Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Q (j + 1)) (Spec.Aes.bytesAt s.mem K (j + 1))) := by
    rw [mem', hq, hkk, mem, Proof.Cmac.bytesAt_succ, Proof.Cmac.bytesAt_succ,
      Proof.Cmac.xor_append (by simp [Spec.Aes.bytesAt]),
      show Spec.Cmac.xor [s.mem (Q + BitVec.ofNat 64 j)] [s.mem (K + BitVec.ofNat 64 j)] =
        [s.mem (Q + BitVec.ofNat 64 j) ^^^ s.mem (K + BitVec.ofNat 64 j)] from rfl,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev : isa.eval (.nonzero .x .x8) t' = some !decide (n - (j + 1) = 0) :=
    eval_nonzero (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
  by_cases he : j + 1 = n
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega,
      by rw [x6', x6, BitVec.add_assoc, succ_ofNat], by rw [x7', x7, BitVec.add_assoc, succ_ofNat], x8'', hmem,
      gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The counter -/

/-- `adds 1` on the low word and `adc 0` on the high word increment the
128-bit integer `hi ++ lo`. -/
theorem inc_words (hi lo : BitVec 64) :
    ((hi + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + (1 : BitVec 64).toNat + false.toNat)).toNat :
        BitVec 64) ++ (lo + 1 + BitVec.ofNat 64 false.toNat : BitVec 64) : BitVec 128) =
      (hi ++ lo : BitVec 128) + (1 : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false,
    show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 128).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  by_cases h : 2 ^ 64 ≤ lo.toNat + 1 + 0
  · have : lo.toNat = 2 ^ 64 - 1 := by omega
    rw [decide_eq_true h, Bool.toNat_true, this]
    omega
  · rw [decide_eq_false h, Bool.toNat_false]
    omega

/-! ## A block -/

theorem ctrPre_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (h20 : s.gpr .x20 = C)
    (h21 : s.gpr .x21 = BitVec.ofNat 64 R) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa ctrPre s = some s' ∧ s'.gpr .x0 = C + BitVec.ofNat 64 272 ∧
      s'.gpr .x1 = BitVec.ofNat 64 R ∧ s'.gpr .x2 = W + BitVec.ofNat 64 96 ∧
      s'.gpr .x3 = W + BitVec.ofNat 64 80 ∧ s'.gpr .x4 = 1 ∧ s'.gpr .x5 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = copyMem (Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 80)) (W + BitVec.ofNat 64 96)
        (W + BitVec.ofNat 64 64) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok h19 hwr (d := ksOff) (by decide) (by decide)
  have x19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), h19]
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.AArch64.copy16_ok x19₁ (src := cntOff) (dst := cbOff) (by decide) (by decide)
    (h.inRW (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (by decide))
    (h.inRW (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (by decide))
    (h.inW (by rw [wr₁, hwr]) (by decide)) (h.inW (by rw [wr₁, hwr]) (by decide))
  have g (r : Reg) (hr : r ≠ .x9) : s₂.gpr r = s.gpr r := by rw [g₂ r hr, g₁ r hr]
  refine ⟨_, by
    rw [ctrPre, VG.Proof.AesSiv.AArch64.runBlock_append, VG.Proof.AesSiv.AArch64.runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, mov, csOff, cbOff, ksOff, runBlock_cons, runStep_some, runBlock_nil,
      exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, g _ (by decide : Reg.x20 ≠ .x9), h20],
    by simp [gpr_write, g _ (by decide : Reg.x21 ≠ .x9), h21],
    by simp [gpr_write, g _ (by decide : Reg.x19 ≠ .x9), h19],
    by simp [gpr_write, g _ (by decide : Reg.x19 ≠ .x9), h19], by simp [gpr_write],
    by simp [gpr_write, g _ (by decide : Reg.x19 ≠ .x9), h19], fun r hr => ?_,
    by simp only [mem_write, m₂, m₁], by simp only [sp_write, sp₂, sp₁], by simp only [rd_write, rd₂, rd₁],
    by simp only [wr_write, wr₂, wr₁]⟩
  rw [← g r (by rintro rfl; revert hr; decide)]
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem ctrMin_wp {s : State} {Q : Addr} {left : Nat} (h23 : s.gpr .x23 = BitVec.ofNat 64 left)
    (h22 : s.gpr .x22 = Q) (h19 : s.gpr .x19 = W) (hl : left < 2 ^ 64) :
    WP isa ctrMin s fun s' => s'.gpr .x8 = BitVec.ofNat 64 (min 16 left) ∧ s'.gpr .x6 = Q ∧
      s'.gpr .x7 = W + BitVec.ofNat 64 80 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [ctrMin]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, ksOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : (((s.write .x .x9 (s.gpr .x23 >>> 4)).write .x .x8 (s.gpr .x23 + BitVec.ofNat 64 0)).write .x
      .x6 (s.gpr .x22 + BitVec.ofNat 64 0)).write .x .x7 (s.gpr .x19 + BitVec.ofNat 64 80) = t
  have x9 : t.gpr .x9 = BitVec.ofNat 64 (left / 16) := by rw [← ht]; simp [gpr_write, h23, VG.Proof.AesSiv.AArch64.lsr4 hl]
  have x8 : t.gpr .x8 = BitVec.ofNat 64 left := by rw [← ht]; simp [gpr_write, h23]
  have x6 : t.gpr .x6 = Q := by rw [← ht]; simp [gpr_write, h22]
  have x7 : t.gpr .x7 = W + BitVec.ofNat 64 80 := by rw [← ht]; simp [gpr_write, h19]
  have gt : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r := fun r a b c d => by
    rw [← ht]; simp [gpr_write, a, b, c, d]
  have ev := eval_zero (s := t) (r := .x9) (x := left / 16) (by omega) x9
  have e : t.sp = s.sp ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by rw [← ht]; exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases hl16 : left < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [x8, Nat.min_eq_right (by omega)], x6, x7, gt, e.1, e.2.1, e.2.2.1, e.2.2.2⟩
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write, Nat.min_eq_left (show 16 ≤ left by omega)], by simp [gpr_write, x6],
      by simp [gpr_write, x7], fun r a b c d => by simp [gpr_write, c, gt r a b c d], e.1, e.2.1, e.2.2.1,
      e.2.2.2⟩

theorem ctrPost_ok {s : State} {Q : Addr} {left : Nat} {hi lo : BitVec 64} (h19 : s.gpr .x19 = W)
    (h22 : s.gpr .x22 = Q) (h23 : s.gpr .x23 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64)
    (hhi : s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi)
    (hlo : s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 cntOff) 8)
    (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (cntOff + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 cntOff) 8) (w₈ : InRegions s.wr (W + BitVec.ofNat 64 (cntOff + 8)) 8) :
    ∃ s', runBlock isa ctrPost s = some s' ∧
      (∃ hi' lo' : BitVec 64, s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (rev64 hi')).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (rev64 lo') ∧
        (hi' ++ lo' : BitVec 128) = (hi ++ lo : BitVec 128) + 1) ∧
      s'.gpr .x22 = Q + BitVec.ofNat 64 16 ∧ s'.gpr .x9 = BitVec.ofNat 64 (left / 16) ∧
      s'.gpr .x10 = BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, ctrPost, cntOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, State.addWithCarry, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀,
      r₈, w₀, w₈]
    rfl, ?_⟩
  refine ⟨⟨_, _, rfl, ?_⟩, ?_, ?_, ?_, fun r a b c d => ?_, rfl, rfl, rfl⟩
  · have hhi' : s.mem.read (W + BitVec.ofNat 64 64) 8 = rev64 hi := by rw [← hhi]; simp [Mem.readW]
    have hlo' : s.mem.read (W + BitVec.ofNat 64 (64 + 8)) 8 = rev64 lo := by rw [← hlo]; simp [Mem.readW]
    simp only [c_write, hhi', hlo', rev64_rev64,
      ]
    exact VG.Proof.AesSiv.AArch64.inc_words hi lo
  · simp [gpr_write, h22]
  · simp [gpr_write, h23, VG.Proof.AesSiv.AArch64.lsr4 hl]
  · simp [gpr_write]
  · simp [gpr_write, a, b, c, d]

/-- `min(16, left)` subtracted from the length left. -/
theorem ctrLeft_wp {s : State} {left : Nat} (h23 : s.gpr .x23 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (left / 16)) (h10 : s.gpr .x10 = BitVec.ofNat 64 16) :
    WP isa ctrLeft s fun s' => s'.gpr .x23 = BitVec.ofNat 64 (left - min 16 left) ∧
      (∀ r, r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ev := eval_zero (s := s) (r := .x9) (x := left / 16) (by omega) h9
  by_cases hl16 : left < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write, Nat.min_eq_right (show left ≤ 16 by omega)],
      fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, BitVec.setWidth_eq]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write, h23, h10, Nat.min_eq_left (show 16 ≤ left by omega),
        VG.Proof.AesSiv.AArch64.ofNat_sub (show 16 ≤ left by omega) hl],
      fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

/-! ## The loop -/

/-- The regions CTR writes: the data, the counter, keystream and counter
blocks, and the working space of `vg_aes_ctr32`. -/
abbrev ctrRegions (W P : Addr) (L : Nat) : List Region :=
  [⟨P, L⟩, ⟨W + BitVec.ofNat 64 64, 48⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩]

/-- The registers of block `i`. -/
structure CR (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x22 : s.gpr .x22 = P + BitVec.ofNat 64 (16 * i)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (L - 16 * i)
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CR.keep {s₀ s s' : State} {C D P W : Addr} {R L i : Nat} (h : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s)
    (hs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s' :=
  ⟨by rw [hs _ (by decide) (by decide), h.x19], by rw [hs _ (by decide) (by decide), h.x20],
    by rw [hs _ (by decide) (by decide), h.x21], by rw [hs _ (by decide) (by decide), h.x22],
    by rw [hs _ (by decide) (by decide), h.x23], by rw [hs _ (by decide) (by decide), h.x26],
    by rw [hs _ (by decide) (by decide), h.x27], by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

/-- The state at the start of block `i`: the data is CTR's output on its
first `16 i` bytes, the counter is `Q + i`, and the context (so the
cipher) is as at the start. -/
structure CInv (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (i : Nat) (s : State) :
    Prop where
  cr : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s
  lt : 16 * i < L
  cnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
    (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i
  data : Spec.Aes.bytesAt s.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i)
  frame : Frame (VG.Proof.AesSiv.AArch64.ctrRegions W P L) m₀ s.mem

/-- What the setup of a block, the call and the length leave. -/
structure CHead (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q : List Byte) (i : Nat) (s s' : State) :
    Prop where
  cr : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s'
  x8 : s'.gpr .x8 = BitVec.ofNat 64 (min 16 (L - 16 * i))
  x6 : s'.gpr .x6 = P + BitVec.ofNat 64 (16 * i)
  x7 : s'.gpr .x7 = W + BitVec.ofNat 64 80
  ks : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 80) 16 = Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i
  frame : Frame [⟨W + BitVec.ofNat 64 80, 32⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩] s.mem s'.mem

theorem ctr_head (v : Proof.Aes.AArch64.Ctr32Impl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) {m₀ : Mem}
    {q x : List Byte} {i : Nat} {s : State} (hi : VG.Proof.AesSiv.AArch64.CInv s₀ C D P W R L m₀ q x i s) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ s', VG.Proof.AesSiv.AArch64.CHead s₀ C D P W R L m₀ q i s s' → WP isa k s' Q) :
    WP isa (.seq (.block ctrPre) (.seq (.call v.callee.name v.callee.code) (.seq ctrMin k))) s Q := by
  have hwW := h.wW
  have hlt := h.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, g₁, m₁, sp₁, rd₁, wr₁⟩ :=
    VG.Proof.AesSiv.AArch64.ctrPre_ok h hi.cr.x19 hi.cr.x20 hi.cr.x21 hi.cr.rd hi.cr.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  have s₉₆ : Region.Sub ⟨W + BitVec.ofNat 64 96, 16⟩ ⟨W + BitVec.ofNat 64 80, 32⟩ := by
    rw [show W + BitVec.ofNat 64 96 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
    exact Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 80, 32⟩] s.mem s₁.mem := by
    rw [m₁, Proof.Cmac.zero2]
    exact ((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).trans
      ((copyMem_frame _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s₉₆⟩)
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWW 80 16 96 16 (by omega) (by omega) (by omega))
      (by decide), Proof.Cmac.zero2_bytes]
  have hc := h.cargs (s := s₁) (by rw [rd₁, hi.cr.rd]) (by rw [wr₁, hi.cr.wr]) x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ hz
  refine WP.seq (WP.mono (ctr_call v hc) fun s₂ h₂ => ?_)
  have cr₂ : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s₂ :=
    (hi.cr.keep (fun r hr _ => g₁ r hr) sp₁ rd₁ wr₁).keep h₂.saved h₂.sp h₂.rd h₂.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.ctrMin_wp (left := L - 16 * i) cr₂.x23 cr₂.x22 cr₂.x19 (by omega))
    fun s₃ ⟨x8₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => hk s₃ ?_)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩]
      s₁.mem s₂.mem := h₂.frame
  refine ⟨cr₂.keep (fun r hr _ => g₃ r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)) sp₃ rd₃ wr₃, x8₃, x6₃, x7₃, ?_, ?_⟩
  · -- The keystream block: the cipher of the counter block, a copy of `Q + i`.
    obtain ⟨hi', lo', hhi, hlo, hq⟩ := hi.cnt
    have dC (r : Region) (hr : r ∈ VG.Proof.AesSiv.AArch64.ctrRegions W P L) :
        (⟨C + BitVec.ofNat 64 272, 16 * (R + 1)⟩ : Region).Disjoint r := by
      have sub := h.sC (d := 272) (n := 16 * (R + 1)) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hcp.sub_left sub
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
    have sch : Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        Spec.Aes.bytesAt m₀ (C + BitVec.ofNat 64 272) (16 * (R + 1)) := by
      rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.c_w.sub_left (h.sC (by omega))).sub_right (h.sW (by decide))) (by omega),
        Proof.Cmac.bytesAt_frame hi.frame dC (by omega)]
    have hhi' : s.mem.readW (W + BitVec.ofNat 64 64) 64 = rev64 hi' := hhi
    have hlo' : s.mem.readW (W + BitVec.ofNat 64 (64 + 8)) 64 = rev64 lo' := hlo
    have cb : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
      rw [m₁, copyMem_bytes _ (dWW 96 16 64 16 (by omega) (by omega) (by omega)), Proof.Cmac.zero2,
        Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dWW 64 16 80 16 (by omega) (by omega) (by omega))
          (by decide),
        Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Offset.add_add, hhi', hlo',
        le8_rev, hq, be128_add]
    rw [m₃, h₂.out, sch, cb]
    rfl
  · rw [m₃]
    exact (f₁.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s₉₆⟩
      · exact ⟨⟨W + BitVec.ofNat 64 80, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

/-- The state after the last block: the data is CTR's output. -/
structure CDone (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : Spec.Aes.bytesAt s.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph m₀ C R) q x
  frame : Frame (VG.Proof.AesSiv.AArch64.ctrRegions W P L) m₀ s.mem

theorem ctxCiph_length (m : Mem) (C : Addr) (R : Nat) (y : List Byte) : (Spec.Siv.ctxCiph m C R y).length = 16 :=
  Proof.Cmac.aesWith_length _ _ _

theorem ctr_tail (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {m₀ : Mem} {q x : List Byte} {i : Nat}
    {s s₃ : State} (hi : VG.Proof.AesSiv.AArch64.CInv s₀ C D P W R L m₀ q x i s) (hh : VG.Proof.AesSiv.AArch64.CHead s₀ C D P W R L m₀ q i s s₃) :
    WP isa (.seq xorBytes (.seq (.block ctrPost) ctrLeft)) s₃ fun s' =>
      (L - 16 * i ≤ 16 ∧ s'.gpr .x23 = 0 ∧ VG.Proof.AesSiv.AArch64.CDone s₀ C D P W R L m₀ q x s') ∨
      (16 < L - 16 * i ∧ s'.gpr .x23 ≠ 0 ∧ VG.Proof.AesSiv.AArch64.CInv s₀ C D P W R L m₀ q x (i + 1) s') := by
  have hwW := h.wW
  have hwP := h.wP
  have hlt := h.lt
  have hiL := hi.lt
  have hxL : x.length = L := by
    have := congrArg List.length hi.data
    rw [Proof.Cmac.bytesAt_length, length_ctrPart] at this; exact this.symm
  have hn : 0 < min 16 (L - 16 * i) := by omega
  have hn16 : min 16 (L - 16 * i) ≤ 16 := Nat.min_le_left _ _
  have dP (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2048⟩]) :
      (⟨P, L⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.p_w.sub_right (h.sW (by decide))
    · exact h.p_w.sub_right (h.sW (by decide))
  have data₃ : Spec.Aes.bytesAt s₃.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i) := by
    rw [Proof.Cmac.bytesAt_frame hh.frame dP (by omega), hi.data]
  have sQ : Region.Sub ⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩ ⟨P, L⟩ := h.sP (by omega)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.xorBytes_wp s₃ (Q := P + BitVec.ofNat 64 (16 * i)) (K := W + BitVec.ofNat 64 80) hn hn16
    hh.x6 hh.x7 hh.x8
    (fun j hj => by rw [Offset.add_add]; exact h.inRP hh.cr.rd hh.cr.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inRW hh.cr.rd hh.cr.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inWP hPw hh.cr.wr (by omega))
    ((h.p_w.sub_left sQ).sub_right (h.sW (by omega)))
    (by rw [toNat_add_lt P hwP (show 16 * i < L by omega)]; omega)) fun s₄ h₄ => ?_)
  obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hi.cnt
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * i)) (min 16 (L - 16 * i)))
      (Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)))).length = min 16 (L - 16 * i) := by
    rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length, Nat.min_self]
  have fx : Frame [⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  have dW (d n : Nat) (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨P + BitVec.ofNat 64 (16 * i),
      min 16 (L - 16 * i)⟩ : Region)]) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.p_w.sub_left sQ).symm.sub_left (h.sW hd)
  have dH (d : Nat) (hd : d + 8 ≤ 80) (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 256, 2048⟩]) : (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
  have c₄ (d : Nat) (hd : d + 8 ≤ 80) :
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fx.readW (w := 64) (Region.contains_self _ _) (dW d 8 (by omega)) (by decide),
      hh.frame.readW (w := 64) (Region.contains_self _ _) (dH d hd) (by decide)]
  have g₄ (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄' : r ≠ .x9) (h₅ : r ≠ .x10) :=
    h₄.other r h₁ h₂ h₃ h₄' h₅
  have x19₄ : s₄.gpr .x19 = W := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.cr.x19]
  have x22₄ : s₄.gpr .x22 = P + BitVec.ofNat 64 (16 * i) := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.cr.x22]
  have x23₄ : s₄.gpr .x23 = BitVec.ofNat 64 (L - 16 * i) := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.cr.x23]
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, hh.cr.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, hh.cr.wr]
  obtain ⟨s₅, run₅, ⟨hi₁, lo₁, m₅, hq₁⟩, x22₅, x9₅, x10₅, g₅, sp₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.AArch64.ctrPost_ok (W := W) (s := s₄)
    (left := L - 16 * i) (hi := hi₀) (lo := lo₀) x19₄ x22₄ x23₄ (by omega)
    (by rw [c₄ cntOff (by decide)]; exact hhi) (by rw [c₄ (cntOff + 8) (by decide)]; exact hlo)
    (h.inRW rd₄ wr₄ (by decide)) (h.inRW rd₄ wr₄ (by decide)) (h.inW wr₄ (by decide)) (h.inW wr₄ (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have x23₅ : s₅.gpr .x23 = BitVec.ofNat 64 (L - 16 * i) := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide), x23₄]
  refine WP.mono (VG.Proof.AesSiv.AArch64.ctrLeft_wp x23₅ (by omega) x9₅ x10₅) fun s₆ ⟨x23₆, g₆, sp₆, m₆, rd₆, wr₆⟩ => ?_
  have fp : Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅]
    have c64 : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Contains (W + BitVec.ofNat 64 cntOff) (64 / 8) := by
      show Region.Contains _ (W + BitVec.ofNat 64 64) 8
      simpa using Offset.contains_base (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c64).writeW
      (List.mem_singleton_self _) _ (by
        rw [show W + BitVec.ofNat 64 (cntOff + 8) = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
          rw [Offset.add_add]]
        exact Offset.contains_base _ (by decide) (by decide))
  -- The data.
  have kt : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)) =
      (Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i).take (min 16 (L - 16 * i)) := by
    rw [← hh.ks]
    have := take_bytesAt s₃.mem (W + BitVec.ofNat 64 80) (a := min 16 (L - 16 * i)) (b := 16 - min 16 (L - 16 * i))
    rw [show min 16 (L - 16 * i) + (16 - min 16 (L - 16 * i)) = 16 by omega] at this
    exact this.symm
  have st := ctrPart_step (Spec.Siv.ctxCiph m₀ C R) (VG.Proof.AesSiv.AArch64.ctxCiph_length m₀ C R) q x s₃.mem P (i := i)
    (n := min 16 (L - 16 * i)) (by omega) hn16 (by omega) (by rw [hxL]; exact data₃)
  rw [hxL, ← kt, ← h₄.mem] at st
  have data₆ : Spec.Aes.bytesAt s₆.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i + min 16 (L - 16 * i)) := by
    rw [Proof.Cmac.bytesAt_frame fp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.p_w.sub_right (h.sW (by decide))) (by omega), st]
  -- The frame.
  have frame : Frame (VG.Proof.AesSiv.AArch64.ctrRegions W P L) m₀ s₆.mem :=
    ((hi.frame.trans (hh.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
          rw [show W + BitVec.ofNat 64 80 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
          exact Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)).trans
      (fx.sub fun r hr => ⟨⟨P, L⟩, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact sQ⟩)).trans
      (fp.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩)
  have keep (r : Reg) (hr : r ∈ preserved) (h22 : r ≠ .x22) (h23 : r ≠ .x23) : s₆.gpr r = s₃.gpr r := by
    have a : r ≠ .x6 := by rintro rfl; revert hr; decide
    have b : r ≠ .x7 := by rintro rfl; revert hr; decide
    have c : r ≠ .x8 := by rintro rfl; revert hr; decide
    have d : r ≠ .x9 := by rintro rfl; revert hr; decide
    have e : r ≠ .x10 := by rintro rfl; revert hr; decide
    have f : r ≠ .x11 := by rintro rfl; revert hr; decide
    rw [g₆ r h23, g₅ r d e f h22, g₄ r a b c d e]
  have sp₆' : s₆.sp = s₀.sp := by rw [sp₆, sp₅, h₄.sp, hh.cr.sp]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄]
  by_cases hfin : L - 16 * i ≤ 16
  · left
    have hn' : min 16 (L - 16 * i) = L - 16 * i := Nat.min_eq_right hfin
    refine ⟨hfin, by rw [x23₆, hn', Nat.sub_self]; rfl, ⟨by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x19],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x20],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x21],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x26],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x27], sp₆', rd₆', wr₆', ?_, frame⟩⟩
    rw [data₆, hn', show 16 * i + (L - 16 * i) = L by omega]
    exact ctrPart_all _ (VG.Proof.AesSiv.AArch64.ctxCiph_length m₀ C R) q x (by omega)
  · right
    have hn' : min 16 (L - 16 * i) = 16 := Nat.min_eq_left (by omega)
    have x23' : s₆.gpr .x23 = BitVec.ofNat 64 (L - 16 * (i + 1)) := by
      rw [x23₆, hn', show L - 16 * i - 16 = L - 16 * (i + 1) by omega]
    have ne : BitVec.ofNat 64 (L - 16 * (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [toNat_ofNat (by omega)] at this; simp at this; omega
    refine ⟨by omega, by rw [x23']; exact ne,
      ⟨⟨by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x19],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x20],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x21],
      by rw [g₆ _ (by decide), x22₅, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega], x23',
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x26],
      by rw [keep _ (by decide) (by decide) (by decide), hh.cr.x27], sp₆', rd₆', wr₆'⟩, by omega,
      ⟨hi₁, lo₁, ?_, ?_, ?_⟩, ?_, frame⟩⟩
    · rw [m₆, m₅, Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [m₆, m₅, Mem.readW_writeW_self64]
    · rw [hq₁, hq, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [data₆, hn', show 16 * i + 16 = 16 * (i + 1) by omega]

/-! ## The whole -/

/-- What `ctr` leaves: the data is CTR's output, and the registers are back. -/
structure CPost' (s₀ : State) (C D P W : Addr) (R L : Nat) (q : List Byte) (s s' : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s'
  x26 : s'.gpr .x26 = P
  x27 : s'.gpr .x27 = BitVec.ofNat 64 L
  data : Spec.Aes.bytesAt s'.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) q (Spec.Aes.bytesAt s.mem P L)
  frame : Frame (VG.Proof.AesSiv.AArch64.ctrRegions W P L) s.mem s'.mem

theorem ctr_nil (ciph : Spec.Cmac.Cipher) (q : List Byte) : Spec.Siv.ctr ciph q [] = [] := by
  simp [Spec.Siv.ctr, Spec.Siv.xor]

theorem ctrEnd_ok {s : State} (h26 : s.gpr .x26 = P) (h27 : s.gpr .x27 = BitVec.ofNat 64 L) :
    ∃ s', runBlock isa [mov .x22 .x26, mov .x23 .x27] s = some s' ∧
      s'.gpr .x22 = P ∧ s'.gpr .x23 = BitVec.ofNat 64 L ∧ (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  exact ⟨by simp [gpr_write, h26], by simp [gpr_write, h27], fun r a b => by simp [gpr_write, a, b], rfl, rfl,
    rfl, rfl⟩

theorem ctr_wp (v : Proof.Aes.AArch64.Ctr32Impl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hr : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s) {q : List Byte}
    (hcnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q)
    (h26 : s.gpr .x26 = P) (h27 : s.gpr .x27 = BitVec.ofNat 64 L) :
    WP isa (ctr v.callee) s (VG.Proof.AesSiv.AArch64.CPost' s₀ C D P W R L q s) := by
  have hwW := h.wW
  have hlt := h.lt
  have finish {t : State} (hd : VG.Proof.AesSiv.AArch64.CDone s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) t) :
      WP isa (.block [mov .x22 .x26, mov .x23 .x27]) t (VG.Proof.AesSiv.AArch64.CPost' s₀ C D P W R L q s) := by
    obtain ⟨t', run, x22, x23, g, sp, m, rd, wr⟩ := VG.Proof.AesSiv.AArch64.ctrEnd_ok hd.x26 hd.x27
    exact WP.of_runBlock ⟨t', run, ⟨⟨by rw [g _ (by decide) (by decide), hd.x19],
      by rw [g _ (by decide) (by decide), hd.x20], by rw [g _ (by decide) (by decide), hd.x21], x22, x23,
      by rw [sp, hd.sp], by rw [rd, hd.rd], by rw [wr, hd.wr]⟩, by rw [g _ (by decide) (by decide), hd.x26],
      by rw [g _ (by decide) (by decide), hd.x27], by rw [m]; exact hd.data, by rw [m]; exact hd.frame⟩⟩
  have ev := eval_zero (s := s) (r := .x23) (x := L) hlt hr.x23
  refine WP.seq (WP.ite (decide (L = 0)) ev (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have hL0 : L = 0 := of_decide_eq_true hb
    subst hL0
    refine finish ⟨hr.x19, hr.x20, hr.x21, h26, h27, hr.sp, hr.rd, hr.wr, ?_, Frame.refl _ _⟩
    simp [Spec.Aes.bytesAt, VG.Proof.AesSiv.AArch64.ctr_nil]
  · have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hb)
    refine WP.loop (M := isa) (c := .nonzero .x .x23)
      (fun (n : Nat) (t : State) => ∃ i, n = L - 16 * i ∧
        VG.Proof.AesSiv.AArch64.CInv s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) i t) ?_ (L - 16 * 0) s ⟨0, rfl, ?_⟩
    · rintro n t ⟨i, rfl, hi⟩
      refine VG.Proof.AesSiv.AArch64.ctr_head v h hcp hi fun t₃ hh => WP.mono (VG.Proof.AesSiv.AArch64.ctr_tail h hPw hi hh) fun t' ht => ?_
      rcases ht with ⟨_, hz, hd⟩ | ⟨_, hz, hi'⟩
      · exact Or.inl ⟨by show some (t'.read .x .x23 != 0) = some false; simp [State.read, hz], finish hd⟩
      · exact Or.inr ⟨by show some (t'.read .x .x23 != 0) = some true; simp [State.read]; exact hz,
          L - 16 * (i + 1), by have := hi.lt; omega, i + 1, rfl, hi'⟩
    · obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hcnt
      exact ⟨⟨hr.x19, hr.x20, hr.x21, by rw [hr.x22, Nat.mul_zero, k0], by rw [hr.x23, Nat.mul_zero, Nat.sub_zero],
        h26, h27, hr.sp, hr.rd, hr.wr⟩, by omega, ⟨hi₀, lo₀, hhi, hlo, by rw [hq]; exact (BitVec.add_zero _).symm⟩,
        by rw [Nat.mul_zero, ctrPart_zero], Frame.refl _ _⟩

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.CtrCT`. -/
section

/-!
# AES-SIV on AArch64: CTR is constant time

Every block's pointer and length are public (`x22`, `x23`), so the code
around the call of `vg_aes_ctr32` passes the taint analysis, and the call's
arguments are the same in both runs (`ctr_rel` of `CmacAes.AArch64`). Both
runs leave the loop after the same block, the last one (`ctr_tail`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (CallPre ctr_call ctr_rel agree_of k0)
open VG.Proof.CmacAes.Stream.AArch64 (copyMem_frame eval_zero)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem cr_agree {s₀' a b : State} {i : Nat} (hq : s₀.sp = s₀'.sp) (ha : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i a)
    (hb : VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i b) :
    taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) a b := by
  refine VG.Proof.CmacAes.AArch64.agree_of (by rw [ha.sp, hb.sp, hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [ha.x19, hb.x19]
  · rw [ha.x20, hb.x20]
  · rw [ha.x21, hb.x21]
  · rw [ha.x22, hb.x22]
  · rw [ha.x23, hb.x23]

theorem ctrPre_wp (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {i : Nat} {s : State} (hr : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s) :
    WP isa (.block ctrPre) s fun t => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i t := by
  have hwW := h.wW
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, g₁, m₁, sp₁, rd₁, wr₁⟩ :=
    VG.Proof.AesSiv.AArch64.ctrPre_ok h hr.x19 hr.x20 hr.x21 hr.rd hr.wr
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide), Proof.Cmac.zero2_bytes]
  have hr₁ := hr.keep (fun r hr _ => g₁ r hr) sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h.cargs hr₁.rd hr₁.wr x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ hz, hr₁⟩

/-- A block is constant time. -/
theorem body_rel (v : Proof.Aes.AArch64.Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (i : Nat) :
    RelCT isa (fun a b => VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i a ∧ VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i b) (ctrBody v.callee)
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) (.block ctrPre)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.seq ctrMin (.seq xorBytes (.seq (.block ctrPost) ctrLeft))) hc).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i a ∧ VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.cr_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i t)
    (F₂ := fun (t : State) => CallPre t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i t)
    fun a b hab => ⟨VG.Proof.AesSiv.AArch64.ctrPre_wp h hab.1, VG.Proof.AesSiv.AArch64.ctrPre_wp h' hab.2⟩
  have r₂ := (ctr_rel v (P := fun (a b : State) => (CallPre a (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i a) ∧
      CallPre b (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 256) R ∧ VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i b)
    fun a b hab => ⟨hab.1.1, hab.2.1, by rw [hab.1.2.sp, hab.2.2.sp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i) (F₂ := VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i)
    fun a b hab => ⟨WP.mono (ctr_call v hab.1.1) fun _ p => hab.1.2.keep p.saved p.sp p.rd p.wr,
      WP.mono (ctr_call v hab.2.1) fun _ p => hab.2.2.keep p.saved p.sp p.rd p.wr⟩
  have r₃ := RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i a ∧ VG.Proof.AesSiv.AArch64.CR s₀' C D P W R L i b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.cr_agree hq hab.1 hab.2) hB
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq r₃)

/-- Block `i` of a run. -/
def CI (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  ∃ m₀ q x, VG.Proof.AesSiv.AArch64.CInv s₀ C D P W R L m₀ q x i s

/-- After the last block: the registers. -/
structure CE (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What a block leaves, for the loop: the last block, or the next one. -/
def BPost (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  (L - 16 * i ≤ 16 ∧ s.gpr .x23 = 0 ∧ VG.Proof.AesSiv.AArch64.CE s₀ C D P W R L s) ∨
    (16 < L - 16 * i ∧ s.gpr .x23 ≠ 0 ∧ VG.Proof.AesSiv.AArch64.CI s₀ C D P W R L (i + 1) s)

theorem body_wp (v : Proof.Aes.AArch64.Ctr32Impl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {i : Nat} {s : State}
    (hs : VG.Proof.AesSiv.AArch64.CI s₀ C D P W R L i s) :
    WP isa (ctrBody v.callee) s (VG.Proof.AesSiv.AArch64.BPost s₀ C D P W R L i) := by
  obtain ⟨m₀, q, x, hi⟩ := hs
  refine VG.Proof.AesSiv.AArch64.ctr_head v h hcp hi fun t₃ hh => WP.mono (VG.Proof.AesSiv.AArch64.ctr_tail h hPw hi hh) fun t ht => ?_
  rcases ht with ⟨hc, hz, hd⟩ | ⟨hc, hz, hi'⟩
  · exact Or.inl ⟨hc, hz, hd.x19, hd.x20, hd.x21, hd.x26, hd.x27, hd.sp, hd.rd, hd.wr⟩
  · exact Or.inr ⟨hc, hz, m₀, q, x, hi'⟩

theorem CI.cr {i : Nat} {s : State} (hs : VG.Proof.AesSiv.AArch64.CI s₀ C D P W R L i s) : VG.Proof.AesSiv.AArch64.CR s₀ C D P W R L i s :=
  let ⟨_, _, _, hi⟩ := hs; hi.cr

theorem eval_x23 (s : State) : isa.eval (.nonzero .x .x23) s = some (s.gpr .x23 != 0) := by
  show some (s.read .x .x23 != 0) = _
  rw [State.read, BitVec.setWidth_eq]

theorem loop_rel (v : Proof.Aes.AArch64.Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) (n : Nat) :
    RelCT isa (fun a b => ∃ i, n = L - 16 * i ∧ VG.Proof.AesSiv.AArch64.CI s₀ C D P W R L i a ∧ VG.Proof.AesSiv.AArch64.CI s₀' C D P W R L i b)
      (.loop (ctrBody v.callee) (.nonzero .x .x23)) fun a b => VG.Proof.AesSiv.AArch64.CE s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.CE s₀' C D P W R L b := by
  refine RelCT.loop (M := isa) (fun (k : Nat) (a b : State) => ∃ i, k = L - 16 * i ∧ VG.Proof.AesSiv.AArch64.CI s₀ C D P W R L i a ∧
    VG.Proof.AesSiv.AArch64.CI s₀' C D P W R L i b) (fun k => ?_) n
  refine RelCT.exists_ fun i => ?_
  by_cases hk : k = L - 16 * i
  swap
  · exact RelCT.of_false fun a b hab => hk hab.1
  refine (((VG.Proof.AesSiv.AArch64.body_rel v h h' hq i).mono (fun a b hab => ⟨hab.2.1.cr, hab.2.2.cr⟩) fun _ _ h => h).wp
    (F₁ := VG.Proof.AesSiv.AArch64.BPost s₀ C D P W R L i) (F₂ := VG.Proof.AesSiv.AArch64.BPost s₀' C D P W R L i)
    fun a b hab => ⟨VG.Proof.AesSiv.AArch64.body_wp v h hcp hPw hab.2.1, VG.Proof.AesSiv.AArch64.body_wp v h' hcp hPw' hab.2.2⟩).mono
    (fun _ _ h => h) fun a b ⟨_, ha, hb⟩ => ?_
  rw [VG.Proof.AesSiv.AArch64.eval_x23, VG.Proof.AesSiv.AArch64.eval_x23]
  rcases ha with ⟨hc, hz, he⟩ | ⟨hc, hz, hci⟩ <;> rcases hb with ⟨hc', hz', he'⟩ | ⟨hc', hz', hci'⟩
  · exact ⟨by rw [hz, hz'], fun _ => ⟨he, he'⟩, fun e => by simp [hz] at e⟩
  · omega
  · omega
  · exact ⟨by rw [hci.cr.x23, hci'.cr.x23], fun e => (hz (by simpa using e)).elim, fun _ =>
      ⟨L - 16 * (i + 1), by have := hci.cr; omega, i + 1, rfl, hci, hci'⟩⟩

/-- What `ctr` needs of a run: the registers, the data in `x26` and `x27`,
and a counter `Q`. -/
structure CtrPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  cnt : ∃ (hi lo : BitVec 64) (q : List Byte), s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q

theorem CtrPre.ci {s : State} (hs : VG.Proof.AesSiv.AArch64.CtrPre s₀ C D P W R L s) (hL : 0 < L) : VG.Proof.AesSiv.AArch64.CI s₀ C D P W R L 0 s := by
  obtain ⟨hi₀, lo₀, q, hhi, hlo, hq⟩ := hs.cnt
  exact ⟨s.mem, q, Spec.Aes.bytesAt s.mem P L, ⟨⟨hs.regs.x19, hs.regs.x20, hs.regs.x21,
    by rw [hs.regs.x22, Nat.mul_zero, k0], by rw [hs.regs.x23, Nat.mul_zero, Nat.sub_zero], hs.x26, hs.x27,
    hs.regs.sp, hs.regs.rd, hs.regs.wr⟩, by omega,
    ⟨hi₀, lo₀, hhi, hlo, by rw [hq]; exact (BitVec.add_zero _).symm⟩, by rw [Nat.mul_zero, ctrPart_zero],
    Frame.refl _ _⟩⟩

theorem CtrPre.ce {s : State} (hs : VG.Proof.AesSiv.AArch64.CtrPre s₀ C D P W R L s) : VG.Proof.AesSiv.AArch64.CE s₀ C D P W R L s :=
  ⟨hs.regs.x19, hs.regs.x20, hs.regs.x21, hs.x26, hs.x27, hs.regs.sp, hs.regs.rd, hs.regs.wr⟩

theorem ctr_rel' (v : Proof.Aes.AArch64.Ctr32Impl) {s₀' : State} (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (h' : VG.Proof.AesSiv.AArch64.Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => VG.Proof.AesSiv.AArch64.CtrPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.CtrPre s₀' C D P W R L b) (ctr v.callee)
      fun a b => (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ a.gpr .x26 = P ∧ a.gpr .x27 = BitVec.ofNat 64 L) ∧
        VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ b.gpr .x26 = P ∧ b.gpr .x27 = BitVec.ofNat 64 L := by
  have hlt := h.lt
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x26, .x27])
      (.block [mov .x22 .x26, mov .x23 .x27]) hc).isSome = true := ⟨_, by taint_decide⟩
  have ev {σ s : State} (hs : VG.Proof.AesSiv.AArch64.CtrPre σ C D P W R L s) : isa.eval (.zero .x .x23) s = some (decide (L = 0)) :=
    eval_zero hlt hs.regs.x23
  have i := RelCT.ite (M := isa) (c := .zero .x .x23)
    (P := fun a b => VG.Proof.AesSiv.AArch64.CtrPre s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.CtrPre s₀' C D P W R L b)
    (Q := fun a b => VG.Proof.AesSiv.AArch64.CE s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.CE s₀' C D P W R L b)
    (fun a b hab => by rw [ev hab.1, ev hab.2])
    (RelCT.block_nil fun a b hab => ⟨hab.1.1.ce, hab.1.2.ce⟩)
    ((VG.Proof.AesSiv.AArch64.loop_rel v h h' hq hcp hPw hPw' (L - 16 * 0)).mono (fun a b hab => by
      have hL : 0 < L := by
        have e := hab.2; rw [ev hab.1.1] at e
        simp at e; omega
      exact ⟨0, rfl, hab.1.1.ci hL, hab.1.2.ci hL⟩) fun _ _ h => h)
  have we {σ s : State} (hs : VG.Proof.AesSiv.AArch64.CE σ C D P W R L s) :
      WP isa (.block [mov .x22 .x26, mov .x23 .x27]) s fun t =>
        VG.Proof.AesSiv.AArch64.Regs σ C D P W R L t ∧ t.gpr .x26 = P ∧ t.gpr .x27 = BitVec.ofNat 64 L := by
    have hd := hs
    obtain ⟨t, run, x22, x23, g, sp, _, rd, wr⟩ := VG.Proof.AesSiv.AArch64.ctrEnd_ok hd.x26 hd.x27
    exact WP.of_runBlock ⟨t, run, ⟨by rw [g _ (by decide) (by decide), hd.x19], by rw [g _ (by decide) (by decide),
      hd.x20], by rw [g _ (by decide) (by decide), hd.x21], x22, x23, by rw [sp, hd.sp], by rw [rd, hd.rd],
      by rw [wr, hd.wr]⟩, by rw [g _ (by decide) (by decide), hd.x26], by rw [g _ (by decide) (by decide), hd.x27]⟩
  have hx (σ : State) (s : State) (hs : VG.Proof.AesSiv.AArch64.CE σ C D P W R L s) : s.gpr .x26 = P ∧ s.gpr .x27 = BitVec.ofNat 64 L ∧
      s.sp = σ.sp := by
    exact ⟨hs.x26, hs.x27, hs.sp⟩
  have e := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.CE s₀ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.CE s₀' C D P W R L b) _
    (fun a b hab => by
      obtain ⟨a26, a27, asp⟩ := hx _ _ hab.1
      obtain ⟨b26, b27, bsp⟩ := hx _ _ hab.2
      refine VG.Proof.CmacAes.AArch64.agree_of (by rw [asp, bsp, hq]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a26, b26]
      · rw [a27, b27]) hB).wp
    (F₁ := fun (t : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L t ∧ t.gpr .x26 = P ∧ t.gpr .x27 = BitVec.ofNat 64 L)
    (F₂ := fun (t : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L t ∧ t.gpr .x26 = P ∧ t.gpr .x27 = BitVec.ofNat 64 L)
    fun a b hab => ⟨we hab.1, we hab.2⟩
  exact i.seq (e.mono (fun _ _ h => h) fun _ _ h => h.2)

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Seal`. -/
section

/-!
# AES-SIV on AArch64: the counter, and the end of `vg_aes_siv_encrypt`

`encrypt` and `decrypt` set the counter `Q` at `W + 64` from an IV at `W`
(`counter_ok`): the IV's second word with bits 7 and 39 cleared
(`counter_words`). From S2V's state of the associated data on, `encrypt`
finishes S2V with the plaintext into the first 16 bytes of the working space
(`finish_wp`), sets the counter from that IV, encrypts the data in place with
CTR (`ctr_wp`), copies the IV to `siv`, whose address the save left at
`W + 248` (`sivOut_ok`), and restores the registers: `siv` then holds the IV
and the data is the ciphertext (`sealTail_wp`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.AesSiv (qmask counter_words)
open VG.Proof.CmacAes.AArch64 (k0 le8_rev)
open VG.Proof.Gcm.AArch64 (rev64_rev64)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem counter_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 (cntOff + 8)) (s.mem.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₈ := h.inRW hrd hwr (d := 0 + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := cntOff) (n := 8) (by decide)
  have w₈ := h.inW hwr (d := cntOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, counter, cntOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀, r₈, w₀, w₈]
    rfl, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], by rfl, by rfl, by rfl⟩
  have hq : ~~~((BitVec.setWidth 64 (128 : BitVec 16) <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
      BitVec.setWidth 64 (128 : BitVec 16) <<< (16 * 2)).rotateRight 0) = qmask := by decide
  rw [Mem.read_write_sep (Offset.sep W (d := 0 + 8) (n := 8) (e := cntOff) (k := 8) (by decide) (by decide)
    (by decide)) (by decide), hq]
  simp only [Mem.writeW, Mem.readW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

/-- The counter `Q` of the IV, as `ctr` takes it. -/
theorem counter_cnt (m : Mem) (W : Addr) :
    ∃ hi lo : BitVec 64,
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt m W 16)) := by
  refine ⟨rev64 (m.readW (W + BitVec.ofNat 64 0) 64), rev64 (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask),
    ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, rev64_rev64]
  · rw [Mem.readW_writeW_self64, rev64_rev64]
  · rw [← Proof.Cmac.ofBytes_toBytes (rev64 _ ++ rev64 _), ← le8_rev, rev64_rev64, rev64_rev64, counter_words,
      Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, k0, ← Proof.Cmac.bytesAt_split]

/-! ## What each step writes -/

/-- The regions the counter's two words are written to. -/
abbrev cntRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 cntOff, 8⟩, ⟨W + BitVec.ofNat 64 (cntOff + 8), 8⟩]

theorem counter_frame (m : Mem) (W : Addr) (a b : BitVec 64) :
    Frame (VG.Proof.AesSiv.AArch64.cntRegions W) m ((m.writeW (W + BitVec.ofNat 64 cntOff) a).writeW (W + BitVec.ofNat 64 (cntOff + 8)) b) :=
  ((Frame.refl _ _).writeW List.mem_cons_self a (Region.contains_self (W + BitVec.ofNat 64 cntOff) 8)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) b (Region.contains_self (W + BitVec.ofNat 64 (cntOff + 8)) 8)

/-- A range of the working space outside what `finish` writes. -/
theorem fin_dis (_h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {out d n : Nat} (hout : out + 16 ≤ 256) (_hd : d + n ≤ 2560)
    (h1 : out + 16 ≤ d ∨ d + n ≤ out) (h2 : d + n ≤ 32 ∨ 64 ≤ d) (h3 : d + n ≤ 144 ∨ 160 ≤ d)
    (h5 : d + n ≤ 256) :
    ∀ r ∈ VG.Proof.AesSiv.AArch64.finRegions W out, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the working space, outside what `finish` writes. -/
theorem fin_out {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ VG.Proof.AesSiv.AArch64.finRegions W out, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by omega))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ VG.Proof.AesSiv.AArch64.ctrRegions W P L, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega))
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the data and the working space, outside what CTR writes. -/
theorem ctr_out {X : Region} (hp : X.Disjoint ⟨P, L⟩) (hw : X.Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ VG.Proof.AesSiv.AArch64.ctrRegions W P L, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

/-- A range of the working space outside the counter. -/
theorem cnt_dis {d n : Nat} (hd : d + n ≤ 2560) (h1 : d + n ≤ 64 ∨ 80 ≤ d) :
    ∀ r ∈ VG.Proof.AesSiv.AArch64.cntRegions W, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [cntOff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the working space, outside the counter. -/
theorem cnt_out {X : Region} (hw : X.Disjoint ⟨W, 2560⟩) : ∀ r ∈ VG.Proof.AesSiv.AArch64.cntRegions W, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

theorem one_out {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw

/-- What `encrypt`'s and `decrypt`'s ends write: the data and the working space. -/
abbrev endRegions (W P : Addr) (L : Nat) : List Region := [⟨P, L⟩, ⟨W, 2560⟩]

theorem fin_sub (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {out : Nat} (hout : out + 16 ≤ 256) :
    ∀ r ∈ VG.Proof.AesSiv.AArch64.finRegions W out, ∃ r' ∈ VG.Proof.AesSiv.AArch64.endRegions W P L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem cnt_sub (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) : ∀ r ∈ VG.Proof.AesSiv.AArch64.cntRegions W, ∃ r' ∈ VG.Proof.AesSiv.AArch64.endRegions W P L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem ctr_sub (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) : ∀ r ∈ VG.Proof.AesSiv.AArch64.ctrRegions W P L, ∃ r' ∈ VG.Proof.AesSiv.AArch64.endRegions W P L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

/-! ## From S2V's end to the restore -/

/-- The registers, and the data and its length in `x26` and `x27`. -/
structure SPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_bound : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 256 := by decide

theorem restored_sub : ∀ p ∈ restored, p ∈ saved := by decide

theorem restored_restorable : Spill.Restorable .x19 restored := by decide

theorem restored_all : ∀ r ∈ preserved, r ∈ restored.map Prod.fst := by decide

/-- The restore, from the slots the save wrote (`Saved`), with the working
space in `x19`. -/
theorem restore_wp (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) :
    WP isa (.block restore) s fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧
      (∀ r, r ∉ restored.map Prod.fst → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem :=
  WP.mono (Spill.restore_wp h19 (fun p hp => saved_fits.1 p (VG.Proof.AesSiv.AArch64.restored_sub p hp)) VG.Proof.AesSiv.AArch64.restored_restorable
      (fun p hp => by have := VG.Proof.AesSiv.AArch64.saved_bound p (VG.Proof.AesSiv.AArch64.restored_sub p hp); exact h.inRW hrd hwr (by omega))
      (fun p hp => hsv p (VG.Proof.AesSiv.AArch64.restored_sub p hp)))
    fun _ h₇ => ⟨fun r hr => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (VG.Proof.AesSiv.AArch64.restored_all r hr); exact h₇.gpr p hp, h₇.other, h₇.sp, h₇.mem⟩

/-- The copy of the IV at `W` to `T`, whose address is at `W + 248`. -/
theorem sivOut_ok {s : State} {W T : Addr} (h19 : s.gpr .x19 = W)
    (aT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = T)
    (r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 248) 8)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 0) 8) (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 8) 8)
    (w₀ : InRegions s.wr (T + BitVec.ofNat 64 0) 8) (w₈ : InRegions s.wr (T + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa sivOut s = some s' ∧
      s'.mem = (s.mem.writeW (T + BitVec.ofNat 64 0) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (T + BitVec.ofNat 64 8)
        ((s.mem.writeW (T + BitVec.ofNat 64 0) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).readW
          (W + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [Mem.readW, BitVec.setWidth_eq] at aT
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self,
      sivOut, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      h19, r₂, aT, r₀, r₈, w₀, w₈]
    rfl, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], by rfl, by rfl, by rfl⟩
  simp only [Mem.writeW, Mem.readW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

/-- Disjoint ranges are separate. -/
theorem sep_of_disjoint {a b : Addr} {n k n' k' : Nat} (h : (⟨a, n'⟩ : Region).Disjoint ⟨b, k'⟩)
    (hn : n ≤ n') (hk : k ≤ k') : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

theorem sealTail_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State}
    (hs : SPre s₀ C D P W R L s) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) {T : Addr}
    (hgT : g .x6 = T) (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (tP : (⟨T, 16⟩ : Region).Disjoint ⟨P, L⟩) (wT : T.toNat + 16 ≤ 2 ^ 64) :
    WP isa (.seq (finish v.callee v.ctr.callee v.ctr.suffix 0)
        (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (.block sivOut) (.block restore))))) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.sp = s₀.sp ∧
        Frame (⟨T, 16⟩ :: endRegions W P L) s.mem s'.mem ∧
        Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
          (Spec.Aes.bytesAt s.mem P L) = (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.finish_wp v h hs.regs (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.AArch64.counter_ok h h₂.regs.x19 h₂.regs.rd h₂.regs.wr
  have f₃ : Frame (VG.Proof.AesSiv.AArch64.cntRegions W) s₂.mem s₃.mem := m₃ ▸ VG.Proof.AesSiv.AArch64.counter_frame _ _ _ _
  have hr₃ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₃ := h₂.regs.keep' (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₃ rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact VG.Proof.AesSiv.AArch64.counter_cnt s₂.mem W
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.ctr_wp v.ctr h hcp hPw hr₃ hcnt (by rw [g₃ _ (by decide) (by decide), h₂.hold.1, hs.x26])
    (by rw [g₃ _ (by decide) (by decide), h₂.hold.2, hs.x27])) fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hb := saved_bound
  have hsv₄ : Spill.Saved W g saved s₄.mem := by
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
  -- The copy of the IV to `T`.
  have a₂ : s₄.mem.readW (W + BitVec.ofNat 64 248) 64 = T := by
    rw [hsv₄ (.x6, 248) (by decide), hgT]
  have inT (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₄.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [h₄.regs.wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := wT; omega)⟩
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := sivOut_ok h₄.regs.x19 a₂
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 248) (n := 8) (by decide))
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 0) (n := 8) (by decide))
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 8) (n := 8) (by decide)) (inT 0 (by decide)) (inT 8 (by decide))
  have fT : Frame [⟨T, 16⟩] s₄.mem s₅.mem := by rw [m₅, k0]; exact Proof.Cmac.frame_store2 _ _ _
  have hsv₅ : Spill.Saved W g saved s₅.mem := hsv₄.frame fT fun p hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := hb p hp
    exact (tW.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.mono (restore_wp h (by rw [g₅ _ (by decide) (by decide), h₄.regs.x19]) (by rw [rd₅, h₄.regs.rd])
    (by rw [wr₅, h₄.regs.wr]) hsv₅) fun s₆ ⟨h₆a, _, sp₆, m₆⟩ => ?_
  have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  have hv : Spec.Aes.bytesAt s₄.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₄.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₄.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₄.data, Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h.c_w) hRb, ctxCiph_frame f₂ (fin_out (by decide) h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₃ (cnt_out h.p_w) hL, Proof.Cmac.bytesAt_frame f₂ (fin_out (by decide) h.p_w) hL]
  -- The copy.
  have hT : Spec.Aes.bytesAt s₆.mem T 16 = Spec.Aes.bytesAt s₄.mem W 16 := by
    have sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (tW.sub_right (h.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m₆, m₅, k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have hP : Spec.Aes.bytesAt s₆.mem P L = Spec.Aes.bytesAt s₄.mem P L := by
    rw [m₆]
    exact Proof.Cmac.bytesAt_frame fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact tP.symm) hL
  refine ⟨h₆a, by rw [sp₆, sp₅, h₄.regs.sp], ?_, by rw [hT, hP, hc, hv]; rfl⟩
  rw [m₆]
  refine (((f₂.sub (fin_sub h (by decide))).trans (f₃.sub (cnt_sub h))).trans (f₄.sub (ctr_sub h))).mono
    (fun r hr => List.mem_cons_of_mem _ hr) |>.trans (fT.mono fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Open`. -/
section

/-!
# AES-SIV on AArch64: the end of `vg_aes_siv_decrypt`

From S2V's state of the associated data on, `decrypt` sets the counter from
the IV it is given (`counter_ok`), decrypts the data in place with CTR
(`ctr_wp`), finishes S2V with the plaintext into `W + 112` (`finish_wp`),
compares the two IVs without a branch (`compare_ok`), ANDs every byte of the
data with the mask of the result (`maskData_wp`) and restores the registers
(`openTail_wp`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (or_xor_eq_zero le8_append_eq eqz)
open VG.Proof.CmacAes.AArch64 (k0 succ_ofNat read_one)
open VG.Proof.CmacAes.Stream.AArch64 (toNat_ofNat eval_zero eval_nonzero mz0 bytesAt_writeBytes_self)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The OR of the XORs of the halves of the IVs at `W` and `W + 112` is 0
exactly if they are equal. -/
theorem ivs_eq (m : Mem) (W : Addr) :
    ((m.readW (W + BitVec.ofNat 64 0) 64 ^^^ m.readW (W + BitVec.ofNat 64 tOff) 64) |||
        (m.readW (W + BitVec.ofNat 64 8) 64 ^^^ m.readW (W + BitVec.ofNat 64 (tOff + 8)) 64)) = 0 ↔
      Spec.Aes.bytesAt m W 16 = Spec.Aes.bytesAt m (W + BitVec.ofNat 64 tOff) 16 := by
  rw [or_xor_eq_zero, Proof.Cmac.bytesAt_split, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, le8_append_eq, Offset.add_add, k0]

theorem rot0 (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem sw64 (x : BitVec (8 * 8)) : BitVec.setWidth 64 x = x := BitVec.setWidth_eq x

theorem compare_ok (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .x0 = (if Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
        then 1 else 0) ∧
      s'.gpr .x11 = 0 - s'.gpr .x0 ∧
      (∀ r, r ≠ .x0 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₁ := h.inRW hrd hwr (d := tOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := 8) (n := 8) (by decide)
  have r₃ := h.inRW hrd hwr (d := tOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, Impl.AesSiv.AArch64.compare, tOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀, r₁, r₂, r₃]
    rfl, ?_, ?_, ?_, by rfl, by rfl, by rfl, by rfl⟩
  · have e := VG.Proof.AesSiv.AArch64.ivs_eq s.mem W
    have rd8 (a : Addr) : s.mem.read a 8 = s.mem.readW a 64 := (VG.Proof.AesSiv.AArch64.sw64 _).symm
    simp only [gpr_write, reduceCtorEq, ite_true, ite_false, VG.Proof.AesSiv.AArch64.rot0]
    rw [VG.Proof.AesSiv.AArch64.sw64]
    simp only [rd8]
    refine (eqz _).trans ?_
    by_cases hb : Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
    · exact (ite_eq_left (e.mpr hb)).trans (ite_eq_left hb).symm
    · exact (ite_eq_right (mt e.mp hb)).trans (ite_eq_right hb).symm
  · simp [gpr_write]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_write, h₁, h₂, h₃, h₄]

/-! ## Masking the data -/

/-- A byte ANDed with the mask `0 − r` of a result `r` of 0 or 1. -/
theorem mask_byte (b : BitVec (8 * 1)) (c : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) &&&
      ((0 : BitVec 64) - (if c then 1 else 0)))) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp [hj]

/-- The loop body of `maskData`. -/
abbrev maskBody : List Instr :=
  [.ldrb .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .strb .x9 .x6 0, .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]

theorem maskStep_ok (s : State) {A : Addr} {c : Bool} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (h11 : s.gpr .x11 = 0 - (if c then 1 else 0)) (rq : InRegions (s.rd ++ s.wr) A 1) (wq : InRegions s.wr A 1) :
    ∃ s', runBlock isa VG.Proof.AesSiv.AArch64.maskBody s = some s' ∧
      s'.mem = s.mem.writeW A ((if c then s.mem A else 0 : Byte)) ∧
      s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.AesSiv.AArch64.maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, ha, rq, wq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃],
    rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, h11, VG.Proof.AesSiv.AArch64.mask_byte, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- What `maskData` leaves: the data, or zeros. -/
structure Masked (s : State) (P : Addr) (L : Nat) (c : Bool) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P L else Spec.Siv.zeros L)
  other : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_length]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_succ, List.replicate_succ']

theorem maskData_wp (s : State) {P : Addr} {L : Nat} {c : Bool} (hL : L < 2 ^ 64) (h26 : s.gpr .x26 = P)
    (h27 : s.gpr .x27 = BitVec.ofNat 64 L) (h11 : s.gpr .x11 = 0 - (if c then 1 else 0))
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (P + BitVec.ofNat 64 i) 1) :
    WP isa maskData s (VG.Proof.AesSiv.AArch64.Masked s P L c) := by
  rw [maskData]
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩)
  generalize ht : (s.write .x .x6 (s.gpr .x26 + BitVec.ofNat 64 0)).write .x .x8
    (s.gpr .x27 + BitVec.ofNat 64 0) = s₁
  have x6₁ : s₁.gpr .x6 = P := by rw [← ht]; simp [gpr_write, h26]
  have x8₁ : s₁.gpr .x8 = BitVec.ofNat 64 L := by rw [← ht]; simp [gpr_write, h27]
  have g₁ : ∀ r, r ≠ .x6 → r ≠ .x8 → s₁.gpr r = s.gpr r := fun r a b => by rw [← ht]; simp [gpr_write, a, b]
  have e₁ : s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by rw [← ht]; exact ⟨rfl, rfl, rfl, rfl⟩
  have ev := eval_zero (s := s₁) (r := .x8) (x := L) hL x8₁
  refine WP.ite (decide (L = 0)) ev (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hL0 : L = 0 := of_decide_eq_true hb
    subst hL0
    refine ⟨?_, fun r a b _ => g₁ r a b, e₁.1, e₁.2.2.1, e₁.2.2.2⟩
    rw [e₁.2.1]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil]
  have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (body := .block VG.Proof.AesSiv.AArch64.maskBody) (c := .nonzero .x .x8)
    (fun (k : Nat) (t : State) => ∃ j, k = L - j ∧ j < L ∧ t.gpr .x6 = P + BitVec.ofNat 64 j ∧
      t.gpr .x8 = BitVec.ofNat 64 (L - j) ∧
      t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j) ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (L - 0) _ ⟨0, rfl, hL0, by rw [x6₁]; simp, by rw [x8₁, Nat.sub_zero],
      by rw [e₁.2.1]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil],
      fun r a b _ => g₁ r a b, e₁.1, e₁.2.2.1, e₁.2.2.2⟩
  rintro k t ⟨j, rfl, hj, x6, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x6', x8', g', sp', rd', wr'⟩ := VG.Proof.AesSiv.AArch64.maskStep_ok t (A := P + BitVec.ofNat 64 j) (c := c)
    (by rw [x6, BitVec.add_zero]) (by rw [g _ (by decide) (by decide) (by decide), h11])
    (by rw [rd, wr]; exact hr j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨P, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesSiv.AArch64.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesSiv.AArch64.mask_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesSiv.AArch64.length_mask]; omega), VG.Proof.AesSiv.AArch64.length_mask]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (j + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev' := eval_nonzero (s := t') (x := L - (j + 1)) (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : j + 1 = L
  · left
    exact ⟨by rw [ev']; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev']; simp; omega, L - (j + 1), by omega, j + 1, rfl, by omega,
      by rw [x6', x6, BitVec.add_assoc, succ_ofNat], x8'', hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩

/-! ## From S2V's state on -/

theorem openTail_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State}
    (hs : VG.Proof.AesSiv.AArch64.SPre s₀ C D P W R L s) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) :
    WP isa (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (finish v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore)))))) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.sp = s₀.sp ∧
        Frame (VG.Proof.AesSiv.AArch64.endRegions W P L) s.mem s'.mem ∧
        match Spec.Siv.openWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R)
            (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem W 16) (Spec.Aes.bytesAt s.mem P L) with
        | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
        | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  -- The counter.
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.AArch64.counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  have hr₁ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₁ := hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁
  have fc : Frame (VG.Proof.AesSiv.AArch64.cntRegions W) s.mem s₁.mem := m₁ ▸ VG.Proof.AesSiv.AArch64.counter_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hcnt : ∃ hi lo : BitVec 64, s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) := by
    rw [m₁]; exact VG.Proof.AesSiv.AArch64.counter_cnt s.mem W
  -- CTR.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.ctr_wp v.ctr h hcp hPw hr₁ hcnt (by rw [g₁ _ (by decide) (by decide), hs.x26])
    (by rw [g₁ _ (by decide) (by decide), hs.x27])) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  -- S2V into `W + 112`.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.finish_wp v h h₂.regs (out := tOff) (Or.inr rfl)) fun s₃ h₃ => ?_)
  have f₃ := h₃.frame
  -- The comparison.
  obtain ⟨s₄, run₄, x0₄, x11₄, g₄, sp₄, m₄, rd₄, wr₄⟩ := VG.Proof.AesSiv.AArch64.compare_ok h h₃.regs.x19 h₃.regs.rd h₃.regs.wr
  have hr₄ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₄ := h₃.regs.keep' (fun r hr => g₄ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    sp₄ rd₄ wr₄
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.maskData_wp s₄ (c := decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) h.lt
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.hold.1, h₂.x26])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.hold.2, h₂.x27])
    (by rw [x11₄, x0₄]; simp only [decide_eq_true_eq]) (fun i hi => h.inRP hr₄.rd hr₄.wr (by omega))
    (fun i hi => h.inWP hPw hr₄.wr (by omega))) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨P, L⟩] s₄.mem s₅.mem := by
    rw [h₅.mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesSiv.AArch64.length_mask]; exact Region.contains_self _ _)
  have hr₅ : VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L s₅ := hr₄.keep' (fun r hr => h₅.other r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)) h₅.sp h₅.rd h₅.wr
  have hsv₅ : Spill.Saved W g saved s₅.mem := by
    have hb := VG.Proof.AesSiv.AArch64.saved_bound
    refine (((hsv.frame fc fun p hp => ?_).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame
      (m' := s₅.mem) (by rw [← m₄]; exact f₅) fun p hp => ?_
    · have := hb p hp; exact VG.Proof.AesSiv.AArch64.cnt_dis (by omega) (by omega)
    · have := hb p hp; exact VG.Proof.AesSiv.AArch64.ctr_dis h (by omega) (by omega)
    · have := hb p hp
      exact VG.Proof.AesSiv.AArch64.fin_dis h (by decide) (by omega) (by simp only [tOff]; omega) (by omega) (by omega) (by omega)
    · have := hb p hp
      exact VG.Proof.AesSiv.AArch64.one_out (h.p_w.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  refine WP.mono (VG.Proof.AesSiv.AArch64.restore_wp h hr₅.x19 hr₅.rd hr₅.wr hsv₅) fun s₇ ⟨h₇a, h₇b, sp₇, m₇⟩ => ?_
  have x0₇ : s₇.gpr .x0 = s₄.gpr .x0 := by
    rw [h₇b _ (by decide), h₅.other _ (by decide) (by decide) (by decide)]
  -- The IV, the plaintext and S2V's end.
  have hV : Spec.Aes.bytesAt s₃.mem W 16 = Spec.Aes.bytesAt s.mem W 16 := by
    have d₃ := VG.Proof.AesSiv.AArch64.fin_dis h (out := tOff) (d := 0) (n := 16) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    have d₂ := VG.Proof.AesSiv.AArch64.ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have dc := VG.Proof.AesSiv.AArch64.cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at d₃ d₂ dc
    rw [Proof.Cmac.bytesAt_frame f₃ d₃ (by decide), Proof.Cmac.bytesAt_frame f₂ d₂ (by decide),
      Proof.Cmac.bytesAt_frame fc dc (by decide)]
  have hp : Spec.Aes.bytesAt s₂.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R)
      (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₂.data, VG.Proof.AesSiv.AArch64.ctxCiph_frame fc (VG.Proof.AesSiv.AArch64.cnt_out h.c_w) hRb, Proof.Cmac.bytesAt_frame fc (VG.Proof.AesSiv.AArch64.cnt_out h.p_w) hL]
  have hT : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) := by
    rw [h₃.out, hp, VG.Proof.AesSiv.AArch64.ctxMac_frame f₂ (VG.Proof.AesSiv.AArch64.ctr_out hcp h.c_w) hRb, VG.Proof.AesSiv.AArch64.ctxMac_frame fc (VG.Proof.AesSiv.AArch64.cnt_out h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₂ (VG.Proof.AesSiv.AArch64.ctr_out h.d_p h.d_w) (by decide),
      Proof.Cmac.bytesAt_frame fc (VG.Proof.AesSiv.AArch64.cnt_out h.d_w) (by decide)]
  have hd : Spec.Aes.bytesAt s₇.mem P L = if Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 then
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L) else Spec.Siv.zeros L := by
    have hl := VG.Proof.AesSiv.AArch64.length_mask s₄.mem P (decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) L
    have hw := bytesAt_writeBytes_self s₄.mem P (by rw [hl]; exact h.lt)
    rw [hl] at hw
    rw [m₇, h₅.mem, hw, m₄, Proof.Cmac.bytesAt_frame f₃ (VG.Proof.AesSiv.AArch64.fin_out (by decide) h.p_w) hL, hp]
    simp only [decide_eq_true_eq]
  have f₅' : Frame (VG.Proof.AesSiv.AArch64.endRegions W P L) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₇a, by rw [sp₇, hr₅.sp], ?_, ?_⟩
  · rw [m₇]
    rw [m₄] at f₅'
    exact (((fc.sub (VG.Proof.AesSiv.AArch64.cnt_sub h)).trans (f₂.sub (VG.Proof.AesSiv.AArch64.ctr_sub h))).trans (f₃.sub (VG.Proof.AesSiv.AArch64.fin_sub h (by decide)))).trans f₅'
  · rw [x0₇, x0₄, hd, hV, hT]
    simp only [Spec.Siv.openWith]
    by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) = Spec.Aes.bytesAt s.mem W 16
    · rw [ite_eq_left hc, ite_eq_left hc.symm, ite_eq_left hc.symm]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc)]
      exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Enc`. -/
section

/-!
# AES-SIV on AArch64: `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

Both save the registers in the working space and keep the arguments in
callee-saved registers (`encPre`), start S2V into `D = W + 2560` with the
CMAC of the zero block (`start_wp`), absorb the components of associated
data, one per iteration (`ads_wp`), and then go on as `sealTail_wp` and
`openTail_wp` say from S2V's state. The save also leaves the address of
`siv` at `W + 248` (`SivArg`), from which `encrypt` copies the IV to `siv`
at its end and `decrypt` the received IV to the working space after S2V of
the associated data (`sivIn_wp`).

The proofs are on the state whose writable regions are the data, `siv` for
`encrypt`, the first 2560 bytes of the working space and `D` (`EPre`);
`Verified.lean` moves them to the shared contracts with the working space as
an argument, one region of 2576 bytes.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 mn)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs toNat_ofNat toNat_add_lt eval_zero eval_nonzero)

/-- What `encrypt` and `decrypt` need of their arguments, on the state with
narrowed permissions: the key context `C`, the rounds `R`, the `N`
descriptors at `A`, the data `P` (`L` bytes), the working space `W`, and
S2V's state `D` after its first 2560 bytes. Each component a descriptor
lists is a message as the data is (`comps`). -/
structure EPre (s₀ : State) (C A P W D : Addr) (R N L : Nat) : Prop where
  env : VG.Proof.AesSiv.AArch64.Env s₀ C D P W R L
  c_d : (⟨C, 512⟩ : Region).Disjoint ⟨D, 16⟩
  cp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩
  pw : (⟨P, L⟩ : Region) ∈ s₀.wr
  dw : (⟨D, 16⟩ : Region) ∈ s₀.wr
  x0 : s₀.gpr .x0 = C
  x1 : s₀.gpr .x1 = BitVec.ofNat 64 R
  x2 : s₀.gpr .x2 = A
  x3 : s₀.gpr .x3 = BitVec.ofNat 64 N
  x4 : s₀.gpr .x4 = P
  x5 : s₀.gpr .x5 = BitVec.ofNat 64 L
  x7 : s₀.gpr .x7 = W
  descIn : (⟨A, N * 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  desc_w : (⟨A, N * 16⟩ : Region).Disjoint ⟨W, 2560⟩
  desc_d : (⟨A, N * 16⟩ : Region).Disjoint ⟨D, 16⟩
  wA : A.toNat + N * 16 ≤ 2 ^ 64
  comps : ∀ r ∈ Sig.listed 64 s₀.mem .u8 A N, VG.Proof.AesSiv.AArch64.Env s₀ C D r.base W R r.len

variable {s₀ : State} {C A P W D : Addr} {R N L : Nat}

theorem EPre.N_lt (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) : N < 2 ^ 64 := by have := h.wA; omega

/-! ## The save and S2V's first state -/

/-- The memory after the save and the zeroing of the zero block and `D`. -/
def startMem (s₀ : State) (W D : Addr) : Mem :=
  Proof.Cmac.zero2 (Proof.Cmac.zero2 (Spill.saveMem s₀.mem W s₀.gpr saved) (W + BitVec.ofNat 64 zOff)) D

theorem saved_ge : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 256 := by decide

/-- The registers after the save and the moves of the arguments. -/
structure Started (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = C
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = W + BitVec.ofNat 64 zOff
  x4 : s.gpr .x4 = BitVec.ofNat 64 16
  x5 : s.gpr .x5 = W + BitVec.ofNat 64 csOff
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x24 : s.gpr .x24 = A
  x25 : s.gpr .x25 = BitVec.ofNat 64 N
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.AesSiv.AArch64.startMem s₀ W D

theorem start_ok (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) :
    WP isa (.block (encPre ++ startPre)) s₀ (VG.Proof.AesSiv.AArch64.Started s₀ C A P W D R N L) := by
  have e := h.env
  have hwD := e.wD
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (W + BitVec.ofNat 64 (dOff + d)) 8 := by
    rw [← Offset.add_add, ← e.hD]; exact ⟨_, h.dw, Offset.contains_base _ hd (by omega)⟩
  have z₀ := e.inW (s := s₀) rfl (d := zOff) (n := 8) (by decide)
  have z₁ := e.inW (s := s₀) rfl (d := zOff + 8) (n := 8) (by decide)
  have d₀ := inD 0 (by decide)
  have d₁ := inD 8 (by decide)
  rw [Nat.add_zero] at d₀
  rw [show encPre ++ startPre = Spill.saveCode .x7 saved ++
    ([mov .x19 .x7, mov .x20 .x0, mov .x21 .x1, mov .x24 .x2, mov .x25 .x3, mov .x26 .x4, mov .x27 .x5] ++
      startPre) from rfl]
  refine Spill.save_ok (fun p hp => saved_fits.1 p hp) (fun p hp => by
    have := saved_bound p hp; rw [h.x7]; exact e.inW rfl (by omega)) ?_
  refine WP.of_runBlock ⟨_, by
    simp (config := {decide := true}) only [startPre, mov, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write,
      mem_write, rd_write, wr_write, ite_true, ite_false, Option.bind_some, BitVec.setWidth_eq, k0, h.x7, z₀, z₁,
      d₀, d₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  all_goals try simp (config := {decide := true}) only [gpr_write, ite_true, ite_false, h.x0, h.x1, h.x2, h.x3,
    h.x4, h.x5, Proof.CmacAes.Stream.AArch64.mz16, e.hD, BitVec.setWidth_eq]
  simp only [mem_write, VG.Proof.AesSiv.AArch64.startMem, Proof.Cmac.zero2, Mem.writeW, Proof.CmacAes.Stream.AArch64.mz0, Offset.add_add]
  rfl

/-- The arguments of `vg_cmac_aes_finalize` for S2V's first state: the
context as the key, the state `D`, the zero block at `W + 16` and the working
space at `W + 256`. -/
theorem Started.fargs (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) {s : State} (hs : VG.Proof.AesSiv.AArch64.Started s₀ C A P W D R N L s) :
    FArgs s C D (W + BitVec.ofNat 64 zOff) (W + BitVec.ofNat 64 csOff) 16 R :=
  h.env.fargs' hs.rd hs.wr (h.env.d_w.sub_right (h.env.sW (by decide))) h.c_d h.env.wD (VG.Proof.AesSiv.AArch64.cov_base h.dw (by simp))
    (h.env.d_w.sub_right (h.env.sW (d := zOff) (n := 16) (by decide))).symm
    (Offset.disjoint W (by decide) (by decide) (by have := h.env.wW; omega))
    (by rw [toNat_add_lt W h.env.wW (show zOff < 2560 by decide)]; have := h.env.wW; simp only [zOff]; omega)
    (Covers.right (VG.Proof.AesSiv.AArch64.cov_off h.env.workIn (by simp [zOff]))) (by decide)
    hs.x0 hs.x1 hs.x2 hs.x3 hs.x4 hs.x5

/-- The last block of the zero block, with `K1` from memory: `K1 ⊕ 0`, and
XORing it into the zero state leaves it. -/
theorem xor_lastBlock_zeros (m : Mem) (p : Addr) (k2 : List Byte) :
    Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16) =
      Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16) :=
  VG.Proof.AesSiv.xor_zeros (by simp [Spec.Cmac.lastBlock, Proof.Cmac.length_zeros, Proof.Cmac.length_xor,
                    Proof.Cmac.bytesAt_length])

/-- The state before the `i`-th component of associated data (and, for
`i = N`, after the last): `D` is S2V's state of the first `i`, `x24` and
`x25` the next descriptor's address and how many are left, and the data in
`x26` and `x27`. -/
structure AInv (s₀ : State) (C A P W D : Addr) (R N L : Nat) (i : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = C
  x21 : s.gpr .x21 = BitVec.ofNat 64 R
  x24 : s.gpr .x24 = A + BitVec.ofNat 64 (16 * i)
  x25 : s.gpr .x25 = BitVec.ofNat 64 (N - i)
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : i ≤ N
  saved : Spill.Saved W s₀.gpr saved s.mem
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) ((Spec.Siv.components 64 s₀.mem A N).take i)

/-- The save, then S2V's first state `D = AES-CMAC(K1, <zero>)` with
`vg_cmac_aes_finalize` of the zero block from a zero state. -/
theorem start_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) {s₂ : State}
    (h₂ : VG.Proof.AesSiv.AArch64.Started s₀ C A P W D R N L s₂) :
    WP isa (callFinalize v.ctr.callee v.ctr.suffix) s₂ (VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L 0) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  refine WP.mono (VG.Proof.AesSiv.AArch64.finr_call v.ctr _ (h₂.fargs h)) fun s₃ h₃ => ?_
  have g₃ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s₂.gpr r := h₃.saved r hr h30
  -- What the save and S2V's start write.
  have fs : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s₂.mem := by
    rw [h₂.mem, VG.Proof.AesSiv.AArch64.startMem]
    refine ((Spill.saveMem_frame (lo := 16) (n := 2544) (fun p hp => by have := VG.Proof.AesSiv.AArch64.saved_ge p hp; omega)
      (by decide) _ _ _).mono (by simp)).trans (((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have f₃ : Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 csOff, 2176⟩] s₂.mem s₃.mem := h₃.frame
  have fall : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s₃.mem :=
    fs.trans (f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩)
  refine ⟨by rw [g₃ _ (by decide) (by decide), h₂.x19], by rw [g₃ _ (by decide) (by decide), h₂.x20],
    by rw [g₃ _ (by decide) (by decide), h₂.x21], by rw [g₃ _ (by decide) (by decide), h₂.x24, Nat.mul_zero, k0],
    by rw [g₃ _ (by decide) (by decide), h₂.x25, Nat.sub_zero], by rw [g₃ _ (by decide) (by decide), h₂.x26],
    by rw [g₃ _ (by decide) (by decide), h₂.x27], by rw [h₃.sp, h₂.sp], by rw [h₃.rd, h₂.rd],
    by rw [h₃.wr, h₂.wr], Nat.zero_le _, ?_, fall, ?_⟩
  · -- The slots, past what S2V's start writes.
    have sv0 := Spill.saveMem_saved VG.Proof.AesSiv.AArch64.saved_fits s₀.mem W s₀.gpr
    have sv1 := sv0.frame (Proof.Cmac.frame_store2 (W + BitVec.ofNat 64 zOff) 0 0) fun p hp r hr => by
      have := VG.Proof.AesSiv.AArch64.saved_ge p hp
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by simp only [zOff]; omega) (by omega) (by decide)
    have sv2 := sv1.frame (Proof.Cmac.frame_store2 D 0 0) fun p hp r hr => by
      have := VG.Proof.AesSiv.AArch64.saved_ge p hp
      simp only [List.mem_singleton] at hr; subst hr
      exact (e.d_w.sub_right (e.sW (by omega))).symm
    have sv : Spill.Saved W s₀.gpr saved s₂.mem := by rw [h₂.mem]; exact sv2
    refine sv.frame f₃ fun p hp r hr => ?_
    have := VG.Proof.AesSiv.AArch64.saved_ge p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (e.d_w.sub_right (e.sW (by omega))).symm
    · exact Offset.disjoint W (by simp only [csOff]; omega) (by omega) (by decide)
  · -- `CIPH(0 ⊕ (0 ⊕ K1))`, the CMAC of `<zero>`.
    have ctx {d n : Nat} (hd : d + n ≤ 512) :
        Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₀.mem (C + BitVec.ofNat 64 d) n :=
      Proof.Cmac.bytesAt_frame fs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (e.c_w.sub_left (Offset.sub_base C hd)).sub_right (e.sW (by decide))
        · exact h.c_d.sub_left (Offset.sub_base C hd)) (by omega)
    have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 zOff) 16 = Spec.Cmac.zeros 16 := by
      have fr : Frame [⟨D, 16⟩] (Proof.Cmac.zero2 (Spill.saveMem s₀.mem W s₀.gpr saved) (W + BitVec.ofNat 64 zOff))
          (VG.Proof.AesSiv.AArch64.startMem s₀ W D) := Proof.Cmac.frame_store2 _ _ _
      rw [h₂.mem, Proof.Cmac.bytesAt_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (e.d_w.sub_right (e.sW (d := zOff) (n := 16) (by decide))).symm) (by decide)]
      exact Proof.Cmac.zero2_bytes _ _
    have hd : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Cmac.zeros 16 := by
      rw [h₂.mem, VG.Proof.AesSiv.AArch64.startMem]; exact Proof.Cmac.zero2_bytes _ _
    have hk1 := ctx (d := 240) (n := 16) (by decide)
    have hk2 := ctx (d := 256) (n := 16) (by decide)
    have hs := ctx (d := 0) (n := 16 * (R + 1)) (by omega)
    rw [k0] at hs
    rw [List.take_zero, h₃.out, mn, hz, hd, hk1, hk2, hs, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart,
      Spec.Siv.ctxMac, Spec.Siv.schedCiph, show Spec.Siv.zero = [] ++ Spec.Cmac.zeros 16 from rfl,
      Siv.cmacWith_split _ _ _ rfl (by decide) (Or.inl rfl), chain_blocks_nil,
      Proof.Cmac.xor_comm (Spec.Cmac.zeros 16)]
    simp only [VG.Proof.AesSiv.AArch64.xor_lastBlock_zeros]
    rfl

/-! ## The components of associated data -/

/-- The slice the `i`-th descriptor at `A` lists. -/
def comp (m : Mem) (A : Addr) (i : Nat) : Region :=
  ⟨m.readW (A + BitVec.ofNat 64 (16 * i)) 64, (m.readW (A + BitVec.ofNat 64 (16 * i + 8)) 64).toNat⟩

theorem listed_getElem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Sig.listed 64 m .u8 A N)[i]'(by simp [Sig.listed, hi]) = VG.Proof.AesSiv.AArch64.comp m A i := by
  simp only [Sig.listed, List.getElem_map, List.getElem_range, BitVec.setWidth_eq, Elem.size, Nat.mul_one, VG.Proof.AesSiv.AArch64.comp,
    Offset.add_add]
  rw [Nat.mul_comm]

theorem comp_mem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) : VG.Proof.AesSiv.AArch64.comp m A i ∈ Sig.listed 64 m .u8 A N := by
  rw [← VG.Proof.AesSiv.AArch64.listed_getElem m A hi]; exact List.getElem_mem _

theorem components_take_succ (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 64 m A N).take (i + 1) =
      (Spec.Siv.components 64 m A N).take i ++ [Spec.Aes.bytesAt m (VG.Proof.AesSiv.AArch64.comp m A i).base (VG.Proof.AesSiv.AArch64.comp m A i).len] := by
  have hl : i < (Spec.Siv.components 64 m A N).length := by simp [Spec.Siv.components, Sig.listed, hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some]
  simp only [Spec.Siv.components, List.getElem_map, VG.Proof.AesSiv.AArch64.listed_getElem m A hi]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-- The descriptors are as on entry. -/
theorem AInv.desc (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) {i : Nat} {s : State} (hi : VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L i s) {d : Nat}
    (hd : d + 8 ≤ N * 16) : s.mem.readW (A + BitVec.ofNat 64 d) 64 = s₀.mem.readW (A + BitVec.ofNat 64 d) 64 :=
  hi.frame.readW (Offset.contains_base A hd (by have := h.wA; omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.desc_w.sub_right (h.env.sW (by decide))
    · exact h.desc_d) (by decide)

/-- The component's address and length from its descriptor. -/
theorem adNext_wp (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L i s) :
    WP isa (.block adNext) s fun s' =>
      VG.Proof.AesSiv.AArch64.Regs s₀ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len s' ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  have c₀ : InRegions (s.rd ++ s.wr) (s.gpr .x24 + BitVec.ofNat 64 0) 8 := by
    rw [hi.rd, hi.wr, hi.x24, k0]
    exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have c₈ : InRegions (s.rd ++ s.wr) (s.gpr .x24 + BitVec.ofNat 64 8) 8 := by
    rw [hi.rd, hi.wr, hi.x24, Offset.add_add]
    exact ⟨_, h.descIn, Offset.contains_base A (by omega) (by have := h.wA; omega)⟩
  have d₀ := hi.desc h (d := 16 * i) (by omega)
  have d₈ := hi.desc h (d := 16 * i + 8) (by omega)
  rw [adNext]
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_ldr_x (by decide) c₀, runStep_some, runBlock_cons,
      exec_ldr_x (by decide) (by simpa only [gpr_write, rd_write, wr_write, reduceCtorEq, ite_false] using c₈),
      runStep_some, runBlock_nil], ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, hi.sp, hi.rd, hi.wr⟩
    all_goals simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hi.x19, hi.x20, hi.x21, mem_write, hi.x24,
      Offset.add_add, Nat.add_zero, BitVec.setWidth_eq, VG.Proof.AesSiv.AArch64.comp, d₀, d₈]
    exact Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq rfl
  · intro r a b; simp [gpr_write, a, b]
  · rfl

/-- One component: its descriptor read (`adNext_wp`), its CMAC into the
working space (`cmacOf_wp`) and the step of S2V (`adStep_wp`). -/
theorem adBody_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) {i : Nat} (hiN : i < N)
    {s : State} (hi : VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep))) s
      fun s' => VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L (i + 1) s' := by
  have e := h.env
  have hN := h.N_lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  have hQ := h.comps _ (VG.Proof.AesSiv.AArch64.comp_mem s₀.mem A hiN)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.adNext_wp h hiN hi) fun s₁ ⟨hr₁, g₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.cmacOf_wp v hQ hr₁) fun s₂ h₂ => ?_)
  have hr₂ := h₂.regs
  refine WP.mono (VG.Proof.AesSiv.AArch64.adStep_wp hr₂.x19 e.hD (by rw [hr₂.wr]; exact h.dw) (by rw [hr₂.wr]; exact e.workIn) e.d_w e.wD
    e.wW) fun s₃ ⟨g₃, x24₃, x25₃, sp₃, rd₃, wr₃, acc₃, f₃⟩ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s₂.mem := m₁ ▸ h₂.frame
  have k₂ (r : Reg) (hr : r ∈ [Reg.x24, .x25, .x26, .x27]) : s₂.gpr r = s.gpr r := by
    rw [h₂.hold r hr, g₁ r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr)]
  have g₃' (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21, .x26, .x27]) : s₃.gpr r = s₂.gpr r :=
    g₃ r (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr)
      (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr) (VG.Proof.AesSiv.AArch64.dec_ne (by decide) hr)
  have sub₂ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩],
      ∃ r' ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by decide)⟩
  refine ⟨by rw [g₃' _ (by decide), hr₂.x19], by rw [g₃' _ (by decide), hr₂.x20],
    by rw [g₃' _ (by decide), hr₂.x21], ?_, ?_, by rw [g₃' _ (by decide), k₂ _ (by decide), hi.x26],
    by rw [g₃' _ (by decide), k₂ _ (by decide), hi.x27], by rw [sp₃, hr₂.sp], by rw [rd₃, hr₂.rd],
    by rw [wr₃, hr₂.wr], hiN, ?_, ?_, ?_⟩
  · rw [x24₃, k₂ _ (by decide), hi.x24, Offset.add_add, Nat.mul_succ]
  · rw [x25₃, k₂ _ (by decide), hi.x25, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · refine (hi.saved.frame f₂ fun p hp r hr => ?_).frame f₃ fun p hp r hr => ?_
    · have := VG.Proof.AesSiv.AArch64.saved_ge p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · have := VG.Proof.AesSiv.AArch64.saved_ge p hp
      simp only [List.mem_singleton] at hr; subst hr
      exact (e.d_w.sub_right (e.sW (by omega))).symm
  · exact (hi.frame.trans (f₂.sub sub₂)).trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · -- `D = dbl(D) ⊕ CMAC(Sᵢ)`.
    have dD : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Aes.bytesAt s.mem D 16 :=
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.d_w.sub_right (e.sW (by decide))) (by decide)
    have hf3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact e.c_w.sub_right (e.sW (by decide))
      · exact h.c_d
    have hq3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩],
        (⟨(VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base, (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hQ.p_w.sub_right (e.sW (by decide))
      · exact hQ.d_p.symm
    have o₂ := h₂.out
    rw [m₁, VG.Proof.AesSiv.AArch64.ctxMac_frame hi.frame hf3 hRb, Proof.Cmac.bytesAt_frame hi.frame hq3 (by have := hQ.lt; omega)] at o₂
    rw [acc₃, dD, o₂, hi.acc, VG.Proof.AesSiv.AArch64.components_take_succ s₀.mem A hiN, VG.Proof.AesSiv.AArch64.s2vAcc_snoc]
    rfl

/-- S2V over all the components, if there are any. -/
theorem ads_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) {s : State}
    (hs : VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L 0 s) :
    WP isa (s2vAds v.callee v.ctr.callee v.ctr.suffix) s (VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L N) := by
  have hN := h.N_lt
  have ev := eval_zero (s := s) (r := .x25) (x := N) hN (by rw [hs.x25, Nat.sub_zero])
  refine WP.ite (decide (N = 0)) ev (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hN0 : N = 0 := of_decide_eq_true hb
    subst hN0; exact hs
  have hN0 : 0 < N := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .nonzero .x .x25)
    (fun (n : Nat) (t : State) => ∃ i, n = N - i ∧ i < N ∧ VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L i t) ?_ (N - 0) s
    ⟨0, rfl, hN0, hs⟩
  rintro n t ⟨i, rfl, hiN, hi⟩
  refine WP.mono (VG.Proof.AesSiv.AArch64.adBody_wp v h hiN hi) fun t' hi' => ?_
  have ev' := eval_nonzero (s := t') (r := .x25) (x := N - (i + 1)) (by omega) hi'.x25
  by_cases he : i + 1 = N
  · refine Or.inl ⟨by rw [ev']; simp [he], he ▸ hi'⟩
  · exact Or.inr ⟨by rw [ev']; simp; omega, N - (i + 1), by omega, i + 1, rfl, by omega, hi'⟩

/-- What S2V of the associated data leaves: the registers as
`sealTail_wp` and `openTail_wp` take them, the saved registers, and `D`. -/
structure SDone (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  spre : VG.Proof.AesSiv.AArch64.SPre s₀ C D P W R L s
  saved : Spill.Saved W s₀.gpr saved s.mem
  frame : Frame [⟨W + BitVec.ofNat 64 16, 2544⟩, ⟨D, 16⟩] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.components 64 s₀.mem A N)

/-- The data and its length in `x22` and `x23`. -/
theorem adsEnd_wp {s : State} (hs : VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L N s) :
    WP isa (.block [mov .x22 .x26, mov .x23 .x27]) s (VG.Proof.AesSiv.AArch64.SDone s₀ C A P W D R N L) := by
  obtain ⟨s₃, run₃, x22, x23, g₃, sp₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.AArch64.ctrEnd_ok hs.x26 hs.x27
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨?_, ?_, ?_, x22, x23, by rw [sp₃, hs.sp], by rw [rd₃, hs.rd],
    by rw [wr₃, hs.wr]⟩, by rw [g₃ _ (by decide) (by decide), hs.x26], by rw [g₃ _ (by decide) (by decide), hs.x27]⟩,
    m₃ ▸ hs.saved, m₃ ▸ hs.frame, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hs.x19]
  · rw [g₃ _ (by decide) (by decide), hs.x20]
  · rw [g₃ _ (by decide) (by decide), hs.x21]
  · have hl : (Spec.Siv.components 64 s₀.mem A N).length = N := by simp [Spec.Siv.components, Sig.listed]
    rw [m₃, hs.acc, List.take_of_length_le (Nat.le_of_eq hl)]

theorem encS2v_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) :
    WP isa (encS2v v.callee v.ctr.callee v.ctr.suffix) s₀ (VG.Proof.AesSiv.AArch64.SDone s₀ C A P W D R N L) := by
  exact WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.start_ok h) fun _ h₀ => WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.start_wp v h h₀) fun _ h₁ =>
    WP.seq (WP.mono (VG.Proof.AesSiv.AArch64.ads_wp v h h₁) fun _ h₂ => VG.Proof.AesSiv.AArch64.adsEnd_wp h₂)))

/-! ## The whole functions -/

/-- The key context, the data and the IV are outside what S2V of the
associated data writes. -/
theorem EPre.sdone_dis (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨C, 512⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨P, L⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 2544⟩ : Region), ⟨D, 16⟩], (⟨W, 16⟩ : Region).Disjoint r) := by
  have e := h.env
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
  · exact e.c_w.sub_right (e.sW (by decide))
  · exact h.c_d
  · exact e.p_w.sub_right (e.sW (by decide))
  · exact e.d_p.symm
  · exact Offset.base_disjoint W (by decide) (by have := e.wW; omega)
  · exact (e.d_w.sub_right (Region.sub_prefix (by decide))).symm

variable {T : Addr}

/-- The synthetic IV `T`, whose address is in `x6`: its 16 bytes are apart
from the data, the working space and `D`. -/
structure SivArg (s₀ : State) (P W D T : Addr) (L : Nat) : Prop where
  x6 : s₀.gpr .x6 = T
  tIn : (⟨T, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  t_p : (⟨T, 16⟩ : Region).Disjoint ⟨P, L⟩
  t_w : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩
  t_d : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16⟩
  wT : T.toNat + 16 ≤ 2 ^ 64

theorem encrypt_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (hT : SivArg s₀ P W D T L) (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) :
    WP isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' =>
      ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -⟩ := h.sdone_dis
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.mono (sealTail_wp v e h.cp h.pw hs.spre hs.saved
    hT.x6 hTw hT.t_w hT.t_p hT.wT) fun s' ⟨g', sp', _, out'⟩ => ⟨⟨g', sp'⟩, ?_⟩)
  rw [ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
    Proof.Cmac.bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
  rw [Spec.Siv.encryptWith_eq]
  exact out'

/-- The copy of the IV at `T`, whose address is at `W + 248`, to `W`. -/
theorem sivIn_ok {s : State} (h19 : s.gpr .x19 = W)
    (aT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = T)
    (r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 248) 8)
    (r₀ : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 0) 8) (r₈ : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 8) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 0) 8) (w₈ : InRegions s.wr (W + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa sivIn s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 0) (s.mem.readW (T + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 8)
        ((s.mem.writeW (W + BitVec.ofNat 64 0) (s.mem.readW (T + BitVec.ofNat 64 0) 64)).readW
          (T + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [Mem.readW, BitVec.setWidth_eq] at aT
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self,
      sivIn, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      h19, r₂, aT, r₀, r₈, w₀, w₈]
    rfl, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], by rfl, by rfl, by rfl⟩
  simp only [Mem.writeW, Mem.readW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

/-- What `sivIn` keeps of S2V's end, with the received IV now at `W`. -/
theorem sivIn_wp (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) {s : State}
    (hs : SDone s₀ C A P W D R N L s) :
    WP isa (.block sivIn) s fun s' => SPre s₀ C D P W R L s' ∧ Spill.Saved W s₀.gpr saved s'.mem ∧
      Frame [⟨W, 16⟩] s.mem s'.mem ∧ Spec.Aes.bytesAt s'.mem W 16 = Spec.Aes.bytesAt s₀.mem T 16 := by
  have e := h.env
  have hr := hs.spre.regs
  have a₂ : s.mem.readW (W + BitVec.ofNat 64 248) 64 = T := by rw [hs.saved (.x6, 248) (by decide), hT.x6]
  have iT (d : Nat) (hd : d + 8 ≤ 16) : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 d) 8 := by
    rw [hr.rd, hr.wr]; exact ⟨_, hT.tIn, Offset.contains_base T hd (by have := hT.wT; omega)⟩
  obtain ⟨s', run, m', g', sp', rd', wr'⟩ := sivIn_ok hr.x19 a₂ (e.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide))
    (iT 0 (by decide)) (iT 8 (by decide)) (e.inW hr.wr (d := 0) (by decide)) (e.inW hr.wr (d := 8) (by decide))
  have fW : Frame [⟨W, 16⟩] s.mem s'.mem := by rw [m', k0]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.of_runBlock ⟨s', run, ⟨hr.keep' (fun r hr' => g' r (by rintro rfl; revert hr'; decide)
      (by rintro rfl; revert hr'; decide)) sp' rd' wr', by rw [g' _ (by decide) (by decide), hs.spre.x26],
      by rw [g' _ (by decide) (by decide), hs.spre.x27]⟩,
    hs.saved.frame fW fun p hp r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Offset.disjoint_base W (by have := saved_ge p hp; omega) (by have := saved_ge p hp; have := e.wW; omega),
    fW, ?_⟩
  have sp8 : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    sep_of_disjoint ((hT.t_w.sub_left (Offset.sub_base T (d := 8) (n := 8) (by decide))).sub_right
      (Region.sub_prefix (len := 16) (by decide))) (by decide) (by decide)
  rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
    Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  exact Proof.Cmac.bytesAt_frame hs.frame (fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hT.t_w.sub_right (e.sW (by decide))
    · exact hT.t_d) (by decide)

theorem decrypt_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (hT : SivArg s₀ P W D T L) :
    WP isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' =>
      ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem T 16) (Spec.Aes.bytesAt s₀.mem P L) with
      | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega
  obtain ⟨dC, dP, -⟩ := h.sdone_dis
  have wC : ∀ r ∈ [(⟨W, 16⟩ : Region)], (⟨C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact e.c_w.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.seq (WP.mono (sivIn_wp h hT hs)
    fun s₁ ⟨sp₁, sv₁, f₁, v₁⟩ => WP.mono (openTail_wp v e h.cp h.pw sp₁ sv₁)
    fun s' ⟨g', sp', _, out'⟩ => ⟨⟨g', sp'⟩, ?_⟩))
  rw [ctxMac_frame f₁ wC hRb, ctxCiph_frame f₁ wC hRb,
    Proof.Cmac.bytesAt_frame (p := P) f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact e.p_w.sub_right (Region.sub_prefix (len := 16) (by decide))) (by have := e.lt; omega),
    Proof.Cmac.bytesAt_frame (p := D) f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact e.d_w.sub_right (Region.sub_prefix (len := 16) (by decide))) (by decide), v₁,
    ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
    Proof.Cmac.bytesAt_frame hs.frame dP (by have := e.lt; omega), hs.acc] at out'
  rw [Spec.Siv.decryptWith_eq]
  exact out'

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.EncCT`. -/
section

/-!
# AES-SIV on AArch64: `encrypt` and `decrypt` are constant time

Two runs with the same public arguments and the same descriptors (`EPub`)
leak the same trace. The taint analysis proves the straight-line pieces from
the registers that are public, with what correctness says about the values
they load: in each iteration the component's address and length from the
descriptor (`adNext_wp`), the same in both runs since the descriptors are.
The calls are related by their callees' contracts (`fin_rel`, `cmacOf_rel`,
`finish_rel`, `ctr_rel'`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs fin_rel eval_zero eval_nonzero)

variable {s₀ s₀' : State} {C A P W D : Addr} {R N L : Nat}

/-- What two runs agree on besides the arguments `EPre` names: the stack
pointer and the descriptors. -/
structure EPub (s₀ s₀' : State) (A : Addr) (N : Nat) : Prop where
  sp : s₀.sp = s₀'.sp
  desc : ∀ j < N * 16, s₀.mem (A + BitVec.ofNat 64 j) = s₀'.mem (A + BitVec.ofNat 64 j)

/-- The same descriptors list the same components. -/
theorem EPub.comp_eq (hq : VG.Proof.AesSiv.AArch64.EPub s₀ s₀' A N) {i : Nat} (hi : i < N) : VG.Proof.AesSiv.AArch64.comp s₀.mem A i = VG.Proof.AesSiv.AArch64.comp s₀'.mem A i := by
  have r {d : Nat} (hd : d + 8 ≤ N * 16) : s₀.mem.readW (A + BitVec.ofNat 64 d) 64 =
      s₀'.mem.readW (A + BitVec.ofNat 64 d) 64 := by
    have e := Mem.read_congr (m := s₀.mem) (m' := s₀'.mem) (a := A + BitVec.ofNat 64 d) (n := 64 / 8)
      fun j hj => by rw [Offset.add_add]; exact hq.desc (d + j) (by omega)
    simp only [Mem.readW, e]
  unfold VG.Proof.AesSiv.AArch64.comp
  rw [r (d := 16 * i) (by omega), r (d := 16 * i + 8) (by omega)]

/-- The save and S2V's first state. -/
theorem start_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L)
    (h' : VG.Proof.AesSiv.AArch64.EPre s₀' C A P W D R N L) (hq : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (encPre ++ startPre)) (callFinalize v.ctr.callee v.ctr.suffix))
      fun a b => AInv s₀ C A P W D R N L 0 a ∧ AInv s₀' C A P W D R N L 0 b := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x7])
      (.block (encPre ++ startPre)) hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine VG.Proof.CmacAes.AArch64.agree_of hq fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.x0, h'.x0]
    · rw [h.x1, h'.x1]
    · rw [h.x2, h'.x2]
    · rw [h.x3, h'.x3]
    · rw [h.x4, h'.x4]
    · rw [h.x5, h'.x5]
    · rw [h.x7, h'.x7]) hA).wp
    (F₁ := Started s₀ C A P W D R N L) (F₂ := Started s₀' C A P W D R N L)
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨start_ok h, start_ok h'⟩
  have f := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun a b => VG.Proof.AesSiv.AArch64.Started s₀ C A P W D R N L a ∧ VG.Proof.AesSiv.AArch64.Started s₀' C A P W D R N L b)
    fun a b hab => ⟨hab.1.fargs h, hab.2.fargs h', by rw [hab.1.sp, hab.2.sp, hq]⟩).wp
    (F₁ := VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L 0) (F₂ := VG.Proof.AesSiv.AArch64.AInv s₀' C A P W D R N L 0)
    fun a b hab => ⟨VG.Proof.AesSiv.AArch64.start_wp v h hab.1, VG.Proof.AesSiv.AArch64.start_wp v h' hab.2⟩
  exact (a.mono (fun _ _ p => p) fun _ _ p => p.2).seq (f.mono (fun _ _ p => p) fun _ _ p => p.2)

/-- The state before the components, in both runs. -/
abbrev AA (s₀ s₀' : State) (C A P W D : Addr) (R N L i : Nat) (a b : State) : Prop :=
  VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L i a ∧ VG.Proof.AesSiv.AArch64.AInv s₀' C A P W D R N L i b

/-- The descriptor's pointer and the count left, as in the loop's state. -/
def XA (A : Addr) (N i : Nat) (s : State) : Prop :=
  s.gpr .x24 = A + BitVec.ofNat 64 (16 * i) ∧ s.gpr .x25 = BitVec.ofNat 64 (N - i)

/-- One component in both runs. -/
theorem adBody_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L)
    (h' : VG.Proof.AesSiv.AArch64.EPre s₀' C A P W D R N L) (hq : VG.Proof.AesSiv.AArch64.EPub s₀ s₀' A N) {i : Nat} (hiN : i < N) :
    RelCT isa (VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L i)
      (.seq (.block adNext) (.seq (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep)))
      (VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L (i + 1)) := by
  have hQ := h.comps _ (VG.Proof.AesSiv.AArch64.comp_mem s₀.mem A hiN)
  have hQ' := h'.comps _ (VG.Proof.AesSiv.AArch64.comp_mem s₀'.mem A hiN)
  have ec := hq.comp_eq hiN
  rw [← ec] at hQ'
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x24, .x25])
      (.block adNext) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24, .x25])
      (.block adStep) hc).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L i) _
    (fun a b hab => by
      refine VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.sp, hab.2.sp, hq.sp]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hab.1.x19, hab.2.x19]
      · rw [hab.1.x20, hab.2.x20]
      · rw [hab.1.x21, hab.2.x21]
      · rw [hab.1.x24, hab.2.x24]
      · rw [hab.1.x25, hab.2.x25]) hA).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len s ∧ VG.Proof.AesSiv.AArch64.XA A N i s)
    (F₂ := fun (s : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len s ∧ VG.Proof.AesSiv.AArch64.XA A N i s)
    fun a b hab => ⟨WP.mono (VG.Proof.AesSiv.AArch64.adNext_wp h hiN hab.1) fun _ p =>
        ⟨p.1, by rw [p.2.1 _ (by decide) (by decide), hab.1.x24], by rw [p.2.1 _ (by decide) (by decide), hab.1.x25]⟩,
      WP.mono (VG.Proof.AesSiv.AArch64.adNext_wp h' hiN hab.2) fun _ p => ⟨by rw [ec]; exact p.1,
        by rw [p.2.1 _ (by decide) (by decide), hab.2.x24], by rw [p.2.1 _ (by decide) (by decide), hab.2.x25]⟩⟩
  have xa {σ s : State} (hσ : VG.Proof.AesSiv.AArch64.Env σ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len)
      (hs : VG.Proof.AesSiv.AArch64.Regs σ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len s ∧ VG.Proof.AesSiv.AArch64.XA A N i s) :
      WP isa (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) s fun t =>
        VG.Proof.AesSiv.AArch64.Regs σ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len t ∧ VG.Proof.AesSiv.AArch64.XA A N i t :=
    WP.mono (VG.Proof.AesSiv.AArch64.cmacOf_wp v hσ hs.1) fun _ p =>
      ⟨p.regs, by rw [p.hold _ (by decide), hs.2.1], by rw [p.hold _ (by decide), hs.2.2]⟩
  have p₂ := ((VG.Proof.AesSiv.AArch64.cmacOf_rel v hQ hQ' hq.sp).mono
    (P' := fun a b => (VG.Proof.AesSiv.AArch64.Regs s₀ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len a ∧ VG.Proof.AesSiv.AArch64.XA A N i a) ∧
      VG.Proof.AesSiv.AArch64.Regs s₀' C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len b ∧ VG.Proof.AesSiv.AArch64.XA A N i b)
    (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p).wp
    (F₁ := fun (s : State) => VG.Proof.AesSiv.AArch64.Regs s₀ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len s ∧ VG.Proof.AesSiv.AArch64.XA A N i s)
    (F₂ := fun (s : State) => VG.Proof.AesSiv.AArch64.Regs s₀' C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len s ∧ VG.Proof.AesSiv.AArch64.XA A N i s)
    fun a b hab => ⟨xa hQ hab.1, xa hQ' hab.2⟩
  have p₃ := RelCT.taint (A := taint)
    (P := fun a b => (VG.Proof.AesSiv.AArch64.Regs s₀ C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len a ∧ VG.Proof.AesSiv.AArch64.XA A N i a) ∧
      VG.Proof.AesSiv.AArch64.Regs s₀' C D (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).base W R (VG.Proof.AesSiv.AArch64.comp s₀.mem A i).len b ∧ VG.Proof.AesSiv.AArch64.XA A N i b) _
    (fun a b hab => by
      have e := VG.Proof.AesSiv.AArch64.regs_agree' (rs := [.x24, .x25]) hq.sp hab.1.1 hab.2.1 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]
        · rw [hab.1.2.2, hab.2.2.2]
      exact e) hC
  have body := (p₁.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((p₂.mono (fun _ _ p => p) fun _ _ p => p.2).seq p₃)
  exact (body.wp (F₁ := VG.Proof.AesSiv.AArch64.AInv s₀ C A P W D R N L (i + 1)) (F₂ := VG.Proof.AesSiv.AArch64.AInv s₀' C A P W D R N L (i + 1))
    fun a b hab => ⟨VG.Proof.AesSiv.AArch64.adBody_wp v h hiN hab.1, VG.Proof.AesSiv.AArch64.adBody_wp v h' hiN hab.2⟩).mono (fun _ _ p => p) fun _ _ p => p.2

/-- S2V over the components in both runs. -/
theorem ads_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L)
    (h' : VG.Proof.AesSiv.AArch64.EPre s₀' C A P W D R N L) (hq : VG.Proof.AesSiv.AArch64.EPub s₀ s₀' A N) :
    RelCT isa (VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L 0) (s2vAds v.callee v.ctr.callee v.ctr.suffix)
      (VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L N) := by
  have hN := h.N_lt
  have ev {σ s : State} (hs : VG.Proof.AesSiv.AArch64.AInv σ C A P W D R N L 0 s) : isa.eval (.zero .x .x25) s = some (decide (N = 0)) :=
    eval_zero hN (by rw [hs.x25, Nat.sub_zero])
  refine RelCT.ite (fun a b hab => by rw [ev hab.1, ev hab.2]) ?_ ?_
  · refine RelCT.block_nil fun a b hab => ?_
    have e := hab.2
    rw [ev hab.1.1] at e
    have hN0 : N = 0 := by simpa using e
    rw [hN0] at hab ⊢
    exact hab.1
  by_cases hN0 : N = 0
  · exact RelCT.of_false fun a b hab => by
      have e := hab.2; rw [ev hab.1.1] at e; simp [hN0] at e
  refine (RelCT.loop (M := isa) (c := .nonzero .x .x25)
    (fun (n : Nat) (a b : State) => ∃ i, n = N - i ∧ i < N ∧ VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L i a b) (fun n => ?_)
    (N - 0)).mono (fun a b hab => ⟨0, rfl, Nat.pos_of_ne_zero hN0, hab.1⟩) fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : n = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (VG.Proof.AesSiv.AArch64.adBody_rel v h h' hq hiN).mono (fun _ _ p => p.2.2) fun a b p => ?_
  have ea := eval_nonzero (s := a) (r := .x25) (x := N - (i + 1)) (by omega) p.1.x25
  have eb := eval_nonzero (s := b) (r := .x25) (x := N - (i + 1)) (by omega) p.2.x25
  refine ⟨by rw [ea, eb], fun e => ?_, fun e => ?_⟩
  · have he : i + 1 = N := by rw [ea] at e; simp at e; omega
    subst he; exact p
  · have he : i + 1 ≠ N := by rw [ea] at e; simp at e; omega
    exact ⟨N - (i + 1), by omega, i + 1, rfl, by omega, p⟩

/-- S2V of the associated data in both runs. -/
theorem encS2v_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : VG.Proof.AesSiv.AArch64.EPre s₀ C A P W D R N L)
    (h' : VG.Proof.AesSiv.AArch64.EPre s₀' C A P W D R N L) (hq : VG.Proof.AesSiv.AArch64.EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encS2v v.callee v.ctr.callee v.ctr.suffix)
      fun a b => VG.Proof.AesSiv.AArch64.SDone s₀ C A P W D R N L a ∧ VG.Proof.AesSiv.AArch64.SDone s₀' C A P W D R N L b := by
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x26, .x27])
      (.block [mov .x22 .x26, mov .x23 .x27]) hc).isSome = true := ⟨_, by taint_decide⟩
  have e := (RelCT.taint (A := taint) (P := VG.Proof.AesSiv.AArch64.AA s₀ s₀' C A P W D R N L N) _
    (fun a b hab => by
      refine VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.sp, hab.2.sp, hq.sp]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.x26, hab.2.x26]
      · rw [hab.1.x27, hab.2.x27]) hE).wp
    (F₁ := VG.Proof.AesSiv.AArch64.SDone s₀ C A P W D R N L) (F₂ := VG.Proof.AesSiv.AArch64.SDone s₀' C A P W D R N L)
    fun a b hab => ⟨VG.Proof.AesSiv.AArch64.adsEnd_wp hab.1, VG.Proof.AesSiv.AArch64.adsEnd_wp hab.2⟩
  exact RelCT.assoc ((VG.Proof.AesSiv.AArch64.start_rel v h h' hq.sp).seq ((VG.Proof.AesSiv.AArch64.ads_rel v h h' hq).seq
    (e.mono (fun _ _ p => p) fun _ _ p => p.2)))

/-! ## The ends -/

theorem finish_spre (v : Proof.CmacAes.AArch64.UpdateImpl) {σ : State} {C D P W : Addr} {R L : Nat}
    (h : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) {s : State} (hs : VG.Proof.AesSiv.AArch64.SPre σ C D P W R L s) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.ctr.callee v.ctr.suffix out) s (VG.Proof.AesSiv.AArch64.SPre σ C D P W R L) :=
  WP.mono (VG.Proof.AesSiv.AArch64.finish_wp v h hs.regs hout) fun t ht =>
    ⟨ht.regs, by rw [ht.hold.1, hs.x26], by rw [ht.hold.2, hs.x27]⟩

theorem counter_ctrPre {σ : State} {C D P W : Addr} {R L : Nat} (h : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) {s : State}
    (hs : VG.Proof.AesSiv.AArch64.SPre σ C D P W R L s) : WP isa (.block (counter 0)) s (VG.Proof.AesSiv.AArch64.CtrPre σ C D P W R L) := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.AArch64.counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := VG.Proof.AesSiv.AArch64.counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁, by rw [g₁ _ (by decide) (by decide), hs.x26],
    by rw [g₁ _ (by decide) (by decide), hs.x27], ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃⟩⟩

/-- The registers of both runs, with the data in `x26` and `x27`. -/
abbrev RD (s₀ s₀' : State) (C D P W : Addr) (R L : Nat) (a b : State) : Prop :=
  (VG.Proof.AesSiv.AArch64.Regs s₀ C D P W R L a ∧ a.gpr .x26 = P ∧ a.gpr .x27 = BitVec.ofNat 64 L) ∧
    VG.Proof.AesSiv.AArch64.Regs s₀' C D P W R L b ∧ b.gpr .x26 = P ∧ b.gpr .x27 = BitVec.ofNat 64 L

theorem rd_agree {s₀ s₀' : State} {C D P W : Addr} {R L : Nat} (hq : s₀.sp = s₀'.sp) {a b : State}
    (hab : VG.Proof.AesSiv.AArch64.RD s₀ s₀' C D P W R L a b) :
    taint.Agree (Taint.ofRegs (([.x19, .x20, .x21, .x22, .x23] : List Reg) ++ ([.x26, .x27] : List Reg))) a b :=
  VG.Proof.AesSiv.AArch64.regs_agree' hq hab.1.1 hab.2.1 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.2.1, hab.2.2.1]
    · rw [hab.1.2.2, hab.2.2.2]

/-- The address of `siv`, `T`, in its slot of the working space. -/
abbrev Slot (W T : Addr) (s : State) : Prop := s.mem.readW (W + BitVec.ofNat 64 248) 64 = T

theorem finish_slot (v : Proof.CmacAes.AArch64.UpdateImpl) {σ : State} {C D P W T : Addr} {R L : Nat}
    (h : Env σ C D P W R L) {s : State} (hs : SPre σ C D P W R L s) (hl : Slot W T s) :
    WP isa (finish v.callee v.ctr.callee v.ctr.suffix 0) s fun t => SPre σ C D P W R L t ∧ Slot W T t :=
  WP.mono (finish_wp v h hs.regs (Or.inl rfl)) fun t ht =>
    ⟨⟨ht.regs, by rw [ht.hold.1, hs.x26], by rw [ht.hold.2, hs.x27]⟩, by
      rw [Slot, ht.frame.readW (Region.contains_self _ _)
        (fin_dis h (out := 0) (d := 248) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)) (by decide)]
      exact hl⟩

theorem counter_slot {σ : State} {C D P W T : Addr} {R L : Nat} (h : Env σ C D P W R L) {s : State}
    (hs : SPre σ C D P W R L s) (hl : Slot W T s) :
    WP isa (.block (counter 0)) s fun t => CtrPre σ C D P W R L t ∧ Slot W T t := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, ⟨hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁, by rw [g₁ _ (by decide) (by decide), hs.x26],
    by rw [g₁ _ (by decide) (by decide), hs.x27], ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃⟩⟩, ?_⟩
  have f₁ : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  rw [Slot, f₁.readW (Region.contains_self _ _) (cnt_dis (d := 248) (by decide) (by decide)) (by decide)]
  exact hl

theorem ctr_slot (v : Proof.Aes.AArch64.Ctr32Impl) {σ : State} {C D P W T : Addr} {R L : Nat}
    (h : Env σ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ σ.wr)
    {s : State} (hs : CtrPre σ C D P W R L s) (hl : Slot W T s) :
    WP isa (ctr v.callee) s (Slot W T) := by
  obtain ⟨hi, lo, q, e₁, e₂, e₃⟩ := hs.cnt
  refine WP.mono (ctr_wp v h hcp hPw hs.regs ⟨hi, lo, e₁, e₂, e₃⟩ hs.x26 hs.x27) fun t ht => ?_
  rw [Slot, ht.frame.readW (Region.contains_self _ _) (ctr_dis h (d := 248) (by decide) (by decide))
    (by decide)]
  exact hl

/-- The copy of the IV to `siv`, in both runs: its addresses, `T` and `W`,
are the same. -/
theorem sivOut_rel {σ σ' : State} {C D P W T : Addr} {R L : Nat} (h : Env σ C D P W R L)
    (h' : Env σ' C D P W R L) (hq : σ.sp = σ'.sp) (hTw : (⟨T, 16⟩ : Region) ∈ σ.wr)
    (hTw' : (⟨T, 16⟩ : Region) ∈ σ'.wr) (wT : T.toNat + 16 ≤ 2 ^ 64) :
    RelCT isa (fun a b => (RD σ σ' C D P W R L a b ∧ Slot W T a) ∧ Slot W T b) (.block sivOut)
      fun a b => (a.gpr .x19 = W ∧ a.sp = σ.sp) ∧ b.gpr .x19 = W ∧ b.sp = σ'.sp := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19]) (.block (sivOut.take 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x9, .x19]) (.block (sivOut.drop 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have run {σ : State} (e : Env σ C D P W R L) (hTw : (⟨T, 16⟩ : Region) ∈ σ.wr) {s : State}
      (hr : Regs σ C D P W R L s) (hl : Slot W T s) :
      ∃ s', runBlock isa sivOut s = some s' ∧ s'.gpr .x19 = W ∧ s'.sp = σ.sp := by
    have inT (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (T + BitVec.ofNat 64 d) 8 := by
      rw [hr.wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := wT; omega)⟩
    obtain ⟨s', run', -, g', sp', -, -⟩ := sivOut_ok hr.x19 hl (e.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide))
      (e.inRW hr.rd hr.wr (d := 0) (n := 8) (by decide)) (e.inRW hr.rd hr.wr (d := 8) (n := 8) (by decide))
      (inT 0 (by decide)) (inT 8 (by decide))
    exact ⟨s', run', by rw [g' _ (by decide) (by decide), hr.x19], by rw [sp', hr.sp]⟩
  have head {σ : State} (e : Env σ C D P W R L) {s : State} (hr : Regs σ C D P W R L s) (hl : Slot W T s) :
      WP isa (.block (sivOut.take 1)) s fun t => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ.sp := by
    have r₂ := e.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide)
    simp only [Slot, Mem.readW, BitVec.setWidth_eq] at hl
    exact WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self, sivOut, List.take,
        runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
        Option.bind_some, Option.map_some, BitVec.setWidth_eq, hr.x19, r₂, hl]
      rfl, by simp [gpr_write], by simp [gpr_write, hr.x19], by rw [← hr.sp]; rfl⟩
  have a := (RelCT.taint (A := taint) (P := fun (a b : State) => (RD σ σ' C D P W R L a b ∧ Slot W T a) ∧ Slot W T b) _
    (fun a b hab => VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.1.1.1.sp, hab.1.1.2.1.sp, hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.1.1.1.x19, hab.1.1.2.1.x19]) hA).wp
    (F₁ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ.sp)
    (F₂ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ'.sp)
    fun a b hab => ⟨head h hab.1.1.1.1 hab.1.2, head h' hab.1.1.2.1 hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .x9 = T ∧ a.gpr .x19 = W ∧ a.sp = σ.sp) ∧
      b.gpr .x9 = T ∧ b.gpr .x19 = W ∧ b.sp = σ'.sp) _
    (fun a b hab => VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.2.2, hab.2.2.2, hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2.1, hab.2.2.1]) hB
  rw [show (Code.block sivOut : Prog isa) = .block (sivOut.take 1 ++ sivOut.drop 1) by
    rw [List.take_append_drop]]
  refine ((RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (t : State) => t.gpr .x19 = W ∧ t.sp = σ.sp)
    (F₂ := fun (t : State) => t.gpr .x19 = W ∧ t.sp = σ'.sp) fun a b hab => ?_).mono
    (fun _ _ p => p) fun _ _ p => p.2
  rw [List.take_append_drop]
  obtain ⟨a', ra, xa, sa⟩ := run h hTw hab.1.1.1.1 hab.1.2
  obtain ⟨b', rb, xb, sb⟩ := run h' hTw' hab.1.1.2.1 hab.2
  exact ⟨WP.of_runBlock ⟨a', ra, xa, sa⟩, WP.of_runBlock ⟨b', rb, xb, sb⟩⟩

theorem sealTail_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {σ σ' : State} {C D P W T : Addr} {R L : Nat}
    (h : Env σ C D P W R L) (h' : Env σ' C D P W R L) (hq : σ.sp = σ'.sp)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ σ.wr)
    (hPw' : (⟨P, L⟩ : Region) ∈ σ'.wr) (hTw : (⟨T, 16⟩ : Region) ∈ σ.wr)
    (hTw' : (⟨T, 16⟩ : Region) ∈ σ'.wr) (wT : T.toNat + 16 ≤ 2 ^ 64) :
    RelCT isa (fun a b => (SPre σ C D P W R L a ∧ Slot W T a) ∧ SPre σ' C D P W R L b ∧ Slot W T b)
      (.seq (finish v.callee v.ctr.callee v.ctr.suffix 0)
        (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (.block sivOut) (.block restore)))))
      fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19]) (.block restore) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have f := ((finish_rel v h h' hq (Or.inl rfl)).mono
      (P' := fun (a b : State) => (SPre σ C D P W R L a ∧ Slot W T a) ∧ SPre σ' C D P W R L b ∧ Slot W T b)
      (fun _ _ p => ⟨p.1.1.regs, p.2.1.regs⟩) fun _ _ p => p).wp
    (F₁ := fun (t : State) => SPre σ C D P W R L t ∧ Slot W T t)
    (F₂ := fun (t : State) => SPre σ' C D P W R L t ∧ Slot W T t)
    fun a b hab => ⟨finish_slot v h hab.1.1 hab.1.2, finish_slot v h' hab.2.1 hab.2.2⟩
  have c := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (SPre σ C D P W R L a ∧ Slot W T a) ∧ SPre σ' C D P W R L b ∧ Slot W T b) _
    (fun a b hab => regs_agree hq hab.1.1.regs hab.2.1.regs) hB).wp
    (F₁ := fun (t : State) => CtrPre σ C D P W R L t ∧ Slot W T t)
    (F₂ := fun (t : State) => CtrPre σ' C D P W R L t ∧ Slot W T t)
    fun a b hab => ⟨counter_slot h hab.1.1 hab.1.2, counter_slot h' hab.2.1 hab.2.2⟩
  have k := ((ctr_rel' v.ctr h h' hq hcp hPw hPw').mono
      (P' := fun (a b : State) => (CtrPre σ C D P W R L a ∧ Slot W T a) ∧ CtrPre σ' C D P W R L b ∧ Slot W T b)
      (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p).wp
    (F₁ := Slot W T) (F₂ := Slot W T)
    fun a b hab => ⟨ctr_slot v.ctr h hcp hPw hab.1.1 hab.1.2, ctr_slot v.ctr h' hcp hPw' hab.2.1 hab.2.2⟩
  have r := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .x19 = W ∧ a.sp = σ.sp) ∧ b.gpr .x19 = W ∧ b.sp = σ'.sp) _
    (fun a b hab => VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.2, hab.2.2, hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.1, hab.2.1]) hC
  exact (f.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((c.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((k.mono (fun _ _ p => p) fun _ _ p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩).seq ((sivOut_rel h h' hq hTw hTw' wT).seq r)))

/-- `decrypt`'s end, from the registers in both runs: it compares the IVs
and masks the data without a branch, so nothing it does depends on the
result. -/
theorem openTail_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {σ σ' : State} {C D P W : Addr} {R L : Nat}
    (h : VG.Proof.AesSiv.AArch64.Env σ C D P W R L) (h' : VG.Proof.AesSiv.AArch64.Env σ' C D P W R L) (hq : σ.sp = σ'.sp)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ σ.wr)
    (hPw' : (⟨P, L⟩ : Region) ∈ σ'.wr) :
    RelCT isa (fun a b => VG.Proof.AesSiv.AArch64.SPre σ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.SPre σ' C D P W R L b)
      (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (finish v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore))))))
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs (([.x19, .x20, .x21, .x22, .x23] : List Reg) ++ ([.x26, .x27] : List Reg)))
      (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore))) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.SPre σ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.SPre σ' C D P W R L b) _
    (fun a b hab => VG.Proof.AesSiv.AArch64.regs_agree hq hab.1.regs hab.2.regs) hA).wp
    (F₁ := VG.Proof.AesSiv.AArch64.CtrPre σ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.CtrPre σ' C D P W R L) fun a b hab =>
      ⟨VG.Proof.AesSiv.AArch64.counter_ctrPre h hab.1, VG.Proof.AesSiv.AArch64.counter_ctrPre h' hab.2⟩
  have f := ((VG.Proof.AesSiv.AArch64.finish_rel v h h' hq (Or.inr rfl)).mono (P' := VG.Proof.AesSiv.AArch64.RD σ σ' C D P W R L)
      (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p).wp
    (F₁ := VG.Proof.AesSiv.AArch64.SPre σ C D P W R L) (F₂ := VG.Proof.AesSiv.AArch64.SPre σ' C D P W R L) fun a b hab =>
      ⟨VG.Proof.AesSiv.AArch64.finish_spre v h ⟨hab.1.1, hab.1.2.1, hab.1.2.2⟩ (Or.inr rfl),
        VG.Proof.AesSiv.AArch64.finish_spre v h' ⟨hab.2.1, hab.2.2.1, hab.2.2.2⟩ (Or.inr rfl)⟩
  have t := RelCT.taint (A := taint) (P := fun a b => VG.Proof.AesSiv.AArch64.SPre σ C D P W R L a ∧ VG.Proof.AesSiv.AArch64.SPre σ' C D P W R L b)
    _
    (fun a b hab => VG.Proof.AesSiv.AArch64.rd_agree hq ⟨⟨hab.1.regs, hab.1.x26, hab.1.x27⟩, hab.2.regs, hab.2.x26, hab.2.x27⟩) hB
  exact (c.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((VG.Proof.AesSiv.AArch64.ctr_rel' v.ctr h h' hq hcp hPw hPw').seq
    ((f.mono (fun _ _ p => p) fun _ _ p => p.2).seq t))

/-- The address of `siv` in its slot after S2V. -/
theorem SDone.slot {T : Addr} (hT : SivArg s₀ P W D T L) {s : State} (hs : SDone s₀ C A P W D R N L s) :
    Slot W T s := by
  show s.mem.readW (W + BitVec.ofNat 64 248) 64 = T
  rw [hs.saved (.x6, 248) (by decide), hT.x6]

theorem encrypt_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L)
    (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) (hTw' : (⟨T, 16⟩ : Region) ∈ s₀'.wr) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encrypt v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sealTail_rel v h.env h'.env hq.sp h.cp h.pw h'.pw hTw hTw' hT.wT).mono
    (fun _ _ p => ⟨⟨p.1.spre, p.1.slot hT⟩, p.2.spre, p.2.slot hT'⟩) fun _ _ p => p)

/-- The copy of the received IV to `W`, in both runs: its addresses, `T` and
`W`, are the same. -/
theorem sivIn_rel (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L) {T : Addr}
    (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L) (hq : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b) (.block sivIn)
      fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19]) (.block (sivIn.take 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x9, .x19]) (.block (sivIn.drop 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have head {σ : State} (e : EPre σ C A P W D R N L) (hT : SivArg σ P W D T L) {s : State}
      (hs : SDone σ C A P W D R N L s) :
      WP isa (.block (sivIn.take 1)) s fun t => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = σ.sp := by
    have hr := hs.spre.regs
    have r₂ := e.env.inRW hr.rd hr.wr (d := 248) (n := 8) (by decide)
    have hl := hs.slot hT
    simp only [Slot, Mem.readW, BitVec.setWidth_eq] at hl
    exact WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self, sivIn, List.take,
        runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
        Option.bind_some, Option.map_some, BitVec.setWidth_eq, hr.x19, r₂, hl]
      rfl, by simp [gpr_write], by simp [gpr_write, hr.x19], by rw [← hr.sp]; rfl⟩
  have a := (RelCT.taint (A := taint)
    (P := fun (a b : State) => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b) _
    (fun a b hab => VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.spre.regs.sp, hab.2.spre.regs.sp, hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.spre.regs.x19, hab.2.spre.regs.x19]) hA).wp
    (F₁ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = s₀.sp)
    (F₂ := fun (t : State) => t.gpr .x9 = T ∧ t.gpr .x19 = W ∧ t.sp = s₀'.sp)
    fun a b hab => ⟨head h hT hab.1, head h' hT' hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .x9 = T ∧ a.gpr .x19 = W ∧ a.sp = s₀.sp) ∧
      b.gpr .x9 = T ∧ b.gpr .x19 = W ∧ b.sp = s₀'.sp) _
    (fun a b hab => VG.Proof.CmacAes.AArch64.agree_of (by rw [hab.1.2.2, hab.2.2.2, hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2.1, hab.2.2.1]) hB
  rw [show (Code.block sivIn : Prog isa) = .block (sivIn.take 1 ++ sivIn.drop 1) by
    rw [List.take_append_drop]]
  refine ((RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := SPre s₀ C D P W R L) (F₂ := SPre s₀' C D P W R L) fun a b hab => ?_).mono
    (fun _ _ p => p) fun _ _ p => p.2
  rw [List.take_append_drop]
  exact ⟨WP.mono (sivIn_wp h hT hab.1) fun _ p => p.1, WP.mono (sivIn_wp h' hT' hab.2) fun _ p => p.1⟩

theorem decrypt_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (h : EPre s₀ C A P W D R N L)
    (h' : EPre s₀' C A P W D R N L) {T : Addr} (hT : SivArg s₀ P W D T L) (hT' : SivArg s₀' P W D T L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sivIn_rel h h' hT hT' hq.sp).seq
    (openTail_rel v h.env h'.env hq.sp h.cp h.pw h'.pw))

end VG.Proof.AesSiv.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.AArch64.Verified`. -/
section

/-!
# AES-SIV on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_cmac_aes_update`, with the implementation of `vg_aes_ctr32` that goes
with it, or for `init` any implementation of `vg_aes_ctr32`), a state
satisfying each precondition, and the shared contracts of
`Spec/Siv/Contract.lean`, with no stack: the calls keep their return address
in `x30`, which the functions save in the working space.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.Impl.AesSiv.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.AArch64 (toNat_add_lt)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, Proof.CmacAes.AArch64.subkeys_keepsV v]; decide +kernel

theorem encrypt_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    (VG.Impl.AesSiv.AArch64.encrypt v.callee v.ctr.callee v.ctr.suffix).allInstrs keepsV = true := by
  simp only [VG.Impl.AesSiv.AArch64.encrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, ctr,
    ctrBody, ctrMin, ctrLeft, xorBytes, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
    Proof.CmacAes.AArch64.finalize_keepsV v.ctr, v.ctr.keepsV]
  decide +kernel

theorem decrypt_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    (decrypt v.callee v.ctr.callee v.ctr.suffix).allInstrs keepsV = true := by
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    ctr, ctrBody, ctrMin, ctrLeft, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
    Proof.CmacAes.AArch64.finalize_keepsV v.ctr, v.ctr.keepsV]
  decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.AesSiv.AArch64.init_wp v hs) (VG.Proof.AesSiv.AArch64.init_keepsV v)

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract AArch64.abi 0) :=
  Verified.of_correct (VG.Proof.AesSiv.AArch64.init_correct v) (VG.Proof.AesSiv.AArch64.init_ct v) (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, VG.Proof.AesSiv.AArch64.initAArch64, AArch64.abi, AArch64.argRegs] [initSat]
      using VG.Proof.AesSiv.AArch64.initSat)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are against the shared contracts with the working space `W` as a
last argument (`Proof/AesSiv/Scratch.lean`), in `x7`, after `siv` (`T`) in
`x6`. They are on the state whose writable regions are the data, `T` for
`encrypt`, the first 2560 bytes of the working space and S2V's state after
them (`encWrE`, `encWrD`), where `EPre` and `SivArg` hold (`encPre_of`,
`decPre_of`); a run from it is a run from the state itself (`Exec.widen`),
so `Verified.of_narrow` moves them to the shared contracts. -/

/-- The writable regions of `encrypt`'s proof. -/
def encWrE (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 2560⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 dOff, 16⟩]

/-- The writable regions of `decrypt`'s proof. -/
def encWrD (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 2560⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 dOff, 16⟩]

/-- The arguments of `encrypt` and `decrypt`. -/
abbrev EPreS (s : State) : Prop :=
  EPre s (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x7) (s.gpr .x7 + BitVec.ofNat 64 dOff)
    (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat

/-- The synthetic IV of `encrypt` and `decrypt`. -/
abbrev SivArgS (s : State) : Prop :=
  SivArg s (s.gpr .x4) (s.gpr .x7) (s.gpr .x7 + BitVec.ofNat 64 dOff) (s.gpr .x6) (s.gpr .x5).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    EPub s₁ s₂ (s₁.gpr .x2) (s₁.gpr .x3).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s ∧ (⟨s.gpr .x6, 16⟩ : Region) ∈ s.wr
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (Spec.Aes.bytesAt s'.mem (s.gpr .x6) 16, Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat)
  pub := VG.Proof.AesSiv.AArch64.encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s
  post s s' :=
    match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .x6) 16)
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Siv.zeros (s.gpr .x5).toNat
  pub := VG.Proof.AesSiv.AArch64.encPub

/-- The second run's arguments are the first's. -/
theorem EPreS.of_pub {s₁ s₂ : State} (h₂ : EPreS s₂) (hq : encPub s₁ s₂) :
    EPre s₂ (s₁.gpr .x0) (s₁.gpr .x2) (s₁.gpr .x4) (s₁.gpr .x7) (s₁.gpr .x7 + BitVec.ofNat 64 dOff)
      (s₁.gpr .x1).toNat (s₁.gpr .x3).toNat (s₁.gpr .x5).toNat := by
  obtain ⟨q0, q1, q2, q3, q4, q5, -, q7, -⟩ := hq
  rw [q0, q1, q2, q3, q4, q5, q7]; exact h₂

theorem SivArgS.of_pub {s₁ s₂ : State} (h₂ : SivArgS s₂) (hq : encPub s₁ s₂) :
    SivArg s₂ (s₁.gpr .x4) (s₁.gpr .x7) (s₁.gpr .x7 + BitVec.ofNat 64 dOff) (s₁.gpr .x6) (s₁.gpr .x5).toNat := by
  obtain ⟨-, -, -, -, q4, q5, q6, q7, -⟩ := hq
  rw [q4, q5, q6, q7]; exact h₂

theorem encryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : encryptN.pre s) :
    ∃ t s', Exec isa (VG.Impl.AesSiv.AArch64.encrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      encryptN.post s s' :=
  WP.withPreservedV (encrypt_wp v hs.1 hs.2.1 hs.2.2) (encrypt_keepsV v)

theorem decryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : decryptN.pre s) :
    ∃ t s', Exec isa (VG.Impl.AesSiv.AArch64.decrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      decryptN.post s s' :=
  WP.withPreservedV (decrypt_wp v hs.1 hs.2) (decrypt_keepsV v)

theorem encryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa encryptN.pre encryptN.pub (VG.Impl.AesSiv.AArch64.encrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2.1 (SivArgS.of_pub h₂.2.1 hq) h₁.2.2
      (by rw [hq.2.2.2.2.2.2.1]; exact h₂.2.2) hq.2.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa decryptN.pre decryptN.pub (VG.Impl.AesSiv.AArch64.decrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2 (SivArgS.of_pub h₂.2 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### From the shared contracts -/

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem listed_len {m : Mem} {p : Addr} {n : Nat} {r : Region} (hr : r ∈ Sig.listed 64 m .u8 p n) :
    r.len < 2 ^ 64 := by
  simp only [Sig.listed, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  simp only [Elem.size, Nat.mul_one]
  exact BitVec.isLt _

/-- `EPre` and `SivArg` from the facts the shared contracts give, on the
narrowed state `σ`: the whole working space at `W` is 2576 bytes. -/
theorem mkPre {σ : State} {C A P W T : Addr} {R N L : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (x0 : σ.gpr .x0 = C) (x1 : σ.gpr .x1 = BitVec.ofNat 64 R) (x2 : σ.gpr .x2 = A)
    (x3 : σ.gpr .x3 = BitVec.ofNat 64 N) (x4 : σ.gpr .x4 = P) (x5 : σ.gpr .x5 = BitVec.ofNat 64 L)
    (x6 : σ.gpr .x6 = T) (x7 : σ.gpr .x7 = W)
    (inC : (⟨C, 512⟩ : Region) ∈ σ.rd ++ σ.wr) (inA : (⟨A, N * 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r ∈ σ.rd ++ σ.wr) (inT : (⟨T, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inP : (⟨P, L⟩ : Region) ∈ σ.wr) (inW : (⟨W, 2560⟩ : Region) ∈ σ.wr)
    (inD : (⟨W + BitVec.ofNat 64 dOff, 16⟩ : Region) ∈ σ.wr)
    (cP : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (cW : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2576⟩)
    (pW : (⟨P, L⟩ : Region).Disjoint ⟨W, 2576⟩) (pT : (⟨P, L⟩ : Region).Disjoint ⟨T, 16⟩)
    (wA : (⟨W, 2576⟩ : Region).Disjoint ⟨A, N * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨W, 2576⟩ : Region).Disjoint r)
    (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2576⟩)
    (wrC : C.toNat + 512 ≤ 2 ^ 64) (wrP : P.toNat + L ≤ 2 ^ 64) (wrT : T.toNat + 16 ≤ 2 ^ 64)
    (wrW : W.toNat + 2576 ≤ 2 ^ 64) (wrA : A.toNat + N * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r.base.toNat + r.len ≤ 2 ^ 64) (hL : L < 2 ^ 64) :
    EPre σ C A P W (W + BitVec.ofNat 64 dOff) R N L ∧ SivArg σ P W (W + BitVec.ofNat 64 dOff) T L := by
  have sw : Region.Sub ⟨W, 2560⟩ ⟨W, 2576⟩ := Region.sub_prefix (by decide)
  have sd : Region.Sub ⟨W + BitVec.ofNat 64 dOff, 16⟩ ⟨W, 2576⟩ := Offset.sub_base _ (by decide)
  have dw := Offset.disjoint_base W (d := dOff) (n := 16) (k := 2560) (by decide) (by decide)
  have wD : (W + BitVec.ofNat 64 dOff).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ wrW (show dOff < 2576 by decide)]; simp only [dOff]; omega
  have inR {r : Region} (h : r ∈ σ.wr) : r ∈ σ.rd ++ σ.wr := List.mem_append_right _ h
  have env (Q : Addr) (n : Nat) (hQ : (⟨Q, n⟩ : Region) ∈ σ.rd ++ σ.wr) (qW : (⟨Q, n⟩ : Region).Disjoint ⟨W, 2576⟩)
      (wQ : Q.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) : Env σ C (W + BitVec.ofNat 64 dOff) Q W R n :=
    ⟨hR, rfl, inC, inR inD, hQ, inW, cW.sub_right sw, (qW.sub_right sd).symm, dw, qW.sub_right sw, wrC, wD, wQ,
      by omega, hn⟩
  exact ⟨⟨env P L (inR inP) pW wrP hL, cW.sub_right sd, cP, inP, inD, x0, x1, x2, x3, x4, x5, x7, inA,
    wA.symm.sub_right sw, wA.symm.sub_right sd, wrA,
    fun r hr => env r.base r.len (inL r hr) (wL r hr).symm (wrL r hr) (listed_len hr)⟩,
    ⟨x6, inT, pT.symm, tW.sub_right sw, tW.sub_right sd, wrT⟩⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `encryptN`'s on the
narrowed state. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract AArch64.abi 0).pre s) :
    encryptN.pre (s.withRegions s.rd (encWrE s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 2576⟩] := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs, List.append_eq] at h
  sig_split h
  rename_i hrd hwr hcP hcT hc1 hwC hwP hwT hwW hc3
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.nil_append, List.append_nil, Sig.conj] at hrd hwr hc1 hc3
  rw [pairFacts_ro _ (by simp)] at hc1
  obtain ⟨cW, pT, pW, -, -, tW, -, -, wA, wL, -⟩ := hc1
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrE s := List.mem_append_left _ hr
  have wT : (⟨s.gpr .x6, 16⟩ : Region) ∈ encWrE s := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨e, t⟩ := mkPre (σ := s.withRegions s.rd (encWrE s)) (C := s.gpr .x0) (A := s.gpr .x2) (P := s.gpr .x4)
    (W := s.gpr .x7) (T := s.gpr .x6) (R := (s.gpr .x1).toNat) (N := (s.gpr .x3).toNat)
    (L := (s.gpr .x5).toNat) h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    (List.mem_append_right _ wT) List.mem_cons_self
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    hcP cW pW pT wA wL tW hwC hwP hwT hwW wrA wrL (BitVec.isLt _)
  exact ⟨⟨e, t, wT⟩, hwr⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `decryptN`'s on the
narrowed state. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract AArch64.abi 0).pre s) :
    decryptN.pre (s.withRegions s.rd (encWrD s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 2576⟩] := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, AArch64.abi,
    AArch64.argRegs, List.append_eq] at h
  sig_split h
  rename_i hrd hwr hcP hc1 hwC hwP hwT hwW hc3
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.nil_append, List.append_nil, Sig.conj] at hrd hwr hc1 hc3
  rw [pairFacts_ro _ (by simp)] at hc1
  obtain ⟨cW, pT, pW, -, -, tW, wA, wL, -⟩ := hc1
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrD s := List.mem_append_left _ hr
  exact ⟨mkPre (σ := s.withRegions s.rd (encWrD s)) (C := s.gpr .x0) (A := s.gpr .x2) (P := s.gpr .x4)
    (W := s.gpr .x7) (T := s.gpr .x6) (R := (s.gpr .x1).toNat) (N := (s.gpr .x3).toNat)
    (L := (s.gpr .x5).toNat) h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hr))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    hcP cW pW pT wA wL tW hwC hwP hwT hwW wrA wrL (BitVec.isLt _), hwr⟩

/-- A run from a narrowed state is a run from the state. -/
theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} {ws : List Region} (hc : Covers ws s.wr)
    (he : Exec isa c (s.withRegions s.rd ws) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd ws) (rd := s.rd) (wr := s.wr) he (Covers.append (Covers.refl s.rd) hc) hc

theorem encWrE_covers {s : State}
    (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 2576⟩]) :
    Covers (encWrE s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0,
      by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), dOff, rfl, by simp [dOff]⟩

theorem encWrD_covers {s : State} (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 2576⟩]) :
    Covers (encWrD s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dOff, rfl, by simp [dOff]⟩

/-- A state satisfying the precondition of `vg_aes_siv_encrypt`, with no
associated data and no data: `siv` at `0x5000`, the working space at
`0x4000`. -/
def encSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x5000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

/-- `encSat`, with `siv` read only. -/
def decSat : State := { encSat with rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩] }

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract AArch64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    AArch64.abi, AArch64.argRegs] [encSat] using encSat

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract AArch64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    AArch64.abi, AArch64.argRegs] [decSat, encSat] using decSat

theorem encPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.encryptScratchContract AArch64.abi 0).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrE s₁)) (s₂.withRegions s₂.rd (encWrE s₂)) := by
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem decPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.decryptScratchContract AArch64.abi 0).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrD s₁)) (s₂.withRegions s₂.rd (encWrD s₂)) := by
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, AArch64.abi, AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem encrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (encrypt v.callee v.ctr.callee v.ctr.suffix)
      (Proof.AesSiv.encryptScratchContract AArch64.abi 0) :=
  Verified.of_narrow (k := encryptN)
    ⟨encryptN_correct v, encryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrE s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrE_covers (encPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
        AArch64.abi, AArch64.argRegs]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) encSat_pre

theorem decrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (decrypt v.callee v.ctr.callee v.ctr.suffix)
      (Proof.AesSiv.decryptScratchContract AArch64.abi 0) :=
  Verified.of_narrow (k := decryptN)
    ⟨decryptN_correct v, decryptN_ct v, decSat_pre.elim fun s hs => ⟨_, (decPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrD s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (decPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrD_covers (decPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
        AArch64.abi, AArch64.argRegs]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) decSat_pre

end VG.Proof.AesSiv.AArch64

end
