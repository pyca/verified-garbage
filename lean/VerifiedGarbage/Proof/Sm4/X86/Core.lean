import VerifiedGarbage.Proof.Sm4.X86.Round
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Sm4.X86.Ecb

/-!
# Eight blocks of bitsliced SM4 on x86 (32-bit): the rounds

As on ARMv7 (`Proof/Sm4/Arm/Core.lean`): with the table of bitsliced
round keys `E 0 … E 31` in the scratch buffer (`KeyCtx`), the rounds are
`round_ok`, four at a time (`rounds4_ok`), in a loop whose invariant is
`quads`; they write only the slots below the table (`Ctx`). `rounds_wp`
is that loop for either linear transformation, which the key schedule
runs too.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Bitslice (lanes)
open VG.Impl.Aes.X86 (sb tmpRegs movR addI subR)
open VG.Proof.Sm4 (sround quad quads W32.WordRel)
open VG.Impl.Sm4 (Lin)

theorem slots_eq : slots = 358 := rfl
theorem tableSlot_eq : tableSlot = 96 := rfl
theorem tableEnd_eq : tableEnd = 352 := rfl
theorem tailSlot_eq : tailSlot = 64 := rfl
theorem savedSlot_eq : savedSlot = 352 := rfl
theorem dSlot_eq : dSlot = 356 := rfl
theorem nSlot_eq : nSlot = 357 := rfl

/-- Word `j` of entry `e` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : BitVec 32) (e j : Nat) : BitVec 32 :=
  m.readW (wordAddr b (tableSlot + 8 * e + j)) 32

/-- The scratch buffer at `b`, of `slots` slots or more (a mode keeps its
own after them), in the regions `rs`. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : ∃ n, slots ≤ n ∧ b.toNat + 4 * n ≤ 2 ^ 32 ∧ (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

/-- A scratch buffer of exactly `slots` slots. -/
theorem ScrIn.exact {rs : List Region} {b : BitVec 32} (hr : (⟨b.setWidth 64, 4 * slots⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) : ScrIn rs b := ⟨⟨slots, Nat.le_refl _, hfit, hr⟩, hfit⟩

/-- What the rounds need: the scratch buffer, writable, and a table of 32
round keys. -/
structure KeyCtx (s₀ : State) (E : Nat → Spec.Sm4.Word) : Prop where
  scr : ScrIn s₀.wr (s₀.gpr sb)
  keys : ∀ e < 32, W32.WordRel (entryW s₀.mem (s₀.gpr sb) e) fun _ => E e

/-- What stays the same: the regions, the registers but the layers' and
`kp`, and the memory outside the slots below the table. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨(s₀.gpr sb).setWidth 64, 4 * tableSlot⟩] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ tmpRegs → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [⟨(s₀.gpr sb).setWidth 64, 4 * tableSlot⟩] s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2), hc.frame.trans hf⟩

theorem Ctx.trans {s₀ s₁ s₂ : State} (h₁ : Ctx s₀ s₁) (h₂ : Ctx s₁ s₂) : Ctx s₀ s₂ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b => (h₂.keep r a b).trans (h₁.keep r a b),
    h₁.frame.trans (by rw [← h₁.base]; exact h₂.frame)⟩

/-! ## Addresses -/

theorem setWidth_toNat (b : BitVec 32) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- Slot `k` of the scratch buffer at `b`, as a 64-bit offset. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)

/-- Slot `k` is in the scratch buffer. -/
theorem slot_in {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega)]
    have := setWidth_toNat b
    exact VG.Offset.contains_base _ (by omega) (by omega)⟩

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 :=
  let ⟨_, hn, hf, hr⟩ := h.mem
  slot_in hr hf (Nat.lt_of_lt_of_le hk hn)

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : BitVec 32) (m : Nat) : Prop :=
  s.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * m)

theorem kp_word {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (j : Nat) :
    wordAddr (s.gpr kp) j = wordAddr b (tableSlot + 8 * m + j) := by
  simp only [wordAddr, addr]
  rw [show s.gpr kp = _ from hk, VG.Offset.add_add,
    show 4 * tableSlot + 32 * m + 4 * j = 4 * (tableSlot + 8 * m + j) by omega]

theorem keyW_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (8 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, entryW]
  rw [kp_word hk, show tableSlot + 8 * m + (8 * e + j) = tableSlot + 8 * (m + e) + j by omega]

theorem ok_layer {s : State} {b : BitVec 32} {m : Nat} (hscr : ScrIn s.wr b) (hb : s.gpr sb = b)
    (hk : AtEntry s b m) (hm : m + 4 ≤ 32) : Ok layerCfg s where
  slotIn k hk' := by
    simp only [layerCfg, tableSlot_eq] at hk' ⊢
    rw [hb]; exact hscr.slot (by rw [slots_eq]; omega)
  extIn j hj := by
    simp only [layerCfg] at hj ⊢
    rw [kp_word hk]
    obtain ⟨r, hr, hc⟩ := hscr.slot (k := tableSlot + 8 * m + j) (by rw [slots_eq, tableSlot_eq]; omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  fit := by have := hscr.fit; simp only [layerCfg, tableSlot_eq]; rw [hb]; rw [slots_eq] at this; omega
  sep k hk' j hj := by
    have := hscr.fit
    simp only [layerCfg, tableSlot_eq] at hk' hj ⊢
    rw [kp_word hk, hb]
    rw [slots_eq] at this
    exact slot_sep b (by omega) (by rw [tableSlot_eq]; omega) (by rw [tableSlot_eq]; omega)

/-! ## Under `Ctx` -/

theorem Ctx.entry {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {e j : Nat} (he : e < 32) (hj : j < 8) :
    entryW s.mem (s₀.gpr sb) e j = entryW s₀.mem (s₀.gpr sb) e j := by
  have hfit := hp.scr.fit
  rw [slots_eq] at hfit
  have hb := setWidth_toNat (s₀.gpr sb)
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega)]
  refine hc.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq]; omega) (by rw [tableSlot_eq]; omega)

theorem Ctx.keyRel {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < 32) :
    W32.WordRel (fun j => keyW s (8 * e + j)) fun _ => E (m + e) :=
  (hp.keys _ hme).congr fun j hj => by rw [keyW_entry hk, hc.entry hp hme hj]

theorem Ctx.ok {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hc.base hk hm

/-- A round, under `Ctx`: `round l a …` with the round key at entry `m + a`. -/
theorem round_step (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {a b c d m : Nat} (ha : a < 4) (hb : b = (a + 1) % 4) (hc' : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 32 11) layerCfg (linExt 32) (preX a b c d) (linEnv (stateIns 0))
      (linPost tableSlot 11 (preOuts a b c d)) = true)
    (hlin : check (lanes 32 11) linCfg (linExt 40) (lin l a) (linEnv linIns)
      (linPost tableSlot 11 (linOuts l a)) = true)
    (hall : ([Reg.esp, .esi, .edi].all fun r => (preX a b c d ++ lin l a).all fun i => i.dst != some r) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      StRel s' (fun b' => sround l (E (m + a)) a (X b')) := by
  obtain ⟨s', h', hX', rd', wr', o', f'⟩ :=
    round_ok l ha hb hc' hd hpre hlin hall (hc.ok hp hk hm) hX (hc.keyRel hp hk (e := a) (by omega))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ => o' r hr) (f'.mono fun r hr => ?_), o' _ (by decide), hX'⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg, hc.base]; simp

/-- Four rounds, the round keys at entries `4 m … 4 m + 3`. -/
theorem rounds4_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (rounds4 l) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      StRel s' (fun b => quad l E m (X b)) := by
  have hm4 : 4 * m + 4 ≤ 32 := by omega
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := round_step l hp hc (a := 0) (by decide) rfl rfl rfl pre0_check
    (by cases l <;> [exact linE0_check; exact linK0_check]) (by cases l <;> decide +kernel) hk hm4 hX
  obtain ⟨s₂, e₂, c₂, k₂, X₂⟩ := round_step l hp c₁ (a := 1) (by decide) rfl rfl rfl pre1_check
    (by cases l <;> [exact linE1_check; exact linK1_check]) (by cases l <;> decide +kernel)
    (by rw [AtEntry, k₁]; exact hk) hm4 X₁
  obtain ⟨s₃, e₃, c₃, k₃, X₃⟩ := round_step l hp c₂ (a := 2) (by decide) rfl rfl rfl pre2_check
    (by cases l <;> [exact linE2_check; exact linK2_check]) (by cases l <;> decide +kernel)
    (by rw [AtEntry, k₂, k₁]; exact hk) hm4 X₂
  obtain ⟨s₄, e₄, c₄, k₄, X₄⟩ := round_step l hp c₃ (a := 3) (by decide) rfl rfl rfl pre3_check
    (by cases l <;> [exact linE3_check; exact linK3_check]) (by cases l <;> decide +kernel)
    (by rw [AtEntry, k₃, k₂, k₁]; exact hk) hm4 X₃
  refine ⟨s₄, ?_, c₄, by rw [k₄, k₃, k₂, k₁], ?_⟩
  · rw [rounds4, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄]
  · simpa only [quad, Nat.add_zero] using X₄

/-! ## Single instructions -/

/-- `add d, v`. -/
theorem addI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [addI d v] s = some s' ∧ s'.gpr d = s.gpr d + v ∧
      s'.zf = some (s.gpr d + v == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d + v) (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat) (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d
      (s.gpr d + v), rfl, RegUpd.gpr_setReg_self _ _ _, rfl, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `sub d, v`. -/
theorem subI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [VG.Impl.Aes.X86.subI d v] s = some s' ∧ s'.gpr d = s.gpr d - v ∧
      s'.zf = some (s.gpr d - v == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d - v) ((s.gpr d).toNat < v.toNat) (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d
      (s.gpr d - v), rfl, RegUpd.gpr_setReg_self _ _ _, rfl, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `mov d, s`. -/
theorem movR_ok (s : State) (d r₀ : Reg) :
    ∃ s', runBlock isa [movR d r₀] s = some s' ∧ s'.gpr d = s.gpr r₀ ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf :=
  ⟨s.setReg d (s.gpr r₀), rfl, RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl, rfl, rfl⟩

/-- `mov d, v`. -/
theorem movI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [VG.Impl.Aes.X86.movI d v] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d v, rfl, RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `mov eax, kp; sub eax, edi; cmp eax, v`. -/
theorem endTest_ok (s : State) (v : BitVec 32) :
    ∃ s', runBlock isa [movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm v)] s = some s' ∧
      s'.zf = some (s.gpr kp - s.gpr .edi - v == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .eax kp
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ .eax (s₁.gpr .edi)
  let s₃ := arithFlags s₂ (s₂.gpr .eax - v) ((s₂.gpr .eax).toNat < v.toNat) (subOverflow (s₂.gpr .eax) v (s₂.gpr .eax - v))
  refine ⟨s₃, ?_, ?_, fun r hr => by rw [RegUpd.gpr_arithFlags, o₂ r hr, o₁ r hr], by rw [RegUpd.mem_arithFlags, m₂, m₁],
    by rw [RegUpd.rd_arithFlags, rd₂, rd₁], by rw [RegUpd.wr_arithFlags, wr₂, wr₁]⟩
  · rw [show ([movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm v)] : List Instr) =
      [movR .eax kp] ++ ([subR .eax .edi] ++ [.alu .cmp .eax (.imm v)]) from rfl, runBlock_app, e₁, Option.bind_some,
      runBlock_app, show runBlock isa [subR .eax .edi] s₁ = runBlock isa [VG.Impl.Aes.X86.subI .eax (s₁.gpr .edi)] s₁ from rfl,
      e₂, Option.bind_some]
    rfl
  · rw [RegUpd.zf_arithFlags, r₂, r₁, o₁ _ (by decide)]

theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e (s : State) : isa.eval .e s = s.zf := rfl
theorem eval_b (s : State) : isa.eval .b s = s.cf := rfl

/-- A step that changes only `kp` (and the flags) keeps `Ctx`. -/
theorem Ctx.kp {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ kp → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r _ h2 => hg r h2) (by rw [hm]; exact Frame.refl _ _)

/-- A step that changes only `eax` (and the flags) keeps `Ctx`. -/
theorem Ctx.eax {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h1 _ => hg r fun h => h1 (by subst h; decide)) (by rw [hm]; exact Frame.refl _ _)

theorem StRel.congr {s s' : State} {X : Nat → Nat → Spec.Sm4.Word} (h : StRel s X)
    (hs : ∀ k, slotW s' k = slotW s k) : StRel s' X :=
  fun w hw => (h w hw).congr fun _ _ => hs _

/-- Four rounds, `kp += 128` and the end test. -/
theorem roundsBody_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (roundsBody l) s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (4 * (m + 1)) ∧
      StRel s' (fun b => quad l E m (X b)) ∧ s'.zf = some (decide (m + 1 = 8)) := by
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok l hp hc hk hm hX
  obtain ⟨s₂, e₂, kp₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ kp 128
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := endTest_ok s₂ (BitVec.ofNat 32 (4 * tableEnd))
  have hc₂ : Ctx s₀ s₂ := c₁.kp o₂ m₂ rd₂ wr₂
  have hk₂ : AtEntry s₂ (s₀.gpr sb) (4 * (m + 1)) := by
    rw [AtEntry, kp₂, k₁, show s.gpr kp = _ from hk, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
      VG.Offset.add_add, show 4 * tableSlot + 32 * (4 * m) + 128 = 4 * tableSlot + 32 * (4 * (m + 1)) by omega]
  refine ⟨s₃, ?_, hc₂.eax g₃ m₃ rd₃ wr₃, by rw [AtEntry, g₃ _ (by decide)]; exact hk₂, ?_, ?_⟩
  · rw [roundsBody, runBlock_app, e₁, Option.bind_some,
      show ([addI kp 128, movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * tableEnd)))] :
        List Instr) = [addI kp 128] ++ [movR .eax kp, subR .eax .edi,
          .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * tableEnd)))] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃]
  · exact X₁.congr fun k => by simp only [slotW, m₃, g₃ sb (by decide), m₂, o₂ sb (by decide)]
  · rw [z₃, show s₂.gpr kp = _ from hk₂, show s₂.gpr .edi = s₀.gpr sb from hc₂.base,
      VG.Offset.add_sub_cancel_left, ofNat32_sub_beq
      (by rw [tableSlot_eq]; omega) (by rw [tableEnd_eq]; omega), tableSlot_eq, tableEnd_eq]
    simp only [Option.some.injEq, decide_eq_decide]; omega

/-- The 32 rounds, the round keys at entries `0 … 31`. -/
theorem rounds_wp (l : Lin) {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s₀ X) :
    WP isa (rounds l) s₀ fun s' => Ctx s₀ s' ∧ StRel s' (fun b => quads l E 8 (X b)) := by
  obtain ⟨s₁a, e₁a, k₁a, o₁a, m₁a, rd₁a, wr₁a, -, -⟩ := movR_ok s₀ kp .edi
  obtain ⟨s₁, e₁, k₁, -, o₁, m₁, rd₁, wr₁⟩ := addI_ok s₁a kp (BitVec.ofNat 32 (4 * tableSlot))
  have hc₁ : Ctx s₀ s₁ := ((Ctx.refl s₀).kp o₁a m₁a rd₁a wr₁a).kp o₁ m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [kpAt, show ([movR kp .edi, addI kp (BitVec.ofNat 32 (4 * tableSlot))] : List Instr) =
      [movR kp .edi] ++ [addI kp (BitVec.ofNat 32 (4 * tableSlot))] from rfl, runBlock_app, e₁a,
      Option.bind_some, e₁], ?_⟩)
  let Inv : Nat → State → Prop := fun n s' => ∃ m, n = 8 - m ∧ m < 8 ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (4 * m) ∧ StRel s' (fun b => quads l E m (X b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) 8 s₁
    ⟨0, rfl, by omega, hc₁, by rw [AtEntry, k₁, k₁a]; simp; rfl,
      hX.congr fun k => by simp only [slotW, m₁, o₁ sb (by decide), m₁a, o₁a sb (by decide)]⟩
  obtain ⟨m, rfl, hm8, hc', hk', hX'⟩ := hs'
  obtain ⟨s'', e'', c'', k'', X'', z''⟩ := roundsBody_ok l hp hc' hk' hm8 hX'
  have X3 : StRel s'' fun b => quads l E (m + 1) (X b) := X''
  refine WP.of_runBlock ⟨s'', e'', ?_⟩
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_ne, z'', h8]; rfl, c'', ?_⟩
    rw [h8] at X3; exact X3
  · exact .inr ⟨by rw [eval_ne, z'']; simp [h8], 8 - (m + 1), by omega, m + 1, rfl, by omega, c'', k'', X3⟩

end VG.Proof.Sm4.X86
