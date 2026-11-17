module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.Layout
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Round
public import VerifiedGarbage.Impl.Aes.PPC64LE.Linear

/-! ### `Sm4.PPC64LE.Group`, which this module and modules that import it used -/

section

/-! ### `Sm4.PPC64LE.Core`, which this module and modules that import it used -/

section

/-!
# Sixteen blocks of bitsliced SM4 on PPC64LE

`crypt16_ok`: with the table of bitsliced round keys `E 0 … E 31` in the
scratch buffer (`KeyCtx`), `crypt16` replaces each of the sixteen blocks of
the tail buffer with the output of the 32 rounds with those keys, writing
only the slots below the table (`Ctx`). The rounds are `round_ok`, four at
a time (`rounds4_ok`), in a loop whose invariant is `quads`
(`Proof/Sm4/Rounds.lean`); `rounds_wp` is that loop for either linear
transformation, which the key schedule runs too.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR)
open VG.Proof.Sm4 (WordRel sround quad quads ofBlock outBlock)
open VG.Impl.Sm4 (Lin)

/-- Word `j` of entry `e` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : Addr) (e j : Nat) : BitVec 64 :=
  m.readW (b + BitVec.ofNat 64 (8 * tableSlot + 64 * e + 8 * j)) 64

/-- What the rounds need: the scratch buffer, writable, and a table of 32
round keys. -/
structure KeyCtx (s₀ : State) (E : Nat → Spec.Sm4.Word) : Prop where
  scr : (⟨s₀.gpr sb, 8 * slots⟩ : Region) ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 8 * slots ≤ 2 ^ 64
  keys : ∀ e < 32, WordRel (entryW s₀.mem (s₀.gpr sb) e) fun _ => E e

/-- What stays the same: the regions, the registers but the state's and
`kr`, the memory outside the slots below the table, and the masks. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ sboxWrites → r ≠ kr → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * tableSlot⟩] s₀.mem s.mem
  masks : MasksOk s

theorem Ctx.refl {s₀ : State} (hm : MasksOk s₀) : Ctx s₀ s₀ :=
  ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _, hm⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → r ≠ kr → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s₀.gpr sb, 8 * tableSlot⟩] s.mem s'.mem) (hm : MasksOk s') : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans hf, hm⟩

/-! ## Addresses -/

theorem slots_eq : slots = 402 := rfl
theorem tableSlot_eq : tableSlot = 128 := rfl
theorem tableEnd_eq : tableEnd = 384 := rfl
theorem tailSlot_eq : tailSlot = 96 := rfl

/-- `kr` at entry `m` of the table. -/
def AtEntry (s : State) (b : Addr) (m : Nat) : Prop := s.gpr kr = b + BitVec.ofNat 64 (8 * tableSlot + 64 * m)

theorem addr_add (b : Addr) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := VG.Offset.add_add b x y

theorem keyW_entry {s : State} {b : Addr} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (8 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, wordAddr, entryW]
  rw [hk, addr_add, show 8 * tableSlot + 64 * m + 8 * (8 * e + j) = 8 * tableSlot + 64 * (m + e) + 8 * j by omega_using []]

theorem ok_layer {s : State} {b : Addr} {m : Nat} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hk : AtEntry s b m) (hm : m + 4 ≤ 32) :
    Ok layerCfg s where
  slotIn k hk' := ⟨_, hscr, by
    simp only [layerCfg, tableSlot_eq] at hk'
    simp only [wordAddr, layerCfg, hb]
    rw [slots_eq]
    exact VG.Offset.contains_base b (by omega_using [hk']) (by omega_using [hk'])⟩
  extIn j hj := ⟨_, List.mem_append_right _ hscr, by
    simp only [layerCfg] at hj
    simp only [wordAddr, layerCfg]
    rw [show s.gpr kr = _ from hk, addr_add]
    rw [slots_eq]
    rw [tableSlot_eq]
    exact VG.Offset.contains_base b (by omega_using [hm, hj]) (by omega_using [hm, hj])⟩
  slots := by simp only [layerCfg, tableSlot_eq]; omega_using []
  sep k hk' j hj := by
    simp only [layerCfg, tableSlot_eq] at hk' hj
    simp only [wordAddr, layerCfg, hb]
    rw [show s.gpr kr = _ from hk, addr_add, tableSlot_eq]
    exact VG.Offset.sep b (by omega_using [hk']) (by omega_using [hk']) (by omega_using [hm, hj])

/-! ## Under `Ctx` -/

theorem Ctx.entry {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {e j : Nat} (he : e < 32) (hj : j < 8) :
    entryW s.mem (s₀.gpr sb) e j = entryW s₀.mem (s₀.gpr sb) e j := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  simp only [entryW]
  refine hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * tableSlot + 64 * e + 8 * j), 8⟩)
    (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq]; omega_using []) (by rw [tableSlot_eq]; omega_using [he, hj])

theorem Ctx.keyRel {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < 32) :
    WordRel (fun j => keyW s (8 * e + j)) fun _ => E (m + e) :=
  (hp.keys _ hme).congr fun j hj => by rw [keyW_entry hk, hc.entry hp hme hj]

theorem Ctx.ok {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hc.base hk hm

/-- A round, under `Ctx`: `round l a …` with the round key at entry `m + a`. -/
theorem round_step (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {a b c d m : Nat} (ha : a < 4) (hb : b = (a + 1) % 4) (hc' : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 64 12) layerCfg (linExt 32) (preX a b c d) preEnv
      (linPostG 12 (qOuts (preG a b c d)) [] (keyMaskSlots ++ stateSlots) preEnv) = true)
    (hlin : check (lanes 64 12) linCfg (linExt 40) (lin l a) linEnv
      (linPostG 12 [] (linOuts l a) (linKeep a) linEnv) = true)
    (hall : (restRegs.all fun r =>
      (preX a b c d ++ lin l a).all fun i => dstOf i != some r) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧
      StRel s' (fun b' => sround l (E (m + a)) a (X b')) := by
  obtain ⟨s', h', hX', hm', rd', wr', -, o', f'⟩ :=
    round_ok l ha hb hc' hd hpre hlin hall (hc.ok hp hk hm) hc.masks hX (hc.keyRel hp hk (e := a) (by omega_using [ha, hm]))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ => o' r hr) (f'.mono fun r hr => ?_) hm', o' _ (by decide), hX'⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg, hc.base]; simp

/-- Four rounds, the round keys at entries `4 m … 4 m + 3`. -/
theorem rounds4_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (rounds4 l) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧
      StRel s' (fun b => quad l E m (X b)) := by
  have hm4 : 4 * m + 4 ≤ 32 := by omega_using [hm]
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

/-! ## The loop of the rounds -/

/-- `addi kr, kr, n`, keeping all else. -/
theorem addKp_ok (s : State) (n : Nat) (hn : n < 2 ^ 15) :
    ∃ s', runBlock isa [.addi kr kr n] s = some s' ∧
      s'.gpr kr = s.gpr kr + BitVec.ofNat 64 n ∧ (∀ r, r ≠ kr → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s kr (s.gpr kr + BitVec.ofNat 64 n)
  ⟨_, by simp only [runBlock_cons, exec_addi (show kr ≠ .r0 by decide) hn, runStep_some, runBlock_nil],
    u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- `sub d, n, m`, keeping all else. -/
theorem subR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.sub d n m] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (s.gpr n - s.gpr m)
  ⟨_, by simp only [runBlock_cons, exec_sub, runStep_some, runBlock_nil], u.gpr, u.other, u.mem, u.rd, u.wr⟩

theorem entry_beq (b : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x - (b + BitVec.ofNat 64 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, VG.Offset.ofNat_sub_ofNat_beq hx hy]

/-- `bne`: whether `r` is not zero. -/
theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some !(s.gpr r == 0) := by
  show VG.PPC64LE.eval (.nonzero .d r) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, bne]

/-- `beq`: whether `r` is zero. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0) := by
  show VG.PPC64LE.eval (.zero .d r) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- A step that changes only `kr` and the layers' registers keeps `Ctx`. -/
theorem Ctx.kr {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ kr → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r _ h2 => hg r h2) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
    simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

/-- A step that changes only `t0` keeps `Ctx`. -/
theorem Ctx.t0 {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h1 _ => hg r fun h => h1 (by subst h; decide))
    (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
      simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

theorem StRel.congr {s s' : State} {X : Nat → Nat → Spec.Sm4.Word} (h : StRel s X)
    (hs : ∀ k, slotW s' k = slotW s k) : StRel s' X :=
  fun w hw => (h w hw).congr fun _ _ => hs _

/-- Four rounds, `add kr, kr, #256` and `sub t0, kr, r11`. -/
theorem roundsBody_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    (hr11 : s₀.gpr .r11 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd))
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (roundsBody l) s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (4 * (m + 1)) ∧
      StRel s' (fun b => quad l E m (X b)) ∧ (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok l hp hc hk hm hX
  obtain ⟨s₂, e₂, kr₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := subR_ok s₂ t0 kr .r11
  have hc₂ : Ctx s₀ s₂ := c₁.kr o₂ m₂ rd₂ wr₂
  have hk₂ : AtEntry s₂ (s₀.gpr sb) (4 * (m + 1)) := by
    rw [AtEntry, kr₂, k₁, show s.gpr kr = _ from hk, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_using []]
  have hk₃ : AtEntry s₃ (s₀.gpr sb) (4 * (m + 1)) := by rw [AtEntry, g₃ _ (by decide)]; exact hk₂
  have hr11₂ : s₂.gpr .r11 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [hc₂.keep _ (by decide) (by decide), hr11]
  refine ⟨s₃, ?_, hc₂.t0 g₃ m₃ rd₃ wr₃, hk₃, ?_, ?_⟩
  · rw [roundsBody, runBlock_app, e₁, Option.bind_some,
      show ([.addi kr kr 256, .sub t0 kr .r11] : List Instr) =
        [.addi kr kr 256] ++ [.sub t0 kr .r11] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃]
  · exact X₁.congr fun k => by simp only [slotW, m₃, g₃ sb (by decide), m₂, o₂ sb (by decide)]
  · rw [z₃, show s₂.gpr kr = _ from hk₂, hr11₂,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_using [hm]) (by rw [tableSlot_eq]; omega_using [])]
    simp only [decide_eq_decide]; omega_using []

/-- `addi r, sb, 8 k`. -/
theorem slotAddr_ok (s : State) (r : Reg) (k : Nat) (hk : 8 * k < 2 ^ 15) :
    ∃ s', runBlock isa (slotAddr r k) s = some s' ∧
      s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * k) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s r (s.gpr sb + BitVec.ofNat 64 (8 * k))
  ⟨_, by simp only [slotAddr, runBlock_cons, exec_addi (show sb ≠ .r0 by decide) hk, runStep_some,
      runBlock_nil], u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- The 32 rounds, the round keys at entries `0 … 31`, `r11` the table's end. -/
theorem rounds_wp (l : Lin) {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (hr11 : s₀.gpr .r11 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s₀ X) :
    WP isa (rounds l) s₀ fun s' => Ctx s₀ s' ∧ StRel s' (fun b => quads l E 8 (X b)) := by
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s₀ kr tableSlot (by decide)
  have hc₁ : Ctx s₀ s₁ := (Ctx.refl hm).kr o₁ m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  let Inv : Nat → State → Prop := fun n s' => ∃ m, n = 8 - m ∧ m < 8 ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (4 * m) ∧ StRel s' (fun b => quads l E m (X b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) 8 s₁
    ⟨0, rfl, by omega_using [], hc₁, by rw [AtEntry, k₁]; simp, hX.congr fun k => by simp only [slotW, m₁, o₁ sb (by decide)]⟩
  obtain ⟨m, rfl, hm8, hc', hk', hX'⟩ := hs'
  obtain ⟨s'', e'', c'', k'', X'', z''⟩ := roundsBody_ok l hp hc' hr11 hk' hm8 hX'
  have X3 : StRel s'' fun b => quads l E (m + 1) (X b) := X''
  refine WP.of_runBlock ⟨s'', e'', ?_⟩
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_nonzero, z'', h8]; rfl, c'', ?_⟩
    rw [h8] at X3; exact X3
  · exact .inr ⟨by rw [eval_nonzero, z'']; simp [h8], 8 - (m + 1), by omega_using [hm8], m + 1, rfl, by omega_using [hm8, h8], c'', k'', X3⟩

end VG.Proof.Sm4.PPC64LE

end

end

/-! ### `Sm4.PPC64LE.Crypt16`, which this module and modules that import it used -/

section

/-!
# The transposes, and sixteen blocks of bitsliced SM4 on PPC64LE

`toBs_step` turns the sixteen blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt16_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock readW64_bit getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (s.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  fit := by rw [hc.base]; exact hp.fit
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem Ctx.trans {s₀ s₁ s₂ : State} (h₁ : Ctx s₀ s₁) (h₂ : Ctx s₁ s₂) : Ctx s₀ s₂ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b => (h₂.keep r a b).trans (h₁.keep r a b),
    h₁.frame.trans (by rw [← h₁.base]; exact h₂.frame), h₂.masks⟩

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := ⟨_, by rw [hc.wr]; exact hp.scr, by
    have hfit := hp.fit
    simp only [bsCfg, tableSlot_eq] at hk
    simp only [wordAddr, bsCfg, hc.base]
    rw [slots_eq] at hfit ⊢
    exact VG.Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  extIn k hk := by simp [bsCfg] at hk
  slots := by simp only [bsCfg, tableSlot_eq]; omega_using []
  sep k _ j hj := by simp [bsCfg] at hj

/-- What a block of slots below the table that keeps the masks keeps of `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem)
    (hm : MasksOk s') : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h _ => hk r h) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base]) hm

theorem byte_addr (b : Addr) {k i : Nat} {n : Nat} (hn : 8 * k + i = n) :
    wordAddr b k + BitVec.ofNat 64 i = b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega_using [hk], by omega_using [hk], rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_using [this], hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => toBs.all fun i => dstOf i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), fun w hw b hb i hi j hj => ?_⟩
  · rw [slotW, hb', hkr kv.1 (List.mem_map_of_mem hkv) (by have := mask_lt hkv; rw [tableSlot_eq]; omega_using [this])]
    exact hc.masks kv hkv
  · have hp16 : 16 * i + b < 64 := by omega_using [hb, hi]
    have hmem := hso (64 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
        simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_using [hw, hj], rfl⟩)
        (by rw [tableSlot_eq]; omega_using [hw, hj]) _ hp16
    rw [show (8 * w + j) / 8 = w by omega_using [hj], show (8 * w + j) % 8 = j by omega_using [hj]] at hmem
    have ht : 8 * (4 * (w % 2) + i) + j < 64 := by omega_using [hi, hj]
    show (slotW s' (stateSlot w j)).getLsbD (16 * i + b) = _
    rw [slotW, hb', show stateSlot w j = 64 + (8 * w + j) by simp only [stateSlot]; omega_using [], hmem, toBsG,
      show (16 * i + b) % 16 = b by omega_using [hb], show (16 * i + b) / 16 = i by omega_using [hb], xorBits_cons, xorBits_nil,
      Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW64_bit _ _ (by omega_using [hi]) hj]
    simp only [ofBlock]
    rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega_using [hw, hi]), byte_addr _ rfl, addr_add]
    rw [show 8 * (tailSlot + (2 * b + w / 2)) + (4 * (w % 2) + i) = 8 * tailSlot + 16 * b + (4 * w + i) by omega_using []]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧ StRel s' X ∧
      ∀ b < 16, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (64 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => fromBs.all fun i => dstOf i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have keep : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s' k = slotW s k := fun k hk => by
    have hk' : k < 128 := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega_arith
    rw [slotW, hb', hkr k hk (by rw [tableSlot_eq]; exact hk')]
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), ?_, fun b hb => ?_⟩
  · rw [keep kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hc.masks kv hkv
  · exact fun w hw => (hX w hw).congr fun j hj => by
      show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
      exact keep _ (List.mem_append_right _ (by
        simp only [stateSlots, List.mem_map, List.mem_range]
        exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩))
  · apply Vector.ext
    intro k hk
    refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
    rw [getLsbD_outBlock' (X b) hk hj]
    have ht : 8 * (k % 8) + j < 64 := by omega_arith
    have hmem := hso (tailSlot + (2 * b + k / 8)) (fromBsG (2 * b + k / 8)) (by
        simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨2 * b + k / 8, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
    rw [readW64_bit _ _ (by omega_arith) hj, byte_addr _ rfl] at hmem
    have e1 : 8 * (3 - (2 * ((2 * b + k / 8) % 2) + (8 * (k % 8) + j) / 32)) + (8 * (k % 8) + j) % 8 =
        8 * (3 - k / 4) + j := by omega_arith
    have e2 : 16 * ((8 * (k % 8) + j) / 8 % 4) + (2 * b + k / 8) / 2 = 16 * (k % 4) + b := by omega_arith
    have hw : 3 - k / 4 < 4 := by omega_arith
    have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega_arith) j hj
    rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [addr_add, show 8 * tailSlot + 16 * b + k = 8 * (tailSlot + (2 * b + k / 8)) + k % 8 by omega_arith,
      hb', hmem, ← hbit, planes_eq]

/-- `crypt16`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt16_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (hr11 : s₀.gpr .r11 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) :
    WP isa crypt16 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 16, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, -, X₁⟩ := toBs_step hp (Ctx.refl hm)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hr11₁ : s₁.gpr .r11 = s₁.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [c₁.keep _ (by decide) (by decide), c₁.base, hr11]
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) c₁.masks hr11₁ X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.PPC64LE

end

end

/-! ### `Sm4.PPC64LE.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced round keys on PPC64LE

`keyOne_step`: `keyOne h` bitslices round key `2 m + h`, half `h` of the
64-bit word at `r3`, into the table's entry at `kr`, every block's copy of
it alike. `keys_wp` builds the table in the order the rounds use the round
keys: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR)
open VG.Proof.Sm4 (WordRel readW64_bit getLsbD_scheduleAt)

/-- Round key `2 m + h`, half `h` of the 64-bit word `x`. -/
def rkWord (x : BitVec 64) (h : Nat) : Spec.Sm4.Word := (x >>> (32 * h)).setWidth 32

theorem keyStore_eq (h : Nat) : keyOne h = keyLoad h ++ keyStore := rfl

/-- Round key `2 m + h` from the word at `r3` to the entry at `kr`. -/
theorem keyOne_step {s : State} {b : Addr} {e h : Nat} (hh : h = 0 ∨ h = 1)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hkr : s.gpr kr = b + BitVec.ofNat 64 (8 * tableSlot + 64 * e)) (he : e < 32)
    (hx0 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r3) 0) 8)
    (hsep : ∀ k < 64, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .r3) 0) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne h) s = some s' ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] s.mem s'.mem ∧
      WordRel (entryW s'.mem b e) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .r3) 0) 64) h) := by
  rw [slots_eq] at hscr
  have hok : Ok keyCfg s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => by simp only [keyCfg] at hk ⊢; obtain rfl : k = 0 := by omega_arith
                              exact hx0
      slots := by simp [keyCfg]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; obtain rfl : j = 0 := by omega_arith
        rw [hb]; exact hsep k hk }
  have hchk : check (lanes 64 7) keyCfg (linExt 0) (keyLoad h) keyEnv
      (linPostG 7 (qOuts (keyBsG h)) [] keyMaskSlots keyEnv) = true := by
    rcases hh with rfl | rfl
    · exact keyLoad0_check
    · exact keyLoad1_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkr₁, rd₁, wr₁, -, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .r3) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega_arith, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₁ hkr₁ f₁
  have hall₁ : ∀ r, r ∉ sboxWrites → ((keyLoad h).all fun i => dstOf i != some r) = true := fun r hr => by
    have : (restRegs.all fun r => (keyLoad h).all fun i => dstOf i != some r) =
        true := by rcases hh with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r (not_sboxWrites r hr)
  have k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s.gpr r := fun r hr => o₁ r (hall₁ r hr)
  -- The planes of the round key.
  have hQ : WordRel (Qs s₁) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .r3) 0) 64) h) := by
    intro b' hb' i hi j hj
    have hp : 16 * i + b' < 64 := by omega_arith
    rw [Qs, ho₁ (q j) (keyBsG h j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      _ hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 32 * h + 8 * (3 - (16 * i + b') / 16) + j = 64 * 0 + (32 * h + 8 * (3 - i) + j) by omega_arith,
      bitOf_word _ _ _ (by rcases hh with rfl | rfl <;> omega_arith), rkWord, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp only [show 8 * (3 - i) + j < 32 by omega_arith, decide_true, Bool.true_and]
    exact congrArg (BitVec.getLsbD _) (by omega_arith)
  -- The stores.
  have hkr₁' : s₁.gpr kr = s.gpr kr := k₁ kr (by decide)
  have hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hkr₁', hkr, wordAddr, addr_add, tableSlot_eq]
        exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, -, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  have k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (by simp [keyStore, dstOf])
  have he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    have h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hkr₁', hkr, addr_add]
  refine ⟨s₂, ?_, fun r hr => by rw [k₂, k₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun kv hkv => ?_,
    ?_, hQ.congr fun j hj => he₂ j hj⟩
  · rw [keyStore_eq, runBlock_app, e₁, Option.bind_some, e₂]
  · have hk : kv.1 < 64 := mask_lt hkv
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    have h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hkr₁', hkr, hb, wordAddr]
      rw [tableSlot_eq]
      exact VG.Offset.disjoint b (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    rw [k₂, hb₁, h2, hkr₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hkr₁', hkr]

/-! ## Steps of the pointers and the counter -/

theorem addI_ok (s : State) (d n : Reg) {imm : Nat} (hn : n ≠ .r0 := by decide) (h : imm < 2 ^ 15 := by decide) :
    ∃ s', runBlock isa [.addi d n imm] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (s.gpr n + BitVec.ofNat 64 imm)
  ⟨_, by simp only [runBlock_cons, exec_addi hn h, runStep_some, runBlock_nil], u.gpr, u.other, u.mem, u.rd, u.wr⟩

theorem subI_ok (s : State) (d n : Reg) {imm : Nat} (hn : n ≠ .r0 := by decide) (h : imm ≤ 2 ^ 15 := by decide) :
    ∃ s', runBlock isa [.subi d n imm] s = some s' ∧ s'.gpr d = s.gpr n - BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (s.gpr n - BitVec.ofNat 64 imm)
  ⟨_, by simp only [runBlock_cons, exec_subi hn h, runStep_some, runBlock_nil], u.gpr, u.other, u.mem, u.rd, u.wr⟩

theorem li_ok (s : State) (d : Reg) {v : Nat} (hv : v < 2 ^ 15 := by decide) :
    ∃ s', runBlock isa [.li d v] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (BitVec.ofNat 64 v)
  ⟨_, by simp only [runBlock_cons, exec_li hv, runStep_some, runBlock_nil], u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `kr` before iteration `m`, as an offset in the scratch buffer. -/
def rsiAt : Dir → Nat → Nat
  | .encrypt, m => 8 * tableSlot + 128 * m
  | .decrypt, m => 8 * tableSlot - 64 + 64 * (32 - 2 * m)

/-- The instruction stepping `kr`. -/
def krStep : Dir → Instr
  | .encrypt => .addi kr kr 64
  | .decrypt => .subi kr kr 64


/-- `kr` moves from `x` to `y`. -/
def RsiStep : Dir → Nat → Nat → Prop
  | .encrypt, x, y => y = x + 64
  | .decrypt, x, y => x = y + 64

/-- `kr ± 64`. -/
theorem rsiStep_ok (dir : Dir) (s : State) {b : Addr} {x y : Nat} (hxy : RsiStep dir x y)
    (hkr : s.gpr kr = b + BitVec.ofNat 64 x) :
    ∃ s', runBlock isa [krStep dir] s = some s' ∧
      s'.gpr kr = b + BitVec.ofNat 64 y ∧
      (∀ r, r ≠ kr → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := addI_ok s kr kr (imm := 64) (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    rw [r', hkr, addr_add, show y = x + 64 from hxy]
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := subI_ok s kr kr (imm := 64) (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    have hxy : x = y + 64 := hxy
    rw [r', hkr, VG.Offset.add_ofNat_sub _ (by omega_arith), show x - 64 = y by omega_arith]

/-- The scratch buffer at `b` and the schedule at `sched`, apart. -/
structure SchedPre (s : State) (b sched : Addr) : Prop where
  base : s.gpr sb = b
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  sch : (⟨sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 64
  sep : Region.Disjoint ⟨sched, 128⟩ ⟨b, 8 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : Addr} (h : SchedPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

theorem SchedPre.rdiIn {s : State} {b sched : Addr} (h : SchedPre s b sched) {m : Nat} (hm : m < 16) :
    InRegions (s.rd ++ s.wr) (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 8 :=
  ⟨_, h.sch, by rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)⟩

theorem SchedPre.rdiSep {s : State} {b sched : Addr} (h : SchedPre s b sched) {m : Nat} (hm : m < 16)
    {k : Nat} (hk : k < 64) : Mem.Sep (wordAddr b k) 8 (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf
  refine h.sep.symm.sep (VG.Offset.contains_base b (by rw [slots_eq]; omega_arith) (by omega_arith)) ?_
  rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)

/-- The schedule's round keys `2 m` and `2 m + 1`, as halves of its word `m`. -/
theorem rkWord_eq (mem : Mem) (sched : Addr) {m h : Nat} (hm : m < 16) (hh : h < 2) :
    rkWord (mem.readW (wordAddr (sched + BitVec.ofNat 64 (8 * m)) 0) 64) h =
      (Spec.Sm4.scheduleAt mem sched).getD (2 * m + h) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 2 * m + h < 32 := by omega_arith
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    rkWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [show 8 * (k / 8) + k % 8 < 32 by omega_arith, decide_true, Bool.true_and]
  rw [show 32 * h + (8 * (k / 8) + k % 8) = 8 * (4 * h + k / 8) + k % 8 by omega_arith,
    readW64_bit _ _ (by omega_arith) (by omega_arith), wordAddr, addr_add, addr_add]
  rw [show 8 * m + (8 * 0 + (4 * h + k / 8)) = 4 * (2 * m + h) + k / 8 by omega_arith]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [tableSlot_eq] at *
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by omega_arith) (by omega_arith)
  · exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)

/-- What the loop keeps, after `m` of its 16 iterations. -/
structure KInv (s₀ : State) (b sched : Addr) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : SchedPre s b sched
  rsi : s.gpr kr = b + BitVec.ofNat 64 (rsiAt dir m)
  rdi : s.gpr .r3 = sched + BitVec.ofNat 64 (8 * m)
  ent : ∀ i < 2 * m, WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem sched).getD i 0)
  masks : MasksOk s
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .r3 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem entOf_lt (dir : Dir) {i : Nat} (hi : i < 32) : entOf dir i < 32 := by cases dir <;> simp [entOf] <;> omega_arith

theorem entOf_inj (dir : Dir) {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : entOf dir i = entOf dir i') :
    i = i' := by cases dir <;> simp [entOf] at h <;> omega_arith

theorem rsiAt_ent (dir : Dir) {m : Nat} (hm : m < 16) :
    rsiAt dir m = 8 * tableSlot + 64 * entOf dir (2 * m) := by
  cases dir <;> simp only [rsiAt, entOf, tableSlot_eq] <;> omega_arith

/-- The schedule is outside the scratch buffer. -/
theorem SchedPre.sched_eq' {s : State} {b sched : Addr} (h : SchedPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨b, 8 * n⟩] m m') :
    Spec.Sm4.scheduleAt m' sched = Spec.Sm4.scheduleAt m sched := by
  have hb : ∀ k < 128, m' (sched + BitVec.ofNat 64 k) = m (sched + BitVec.ofNat 64 k) := fun k hk =>
    hf.bytes (R := ⟨sched, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_right (Region.sub_prefix (by omega_arith))) (by show 128 ≤ 2 ^ 64; omega_arith) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith), hb (4 * i + 3) (by omega_arith)]

theorem SchedPre.sched_eq {s : State} {b sched : Addr} (h : SchedPre s b sched) {m m' : Mem}
    (hf : Frame [⟨b, 8 * tableEnd⟩] m m') :
    Spec.Sm4.scheduleAt m' sched = Spec.Sm4.scheduleAt m sched :=
  h.sched_eq' (by rw [tableEnd_eq, slots_eq]; omega_arith) hf

theorem rsiAt_succ (dir : Dir) {m : Nat} (hm : m < 16) :
    RsiStep dir (rsiAt dir m) (8 * tableSlot + 64 * entOf dir (2 * m + 1)) ∧
    RsiStep dir (8 * tableSlot + 64 * entOf dir (2 * m + 1)) (rsiAt dir (m + 1)) := by
  cases dir <;> simp only [RsiStep, rsiAt, entOf, tableSlot_eq] <;> omega_arith

/-- One iteration: round keys `2 m` and `2 m + 1`. -/
theorem keyIter_ok (dir : Dir) {s₀ s : State} {b sched : Addr} {m : Nat} (hm : m < 16)
    (hi : KInv s₀ b sched dir m s) :
    ∃ s', runBlock isa (keyOne 0 ++ ([krStep dir] : List Instr) ++ keyOne 1 ++
        ([krStep dir, .addi .r3 .r3 8] : List Instr)) s = some s' ∧
      KInv s₀ b sched dir (m + 1) s' := by
  have hpre := hi.pre
  have hfit := hpre.fit
  have he0 := entOf_lt dir (show 2 * m < 32 by omega_arith)
  have he1 := entOf_lt dir (show 2 * m + 1 < 32 by omega_arith)
  have hsched : Spec.Sm4.scheduleAt s.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hpre.sched_eq hi.frame
  -- Round key `2 m`.
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (h := 0) (e := entOf dir (2 * m)) (Or.inl rfl)
    hpre.base hpre.scr (by rw [hi.rsi, rsiAt_ent dir hm]) he0 (by rw [hi.rdi]; exact hpre.rdiIn hm)
    (fun k hk => by rw [hi.rdi]; exact hpre.rdiSep hm hk) hi.masks
  rw [hi.rdi, rkWord_eq _ _ hm (by decide), hsched] at E₁
  obtain ⟨st1, st2⟩ := rsiAt_succ dir hm
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := rsiStep_ok dir s₁ (b := b) (x := rsiAt dir m)
    (y := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) st1
    (by rw [o₁ _ (by decide), hi.rsi])
  have hpre₂ : SchedPre s₂ b sched :=
    hpre.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hrdi₂ : s₂.gpr .r3 = sched + BitVec.ofNat 64 (8 * m) := by
    rw [o₂ _ (by decide), o₁ _ (by decide), hi.rdi]
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact m₁ kv hkv
  -- Round key `2 m + 1`.
  obtain ⟨s₃, e₃, o₃, rd₃, wr₃, m₃, f₃, E₃⟩ := keyOne_step (h := 1) (e := entOf dir (2 * m + 1)) (Or.inr rfl)
    hpre₂.base hpre₂.scr r₂ he1 (by rw [hrdi₂]; exact hpre₂.rdiIn hm)
    (fun k hk => by rw [hrdi₂]; exact hpre₂.rdiSep hm hk) hm₂
  have hfr₂ : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s₂.mem := by
    rw [m₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [tableEnd_eq]
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega_arith)
    · rw [tableSlot_eq]; exact VG.Offset.sub_base b (by omega_arith)
  rw [hrdi₂, rkWord_eq _ _ hm (by decide), hpre₂.sched_eq hfr₂] at E₃
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rsiStep_ok dir s₃ (b := b)
    (x := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) (y := rsiAt dir (m + 1))
    st2 (by rw [o₃ _ (by decide), r₂])
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .r3 .r3 (imm := 8) (by decide)
  have hmem : s₅.mem = s₃.mem := by rw [m₅, m₄]
  have hb₆ : s₅.gpr sb = s₃.gpr sb := by rw [o₅ _ (by decide), o₄ _ (by decide)]
  have hf₃ : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s₃.mem := by
    refine hfr₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [tableEnd_eq]
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega_arith)
    · rw [tableSlot_eq]; exact VG.Offset.sub_base b (by omega_arith)
  refine ⟨s₅, ?_, ⟨hpre₂.congr (by rw [hb₆, o₃ _ (by decide)]) (by rw [rd₅, rd₄, rd₃])
      (by rw [wr₅, wr₄, wr₃]), by rw [o₅ _ (by decide), r₄], ?_, fun i hi' => ?_,
      fun kv hkv => ?_, by rw [hmem]; exact hf₃, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩⟩
  · rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃,
      Option.bind_some,
      show ([krStep dir, .addi .r3 .r3 8] : List Instr) = [krStep dir] ++ [.addi .r3 .r3 8] from rfl,
      runBlock_app, e₄, Option.bind_some, e₅]
  · rw [r₅, o₄ _ (by decide), o₃ _ (by decide), hrdi₂, addr_add,
      show 8 * m + 8 = 8 * (m + 1) by omega_arith]
  · have hent : ∀ i' < 32, i' ≠ entOf dir (2 * m) → i' ≠ entOf dir (2 * m + 1) → ∀ j < 8,
        entryW s₅.mem b i' j = entryW s.mem b i' j := fun i' hi'' h0 h1 j hj => by
      rw [hmem, entryW_frame f₃ hi'' he1 h1 hj, m₂, entryW_frame f₁ hi'' he0 h0 hj]
    rcases (show i < 2 * m ∨ i = 2 * m ∨ i = 2 * m + 1 by omega_arith) with hlt | rfl | rfl
    · exact (hi.ent i hlt).congr fun j hj => hent _ (entOf_lt dir (by omega_arith))
        (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith)
        (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith) j hj
    · refine E₁.congr fun j hj => ?_
      rw [hmem, entryW_frame f₃ he0 he1 (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith) hj, m₂]
    · exact E₃.congr fun j hj => by rw [hmem]
  · show s₅.mem.readW (wordAddr (s₅.gpr sb) kv.1) 64 = kv.2
    rw [hmem, hb₆]; exact m₃ kv hkv
  · rw [o₅ r h3, o₄ r h2, o₃ r h1, o₂ r h2, o₁ r h1, hi.regs r h1 h2 h3 h4]

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega_arith

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

/-- What the table's construction leaves. -/
structure KeysPost (s₀ : State) (b sched : Addr) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched))
  masks : MasksOk s
  rdi : s.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd)
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .r3 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem keyPairs_wp (dir : Dir) {s₀ : State} {b sched : Addr} :
    ∀ n m, m + n = 16 → ∀ s, KInv s₀ b sched dir m s →
      WP isa (keyPairs (krStep dir) n) s (KInv s₀ b sched dir 16)
  | 0, m, h, s, hi => wp_nil (by rw [show m = 16 by omega_arith] at hi; exact hi)
  | n + 1, m, h, s, hi => by
    obtain ⟨s', e', hi'⟩ := keyIter_ok dir (by omega_arith) hi
    exact WP.seq (WP.of_runBlock ⟨s', e', keyPairs_wp dir n (m + 1) (by omega_arith) s' hi'⟩)

theorem keysGen_wp (dir : Dir) (k : Nat) (hk : 8 * k = rsiAt dir 0) (hse : 8 * k < 2 ^ 15)
    {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched) (hrdi : s₀.gpr .r3 = sched) (hm : MasksOk s₀) :
    WP isa (.seq (.seq (.block (slotAddr kr k)) (keyPairs (krStep dir) 16))
      (.block (slotAddr .r11 tableEnd))) s₀ (KeysPost s₀ b sched dir) := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s₀ kr k hse
  have hinv : KInv s₀ b sched dir 0 s₁ := by
    refine ⟨hp.congr (by rw [o₁ _ (by decide)]) rd₁ wr₁,
      by rw [r₁, hp.base, hk], by rw [o₁ _ (by decide), hrdi]; simp,
      fun i hi => by omega_arith, fun kv hkv => ?_, by rw [m₁]; exact Frame.refl _ _,
      fun r _ h2 _ _ => by rw [o₁ r h2], rd₁, wr₁⟩
    show s₁.mem.readW (wordAddr (s₁.gpr sb) kv.1) 64 = kv.2
    rw [m₁, o₁ _ (by decide)]; exact hm kv hkv
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.mono (keyPairs_wp dir 16 0 rfl s₁ hinv) fun s h => ?_⟩))
  have hfit := h.pre.fit
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s .r11 tableEnd (by decide)
  refine WP.of_runBlock ⟨s₃, e₃, h.pre.congr (o₃ _ (by decide)) rd₃ wr₃, ⟨?_, ?_, fun e he => ?_⟩, fun kv hkv => ?_,
    by rw [r₃, h.pre.base], by rw [m₃]; exact h.frame, fun r h1 h2 h3 h4 => by rw [o₃ r h4, h.regs r h1 h2 h3 h4],
    by rw [rd₃, h.rd], by rw [wr₃, h.wr]⟩
  · rw [wr₃, o₃ _ (by decide), h.pre.base]; exact h.pre.scr
  · rw [o₃ _ (by decide), h.pre.base]; exact hfit
  · rw [o₃ _ (by decide), h.pre.base, m₃]
    have := h.ent (entOf dir e) (by have := entOf_lt dir he; omega_arith)
    rw [entOf_entOf dir he] at this
    exact this
  · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    rw [m₃, o₃ _ (by decide)]; exact h.masks kv hkv

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched)
    (hrdi : s₀.gpr .r3 = sched) (hm : MasksOk s₀) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  cases dir
  · exact keysGen_wp .encrypt tableSlot (by simp [rsiAt]) (by decide) hp hrdi hm
  · exact keysGen_wp .decrypt (tableSlot + 8 * 31) (by simp [rsiAt, tableSlot_eq]) (by decide) hp hrdi hm

end VG.Proof.Sm4.PPC64LE

end

end

/-! ### `Sm4.PPC64LE.Prologue`, which this module and modules that import it used -/

section

/-! ### `Sm4.PPC64LE.Imm`, which this module and modules that import it used -/

section

/-!
# 64-bit constants on PPC64LE

`imm_ok`: `imm64 d v` (`lis` and `ori` of the high word, `sldi 32`, then
`oris` and `ori` of the low word) leaves `v` in `d` and changes nothing
else.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE (imm64)

/-- The value `imm64 d v` builds, bit by bit, is `v`. -/
theorem imm64_val (v : BitVec 64) :
    ((((v.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64 ||| (v.extractLsb' 32 16).setWidth 64) <<< 32) |||
      (v.extractLsb' 16 16).setWidth 64 <<< 16) ||| (v.extractLsb' 0 16).setWidth 64 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h1 : i < 16
  · simp [h1, show i < 32 by omega_using [h1]]
  by_cases h2 : i < 32
  · simp [h1, h2, show i - 16 < 16 by omega_using [h2], show 16 + (i - 16) = i by omega_using [h1], show i - 16 < 64 by omega_using [hi]]
  by_cases h3 : i < 48
  · simp [h1, h2, show i - 32 < 16 by omega_using [h3], show 32 + (i - 32) = i by omega_using [h2], show ¬ i - 16 < 16 by omega_using [h2],
      show i - 32 < 32 by omega_using [hi], show i - 32 < 64 by omega_using [hi]]
  · simp [h1, h2, show ¬ i - 32 < 16 by omega_using [h3], show i - 32 < 64 by omega_using [hi], show i - 32 - 16 < 16 by omega_using [hi],
      show 48 + (i - 32 - 16) = i by omega_using [h3], show ¬ i - 16 < 16 by omega_using [h2], show i - 32 < 32 by omega_using [hi]]

theorem gpr_write_self (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).gpr d = v := (Upd.write s d v).gpr

/-- `imm64 d v` leaves `v` in `d`. -/
theorem imm_ok (s : State) (d : Reg) (v : BitVec 64) :
    ∃ s', runBlock isa (imm64 d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v₁ := (v.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64
  let s₁ := s.write d v₁
  have u₁ := Upd.write s d v₁
  let v₂ := v₁ ||| (v.extractLsb' 32 16).setWidth 64
  have u₂ := Upd.write s₁ d v₂
  let v₃ := v₂ <<< 32
  have u₃ := Upd.write (s₁.write d v₂) d v₃
  let v₄ := v₃ ||| (v.extractLsb' 16 16).setWidth 64 <<< 16
  have u₄ := Upd.write ((s₁.write d v₂).write d v₃) d v₄
  let v₅ := v₄ ||| (v.extractLsb' 0 16).setWidth 64
  have u₅ := Upd.write (((s₁.write d v₂).write d v₃).write d v₄) d v₅
  refine ⟨_, ?_, u₅.gpr.trans (imm64_val v), fun r hr => ?_, u₅.mem.trans (u₄.mem.trans (u₃.mem.trans (u₂.mem.trans u₁.mem))),
    u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))),
    u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr)))⟩
  · simp only [imm64, runBlock_cons, exec_lis, exec_ori, exec_lsl (show 32 < 64 by decide), exec_oris, runStep_some,
      runBlock_nil, gpr_write_self]
    rfl
  · rw [u₅.other r hr, u₄.other r hr, u₃.other r hr, u₂.other r hr, u₁.other r hr]

end VG.Proof.Sm4.PPC64LE

end

end

/-!
# SM4's prologue and epilogue on PPC64LE

Saving and restoring the callee-saved registers `r14`–`r31` in their slots
(`save_ok`, `restore_ok`, by symbolic execution of the stores and loads,
as Camellia's), and storing constants to slots (`setSlotsN_ok`, through
`imm_ok`): the masks of the round keys' planes, and the key schedule's
table of `CK`.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS imm64)

theorem savedSlot_eq : savedSlot = 384 := rfl
theorem sb_ne_t0 : sb ≠ t0 := by decide

/-! ## Loads and stores of slots -/

/-- `ld r, 8 k(sb)`. -/
theorem ldMask_ok {s : State} {r : Reg} {k : Nat} {M : BitVec 64} (hk : 8 * k < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8)
    (hv : s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64 = M) :
    ∃ s', runBlock isa [ldS r k] s = some s' ∧ s'.gpr r = M ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have u := Upd.write s r (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64)
  exact ⟨_, by simp only [ldS, runBlock_cons, exec_load_d (show sb ≠ .r0 by decide) ⟨by omega_using [hk], by omega_using []⟩ hin,
    runStep_some, runBlock_nil], u.gpr.trans hv, u.other, u.mem, u.rd, u.wr⟩

/-- Loads of slots into distinct registers other than `sb`. -/
theorem ldS_list_ok : ∀ (L : List (Reg × Nat)) (s : State), (∀ x ∈ L, x.1 ≠ sb) → (L.map (·.1)).Nodup →
    (∀ x ∈ L, 8 * x.2 < 32768 ∧ InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * x.2)) 8) →
    ∃ s', runBlock isa (L.map fun x => ldS x.1 x.2) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧ ∀ x ∈ L, s'.gpr x.1 = slotW s x.2
  | [], s, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hsb, hnd, hin => by
    have hx := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := x.1) (k := x.2) hx.1 hx.2 rfl
    have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hsb x List.mem_cons_self).symm
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s₁ (fun y hy => hsb y (List.mem_cons_of_mem _ hy))
      hnd.2 (fun y hy => by rw [rd₁, wr₁, hb₁]; exact hin y (List.mem_cons_of_mem _ hy))
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact (o' _ hnd.1).trans v₁
      · rw [v' y hy]; simp only [slotW, m₁, hb₁]

/-- `std t, 8 k(sb)`. -/
theorem stS_ok (s : State) {k : Nat} (t : Reg) (hk : 8 * k < 32768)
    (hin : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8) :
    runBlock isa [stS k t] s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr t) } := by
  simp only [stS, runBlock_cons, runStep_some, runBlock_nil, exec_store_d (show sb ≠ .r0 by decide) ⟨by omega_using [hk], by omega_using []⟩ hin]

/-- Stores of registers to distinct slots in the region `R`. -/
theorem stS_list_ok (R : Region) : ∀ (L : List (Nat × Reg)) (s : State), (L.map (·.1)).Nodup →
    (∀ x ∈ L, 8 * x.1 < 32768 ∧ InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * x.1)) 8 ∧
      R.Contains (wordAddr (s.gpr sb) x.1) 8) →
    ∃ s', runBlock isa (L.map fun x => stS x.1 x.2) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [R] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < 2 ^ 58 → slotW s' k = slotW s k) ∧ ∀ x ∈ L, slotW s' x.1 = s.gpr x.2
  | [], s, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hnd, hin => by
    have hx := hin x List.mem_cons_self
    let s₁ : State := { s with mem := s.mem.writeW (wordAddr (s.gpr sb) x.1) (s.gpr x.2) }
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stS_list_ok R L s₁ hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hsep : ∀ k, k ≠ x.1 → k < 2 ^ 58 → slotW s₁ k = slotW s k := fun k hk hk58 =>
      Mem.readW_writeW_sep (slot_sep _ (by omega_using [hk58]) (by omega) hk) (by decide)
    refine ⟨s', ?_, g', rd', wr', ?_, fun k hk hk58 => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, stS_ok s x.2 hx.1 hx.2.1,
        Option.bind_some]
      exact e'
    · exact ((Frame.refl _ _).writeW (List.mem_singleton_self R) _ hx.2.2).trans f'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hk58]; exact hsep k hk.1 hk58
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (by omega)]; exact Mem.readW_writeW_self64 _ _ _
      · exact v' y hy

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r14

theorem savedRegs_eq : savedRegs = (List.range 18).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 18, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem sreg_ne_sb : ∀ i < 18, sreg i ≠ sb := by decide

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → slotW s' k = slotW s k := by
  let L : List (Nat × Reg) := (List.range 18).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs = L.map fun x => stS x.1 x.2 := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 18).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  have hw' := hw
  rw [slots_eq] at hw'
  obtain ⟨s', e', g', rd', wr', f', o', v'⟩ := stS_list_ok ⟨b, 8 * slots⟩ L s (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega, ⟨_, hw', ?_⟩, ?_⟩
      · rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega)
      · rw [hb, wordAddr, slots_eq]
        exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', f', fun k hk => o' k ?_ (by
    rw [savedSlot_eq] at hk; omega_using [hk])⟩
  · have := v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    simp only [slotW, g', hb] at this
    exact this
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_using [hk, h]

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 18, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := (List.range 18).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs = L.map fun x => ldS x.1 x.2 := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 18).map sreg := by simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_sb i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega, ⟨_, List.mem_append_right _ hw, ?_⟩⟩
      rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩), slotW, hb]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

/-! ## Constants -/

/-- `imm64 t0, v; std t0, 8 k(sb)`. -/
theorem setOne_ok {s : State} {b : Addr} {k : Nat} (v : BitVec 64) (hb : s.gpr sb = b) (hk : 8 * k < 32768)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa (imm64 t0 v ++ [stS k t0]) s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) v ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := imm_ok s t0 v
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ sb_ne_t0, hb]
  refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) }, ?_, ?_, fun r hr => o₁ r hr,
    rd₁, wr₁⟩
  · rw [runBlock_app, e₁, Option.bind_some]
    exact stS_ok s₁ t0 hk (by rw [wr₁, hb₁]; exact hw)
  · show s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) = _
    rw [hb₁, v₁, m₁]

theorem setSlotsN_ok (N : Nat) (hN : N ≤ slots) (ms : List (Nat × BitVec 64)) {s : State} {b : Addr}
    (hb : s.gpr sb = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : ∀ kv ∈ ms, kv.1 < N)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setSlots ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * N⟩] s.mem s'.mem := by
  rw [slots_eq] at hN
  induction ms generalizing s with
  | nil => exact ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | cons kv ms ih =>
    have hk0 : kv.1 < N := hk kv List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := setOne_ok (k := kv.1) kv.2 hb (by omega_using [hN, hk0]) ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [slots_eq]; omega_using [hN, hk0]) (by omega_using [hN, hk0])⟩
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := ih (s := s₁) (by rw [g₁ _ sb_ne_t0, hb]) (by rw [wr₁]; exact hw)
      (fun kv h => hk kv (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ sb_ne_t0, hb]
    have hnot : kv.1 ∉ ms.map (·.1) := (List.nodup_cons.mp hnd).1
    have hslot : ∀ k < slots, slotW s₁ k = if k = kv.1 then kv.2 else slotW s k := fun k hk' => by
      simp only [slotW, hb₁, hb, m₁]
      split
      · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
      · rename_i h
        rw [slots_eq] at hk'
        exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hk']) (by omega_using [hN, hk0]) h) (by decide)
    refine ⟨s', by
      rw [show setSlots (kv :: ms) = (imm64 t0 kv.2 ++ [stS kv.1 t0]) ++ setSlots ms from rfl,
        runBlock_app, e₁, Option.bind_some, e'], fun x hx => ?_, fun k hk' hn => ?_,
      fun r hr => by rw [g' r hr, g₁ r hr], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [k' _ (by rw [slots_eq]; omega_using [hN, hk0]) hnot, hslot _ (by rw [slots_eq]; omega_using [hN, hk0]), ite_eq_left rfl]
      · exact v' x hx
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' k hk' hn.2, hslot k hk', ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      rw [m₁]
      simp only [Mem.writeW, Mem.write, wordAddr]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * kv.1 + 8 ≤ 8 * N by omega_using [hk0]) _ (by simp only [Region.Contains]; omega_using [h]))

theorem setSlots_ok (ms : List (Nat × BitVec 64)) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : ∀ kv ∈ ms, kv.1 < tableSlot)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setSlots ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * tableSlot⟩] s.mem s'.mem :=
  setSlotsN_ok tableSlot (by rw [tableSlot_eq, slots_eq]; omega_using []) ms hb hw hk hnd

end VG.Proof.Sm4.PPC64LE

end

end

/-! ### `Sm4.PPC64LE.Copy`, which only this module used -/

section

/-!
# Copying blocks on PPC64LE

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `r6` to `r7` (areas that do not overlap), through `t0`,
counting down `r3`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (t0)

/-- `ld t0, d(r6); std t0, d(r7)`. -/
theorem copyWord_ok (s : State) {d : Nat} (hd : d % 8 = 0 ∧ d < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.load .d t0 .r6 d, .store .d t0 .r7 d] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r7 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain u := Upd.write s t0 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64)
  obtain h7 : (s.write t0 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64)).gpr .r7 = s.gpr .r7 :=
    u.other _ (by decide)
  let s₁ := s.write t0 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 d) 64)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .r7 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_, u.other,
    u.rd, u.wr⟩
  · simp only [runBlock_cons, exec_load_d (show Reg.r6 ≠ .r0 by decide) ⟨hd.2, by omega_using [hd]⟩ hr, runStep_some,
      exec_store_d (show Reg.r7 ≠ .r0 by decide) ⟨hd.2, by omega_using [hd]⟩ (by rw [h7]; exact hw), runBlock_nil, s₁]
  · show Mem.writeW _ _ _ = _
    rw [h7, u.gpr, u.mem]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r6 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .r7 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c ≤ 16)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain hA0 := hA (2 * j) (by omega_arith)
  obtain hA1 := hA (2 * j + 1) (by omega_arith)
  obtain hB0 := hB (2 * j) (by omega_arith)
  obtain hB1 := hB (2 * j + 1) (by omega_arith)
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  obtain hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s (d := 0) (by decide)
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ (d := 8) (by decide)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .r6 .r6 (imm := 16) (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .r7 .r7 (imm := 16) (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .r3 .r3 (imm := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.load .d t0 .r6 0, .store .d t0 .r7 0, .load .d t0 .r6 8, .store .d t0 .r7 8,
      .addi .r6 .r6 16, .addi .r7 .r7 16, .subi .r3 .r3 1] : List Instr) =
      [.load .d t0 .r6 0, .store .d t0 .r7 0] ++ ([.load .d t0 .r6 8, .store .d t0 .r7 8] ++
      ([.addi .r6 .r6 16] ++ ([.addi .r7 .r7 16] ++ [.subi .r3 .r3 1]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  obtain hn : 16 * c < 2 ^ 64 := by omega_arith
  obtain r1 : s₁.gpr .r7 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.dst]
  obtain a1 : s₁.gpr .r6 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.src]
  obtain hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  obtain hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  obtain hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  obtain hc₅ : s₅.gpr .r3 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show c - j - 1 = c - (j + 1) by omega_arith]
  obtain hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_arith)]; omega_arith), off_sub_toNat B h8 (by omega_arith), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_arith, hA₁ t (by omega_arith), hAs t (by omega_arith)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_arith)]; omega_arith), off_sub_toNat B h0 (by omega_arith), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_arith, hAs t (by omega_arith)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
          exact hi.copied t (by omega_arith)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_arith))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_arith)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_arith))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  obtain hz : (s₅.gpr .r3 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .r3).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .r3).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

end VG.Proof.Sm4.PPC64LE

end

end


/-!
# A group of blocks of SM4 ECB on PPC64LE

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(sixteen, or the last one to fifteen) to the tail buffer, transforms it
(`crypt16_wp`, which keeps the data pointer, the blocks left and the
table's end in `r4`–`r11`), copies the blocks back and steps to the next
group.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS shrI)

/-! ## Small blocks -/

theorem lsr4_beq {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 4 == 0) = decide (v < 16) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega_using [this]
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    simp
    omega_using [h]

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (s.gpr n ||| s.gpr n)
  ⟨_, by simp only [movR, runBlock_cons, exec_logic, runStep_some, runBlock_nil], u.gpr.trans BitVec.or_self,
    u.other, u.mem, u.rd, u.wr⟩

/-- `r12 := min(r5, 16)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r5 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (min v 16) ∧
      (∀ r, r ≠ .r12 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .r5 >>> 4)
  obtain u₁ := Upd.write s t0 (s.gpr .r5 >>> 4)
  obtain e₁ : runBlock isa [shrI t0 .r5 4] s = some s₁ := by
    simp only [shrI, runBlock_cons, exec_lsr_d (show 4 < 64 by decide), runStep_some, runBlock_nil, s₁]
  obtain t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 4 := by rw [u₁.gpr, hr]
  have o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := u₁.other
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (16 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr4_beq hv]; by_cases h : v < 16 <;> simp [h] <;> omega_using [h]))
    (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := li_ok s₁ .r12 (v := 16)
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, Nat.min_eq_right (by simp at h; omega_using [h])]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r12 .r5
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_using [h])]

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hj]) (by omega_using [hk]) h) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ keyMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ e < 32, VG.Proof.Sm4.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–50, the table (128–383) and 384–401. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 24⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩]

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : 48 ≤ kv.1 ∧ kv.1 < 51 := by
  simp [keyMasks] at hkv; rcases hkv with h | h | h <;> subst h <;> simp [evenSlot, oddSlot, grpSlot]

theorem ScrOk.frame {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b E m' := by
  obtain hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk := mask_range hkv
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_using [hk]) (by omega_using [hk]))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_using []) (by rw [tableSlot_eq]; omega_using [hi, hj]))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_using []) (by omega_using [hi]))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b E m' := by
  obtain hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_using []) (by rw [tableSlot_eq]; omega_using [hi, hj]))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_using []) (by omega_using [hi]))

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64

/-- `copyBlocks` from `r6` to `r7`, `r3` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc16 : c ≤ 16)
    (hx : s.gpr .r6 = X) (hy : s.gpr .r7 = Y) (hcx : s.gpr .r3 = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc16 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 (256 * k)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  r11 : s.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd)
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n (16 * k) (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa Impl.Sm4.PPC64LE.group s fun s' => (s'.gpr .r5 = 0 ∧ GDone s₀ b D n E s') ∨
      (s'.gpr .r5 ≠ 0 ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc16 : c ≤ 16 := by omega_arith
  obtain hkc : 256 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t, t < 32 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  obtain sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Sm4.PPC64LE.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r5 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .r6 .r4
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := slotAddr_ok s₂a .r7 tailSlot (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₂b .r3 .r12
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, runBlock_app, e₂a, Option.bind_some, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.r4])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain g₃' : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3 h5, g₂ r h1 h2 h3 h4 h5]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega_arith
  -- The sixteen blocks.
  obtain hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  obtain hr11₃ : s₃.gpr .r11 = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r11, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) hr11₃) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  obtain f₅ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₅.mem := by have := c₅.frame; rw [base₃] at this; exact this
  obtain sc₅ : ScrOk s₀ b E s₅.mem := by
    refine sc₃.frame2 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  obtain k₅ : ∀ r, r ∉ sboxWrites → r ≠ kr → s₅.gpr r = s₃.gpr r := fun r h1 h2 => c₅.keep r h1 h2
  obtain r4₅ : s₅.gpr .r4 = A := by
    rw [k₅ _ (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r4]
  obtain r5₅ : s₅.gpr .r5 = BitVec.ofNat 64 v := by
    rw [k₅ _ (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r5]
  obtain r11₅ : s₅.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [k₅ _ (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.r11]
  obtain wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  obtain rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r5₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := slotAddr_ok s₇ .r6 tailSlot (by decide)
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .r7 .r4
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈b .r3 .r12
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_app, e₈a, Option.bind_some,
      show ([movR .r7 .r4, movR .r3 .r12] : List Instr) = [movR .r7 .r4] ++ [movR .r3 .r12] from rfl,
      runBlock_app, e₈b, Option.bind_some, e₈], ?_⟩)
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  obtain g₈ : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), r4₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  obtain g₉' : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r3 → r ≠ .r12 → r ≠ t0 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₉ r h1 h2 h3 h5, g₈ r h1 h2 h3 h4 h5]
  obtain r12₉ : s₉.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  obtain base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  obtain r4₉ : s₉.gpr .r4 = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r4₅]
  obtain r5₉ : s₉.gpr .r5 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r5₅]
  obtain r11₉ : s₉.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide), r11₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₉ : ScrOk s₀ b E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the sixteen-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₃ j = Spec.Sm4.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add, addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega_arith, this, mem₂, addr_add,
      hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      obtain hj : (i - 256 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 256 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₅, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega_arith), ite_eq_left (show i < 16 * (16 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .r5 .r5 .r12
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .r4 .r4 (imm := 256) (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .r5 .r5 .r12, .addi .r4 .r4 256] : List Instr) =
      [.sub .r5 .r5 .r12] ++ [.addi .r4 .r4 256] from rfl, runBlock_app, e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  obtain hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  obtain r5₁₁ : s₁₁.gpr .r5 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, r5₉, r12₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  obtain rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  obtain wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 16
  · have hn : 16 * k + c = n := by omega_arith
    refine .inl ⟨by rw [r5₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 16 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [r5₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), r4₉, addr_add, show 256 * k + 256 = 256 * (k + 1) by omega_arith]
    · rw [r5₁₁, show v - c = n - 16 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), r11₉]
    · rw [hm, show 16 * (k + 1) = 16 * k + c by omega_arith]; exact hdata

end VG.Proof.Sm4.PPC64LE

end

end

/-!
# SM4 ECB on PPC64LE: the whole function

`ecb_wp`: with the working space as an argument (`ecbPPC64LE`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE

/-- The specification's direction. -/
def specDirPPC64LE : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on PPC64LE with its working space at `r6`. -/
def ecbPPC64LE (dir : Dir) : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let data : Region := ⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, 8 * slots⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 16 * (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)) (specDirPPC64LE dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirPPC64LE ecbPPC64LE crypt_eq quads ofBlock outBlock)

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.PPC64LE.group (.nonzero .d .r5)) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_nonzero s' .r5).trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_nonzero s' .r5).trans (by rw [beq_false_of_ne z]; rfl), n - 16 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) (hi : i < 18) : sreg i ≠ sb := by
  revert i; decide

theorem prologue_ok {sr : Reg} {s₀ : State} {b : Addr} (hb : s₀.gpr sr = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb sr] : List Instr) ++ saveRegs ++ setSlots keyMasks) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb sr
  have hb₁ : s₁.gpr sb = b := by rw [r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁]; exact hw) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega_using [this])
    (by decide)
  refine ⟨s₃, by
    rw [runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ (by decide), g₂, hb₁],
    fun r h1 h2 => by rw [g₃ r h2, g₂, o₁ r h1], fun i hi => ?_, fun kv hkv => v₃ kv hkv, ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [← o₁ _ (sreg_ne i hi), ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  · rw [← m₁]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_using [])

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j = blockFn sch (specDirPPC64LE dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirPPC64LE, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirPPC64LE, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-- `ecbWith sr k`, from the arguments' regions with the working space at
`sr`, for code `k` that builds the table of `dir` from the prologue's state. -/
theorem ecbWith_wp (sr : Reg) (k : Prog isa) (dir : Dir) {s₀ : State}
    (hrd : s₀.rd = [⟨s₀.gpr .r3, 128⟩]) (hwr : s₀.wr = [⟨s₀.gpr .r4, 16 * (s₀.gpr .r5).toNat⟩, ⟨s₀.gpr sr, 8 * slots⟩])
    (dSS : Region.Disjoint ⟨s₀.gpr .r3, 128⟩ ⟨s₀.gpr sr, 8 * slots⟩)
    (dDS : Region.Disjoint ⟨s₀.gpr .r4, 16 * (s₀.gpr .r5).toNat⟩ ⟨s₀.gpr sr, 8 * slots⟩)
    (fitK : (s₀.gpr .r3).toNat + 128 ≤ 2 ^ 64) (fitD : (s₀.gpr .r4).toNat + 16 * (s₀.gpr .r5).toNat ≤ 2 ^ 64)
    (fitB : (s₀.gpr sr).toNat + 8 * slots ≤ 2 ^ 64)
    (hk : ∀ s₁, SchedPre s₁ (s₀.gpr sr) (s₀.gpr .r3) → s₁.gpr .r3 = s₀.gpr .r3 → MasksOk s₁ →
      (∀ r, r ≠ sb → r ≠ t0 → s₁.gpr r = s₀.gpr r) →
      WP isa k s₁ (KeysPost s₁ (s₀.gpr sr) (s₀.gpr .r3) dir)) :
    WP isa (ecbWith sr k) s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Sm4.blocksAt s'.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat =
        Spec.Sm4.ecb (Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .r3)) (specDirPPC64LE dir)
          (Spec.Sm4.blocksAt s₀.mem (s₀.gpr .r4) (s₀.gpr .r5).toNat) := by
  let b := s₀.gpr sr
  let D := s₀.gpr .r4
  let n := (s₀.gpr .r5).toNat
  let sched := s₀.gpr .r3
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecbWith
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have r3₁ : s₁.gpr .r3 = sched := g₁ _ (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (hk s₁ hk₁ r3₁ m₁ g₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched)
  have hsch : Spec.Sm4.scheduleAt s₁.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hk₁.sched_eq' (Nat.le_refl _) f₁
  have hfitB := fitB
  rw [slots_eq] at hfitB
  have f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega_using [])⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega_using [])
        (by rw [savedSlot_eq]; omega_using [hi])
  have data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  have fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have r5₂ : s₂.gpr .r5 = s₀.gpr .r5 := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
  have r4₂ : s₂.gpr .r4 = D := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  have hz₃ : (s₂.gpr .r5 == 0) = decide (n = 0) := by
    rw [r5₂, show s₀.gpr .r5 = BitVec.ofNat 64 n by simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])] at this
    · intro h; rw [h]; rfl
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_zero s₂ .r5).trans (by rw [hz₃])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₂, sc₂, fun i hi => by omega, fr₂, rd₂, wr₂⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD⟩ ⟨base₂, by rw [r4₂]; simp,
      by rw [r5₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega_using [hn0], k₂.rdi, sc₂, fun i hi => ?_, fr₂, rd₂, wr₂⟩
    rw [data₂ i hi, ite_eq_right (by omega_using [])]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, -, m₅, -, -⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, rg₅, ?_⟩
  have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
    rw [m₅]; exact d₄.data i hi
  show Spec.Sm4.blocksAt s₅.mem D n = _
  rw [blocksAt_of_dinv hd₅, ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  exact outF_spec dir s₀.mem _ D j

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbPPC64LE dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (ecbPPC64LE dir).post s₀ s' := by
  obtain ⟨hrd, hwr, -, dSS, dDS, fitK, fitD, fitB⟩ := hp
  exact ecbWith_wp .r6 (keys dir) dir hrd hwr dSS dDS fitK fitD fitB
    fun _ hk₁ r3₁ m₁ _ => keys_wp dir hk₁ r3₁ m₁

/-- The direction `vg_sm4_prepare_keys`'s `decrypt` selects. -/
def dirOf (decrypt : BitVec 64) : Dir := if decrypt = 0 then .encrypt else .decrypt

theorem specDirA_dirOf (decrypt : BitVec 64) :
    specDirPPC64LE (dirOf decrypt) = Proof.Sm4.directionOf decrypt.toNat := by
  unfold dirOf Proof.Sm4.directionOf
  by_cases h : decrypt = 0
  · subst h; rfl
  · have h' : decrypt.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [h, h', ite_false]; rfl

end VG.Proof.Sm4.PPC64LE
