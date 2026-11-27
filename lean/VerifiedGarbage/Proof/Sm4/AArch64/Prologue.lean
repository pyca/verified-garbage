module

public import VerifiedGarbage.Proof.Sm4.AArch64.Round
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Sm4.AArch64.Core`, which this module and modules that import it used -/

section

/-!
# Sixteen blocks of bitsliced SM4 on AArch64

`crypt16_ok`: with the table of bitsliced round keys `E 0 … E 31` in the
scratch buffer (`KeyCtx`), `crypt16` replaces each of the sixteen blocks of
the tail buffer with the output of the 32 rounds with those keys, writing
only the slots below the table (`Ctx`). The rounds are `round_ok`, four at
a time (`rounds4_ok`), in a loop whose invariant is `quads`
(`Proof/Sm4/Rounds.lean`); `rounds_wp` is that loop for either linear
transformation, which the key schedule runs too.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR)
open VG.Proof.Camellia.AArch64 (linEnvG linPostG linG_ok)
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
`kp`, the memory outside the slots below the table, and the masks. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * tableSlot⟩] s₀.mem s.mem
  masks : MasksOk s

theorem Ctx.refl {s₀ : State} (hm : MasksOk s₀) : Ctx s₀ s₀ :=
  ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _, hm⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s₀.gpr sb, 8 * tableSlot⟩] s.mem s'.mem) (hm : MasksOk s') : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans hf, hm⟩

/-! ## Addresses -/

theorem slots_eq : slots = 396 := rfl
theorem tableSlot_eq : tableSlot = 128 := rfl
theorem tableEnd_eq : tableEnd = 384 := rfl
theorem tailSlot_eq : tailSlot = 96 := rfl

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : Addr) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 64 (8 * tableSlot + 64 * m)

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
    rw [show s.gpr kp = _ from hk, addr_add]
    rw [slots_eq]
    rw [tableSlot_eq]
    exact VG.Offset.contains_base b (by omega_using [hm, hj]) (by omega_using [hm, hj])⟩
  slots := by simp only [layerCfg, tableSlot_eq]; omega_using []
  sep k hk' j hj := by
    simp only [layerCfg, tableSlot_eq] at hk' hj
    simp only [wordAddr, layerCfg, hb]
    rw [show s.gpr kp = _ from hk, addr_add, tableSlot_eq]
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
    (hall : (layerKeep.all fun r =>
      (preX a b c d ++ lin l a).all fun i => !clobbers i r) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 4 ≤ 32) {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
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
    ∃ s', runBlock isa (rounds4 l) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
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

theorem read_x' (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

/-- `add kp, kp, #n`, keeping all else. -/
theorem addKp_ok (s : State) (n : Nat) (hn : n < 4096) :
    ∃ s', runBlock isa [.addImm .x kp kp n] s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 n ∧ (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x kp (s.gpr kp + BitVec.ofNat 64 n), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x hn, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

/-- `sub d, n, m`, keeping all else. -/
theorem subR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.sub .x d n m] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n - s.gpr m), by
    simp only [runBlock_cons]; rfl,
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem entry_beq (b : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x - (b + BitVec.ofNat 64 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, VG.Offset.ofNat_sub_ofNat_beq hx hy]

/-- `cbnz r`: whether `r` is not zero. -/
theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some !(s.gpr r == 0) := by
  show VG.AArch64.eval (.nonzero .x r) s = _
  simp only [VG.AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, bne]

/-- `cbz r`: whether `r` is zero. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  show VG.AArch64.eval (.zero .x r) s = _
  simp only [VG.AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- A step that changes only `kp` and the layers' registers keeps `Ctx`. -/
theorem Ctx.kp {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ kp → s'.gpr r = s.gpr r)
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

/-- Four rounds, `add kp, kp, #256` and `sub t0, kp, x3`. -/
theorem roundsBody_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    (hx3 : s₀.gpr .x3 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd))
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (roundsBody l) s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (4 * (m + 1)) ∧
      StRel s' (fun b => quad l E m (X b)) ∧ (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok l hp hc hk hm hX
  obtain ⟨s₂, e₂, kp₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := subR_ok s₂ t0 kp .x3
  have hc₂ : Ctx s₀ s₂ := c₁.kp o₂ m₂ rd₂ wr₂
  have hk₂ : AtEntry s₂ (s₀.gpr sb) (4 * (m + 1)) := by
    rw [AtEntry, kp₂, k₁, show s.gpr kp = _ from hk, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_using []]
  have hk₃ : AtEntry s₃ (s₀.gpr sb) (4 * (m + 1)) := by rw [AtEntry, g₃ _ (by decide)]; exact hk₂
  have hx3₂ : s₂.gpr .x3 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [hc₂.keep _ (by decide) (by decide), hx3]
  refine ⟨s₃, ?_, hc₂.t0 g₃ m₃ rd₃ wr₃, hk₃, ?_, ?_⟩
  · rw [roundsBody, runBlock_app, e₁, Option.bind_some,
      show ([.addImm .x kp kp 256, .sub .x t0 kp .x3] : List Instr) =
        [.addImm .x kp kp 256] ++ [.sub .x t0 kp .x3] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃]
  · exact X₁.congr fun k => by simp only [slotW, m₃, g₃ sb (by decide), m₂, o₂ sb (by decide)]
  · rw [z₃, show s₂.gpr kp = _ from hk₂, hx3₂,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_using [hm]) (by rw [tableSlot_eq]; omega_using [])]
    simp only [decide_eq_decide]; omega_using []

/-- `mov r, sb; add r, r, #8 k`. -/
theorem slotAddr_ok (s : State) (r : Reg) (k : Nat) (hk : 8 * k < 4096) :
    ∃ s', runBlock isa (slotAddr r k) s = some s' ∧
      s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * k) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(s.write .x r (s.gpr sb + BitVec.ofNat 64 0)).write .x r
      ((s.gpr sb + BitVec.ofNat 64 0) + BitVec.ofNat 64 (8 * k)), ?_, ?_, fun r' hr' => ?_, rfl, rfl, rfl⟩
  · simp only [slotAddr, movR, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      exec_addImm_x hk, read_x']
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · simp only [RegUpd.gpr_write_of_ne _ _ _ hr']

/-- The 32 rounds, the round keys at entries `0 … 31`, `x3` the table's end. -/
theorem rounds_wp (l : Lin) {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (hx3 : s₀.gpr .x3 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s₀ X) :
    WP isa (rounds l) s₀ fun s' => Ctx s₀ s' ∧ StRel s' (fun b => quads l E 8 (X b)) := by
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s₀ kp tableSlot (by decide)
  have hc₁ : Ctx s₀ s₁ := (Ctx.refl hm).kp o₁ m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  let Inv : Nat → State → Prop := fun n s' => ∃ m, n = 8 - m ∧ m < 8 ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (4 * m) ∧ StRel s' (fun b => quads l E m (X b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) 8 s₁
    ⟨0, rfl, by omega_using [], hc₁, by rw [AtEntry, k₁]; simp, hX.congr fun k => by simp only [slotW, m₁, o₁ sb (by decide)]⟩
  obtain ⟨m, rfl, hm8, hc', hk', hX'⟩ := hs'
  obtain ⟨s'', e'', c'', k'', X'', z''⟩ := roundsBody_ok l hp hc' hx3 hk' hm8 hX'
  have X3 : StRel s'' fun b => quads l E (m + 1) (X b) := X''
  refine WP.of_runBlock ⟨s'', e'', ?_⟩
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_nonzero, z'', h8]; rfl, c'', ?_⟩
    rw [h8] at X3; exact X3
  · exact .inr ⟨by rw [eval_nonzero, z'']; simp [h8], 8 - (m + 1), by omega_using [hm8], m + 1, rfl, by omega_using [hm8, h8], c'', k'', X3⟩

end VG.Proof.Sm4.AArch64

end

end

/-!
# SM4's prologue and epilogue on AArch64

Saving and restoring the callee-saved registers `x19`–`x28` in their slots
(`save_ok`, `restore_ok`, by symbolic execution of the stores and loads,
as Camellia's), and storing constants to slots (`setSlotsN_ok`, through
`imm_ok`): the masks of the round keys' planes, and the key schedule's
table of `CK`.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR ldS stS imm)

theorem savedSlot_eq : savedSlot = 384 := rfl
theorem sb_ne_t0 : sb ≠ t0 := by decide

/-! ## Loads and stores of slots -/

/-- `ldr r, [sb, #8 k]`. -/
theorem ldMask_ok {s : State} {r : Reg} {k : Nat} {M : BitVec 64} (hk : 8 * k < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8)
    (hv : s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64 = M) :
    ∃ s', runBlock isa [ldS r k] s = some s' ∧ s'.gpr r = M ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x r (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64), by
    simp only [ldS, runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x ⟨by omega_using [], hk⟩ hin], ?_,
    fun r' h => RegUpd.gpr_write_of_ne _ _ _ h, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, hv]

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

/-- `str t, [sb, #8 k]`. -/
theorem stS_ok (s : State) {k : Nat} (t : Reg) (hk : 8 * k < 32768)
    (hin : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8) :
    runBlock isa [stS k t] s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr t) } := by
  simp only [stS, runBlock_cons, runStep_some, runBlock_nil, exec_str_x ⟨by omega_using [], hk⟩ hin]

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
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .x19

theorem savedRegs_eq : savedRegs = (List.range 10).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 10, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem sreg_ne_sb : ∀ i < 10, sreg i ≠ sb := by decide

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → slotW s' k = slotW s k := by
  let L : List (Nat × Reg) := (List.range 10).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs = L.map fun x => stS x.1 x.2 := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 10).map fun i => savedSlot + i := by
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
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 10, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := (List.range 10).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs = L.map fun x => ldS x.1 x.2 := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 10).map sreg := by simp only [L, List.map_map]; rfl
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

/-- `imm t0, v; str t0, [sb, #8 k]`. -/
theorem setOne_ok {s : State} {b : Addr} {k : Nat} (v : BitVec 64) (hb : s.gpr sb = b) (hk : 8 * k < 32768)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa (imm t0 v ++ [stS k t0]) s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) v ∧
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
      rw [show setSlots (kv :: ms) = (imm t0 kv.2 ++ [stS kv.1 t0]) ++ setSlots ms from rfl,
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

end VG.Proof.Sm4.AArch64
