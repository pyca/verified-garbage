module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Round
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
public import VerifiedGarbage.Impl.Sm4.RISCV64.Ecb
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Sm4.RISCV64.Core`, which this module and modules that import it used -/

section

/-!
# Sixteen blocks of bitsliced SM4 on RISCV64

`crypt16_ok`: with the table of bitsliced round keys `E 0 … E 31` in the
scratch buffer (`KeyCtx`), `crypt16` replaces each of the sixteen blocks of
the tail buffer with the output of the 32 rounds with those keys, writing
only the slots below the table (`Ctx`). The rounds are `round_ok`, four at
a time (`rounds4_ok`), in a loop whose invariant is `quads`
(`Proof/Sm4/Rounds.lean`); `rounds_wp` is that loop for either linear
transformation, which the key schedule runs too.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR)
open VG.Proof.Sm4 (WordRel sround quad quads ofBlock outBlock)
open VG.Impl.Sm4 (Lin)
open VG.Proof.Aes.RISCV64 (sboxWrites restRegs)

/-- Word `j` of entry `e` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : Addr) (e j : Nat) : BitVec 64 :=
  m.readW (b + BitVec.ofNat 64 (8 * tableSlot + 64 * e + 8 * j)) 64

/-- What the rounds need: the scratch buffer, writable, and a table of 32
round keys. -/
structure KeyCtx (s₀ : State) (E : Nat → Spec.Sm4.Word) : Prop where
  scr : (⟨s₀.gpr sb, 8 * slots⟩ : Region) ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 8 * slots ≤ 2 ^ 64
  al : (s₀.gpr sb).toNat % 8 = 0
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

theorem slots_eq : slots = 396 := rfl
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
    (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0) (hk : AtEntry s b m) (hm : m + 4 ≤ 32) :
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
  baseAl _ := by simp only [layerCfg, hb]; exact hal
  extAl _ := by
    simp only [layerCfg]; rw [show s.gpr kr = _ from hk]
    exact Spill.al8 hal (by omega_using [])
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
  ok_layer (by rw [hc.wr]; exact hp.scr) hc.base hp.al hk hm

/-- A round, under `Ctx`: `round l a …` with the round key at entry `m + a`. -/
theorem round_step (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {a b c d m : Nat} (ha : a < 4) (hb : b = (a + 1) % 4) (hc' : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 64 12) layerCfg (linExt 32) (preX a b c d) preEnv
      (linPostG 12 (qOuts (preG a b c d)) [] (keyMaskSlots ++ stateSlots) preEnv) = true)
    (hlin : check (lanes 64 12) linCfg (linExt 40) (lin l a) linEnv
      (linPostG 12 [] (linOuts l a) (linKeep a) linEnv) = true)
    (hall : (restRegs.all fun r =>
      (preX a b c d ++ lin l a).all fun i => dst i != some r) = true)
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
theorem addKp_ok (s : State) (n : Int) (hn : imm12 n) :
    ∃ s', runBlock isa [.addi kr kr n] s = some s' ∧
      s'.gpr kr = s.gpr kr + BitVec.ofInt 64 n ∧ (∀ r, r ≠ kr → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [runBlock_cons, exec_addi hn, runStep_some, runBlock_nil], RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `sub d, n, m`, keeping all else. -/
theorem subR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.sub d n m] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, rfl, RegUpd.gpr_write_self _ _ _, fun _ hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem entry_beq (b : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x - (b + BitVec.ofNat 64 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, VG.Offset.ofNat_sub_ofNat_beq hx hy]

/-- `bnez`: whether `r` is not zero. -/
theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero r) s = some !(s.gpr r == 0) := rfl

/-- `beqz`: whether `r` is zero. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

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

/-- Four rounds, `addi kr, kr, 256` and `sub t0, kr, a0`. -/
theorem roundsBody_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    (hr11 : s₀.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd))
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (roundsBody l) s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (4 * (m + 1)) ∧
      StRel s' (fun b => quad l E m (X b)) ∧ (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok l hp hc hk hm hX
  obtain ⟨s₂, e₂, kr₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := subR_ok s₂ t0 kr .a0
  have hc₂ : Ctx s₀ s₂ := c₁.kr o₂ m₂ rd₂ wr₂
  have hk₂ : AtEntry s₂ (s₀.gpr sb) (4 * (m + 1)) := by
    rw [AtEntry, kr₂, k₁, show s.gpr kr = _ from hk, show BitVec.ofInt 64 256 = BitVec.ofNat 64 256 from rfl,
      addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_using []]
  have hk₃ : AtEntry s₃ (s₀.gpr sb) (4 * (m + 1)) := by rw [AtEntry, g₃ _ (by decide)]; exact hk₂
  have hr11₂ : s₂.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [hc₂.keep _ (by decide) (by decide), hr11]
  refine ⟨s₃, ?_, hc₂.t0 g₃ m₃ rd₃ wr₃, hk₃, ?_, ?_⟩
  · rw [roundsBody, runBlock_app, e₁, Option.bind_some,
      show ([.addi kr kr 256, .sub t0 kr .a0] : List Instr) =
        [.addi kr kr 256] ++ [.sub t0 kr .a0] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃]
  · exact X₁.congr fun k => by simp only [slotW, m₃, g₃ sb (by decide), m₂, o₂ sb (by decide)]
  · rw [z₃, show s₂.gpr kr = _ from hk₂, hr11₂,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_using [hm]) (by rw [tableSlot_eq]; omega_using [])]
    simp only [decide_eq_decide]; omega_using []

/-- `r := ` the address of slot `k`, in one `addi` or two. -/
theorem slotAddr_ok (s : State) (r : Reg) (k : Nat) (hk : 8 * k < 4088 := by decide) :
    ∃ s', runBlock isa (slotAddr r k) s = some s' ∧
      s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * k) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold slotAddr
  split
  · rename_i h
    exact ⟨_, by simp only [runBlock_cons, exec_addi_nat h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r' hr' => RegUpd.gpr_write_of_ne _ _ hr', rfl, rfl, rfl⟩
  · rename_i h
    let s₁ := s.write r (s.gpr sb + BitVec.ofInt 64 2040)
    have hi : imm12 ((8 * k - 2040 : Nat) : Int) := by unfold imm12; omega_using [hk]
    refine ⟨s₁.write r (s₁.gpr r + BitVec.ofInt 64 ((8 * k - 2040 : Nat) : Int)), by
      simp only [runBlock_cons, exec_addi (show imm12 2040 by decide), exec_addi hi, runStep_some,
        runBlock_nil, s₁], ?_, fun r' hr' => ?_, rfl, rfl, rfl⟩
    · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self, BitVec.ofInt_natCast,
        show BitVec.ofInt 64 2040 = BitVec.ofNat 64 2040 from rfl, addr_add,
        show 2040 + (8 * k - 2040) = 8 * k by omega_using [h]]
    · rw [RegUpd.gpr_write_of_ne _ _ hr', RegUpd.gpr_write_of_ne _ _ hr']

/-- The 32 rounds, the round keys at entries `0 … 31`, `a0` the table's end. -/
theorem rounds_wp (l : Lin) {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (hr11 : s₀.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s₀ X) :
    WP isa (rounds l) s₀ fun s' => Ctx s₀ s' ∧ StRel s' (fun b => quads l E 8 (X b)) := by
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s₀ kr tableSlot
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

end VG.Proof.Sm4.RISCV64

end

end

/-!
# SM4's prologue and epilogue on RISCV64

Saving and restoring the callee-saved registers `s0`–`s11` in their slots
(`save_ok`, `restore_ok`), and storing constants to slots (`setSlots_ok`,
through `li64`): the masks of the round keys' planes and of the transposes.
As on PPC64LE (`Proof/Sm4/PPC64LE/Ecb.lean`), with the scratch buffer
aligned to 8 bytes, as `ld` and `sd` need.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Words.RISCV64 (li64)

theorem savedSlot_eq : savedSlot = 384 := rfl
theorem sb_ne_t0 : sb ≠ t0 := by decide
theorem sb_ne_t1 : sb ≠ t1 := by decide

/-! ## Loads and stores of slots -/

/-- `ld r, 8 k(sb)`. -/
theorem ldMask_ok {s : State} {r : Reg} {k : Nat} {M : BitVec 64} (hk : 8 * k < 2048)
    (hal : (s.gpr sb).toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8)
    (hv : s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64 = M) :
    ∃ s', runBlock isa [ldS r k] s = some s' ∧ s'.gpr r = M ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [ldS, runBlock_cons, exec_load_d hk (Spill.al8 hal (by omega_using [])) hin, runStep_some,
    runBlock_nil], (RegUpd.gpr_write_self _ _ _).trans hv, fun _ h => RegUpd.gpr_write_of_ne _ _ h,
    rfl, rfl, rfl⟩

/-- `sd t, 8 k(sb)`. -/
theorem stS_ok (s : State) {k : Nat} (t : Reg) (hk : 8 * k < 2048) (hal : (s.gpr sb).toNat % 8 = 0)
    (hin : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8) :
    runBlock isa [stS k t] s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr t) } := by
  simp only [stS, runBlock_cons, runStep_some, runBlock_nil, exec_store_d hk (Spill.al8 hal (by omega_using [])) hin]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedOffs`. -/
def sreg (i : Nat) : Reg := ((savedOffs.map (·.1))[i]?).getD .s0

theorem savedOffs_eq : savedOffs = (List.range 12).map fun i => (sreg i, 8 * i) := by decide

theorem saveRegs_eq : saveRegs = slotAddr t0 savedSlot ++ Spill.saveCode t0 savedOffs := rfl

theorem restoreRegs_eq : restoreRegs = slotAddr t0 savedSlot ++ Spill.restoreCode t0 savedOffs := rfl

theorem savedOffs_ho : ∀ p ∈ savedOffs, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 12, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem sreg_ne_sb : ∀ i < 12, sreg i ≠ sb := by decide
theorem sreg_ne_t0 : ∀ i < 12, sreg i ≠ t0 := by decide

theorem saved_addr (b : Addr) (i : Nat) :
    wordAddr b (savedSlot + i) = b + BitVec.ofNat 64 (8 * savedSlot) + BitVec.ofNat 64 (8 * i) := by
  rw [wordAddr, addr_add, show 8 * savedSlot + 8 * i = 8 * (savedSlot + i) by omega_using []]

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      (∀ k, k < savedSlot → slotW s' k = slotW s k) ∧
      Frame [⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s t0 savedSlot
  rw [hb] at r₁
  have hal₁ : (s₁.gpr t0).toNat % 8 = 0 := by rw [r₁]; exact Spill.al8 hal (by decide)
  obtain ⟨s', e', st⟩ := Interleave.runBlock_of_WP (Spill.save_wp (b := t0) (l := savedOffs) hal₁
    savedOffs_ho fun p hp => by
      rw [wr₁, r₁, addr_add]
      have := savedOffs_ho p hp
      have h2 : p.2 + 8 ≤ 96 := by revert p; decide
      exact ⟨_, hw, VG.Offset.contains_base b (by rw [slots_eq, savedSlot_eq]; omega_using [h2])
        (by rw [savedSlot_eq]; omega_using [this])⟩)
  have g' : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r := fun r hr => by rw [st.gpr, o₁ r hr]
  have hfr : Frame [⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩] s.mem s'.mem := by
    rw [st.mem, ← r₁, m₁]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  refine ⟨s', by rw [saveRegs_eq, Interleave.runBlock_append, e₁, Option.bind_some]; exact e',
    fun i hi => ?_, g', by rw [st.rd, rd₁], by rw [st.wr, wr₁], hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩,
    fun k hk => ?_, hfr⟩
  · have := Spill.saveMem_saved (l := savedOffs) (by decide) s₁.mem (s₁.gpr t0) s₁.gpr (sreg i, 8 * i)
      (by rw [savedOffs_eq]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [← st.mem, r₁] at this
    rw [saved_addr, this, o₁ _ (sreg_ne_t0 i hi)]
  · simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.sub_base b (by rw [slots_eq, savedSlot_eq])
  · rw [savedSlot_eq] at hk
    rw [slotW, slotW, g' _ sb_ne_t0, hb]
    refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint b (Or.inl (by rw [savedSlot_eq]; omega_using [hk])) (by omega_using [hk]) (by rw [savedSlot_eq]; omega_using [])

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 12, r ≠ sreg i) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s t0 savedSlot
  rw [hb] at r₁
  obtain ⟨s', e', rs⟩ := Interleave.runBlock_of_WP (Spill.restore_wp (b := t0) (l := savedOffs)
    (g := s₀.gpr) (Spill.al8 hal (by decide)) r₁ savedOffs_ho (by decide)
    (fun p hp => by
      rw [rd₁, wr₁, addr_add]
      have := savedOffs_ho p hp
      have h2 : p.2 + 8 ≤ 96 := by revert p; decide
      exact ⟨_, List.mem_append_right _ hw, VG.Offset.contains_base b (by rw [slots_eq, savedSlot_eq]; omega_using [h2])
        (by rw [savedSlot_eq]; omega_using [this])⟩)
    (fun p hp => by
      rw [savedOffs_eq] at hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have hi := List.mem_range.mp hi
      rw [m₁, ← saved_addr]; exact hs i hi))
  refine ⟨s', by rw [restoreRegs_eq, Interleave.runBlock_append, e₁, Option.bind_some]; exact e',
    fun i hi => rs.gpr (sreg i, 8 * i) (by rw [savedOffs_eq]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
    fun r hr h0 => ?_, by rw [rs.mem, m₁], by rw [rs.rd, rd₁], by rw [rs.wr, wr₁]⟩
  rw [rs.other r ?_, o₁ r h0]
  rw [savedOffs_eq, List.map_map]
  simp only [List.mem_map, List.mem_range, Function.comp_def, not_exists, not_and]
  exact fun i hi h => hr i hi h.symm

/-! ## Constants -/

/-- `li64 t0, v` (through `t1`); `sd t0, 8 k(sb)`. -/
theorem setOne_ok {s : State} {b : Addr} {k : Nat} (v : BitVec 64) (hb : s.gpr sb = b) (hk : 8 * k < 2048)
    (hal : b.toNat % 8 = 0) (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa (li64 t0 t1 v ++ [stS k t0]) s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) v ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := Interleave.runBlock_of_WP (ByteLoad.li64_ok (s := s) (d := t0) (tmp := t1) (by decide) v)
  subst h₁
  let s₁ := (s.write t1 (sext32 (v.setWidth 32))).write t0 v
  have hb₁ : s₁.gpr sb = b := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), hb]
  refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) }, ?_, ?_,
    fun r h0 h1 => ?_, rfl, rfl⟩
  · rw [Interleave.runBlock_append, e₁, Option.bind_some]
    exact stS_ok _ t0 hk (by rw [hb₁]; exact hal) (by rw [hb₁]; exact hw)
  · show s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) = _
    rw [hb₁, RegUpd.gpr_write_self]; rfl
  · show s₁.gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]

theorem setSlots_ok (ms : List (Nat × BitVec 64)) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hal : b.toNat % 8 = 0) (hk : ∀ kv ∈ ms, kv.1 < tableSlot)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setSlots ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * tableSlot⟩] s.mem s'.mem := by
  induction ms generalizing s with
  | nil => exact ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | cons kv ms ih =>
    have hk0 : kv.1 < tableSlot := hk kv List.mem_cons_self
    rw [tableSlot_eq] at hk0
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := setOne_ok (k := kv.1) kv.2 hb (by omega_using [hk0]) hal ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [slots_eq]; omega_using [hk0]) (by omega_using [hk0])⟩
    have hb₁ : s₁.gpr sb = b := by rw [g₁ _ sb_ne_t0 sb_ne_t1, hb]
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := ih (s := s₁) hb₁ (by rw [wr₁]; exact hw)
      (fun kv h => hk kv (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2
    have hnot : kv.1 ∉ ms.map (·.1) := (List.nodup_cons.mp hnd).1
    have hslot : ∀ k < slots, slotW s₁ k = if k = kv.1 then kv.2 else slotW s k := fun k hk' => by
      simp only [slotW, hb₁, hb, m₁]
      split
      · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
      · rename_i h
        rw [slots_eq] at hk'
        exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hk']) (by omega_using [hk0]) h) (by decide)
    refine ⟨s', by
      rw [show setSlots (kv :: ms) = (li64 t0 t1 kv.2 ++ [stS kv.1 t0]) ++ setSlots ms from rfl,
        Interleave.runBlock_append, e₁, Option.bind_some, e'], fun x hx => ?_, fun k hk' hn => ?_,
      fun r h0 h1 => by rw [g' r h0 h1, g₁ r h0 h1], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [k' _ (by rw [slots_eq]; omega_using [hk0]) hnot, hslot _ (by rw [slots_eq]; omega_using [hk0]), ite_eq_left rfl]
      · exact v' x hx
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' k hk' hn.2, hslot k hk', ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      rw [m₁]
      simp only [Mem.writeW, Mem.write, wordAddr]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * kv.1 + 8 ≤ 8 * tableSlot by rw [tableSlot_eq]; omega_using [hk0]) _ (by simp only [Region.Contains]; omega_using [h]))

end VG.Proof.Sm4.RISCV64
