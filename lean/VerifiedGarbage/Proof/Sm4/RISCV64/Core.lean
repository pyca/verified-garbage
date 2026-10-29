module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Round
public import VerifiedGarbage.Impl.Sm4.RISCV64.Ecb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

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
  rw [hk, addr_add, show 8 * tableSlot + 64 * m + 8 * (8 * e + j) = 8 * tableSlot + 64 * (m + e) + 8 * j by omega]

theorem ok_layer {s : State} {b : Addr} {m : Nat} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0) (hk : AtEntry s b m) (hm : m + 4 ≤ 32) :
    Ok layerCfg s where
  slotIn k hk' := ⟨_, hscr, by
    simp only [layerCfg, tableSlot_eq] at hk'
    simp only [wordAddr, layerCfg, hb]
    rw [slots_eq]
    exact VG.Offset.contains_base b (by omega) (by omega)⟩
  extIn j hj := ⟨_, List.mem_append_right _ hscr, by
    simp only [layerCfg] at hj
    simp only [wordAddr, layerCfg]
    rw [show s.gpr kr = _ from hk, addr_add]
    rw [slots_eq]
    rw [tableSlot_eq]
    exact VG.Offset.contains_base b (by omega) (by omega)⟩
  baseAl _ := by simp only [layerCfg, hb]; exact hal
  extAl _ := by
    simp only [layerCfg]; rw [show s.gpr kr = _ from hk]
    exact Spill.al8 hal (by omega)
  slots := by simp only [layerCfg, tableSlot_eq]; omega
  sep k hk' j hj := by
    simp only [layerCfg, tableSlot_eq] at hk' hj
    simp only [wordAddr, layerCfg, hb]
    rw [show s.gpr kr = _ from hk, addr_add, tableSlot_eq]
    exact VG.Offset.sep b (by omega) (by omega) (by omega)

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
  exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq]; omega) (by rw [tableSlot_eq]; omega)

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
    round_ok l ha hb hc' hd hpre hlin hall (hc.ok hp hk hm) hc.masks hX (hc.keyRel hp hk (e := a) (by omega))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ => o' r hr) (f'.mono fun r hr => ?_) hm', o' _ (by decide), hX'⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg, hc.base]; simp

/-- Four rounds, the round keys at entries `4 m … 4 m + 3`. -/
theorem rounds4_ok (l : Lin) {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) (4 * m)) (hm : m < 8) {X : Nat → Nat → Spec.Sm4.Word}
    (hX : StRel s X) :
    ∃ s', runBlock isa (rounds4 l) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧
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
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega]
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
      entry_beq _ (by rw [tableSlot_eq]; omega) (by rw [tableSlot_eq]; omega)]
    simp only [decide_eq_decide]; omega

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
    have hi : imm12 ((8 * k - 2040 : Nat) : Int) := by unfold imm12; omega
    refine ⟨s₁.write r (s₁.gpr r + BitVec.ofInt 64 ((8 * k - 2040 : Nat) : Int)), by
      simp only [runBlock_cons, exec_addi (show imm12 2040 by decide), exec_addi hi, runStep_some,
        runBlock_nil, s₁], ?_, fun r' hr' => ?_, rfl, rfl, rfl⟩
    · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self, BitVec.ofInt_natCast,
        show BitVec.ofInt 64 2040 = BitVec.ofNat 64 2040 from rfl, addr_add,
        show 2040 + (8 * k - 2040) = 8 * k by omega]
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
    ⟨0, rfl, by omega, hc₁, by rw [AtEntry, k₁]; simp, hX.congr fun k => by simp only [slotW, m₁, o₁ sb (by decide)]⟩
  obtain ⟨m, rfl, hm8, hc', hk', hX'⟩ := hs'
  obtain ⟨s'', e'', c'', k'', X'', z''⟩ := roundsBody_ok l hp hc' hr11 hk' hm8 hX'
  have X3 : StRel s'' fun b => quads l E (m + 1) (X b) := X''
  refine WP.of_runBlock ⟨s'', e'', ?_⟩
  by_cases h8 : m + 1 = 8
  · refine .inl ⟨by rw [eval_nonzero, z'', h8]; rfl, c'', ?_⟩
    rw [h8] at X3; exact X3
  · exact .inr ⟨by rw [eval_nonzero, z'']; simp [h8], 8 - (m + 1), by omega, m + 1, rfl, by omega, c'', k'', X3⟩

end VG.Proof.Sm4.RISCV64
