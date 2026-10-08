import VerifiedGarbage.Proof.Camellia.X86_64.Round
import VerifiedGarbage.Proof.Camellia.X86_64.Moves
import VerifiedGarbage.Proof.Camellia.X86_64.Fl
import VerifiedGarbage.Proof.Camellia.Layout
import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.Block

/-!
# Eight blocks of bitsliced Camellia on x86-64

`crypt8_ok`: with the table of bitsliced subkeys `E 0 … E (8 g + 1)` in
the scratch buffer (`CorePre`), `crypt8` replaces each of the eight blocks
at `rdx` with `cryptWords g E` of it, writing only the rounds' working
space and the blocks (`Ctx`). The rounds are `round_ok`; the pairs of
rounds, the groups of six and the FL layers are loops and blocks around
them, whose invariants are the specification's `pair`, `group` and
`groups` (`Proof/Camellia/Words.lean`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)
open VG.Proof.Camellia (HalfRel WordRel pair group groups cryptWords)

/-- Word `j` of entry `i` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : Addr) (i j : Nat) : BitVec 64 :=
  m.readW (b + BitVec.ofNat 64 (8 * keySlot + 64 * i + 8 * j)) 64

/-- What `crypt8` needs: the scratch buffer and the eight blocks, writable
and apart, the masks, the table of `8 g + 2` subkeys, and the address of its
postwhitening entry. -/
structure CorePre (s₀ : State) (g : Nat) (E : Nat → BitVec 64) : Prop where
  scr : (⟨s₀.gpr sb, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨s₀.gpr .rdx, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨s₀.gpr .rdx, 128⟩ ⟨s₀.gpr sb, 8 * slots⟩
  fit : (s₀.gpr sb).toNat + 8 * slots ≤ 2 ^ 64
  fitD : (s₀.gpr .rdx).toNat + 128 ≤ 2 ^ 64
  hg : g = 3 ∨ g = 4
  masks : MasksOk s₀
  bound : slotW s₀ endSlot = s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g)
  keys : ∀ i < 8 * g + 2, HalfRel (entryW s₀.mem (s₀.gpr sb) i) fun _ => E i

/-- What stays the same: the regions, the registers but the state's, `kp`
and `rdi`, the memory outside the rounds' working space and the blocks,
and the masks. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * keySlot⟩, ⟨s₀.gpr .rdx, 128⟩] s₀.mem s.mem
  masks : MasksOk s

theorem Ctx.refl {s₀ : State} (hm : MasksOk s₀) : Ctx s₀ s₀ :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, Frame.refl _ _, hm⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide) (by decide)
theorem Ctx.rdx {s₀ s : State} (hc : Ctx s₀ s) : s.gpr .rdx = s₀.gpr .rdx := hc.keep _ (by decide) (by decide) (by decide)

/-- A step that writes only the state's registers, `kp`, `rdi`, the rounds'
working space and the blocks, and keeps the masks, keeps `Ctx`. -/
theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s₀.gpr sb, 8 * keySlot⟩, ⟨s₀.gpr .rdx, 128⟩] s.mem s'.mem) (hm : MasksOk s') :
    Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 h3 => (hk r h1 h2 h3).trans (hc.keep r h1 h2 h3),
    hc.frame.trans hf, hm⟩

/-! ## Addresses -/

theorem addr_add (b : Addr) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := VG.Offset.add_add b x y

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : Addr) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * m)

theorem keyW_entry {s : State} {b : Addr} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (8 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, wordAddr, entryW]
  rw [hk, addr_add, show 8 * keySlot + 64 * m + 8 * (8 * e + j) = 8 * keySlot + 64 * (m + e) + 8 * j by omega]

theorem slots_eq : slots = 392 := rfl
theorem keySlot_eq : keySlot = 96 := rfl
theorem endSlot_eq : endSlot = 368 := rfl

theorem ok_layer {s : State} {b : Addr} {m : Nat} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hk : AtEntry s b m) (hm : m + 2 ≤ 34) :
    Ok layerCfg s where
  slotIn k hk' := ⟨_, hscr, by
    simp only [layerCfg, keySlot_eq] at hk'
    simp only [wordAddr, layerCfg, hb]
    exact VG.Offset.contains_base b (by rw [slots_eq]; omega) (by omega)⟩
  extIn j hj := ⟨_, List.mem_append_right _ hscr, by
    simp only [layerCfg] at hj
    simp only [wordAddr, layerCfg]
    rw [show s.gpr kp = _ from hk, addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, keySlot_eq]; omega) (by rw [keySlot_eq]; omega)⟩
  slots := by simp only [layerCfg, keySlot_eq]; omega
  sep k hk' j hj := by
    simp only [layerCfg, keySlot_eq] at hk' hj
    simp only [wordAddr, layerCfg, hb]
    rw [show s.gpr kp = _ from hk, addr_add]
    exact VG.Offset.sep b (by rw [keySlot_eq]; omega) (by omega) (by rw [keySlot_eq]; omega)

/-! ## Under `Ctx` -/

/-- The table's entries are outside what `Ctx` lets the code write. -/
theorem Ctx.entry {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i j : Nat} (hi : i < 34) (hj : j < 8) :
    entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  simp only [entryW]
  refine hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 64 * i + 8 * j), 8⟩)
    (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)
  · refine (hp.sep.sub_right (VG.Offset.sub_base _ ?_)).symm
    rw [slots_eq, keySlot_eq]; omega

theorem Ctx.keyRel {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < 8 * g + 2) :
    HalfRel (fun j => keyW s (8 * e + j)) fun _ => E (m + e) := by
  have hg : 8 * g + 2 ≤ 34 := by rcases hp.hg with h | h <;> omega
  refine (hp.keys _ hme).congr fun j hj => ?_
  rw [keyW_entry hk, hc.entry hp (by omega) hj]

theorem Ctx.ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 2 ≤ 34) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hc.base hk hm

/-- A round, under `Ctx`: `round off d` with the subkey at entry `m + off / 8`. -/
theorem round_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {off d m : Nat}
    (hkc : check (lanes 64 12) layerCfg (linExt 8) (keyXor off ++ inSel) keyInEnv
      (linPostG 12 (qOuts (Camellia.keyInG off)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true)
    (hfc : check (lanes 64 12) layerCfg (linExt 24) (feistel d) bothEnv
      (linPostG 12 (qOuts (feistelG d)) ((List.range 8).map fun j => (d + j, feistelG d j))
        (feistelKeep d) bothEnv) = true)
    (hoff : off = 0 ∨ off = 8) (hd : d = d1Slot ∨ d = d2Slot)
    (hk : AtEntry s (s₀.gpr sb) m) (hme : m + off / 8 < 8 * g + 2) (hm34 : m + 2 ≤ 34)
    {X Y : Nat → BitVec 64} (hQ : HalfRel (Qs s) X) (hR : HalfRel (fun j => slotW s (d + j)) Y) :
    ∃ s', runBlock isa (round off d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧
      HalfRel (Qs s') (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 8))) ∧
      HalfRel (fun j => slotW s' (d + j)) (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 8))) ∧
      (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j)) := by
  have hK : HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 8) := by
    have := hc.keyRel hp hk (e := off / 8) hme
    rcases hoff with rfl | rfl <;> exact this
  obtain ⟨s', h', hq', hs', hm', hh', rd', wr', o', f'⟩ :=
    round_ok hkc hfc hoff hd (hc.ok hp hk hm34) hc.masks hQ hK hR
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => o' r hr) ?_ hm', o' _ (by decide),
    o' _ (by decide), hq', hs', hh'⟩
  refine f'.mono fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg, hc.base]; simp

/-! ## Pairs of rounds -/

/-- The halves of the eight blocks, `(D1, D2)` of block `b` in `S b`: `D1` in
the state and in its slots, `D2` in its slots. -/
def Halves (s : State) (S : Nat → BitVec 64 × BitVec 64) : Prop :=
  HalfRel (Qs s) (fun b => (S b).1) ∧ HalfRel (fun j => slotW s (d1Slot + j)) (fun b => (S b).1) ∧
    HalfRel (fun j => slotW s (d2Slot + j)) (fun b => (S b).2)

/-- `add kp, n`, keeping all else. -/
theorem addKp_ok (s : State) (n : Nat) (hse : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa [.alu .add kp (.imm (BitVec.ofNat 32 n))] s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 n ∧ (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self, hse]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `cmp kp, rdi`, keeping all else. -/
theorem cmpRdi_ok (s : State) :
    ∃ s', runBlock isa [.alu .cmp kp (.reg .rdi)] s = some s' ∧
      s'.zf = some (s.gpr kp - s.gpr .rdi == 0) ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- The two rounds of a pair, `add kp, 128` and `cmp kp, rdi`. -/
theorem pair_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < 8 * g + 2) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa pairBody s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ Halves s' (fun b => pair (E m) (E (m + 1)) (S b)) ∧
      s'.zf = some (s'.gpr kp - s.gpr .rdi == 0) := by
  obtain ⟨hq, h1, h2⟩ := hS
  obtain ⟨s₁, e₁, c₁, k₁, r₁, q₁, d₁, o₁⟩ := round_step hp hc (off := 0) (d := d2Slot) keyIn0_check
    feistel2_check (by decide) (by decide) hk (by omega) hm34 hq h2
  have h1' : HalfRel (fun j => slotW s₁ (d1Slot + j)) (fun b => (S b).1) :=
    h1.congr fun j hj => o₁ j (by omega) (Or.inl (by simp [d1Slot, d2Slot]; omega))
  obtain ⟨s₂, e₂, c₂, k₂, r₂, q₂, d₂, o₂⟩ := round_step hp c₁ (off := 8) (d := d1Slot) keyIn8_check
    feistel1_check (by decide) (by decide) (by rw [AtEntry, k₁]; exact hk) (by omega) hm34 q₁ h1'
  have d₂' : HalfRel (fun j => slotW s₂ (d2Slot + j))
      (fun b => (S b).2 ^^^ Spec.Camellia.f (S b).1 (E (m + 0 / 8))) :=
    d₁.congr fun j hj => by
      have := o₂ (8 + j) (by omega) (Or.inr (by simp only [d1Slot]; omega))
      rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega] at this
      exact this
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 128 (by decide)
  obtain ⟨s₄, e₄, z₄, g₄, m₄, rd₄, wr₄⟩ := cmpRdi_ok s₃
  have hrdi : s₂.gpr .rdi = s.gpr .rdi := by rw [r₂, r₁]
  refine ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairBody, runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([Instr.alu .add kp (.imm 128), .alu .cmp kp (.reg .rdi)] : List Instr) =
        [.alu .add kp (.imm (BitVec.ofNat 32 128))] ++ [.alu .cmp kp (.reg .rdi)] from rfl,
      runBlock_append', e₃, Option.bind_some, e₄]
  · refine c₂.step (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]) (fun r h1 h2 h3 => by rw [g₄, o₃ r h2])
      (by rw [m₄, m₃]; exact Frame.refl _ _) ?_
    intro kv hkv
    simp only [slotW, g₄, m₄, m₃, o₃ sb (by decide)]
    exact c₂.masks kv hkv
  · simp only [AtEntry, g₄, kp₃, k₂, k₁]
    rw [show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega]
  · rw [g₄, o₃ _ (by decide), hrdi]
  · refine ⟨q₂.congr fun j hj => ?_, d₂.congr fun j hj => ?_, d₂'.congr fun j hj => ?_⟩
    · simp only [Qs, g₄, o₃ _ (q_ne_kp j hj)]
    · simp only [slotW, g₄, m₄, m₃, o₃ sb (by decide)]
    · simp only [slotW, g₄, m₄, m₃, o₃ sb (by decide)]
  · rw [z₄, g₄, o₃ .rdi (by decide), hrdi]

/-! ## Moving halves -/

/-- The input words of `bothEnv`: the state, both halves, the subkey's 16 words. -/
def bothW (s : State) (i : Nat) : BitVec 64 :=
  if i < 8 then Qs s i else if i < 24 then slotW s (d1Slot + (i - 8)) else keyW s (i - 24)

/-- A check over `bothEnv`, on the machine. -/
theorem both_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) {is : List Instr}
    {outs : List (Reg × (Nat → List Nat))} {souts : List (Nat × (Nat → List Nat))} {keep : List Nat}
    (hchk : check (lanes 64 12) layerCfg (linExt 24) is bothEnv (linPostG 12 outs souts keep bothEnv) = true) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 64, (s'.gpr r).getLsbD p = xorBits (bothW s) (g p)) ∧
      (∀ j g, (j, g) ∈ souts → j < keySlot →
        ∀ p < 64, (slotW s' j).getLsbD p = xorBits (bothW s) (g p)) ∧
      (∀ j ∈ keep, j < keySlot → slotW s' j = slotW s j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [⟨s₀.gpr sb, 8 * keySlot⟩] s.mem s'.mem := by
  unfold bothEnv at hchk
  obtain ⟨s', h', ho, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (hc.ok hp hk hm34) (bothW s)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, by simp [bothW, hi]⟩)
    (fun j i hji => by
      simp only [bothIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      refine ⟨by simp [layerCfg, d1Slot, keySlot]; omega, by omega, ?_⟩
      simp [bothW, show ¬ 8 + j < 8 by omega, show 8 + j < 24 by omega]; rfl)
    (fun kv hkv => ⟨by simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [layerCfg, keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot], hc.masks kv hkv⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [bothW, show ¬ 24 + j < 8 by omega, show ¬ 24 + j < 24 by omega]; rfl⟩)
  simp only [layerCfg] at hb' hso hkp f'
  refine ⟨s', h', ho, fun j g hjg hj p hp => ?_, fun j hj hjk => ?_, rd', wr', o', ?_⟩
  · rw [slotW, hb']; exact hso j g hjg hj p hp
  · rw [slotW, hb']; exact hkp j hj hjk
  · simp only [slotRegion, hc.base] at f'; exact f'

theorem bothW_q (s : State) {j : Nat} (hj : j < 8) : bothW s j = Qs s j := by simp [bothW, hj]

theorem bothW_half (s : State) {d j : Nat} (hd : d = d1Slot ∨ d = d2Slot) (hj : j < 8) :
    bothW s (8 + (d - d1Slot) + j) = slotW s (d + j) := by
  have h1 : ¬ 8 + (d - d1Slot) + j < 8 := by omega
  have h2 : 8 + (d - d1Slot) + j < 24 := by rcases hd with rfl | rfl <;> simp only [d1Slot, d2Slot] <;> omega
  have h3 : d1Slot + (8 + (d - d1Slot) + j - 8) = d + j := by
    rcases hd with rfl | rfl <;> simp only [d1Slot, d2Slot] <;> omega
  simp only [bothW, h1, h2, ↓reduceIte, h3]

/-- `loadHalf d`, under `Ctx`. -/
theorem loadHalf_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m d : Nat} (hd : d = d1Slot ∨ d = d2Slot)
    (hchk : check (lanes 64 12) layerCfg (linExt 24) (loadHalf d) bothEnv
      (linPostG 12 (qOuts (loadHalfG d)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa (loadHalf d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ j < 8, Qs s' j = slotW s (d + j)) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) := by
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hq : ∀ j < 8, Qs s' j = slotW s (d + j) := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [Qs, ho (q j) (loadHalfG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, loadHalfG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_half s hd hj]
  have hh : ∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j) := fun j hj =>
    hkp _ (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, keySlot]; omega)
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (loadHalf d).all fun i => i.dst != some r) =
      true := by rcases hd with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), hq, hh⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])]
  exact hc.masks kv hkv

/-- `storeHalf d`, under `Ctx`. -/
theorem storeHalf_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m d : Nat} (hd : d = d1Slot ∨ d = d2Slot)
    (hchk : check (lanes 64 12) layerCfg (linExt 24) (storeHalf d) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d) (feistelKeep d) bothEnv) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa (storeHalf d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ j < 8, Qs s' j = Qs s j) ∧ (∀ j < 8, slotW s' (d + j) = Qs s j) ∧
      (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j)) := by
  obtain ⟨s', h', ho, hso, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hq : ∀ j < 8, Qs s' j = Qs s j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [Qs, ho (q j) (idG j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, idG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_q s hj]
  have hs : ∀ j < 8, slotW s' (d + j) = Qs s j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [hso (d + j) (idG j) (by simp only [storeHalfOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by rcases hd with rfl | rfl <;> simp only [d1Slot, d2Slot, keySlot] <;> omega) p hp,
      idG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_q s hj]
  have hh : ∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j) :=
    fun j hj hjd => hkp _ (List.mem_append_right _ (by
      simp only [List.mem_map, List.mem_range]
      rcases hd with rfl | rfl
      · exact ⟨j - 8, by simp only [d1Slot] at hjd; omega, by simp [d1Slot, d2Slot]; omega⟩
      · exact ⟨j, by simp only [d1Slot, d2Slot] at hjd; omega, by simp [d1Slot, d2Slot]⟩))
      (by simp only [d1Slot, keySlot]; omega)
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (storeHalf d).all fun i => i.dst != some r) =
      true := by rcases hd with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), hq, hs, hh⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])]
  exact hc.masks kv hkv

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- What FL reads, under `Ctx`. -/
theorem Ctx.flMem {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m off : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hoff : off = 0 ∨ off = 8) (hm34 : m + 2 ≤ 34) :
    FlMem s off (fun i => keyW s (off + i)) := by
  have hok := hc.ok hp hk hm34
  have hm := hc.masks
  refine ⟨fun i hi => ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [ofInt_nat]
    exact hok.extIn (off + i) (by simp only [layerCfg]; omega)
  · rw [ofInt_nat]
  · rw [ofInt_nat]
    obtain ⟨r, hr, hc'⟩ := hok.slotIn oddSlot (by simp [layerCfg, oddSlot, keySlot])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [ofInt_nat]; exact hm (oddSlot, _) (by simp [layerMasks])
  · rw [ofInt_nat]
    obtain ⟨r, hr, hc'⟩ := hok.slotIn evenSlot (by simp [layerCfg, evenSlot, keySlot])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [ofInt_nat]; exact hm (evenSlot, _) (by simp [layerMasks])

/-- What a run that writes only the state's registers and the temporaries keeps. -/
theorem Ctx.regs {s₀ s s' : State} (hc : Ctx s₀ s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hk : ∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) :
    Ctx s₀ s' := by
  have hk' : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    hk r (fun i hi h => hr (by subst h; simp only [sboxWrites, List.mem_cons]; revert i; decide))
      (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide))
  refine hc.step hrd hwr (fun r hr _ _ => hk' r hr) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => ?_
  simp only [slotW, hm, hk' sb (by decide)]
  exact hc.masks kv hkv

/-- FL (`flCode`) or FLINV (`flinvCode`) on the state, with the subkey at entry `m + off / 8`. -/
theorem flCode_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m off : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hoff : off = 0 ∨ off = 8)
    (hme : m + off / 8 < 8 * g + 2) (hm34 : m + 2 ≤ 34) {X : Nat → BitVec 64} (hQ : HalfRel (Qs s) X) :
    (∃ s', runBlock isa (flCode off) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.mem = s.mem ∧
      HalfRel (Qs s') (fun b => Spec.Camellia.fl (X b) (E (m + off / 8)))) ∧
    (∃ s', runBlock isa (flinvCode off) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.mem = s.mem ∧
      HalfRel (Qs s') (fun b => Spec.Camellia.flinv (X b) (E (m + off / 8)))) := by
  have hK : HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 8) := by
    have := hc.keyRel hp hk (e := off / 8) hme
    rcases hoff with rfl | rfl <;> exact this
  have hf := hc.flMem hp hk hoff hm34
  have hqkp : ∀ i < 8, kp ≠ q i := fun i hi h => q_ne_kp i hi h.symm
  have hqrdi : ∀ i < 8, Reg.rdi ≠ q i := fun i hi h => by revert i; decide
  constructor
  · obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flRot_ok hf
    have hf₁ := hf.congr m₁ rd₁ wr₁ (o₁ _ hqkp (by decide) (by decide))
      (o₁ _ (fun i hi h => q_ne_sb i hi h.symm) (by decide) (by decide))
    obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := flOr_ok hf₁
    refine ⟨s₂, by rw [flCode, runBlock_append', e₁, Option.bind_some, e₂], ?_, ?_, ?_, by rw [m₂, m₁], ?_⟩
    · exact (hc.regs m₁ rd₁ wr₁ o₁).regs m₂ rd₂ wr₂ fun r h1 h2 _ => o₂ r h1 h2
    · rw [o₂ _ hqkp (by decide), o₁ _ hqkp (by decide) (by decide)]
    · rw [o₂ _ hqrdi (by decide), o₁ _ hqrdi (by decide) (by decide)]
    · exact Camellia.fl_rel hQ hK (rotStep_of g₁) (orStep_of g₂)
  · obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flOr_ok hf
    have hf₁ := hf.congr m₁ rd₁ wr₁ (o₁ _ hqkp (by decide))
      (o₁ _ (fun i hi h => q_ne_sb i hi h.symm) (by decide))
    obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := flRot_ok hf₁
    refine ⟨s₂, by rw [flinvCode, runBlock_append', e₁, Option.bind_some, e₂], ?_, ?_, ?_, by rw [m₂, m₁], ?_⟩
    · exact (hc.regs m₁ rd₁ wr₁ fun r h1 h2 _ => o₁ r h1 h2).regs m₂ rd₂ wr₂ o₂
    · rw [o₂ _ hqkp (by decide) (by decide), o₁ _ hqkp (by decide)]
    · rw [o₂ _ hqrdi (by decide) (by decide), o₁ _ hqrdi (by decide)]
    · exact Camellia.flinv_rel hQ hK (orStep_of g₁) (rotStep_of g₂)

theorem slotW_congr {s₀ s s' : State} (hc : Ctx s₀ s) (hc' : Ctx s₀ s') (hm : s'.mem = s.mem) (k : Nat) :
    slotW s' k = slotW s k := by simp only [slotW, hm, hc.base, hc'.base]

/-- The FL layer: FLINV on `D2` with entry `m + 1`, FL on `D1` with entry `m`. -/
theorem fl_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < 8 * g + 2) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa flLayer s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      s'.gpr .rdi = s.gpr .rdi ∧
      Halves s' (fun b => (Spec.Camellia.fl (S b).1 (E m), Spec.Camellia.flinv (S b).2 (E (m + 1)))) := by
  obtain ⟨-, h1, h2⟩ := hS
  -- FLINV on `D2`.
  obtain ⟨s₁, e₁, c₁, k₁, r₁, q₁, hh₁⟩ := loadHalf_step hp hc (Or.inr rfl) loadHalf2_check hk hm34
  have hq₁ : HalfRel (Qs s₁) (fun b => (S b).2) := h2.congr fun j hj => q₁ j hj
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, r₂, m₂, hq₂⟩ := (flCode_step hp c₁ hk₁ (off := 8) (Or.inr rfl) (by omega) hm34 hq₁).2
  have hk₂ : AtEntry s₂ (s₀.gpr sb) m := by rw [AtEntry, k₂]; exact hk₁
  obtain ⟨s₃, e₃, c₃, k₃, r₃, q₃, sl₃, hh₃⟩ := storeHalf_step hp c₂ (Or.inr rfl) storeHalf2_check hk₂ hm34
  have hk₃ : AtEntry s₃ (s₀.gpr sb) m := by rw [AtEntry, k₃]; exact hk₂
  have d1₃ : ∀ j < 8, slotW s₃ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    rw [hh₃ j (by omega) (Or.inl (by simp only [d1Slot, d2Slot]; omega)), slotW_congr c₁ c₂ m₂,
      hh₁ j (by omega)]
  have d2₃ : HalfRel (fun j => slotW s₃ (d2Slot + j))
      (fun b => Spec.Camellia.flinv (S b).2 (E (m + 8 / 8))) := hq₂.congr fun j hj => sl₃ j hj
  -- FL on `D1`.
  obtain ⟨s₄, e₄, c₄, k₄, r₄, q₄, hh₄⟩ := loadHalf_step hp c₃ (Or.inl rfl) loadHalf1_check hk₃ hm34
  have hq₄ : HalfRel (Qs s₄) (fun b => (S b).1) := h1.congr fun j hj => by rw [q₄ j hj, d1₃ j hj]
  have hk₄ : AtEntry s₄ (s₀.gpr sb) m := by rw [AtEntry, k₄]; exact hk₃
  obtain ⟨s₅, e₅, c₅, k₅, r₅, m₅, hq₅⟩ := (flCode_step hp c₄ hk₄ (off := 0) (Or.inl rfl) (by omega) hm34 hq₄).1
  have hk₅ : AtEntry s₅ (s₀.gpr sb) m := by rw [AtEntry, k₅]; exact hk₄
  obtain ⟨s₆, e₆, c₆, k₆, r₆, q₆, sl₆, hh₆⟩ := storeHalf_step hp c₅ (Or.inl rfl) storeHalf1_check hk₅ hm34
  have d2₆ : HalfRel (fun j => slotW s₆ (d2Slot + j))
      (fun b => Spec.Camellia.flinv (S b).2 (E (m + 8 / 8))) := d2₃.congr fun j hj => by
    have := hh₆ (8 + j) (by omega) (Or.inr (by simp only [d1Slot]; omega))
    rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at this
    have h4 := hh₄ (8 + j) (by omega)
    rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at h4
    rw [this, slotW_congr c₄ c₅ m₅, h4]
  -- `add kp, 128`.
  obtain ⟨s₇, e₇, kp₇, o₇, m₇, rd₇, wr₇⟩ := addKp_ok s₆ 128 (by decide)
  have hq₇ : ∀ j < 8, Qs s₇ j = Qs s₆ j := fun j hj => o₇ _ (q_ne_kp j hj)
  have hs₇ : ∀ k, slotW s₇ k = slotW s₆ k := fun k => by simp only [slotW, m₇, o₇ sb (by decide)]
  refine ⟨s₇, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · rw [flLayer, runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some, e₄,
      Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some]
    exact e₇
  · refine c₆.step rd₇ wr₇ (fun r _ h2 _ => o₇ r h2) (by rw [m₇]; exact Frame.refl _ _) fun kv hkv => ?_
    rw [hs₇]; exact c₆.masks kv hkv
  · simp only [AtEntry, kp₇, k₆, k₅, k₄, k₃, k₂, k₁]
    rw [show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega]
  · rw [o₇ _ (by decide), r₆, r₅, r₄, r₃, r₂, r₁]
  · exact hq₅.congr fun j hj => by rw [hq₇ j hj, q₆ j hj]
  · exact hq₅.congr fun j hj => by rw [hs₇, sl₆ j hj]
  · exact d2₆.congr fun j hj => hs₇ _

/-! ## Groups of six rounds -/

/-- `p` pairs of rounds of group `i`. -/
def pairsN (E : Nat → BitVec 64) (i p : Nat) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range p).foldl (fun d k => pair (E (2 + 8 * i + 2 * k)) (E (3 + 8 * i + 2 * k)) d) d

theorem pairsN_succ (E : Nat → BitVec 64) (i p : Nat) (d : BitVec 64 × BitVec 64) :
    pairsN E i (p + 1) d = pair (E (2 + 8 * i + 2 * p)) (E (3 + 8 * i + 2 * p)) (pairsN E i p d) := by
  simp [pairsN, List.range_succ, List.foldl_append]

theorem group_eq (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) (i : Nat) :
    group g E d i = if i + 1 < g then
      (Spec.Camellia.fl (pairsN E i 3 d).1 (E (8 + 8 * i)), Spec.Camellia.flinv (pairsN E i 3 d).2 (E (9 + 8 * i)))
      else pairsN E i 3 d := by
  simp only [group, pairsN, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.nil_append, show 2 + 8 * i + 2 * 0 = 2 + 8 * i by omega,
    show 3 + 8 * i + 2 * 0 = 3 + 8 * i by omega, show 2 + 8 * i + 2 * 1 = 4 + 8 * i by omega,
    show 3 + 8 * i + 2 * 1 = 5 + 8 * i by omega, show 2 + 8 * i + 2 * 2 = 6 + 8 * i by omega,
    show 3 + 8 * i + 2 * 2 = 7 + 8 * i by omega]

/-- `cmp kp, [endSlot]`, keeping all else. -/
theorem cmpEnd_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * endSlot)) 8) :
    ∃ s', runBlock isa [.alu .cmp kp (.mem (Impl.Aes.X86_64.slotAt sb endSlot))] s = some s' ∧
      s'.zf = some (s.gpr kp - slotW s endSlot == 0) ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofInt 64 ((8 * endSlot : Nat) : Int)) 8 := by
    rw [ofInt_nat]; exact hr
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, State.ea, Impl.Aes.X86_64.slotAt, hr', ite_true, Option.bind_some]; rfl,
    ?_, by rfl, by rfl, by rfl, by rfl⟩
  simp only [RegUpd.zf_arithFlags, slotW, wordAddr, ofInt_nat]

theorem entry_beq (b : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x - (b + BitVec.ofNat 64 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, VG.Offset.ofNat_sub_ofNat_beq hx hy]

/-- `mov rdi, kp; add rdi, 384`. -/
theorem setBound_ok (s : State) :
    ∃ s', runBlock isa [movR .rdi kp, .alu .add .rdi (.imm 384)] s = some s' ∧
      s'.gpr .rdi = s.gpr kp + BitVec.ofNat 64 384 ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.map_some]; rfl, ?_, fun r hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The address of the postwhitening's entry is kept. -/
theorem Ctx.endW {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s) :
    slotW s endSlot = slotW s₀ endSlot := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  simp only [slotW, wordAddr, hc.base]
  refine hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * endSlot), 8⟩)
    (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq, endSlot_eq]; omega) (by rw [endSlot_eq]; omega)
  · refine (hp.sep.sub_right (VG.Offset.sub_base _ ?_)).symm
    rw [slots_eq, endSlot_eq]; omega

theorem Ctx.endIn {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s) :
    InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * endSlot)) 8 := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  refine ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact hp.scr), ?_⟩
  rw [hc.base]
  exact VG.Offset.contains_base _ (by rw [slots_eq, endSlot_eq]; omega) (by rw [endSlot_eq]; omega)

theorem Halves.congr {s s' : State} {S : Nat → BitVec 64 × BitVec 64} (h : Halves s S)
    (hq : ∀ j < 8, Qs s' j = Qs s j) (hs : ∀ k, slotW s' k = slotW s k) : Halves s' S :=
  ⟨h.1.congr hq, h.2.1.congr fun _ _ => hs _, h.2.2.congr fun _ _ => hs _⟩

/-- A step that changes only the flags (and `rdi`) keeps everything. -/
theorem Ctx.flags {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ .rdi → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r _ _ h3 => hg r h3) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
    simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

theorem entry_lt {g i : Nat} (hg : g ≤ 4) (hi : i ≤ 8 * g + 2) : 8 * keySlot + 64 * i < 2 ^ 64 := by
  rw [keySlot_eq]; omega

/-- A group of six rounds, then FL and FLINV unless it is the last. -/
theorem group_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i : Nat} (hi : i < g) (hk : AtEntry s (s₀.gpr sb) (2 + 8 * i)) {S : Nat → BitVec 64 × BitVec 64}
    (hS : Halves s S) :
    WP isa groupBody s fun s' => Ctx s₀ s' ∧ Halves s' (fun b => group g E (S b) i) ∧
      AtEntry s' (s₀.gpr sb) (if i + 1 < g then 2 + 8 * (i + 1) else 8 * g) ∧
      s'.zf = some (decide (i + 1 = g)) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  let b := s₀.gpr sb
  -- The bound of the pairs.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := setBound_ok s
  have hc₁ : Ctx s₀ s₁ := hc.flags (fun r hr => o₁ r hr) m₁ rd₁ wr₁
  have hk₁ : AtEntry s₁ b (2 + 8 * i) := by rw [AtEntry, o₁ kp (by decide)]; exact hk
  have hrdi₁ : s₁.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 + 8 * i)) := by
    rw [r₁, show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * (2 + 8 * i) + 384 = 8 * keySlot + 64 * (8 + 8 * i) by omega]
  have hS₁ : Halves s₁ S := hS.congr (fun j hj => o₁ _ (fun h => by revert j; decide))
    (fun k => by simp only [slotW, m₁, o₁ sb (by decide)])
  unfold groupBody
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  -- The pairs.
  let Inv : Nat → State → Prop := fun n s' => ∃ p, n = 3 - p ∧ p < 3 ∧ Ctx s₀ s' ∧
    AtEntry s' b (2 + 8 * i + 2 * p) ∧ s'.gpr .rdi = s₁.gpr .rdi ∧
    Halves s' (fun b => pairsN E i p (S b))
  let Mid : State → Prop := fun s' => Ctx s₀ s' ∧ AtEntry s' b (8 + 8 * i) ∧
    Halves s' (fun b => pairsN E i 3 (S b))
  refine WP.seq (WP.mono (Q := Mid) (WP.loop Inv (fun n s' hs' => ?_) 3 s₁
    ⟨0, rfl, by omega, hc₁, by simpa using hk₁, rfl, by simpa [pairsN] using hS₁⟩) fun s₂ h₂ => ?_)
  · obtain ⟨p, rfl, hp3, hc', hk', hr', hS'⟩ := hs'
    obtain ⟨s'', e'', c'', k'', r'', S'', z''⟩ := pair_step hp hc' hk' (by omega) (by omega) hS'
    refine WP.of_runBlock ⟨s'', e'', ?_⟩
    have hz : s''.zf = some (decide (p + 1 = 3)) := by
      rw [z'', show s''.gpr kp = _ from k'', hr', hrdi₁, entry_beq b (entry_lt hg4 (by omega))
        (entry_lt hg4 (by omega))]
      simp only [Option.some.injEq, decide_eq_decide]; omega
    have hS'' : Halves s'' (fun b => pairsN E i (p + 1) (S b)) := by
      simpa only [pairsN_succ, show 2 + 8 * i + 2 * p + 1 = 3 + 8 * i + 2 * p by omega] using S''
    by_cases hp2 : p + 1 = 3
    · refine .inl ⟨by simp [X86_64.eval, hz, hp2], c'', ?_, by rw [← hp2]; exact hS''⟩
      rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 8 + 8 * i by omega]
    · refine .inr ⟨by simp [X86_64.eval, hz, hp2], 3 - (p + 1), by omega, p + 1, rfl, by omega, c'',
        by rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 2 + 8 * i + 2 * (p + 1) by omega],
        by rw [r'', hr'], hS''⟩
  · obtain ⟨hc₂, hk₂, hS₂⟩ := h₂
    have hbnd : slotW s₂ endSlot = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 * g)) := by
      rw [hc₂.endW hp, hp.bound, show 512 * g = 64 * (8 * g) by omega]
    obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := cmpEnd_ok (hc₂.endIn hp)
    have hc₃ : Ctx s₀ s₃ := hc₂.flags (fun r _ => by rw [g₃]) m₃ rd₃ wr₃
    have hz₃ : s₃.zf = some (decide (i + 1 = g)) := by
      rw [z₃, show s₂.gpr kp = _ from hk₂, hbnd,
        entry_beq b (entry_lt hg4 (by omega)) (entry_lt hg4 (by omega))]
      simp only [Option.some.injEq, decide_eq_decide]; omega
    have hk₃ : AtEntry s₃ b (8 + 8 * i) := by rw [AtEntry, g₃]; exact hk₂
    have hS₃ : Halves s₃ (fun b => pairsN E i 3 (S b)) :=
      hS₂.congr (fun j _ => by simp only [Qs, g₃]) (fun k => by simp only [slotW, g₃, m₃])
    refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
    refine WP.seq (WP.ite (!decide (i + 1 = g)) (by simp [X86_64.eval, hz₃]) (fun ht => ?_) (fun hf => ?_))
    · have hlt : i + 1 < g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at ht; omega
      obtain ⟨s₄, e₄, c₄, k₄, -, S₄⟩ := fl_step hp hc₃ hk₃ (by omega) (by omega) hS₃
      refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
      have hk₄ : AtEntry s₄ b (2 + 8 * (i + 1)) := by
        rw [AtEntry, show s₄.gpr kp = _ from k₄, show 8 + 8 * i + 2 = 2 + 8 * (i + 1) by omega]
      obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := cmpEnd_ok (c₄.endIn hp)
      refine WP.of_runBlock ⟨s₅, e₅, c₄.flags (fun r _ => by rw [g₅]) m₅ rd₅ wr₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b =>
            (Spec.Camellia.fl (pairsN E i 3 (S b)).1 (E (8 + 8 * i)),
              Spec.Camellia.flinv (pairsN E i 3 (S b)).2 (E (8 + 8 * i + 1))) :=
          funext fun b => by
            rw [group_eq, show 8 + 8 * i + 1 = 9 + 8 * i by omega]; simp only [hlt, ↓reduceIte]
        rw [hG]
        exact S₄.congr (fun j _ => by simp only [Qs, g₅]) (fun k => by simp only [slotW, g₅, m₅])
      · simp only [hlt, ↓reduceIte]; rw [AtEntry, g₅]; exact hk₄
      · rw [z₅, show s₄.gpr kp = _ from hk₄, c₄.endW hp, hp.bound, show 512 * g = 64 * (8 * g) by omega,
          entry_beq b (entry_lt hg4 (by omega)) (entry_lt hg4 (by omega))]
        simp only [Option.some.injEq, decide_eq_decide]; omega
    · have heq : i + 1 = g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hf; exact hf
      refine WP.of_runBlock ⟨s₃, rfl, ?_⟩
      obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := cmpEnd_ok (hc₃.endIn hp)
      refine WP.of_runBlock ⟨s₅, e₅, hc₃.flags (fun r _ => by rw [g₅]) m₅ rd₅ wr₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b => pairsN E i 3 (S b) :=
          funext fun b => by rw [group_eq]; simp only [show ¬ i + 1 < g by omega, ↓reduceIte]
        rw [hG]
        exact hS₃.congr (fun j _ => by simp only [Qs, g₅]) (fun k => by simp only [slotW, g₅, m₅])
      · simp only [show ¬ i + 1 < g by omega, ↓reduceIte]
        rw [AtEntry, g₅, show s₃.gpr kp = _ from hk₃, show 8 + 8 * i = 8 * g by omega]
      · rw [z₅, show s₃.gpr kp = _ from hk₃, hc₃.endW hp, hp.bound,
          show 512 * g = 64 * (8 * g) by omega,
          entry_beq b (entry_lt hg4 (by omega)) (entry_lt hg4 (by omega))]
        simp only [Option.some.injEq, decide_eq_decide]; omega

end VG.Proof.Camellia.X86_64
