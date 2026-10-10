import VerifiedGarbage.Proof.Camellia.AArch64.Round
import VerifiedGarbage.Proof.Camellia.AArch64.Moves
import VerifiedGarbage.Proof.Camellia.AArch64.Fl
import VerifiedGarbage.Proof.Camellia.Layout
import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Block

/-!
# Eight blocks of bitsliced Camellia on AArch64

As on x86-64: with the table of bitsliced subkeys `E 0 … E (8 g + 1)` in
the scratch buffer (`CorePre`), `crypt8` replaces each of the eight blocks
in the tail buffer with `cryptWords g E` of it. Until its last block
(`tail`) it writes only the rounds' working space, below the table (`Ctx`). The rounds are `round_ok`; the pairs of
rounds, the groups of six and the FL layers are loops and blocks around
them, whose invariants are the specification's `pair`, `group` and
`groups` (`Proof/Camellia/Words.lean`).
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 t2 u7 kp movR ldS stS)
open VG.Proof.Camellia (HalfRel WordRel pair group groups cryptWords)

/-- Word `j` of entry `i` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : Addr) (i j : Nat) : BitVec 64 :=
  m.readW (b + BitVec.ofNat 64 (8 * keySlot + 64 * i + 8 * j)) 64

/-- What the rounds need: the scratch buffer, writable, the masks, and a
table of `nk` subkeys. -/
structure KeyCtx (s₀ : State) (nk : Nat) (E : Nat → BitVec 64) : Prop where
  scr : (⟨s₀.gpr sb, 8 * slots⟩ : Region) ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 8 * slots ≤ 2 ^ 64
  nk34 : nk ≤ 34
  masks : MasksOk s₀
  keys : ∀ i < nk, HalfRel (entryW s₀.mem (s₀.gpr sb) i) fun _ => E i

/-- What `crypt8` needs: the rounds' context, with the table of `8 g + 2`
subkeys, and the address of its postwhitening entry in `x4`. -/
structure CorePre (s₀ : State) (g : Nat) (E : Nat → BitVec 64) : Prop extends KeyCtx s₀ (8 * g + 2) E where
  hg : g = 3 ∨ g = 4
  bound : s₀.gpr .x4 = s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g)

/-- What `crypt8` may write in the scratch buffer at `b`: the rounds' working
space and the tail buffer. -/
def ctxRegions (b : Addr) : List Region :=
  [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩]

/-- What stays the same: the regions, the registers but the layers', `kp`
and `x0`, the memory outside the rounds' working space and the tail buffer,
and the masks. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → s.gpr r = s₀.gpr r
  frame : Frame (ctxRegions (s₀.gpr sb)) s₀.mem s.mem
  masks : MasksOk s

theorem Ctx.refl {s₀ : State} (hm : MasksOk s₀) : Ctx s₀ s₀ :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, Frame.refl _ _, hm⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide) (by decide)

/-- A step that writes only the state's registers, `kp`, `rdi`, the rounds'
working space, and keeps the masks, keeps `Ctx`. -/
theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s₀.gpr sb, 8 * keySlot⟩] s.mem s'.mem) (hm : MasksOk s') :
    Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 h3 => (hk r h1 h2 h3).trans (hc.keep r h1 h2 h3),
    hc.frame.trans (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [ctxRegions, hr]), hm⟩

/-- `Ctx.step`, for a step that may also write the tail buffer. -/
theorem Ctx.stepT {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → s'.gpr r = s.gpr r)
    (hf : Frame (ctxRegions (s₀.gpr sb)) s.mem s'.mem) (hm : MasksOk s') :
    Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 h3 => (hk r h1 h2 h3).trans (hc.keep r h1 h2 h3),
    hc.frame.trans hf, hm⟩

/-! ## Addresses -/

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : Addr) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * m)

theorem keyW_entry {s : State} {b : Addr} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (8 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, wordAddr, entryW]
  rw [hk, addr_add, show 8 * keySlot + 64 * m + 8 * (8 * e + j) = 8 * keySlot + 64 * (m + e) + 8 * j by omega]

theorem slots_eq : slots = 406 := rfl
theorem tailSlot_eq : tailSlot = 378 := rfl
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
theorem Ctx.entry {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {i j : Nat} (hi : i < 34) (hj : j < 8) :
    entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  simp only [entryW]
  refine hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 64 * i + 8 * j), 8⟩)
    (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)
  · exact VG.Offset.disjoint _ (by rw [keySlot_eq, tailSlot_eq]; omega) (by rw [keySlot_eq]; omega)
      (by rw [tailSlot_eq]; omega)

theorem Ctx.keyRel {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < nk) :
    HalfRel (fun j => keyW s (8 * e + j)) fun _ => E (m + e) := by
  have hg := hp.nk34
  refine (hp.keys _ hme).congr fun j hj => ?_
  rw [keyW_entry hk, hc.entry hp (by omega) hj]

theorem Ctx.ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 2 ≤ 34) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hc.base hk hm

/-- A round, under `Ctx`: `round off d` with the subkey at entry `m + off / 8`. -/
theorem round_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {off d m : Nat}
    (hkc : check (lanes 64 12) layerCfg (linExt 8) (keyXor off ++ inSel) keyInEnv
      (linPostG 12 (qOuts (Camellia.keyInG off)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true)
    (hfc : check (lanes 64 12) layerCfg (linExt 24) (feistel d) bothEnv
      (linPostG 12 (qOuts (feistelG d)) ((List.range 8).map fun j => (d + j, feistelG d j))
        (feistelKeep d) bothEnv) = true)
    (hoff : off = 0 ∨ off = 8) (hd : d = d1Slot ∨ d = d2Slot)
    (hk : AtEntry s (s₀.gpr sb) m) (hme : m + off / 8 < nk) (hm34 : m + 2 ≤ 34)
    {X Y : Nat → BitVec 64} (hQ : HalfRel (Qs s) X) (hR : HalfRel (fun j => slotW s (d + j)) Y) :
    ∃ s', runBlock isa (round off d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧
      HalfRel (Qs s') (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 8))) ∧
      HalfRel (fun j => slotW s' (d + j)) (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 8))) ∧
      (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, keySlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  have hK : HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 8) := by
    have := hc.keyRel hp hk (e := off / 8) hme
    rcases hoff with rfl | rfl <;> exact this
  obtain ⟨s', h', hq', hs', hm', hh', rd', wr', -, o', f'⟩ :=
    round_ok hkc hfc hoff hd (hc.ok hp hk hm34) hc.masks hQ hK hR
  have f'' : Frame [⟨s₀.gpr sb, 8 * keySlot⟩] s.mem s'.mem := by
    refine f'.mono fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, layerCfg, hc.base]; simp
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => o' r hr) f'' hm', o' _ (by decide),
    o' _ (by decide), hq', hs', hh', fun k hk hk' => ?_⟩
  simp only [slotW, o' sb (by decide), hc.base]; exact slot_above f'' hk hk'

/-! ## Pairs of rounds -/

/-- The halves of the eight blocks, `(D1, D2)` of block `b` in `S b`: `D1` in
the state and in its slots, `D2` in its slots. -/
def Halves (s : State) (S : Nat → BitVec 64 × BitVec 64) : Prop :=
  HalfRel (Qs s) (fun b => (S b).1) ∧ HalfRel (fun j => slotW s (d1Slot + j)) (fun b => (S b).1) ∧
    HalfRel (fun j => slotW s (d2Slot + j)) (fun b => (S b).2)

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

/-- The two rounds of a pair, `kp += 128` and `t0 := kp - x0`. -/
theorem pair_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa pairBody s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ Halves s' (fun b => pair (E m) (E (m + 1)) (S b)) ∧
      s'.gpr t0 = s'.gpr kp - s.gpr .x0 := by
  obtain ⟨hq, h1, h2⟩ := hS
  obtain ⟨s₁, e₁, c₁, k₁, r₁, q₁, d₁, o₁, -⟩ := round_step hp hc (off := 0) (d := d2Slot) keyIn0_check
    feistel2_check (by decide) (by decide) hk (by omega) hm34 hq h2
  have h1' : HalfRel (fun j => slotW s₁ (d1Slot + j)) (fun b => (S b).1) :=
    h1.congr fun j hj => o₁ j (by omega) (Or.inl (by simp [d1Slot, d2Slot]; omega))
  obtain ⟨s₂, e₂, c₂, k₂, r₂, q₂, d₂, o₂, -⟩ := round_step hp c₁ (off := 8) (d := d1Slot) keyIn8_check
    feistel1_check (by decide) (by decide) (by rw [AtEntry, k₁]; exact hk) (by omega) hm34 q₁ h1'
  have d₂' : HalfRel (fun j => slotW s₂ (d2Slot + j))
      (fun b => (S b).2 ^^^ Spec.Camellia.f (S b).1 (E (m + 0 / 8))) :=
    d₁.congr fun j hj => by
      have := o₂ (8 + j) (by omega) (Or.inr (by simp only [d1Slot]; omega))
      rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega] at this
      exact this
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 128 (by decide)
  obtain ⟨s₄, e₄, z₄, g₄', m₄, rd₄, wr₄⟩ := subR_ok s₃ t0 kp .x0
  have g₄ : ∀ r, r ≠ t0 → s₄.gpr r = s₃.gpr r := g₄'
  have hrdi : s₂.gpr .x0 = s.gpr .x0 := by rw [r₂, r₁]
  refine ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairBody, runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.addImm .x kp kp 128, .sub .x t0 kp .x0] : List Instr) =
        [.addImm .x kp kp 128] ++ [.sub .x t0 kp .x0] from rfl,
      runBlock_append', e₃, Option.bind_some, e₄]
  · refine c₂.step (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃])
      (fun r h1 h2 _ => by rw [g₄ r (fun h => h1 (by subst h; decide)), o₃ r h2])
      (by rw [m₄, m₃]; exact Frame.refl _ _) ?_
    intro kv hkv
    simp only [slotW, g₄ sb (by decide), m₄, m₃, o₃ sb (by decide)]
    exact c₂.masks kv hkv
  · simp only [AtEntry, g₄ kp (by decide), kp₃, k₂, k₁]
    rw [show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega]
  · rw [g₄ _ (by decide), o₃ _ (by decide), hrdi]
  · refine ⟨q₂.congr fun j hj => ?_, d₂.congr fun j hj => ?_, d₂'.congr fun j hj => ?_⟩
    · simp only [Qs, g₄ _ (q_ne_t0 j hj), o₃ _ (q_ne_kp j hj)]
    · simp only [slotW, g₄ sb (by decide), m₄, m₃, o₃ sb (by decide)]
    · simp only [slotW, g₄ sb (by decide), m₄, m₃, o₃ sb (by decide)]
  · rw [z₄, g₄ kp (by decide), o₃ .x0 (by decide), hrdi]

/-! ## Moving halves -/

/-- The input words of `bothEnv`: the state, both halves, the subkey's 16 words. -/
def bothW (s : State) (i : Nat) : BitVec 64 :=
  if i < 8 then Qs s i else if i < 24 then slotW s (d1Slot + (i - 8)) else keyW s (i - 24)

/-- A check over `bothEnv`, on the machine. -/
theorem both_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) {is : List Instr}
    {outs : List (Reg × (Nat → List Nat))} {souts : List (Nat × (Nat → List Nat))} {keep : List Nat}
    (hchk : check (lanes 64 12) layerCfg (linExt 24) is bothEnv (linPostG 12 outs souts keep bothEnv) = true) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 64, (s'.gpr r).getLsbD p = xorBits (bothW s) (g p)) ∧
      (∀ j g, (j, g) ∈ souts → j < keySlot →
        ∀ p < 64, (slotW s' j).getLsbD p = xorBits (bothW s) (g p)) ∧
      (∀ j ∈ keep, j < keySlot → slotW s' j = slotW s j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => dstOf i != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [⟨s₀.gpr sb, 8 * keySlot⟩] s.mem s'.mem := by
  unfold bothEnv at hchk
  obtain ⟨s', h', ho, hso, hkp, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (hc.ok hp hk hm34) (bothW s)
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
theorem loadHalf_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m d : Nat} (hd : d = d1Slot ∨ d = d2Slot)
    (hchk : check (lanes 64 12) layerCfg (linExt 24) (loadHalf d) bothEnv
      (linPostG 12 (qOuts (loadHalfG d)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa (loadHalf d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧ (∀ j < 8, Qs s' j = slotW s (d + j)) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, keySlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hq : ∀ j < 8, Qs s' j = slotW s (d + j) := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [Qs, ho (q j) (loadHalfG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, loadHalfG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_half s hd hj]
  have hh : ∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j) := fun j hj =>
    hkp _ (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, keySlot]; omega)
  have hall : (layerKeep.all fun r => (loadHalf d).all fun i => dstOf i != some r) =
      true := by rcases hd with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_layerWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), hq, hh, fun k hk hk' => by
      simp only [slotW, hkeep sb (by decide), hc.base]; exact slot_above f' hk hk'⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])]
  exact hc.masks kv hkv

/-- `storeHalf d`, under `Ctx`. -/
theorem storeHalf_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m d : Nat} (hd : d = d1Slot ∨ d = d2Slot)
    (hchk : check (lanes 64 12) layerCfg (linExt 24) (storeHalf d) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d) (feistelKeep d) bothEnv) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa (storeHalf d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧ (∀ j < 8, Qs s' j = Qs s j) ∧ (∀ j < 8, slotW s' (d + j) = Qs s j) ∧
      (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, keySlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
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
  have hall : (layerKeep.all fun r => (storeHalf d).all fun i => dstOf i != some r) =
      true := by rcases hd with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_layerWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), hq, hs, hh, fun k hk hk' => by
      simp only [slotW, hkeep sb (by decide), hc.base]; exact slot_above f' hk hk'⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])]
  exact hc.masks kv hkv

/-- What FL reads, under `Ctx`. -/
theorem Ctx.flMem {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m off : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hoff : off = 0 ∨ off = 8) (hm34 : m + 2 ≤ 34) :
    FlMem s off (fun i => keyW s (off + i)) := by
  have hok := hc.ok hp hk hm34
  have hm := hc.masks
  refine ⟨fun i hi => ⟨hok.extIn (off + i) (by simp only [layerCfg]; omega), rfl⟩,
    by rcases hoff with rfl | rfl <;> decide, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨r, hr, hc'⟩ := hok.slotIn oddSlot (by simp [layerCfg, oddSlot, keySlot])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · exact hm (oddSlot, _) (by simp [layerMasks])
  · obtain ⟨r, hr, hc'⟩ := hok.slotIn evenSlot (by simp [layerCfg, evenSlot, keySlot])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · exact hm (evenSlot, _) (by simp [layerMasks])

/-- The temporaries of FL are among the layers' registers. -/
theorem fl_temps : ∀ r : Reg, (r ∈ layerWrites ∨ r = kp ∨ r = .x0) ∨
    ((∀ i < 8, r ≠ q i) ∧ r ≠ t0 ∧ r ≠ u7 ∧ r ≠ t1 ∧ r ≠ t2) := by
  intro r; cases r <;> decide

/-- What a run that writes only the state's registers and the temporaries keeps. -/
theorem Ctx.regs {s₀ s s' : State} (hc : Ctx s₀ s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr)
    (hk : ∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) :
    Ctx s₀ s' := by
  have hk' : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr => by
    rcases fl_temps r with (h | h | h) | ⟨h1, h2, h3, h4, h5⟩
    · exact absurd h hr
    · subst h; exact hk _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst h; exact hk _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hk r h1 h2 h3 h4 h5
  refine hc.step hrd hwr (fun r hr _ _ => hk' r hr) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => ?_
  simp only [slotW, hm, hk' sb (by decide)]
  exact hc.masks kv hkv

/-- FL (`flCode`) or FLINV (`flinvCode`) on the state, with the subkey at entry `m + off / 8`. -/
theorem flCode_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m off : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hoff : off = 0 ∨ off = 8)
    (hme : m + off / 8 < nk) (hm34 : m + 2 ≤ 34) {X : Nat → BitVec 64} (hQ : HalfRel (Qs s) X) :
    (∃ s', runBlock isa (flCode off) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.mem = s.mem ∧
      HalfRel (Qs s') (fun b => Spec.Camellia.fl (X b) (E (m + off / 8)))) ∧
    (∃ s', runBlock isa (flinvCode off) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.mem = s.mem ∧
      HalfRel (Qs s') (fun b => Spec.Camellia.flinv (X b) (E (m + off / 8)))) := by
  have hK : HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 8) := by
    have := hc.keyRel hp hk (e := off / 8) hme
    rcases hoff with rfl | rfl <;> exact this
  have hf := hc.flMem hp hk hoff hm34
  have hqkp : ∀ i < 8, kp ≠ q i := fun i hi h => q_ne_kp i hi h.symm
  have hqrdi : ∀ i < 8, Reg.x0 ≠ q i := fun i hi h => by revert i; decide
  constructor
  · obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flRot_ok hf
    have hf₁ := hf.congr m₁ rd₁ wr₁ (o₁ _ hqkp (by decide) (by decide) (by decide) (by decide))
      (o₁ _ (fun i hi h => q_ne_sb i hi h.symm) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := flOr_ok hf₁
    refine ⟨s₂, by rw [flCode, runBlock_append', e₁, Option.bind_some, e₂], ?_, ?_, ?_, by rw [m₂, m₁], ?_⟩
    · exact (hc.regs m₁ rd₁ wr₁ o₁).regs m₂ rd₂ wr₂ fun r h1 h2 h3 _ h5 => o₂ r h1 h2 h3 h5
    · rw [o₂ _ hqkp (by decide) (by decide) (by decide),
        o₁ _ hqkp (by decide) (by decide) (by decide) (by decide)]
    · rw [o₂ _ hqrdi (by decide) (by decide) (by decide),
        o₁ _ hqrdi (by decide) (by decide) (by decide) (by decide)]
    · exact Camellia.fl_rel hQ hK (rotStep_of g₁) (orStep_of g₂)
  · obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flOr_ok hf
    have hf₁ := hf.congr m₁ rd₁ wr₁ (o₁ _ hqkp (by decide) (by decide) (by decide))
      (o₁ _ (fun i hi h => q_ne_sb i hi h.symm) (by decide) (by decide) (by decide))
    obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := flRot_ok hf₁
    refine ⟨s₂, by rw [flinvCode, runBlock_append', e₁, Option.bind_some, e₂], ?_, ?_, ?_, by rw [m₂, m₁], ?_⟩
    · exact (hc.regs m₁ rd₁ wr₁ fun r h1 h2 h3 _ h5 => o₁ r h1 h2 h3 h5).regs m₂ rd₂ wr₂ o₂
    · rw [o₂ _ hqkp (by decide) (by decide) (by decide) (by decide),
        o₁ _ hqkp (by decide) (by decide) (by decide)]
    · rw [o₂ _ hqrdi (by decide) (by decide) (by decide) (by decide),
        o₁ _ hqrdi (by decide) (by decide) (by decide)]
    · exact Camellia.flinv_rel hQ hK (orStep_of g₁) (rotStep_of g₂)

theorem slotW_congr {s₀ s s' : State} (hc : Ctx s₀ s) (hc' : Ctx s₀ s') (hm : s'.mem = s.mem) (k : Nat) :
    slotW s' k = slotW s k := by simp only [slotW, hm, hc.base, hc'.base]

/-- The FL layer: FLINV on `D2` with entry `m + 1`, FL on `D1` with entry `m`. -/
theorem fl_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa flLayer s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      s'.gpr .x0 = s.gpr .x0 ∧
      Halves s' (fun b => (Spec.Camellia.fl (S b).1 (E m), Spec.Camellia.flinv (S b).2 (E (m + 1)))) := by
  obtain ⟨-, h1, h2⟩ := hS
  -- FLINV on `D2`.
  obtain ⟨s₁, e₁, c₁, k₁, r₁, q₁, hh₁, -⟩ := loadHalf_step hp hc (Or.inr rfl) loadHalf2_check hk hm34
  have hq₁ : HalfRel (Qs s₁) (fun b => (S b).2) := h2.congr fun j hj => q₁ j hj
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, r₂, m₂, hq₂⟩ := (flCode_step hp c₁ hk₁ (off := 8) (Or.inr rfl) (by omega) hm34 hq₁).2
  have hk₂ : AtEntry s₂ (s₀.gpr sb) m := by rw [AtEntry, k₂]; exact hk₁
  obtain ⟨s₃, e₃, c₃, k₃, r₃, q₃, sl₃, hh₃, -⟩ := storeHalf_step hp c₂ (Or.inr rfl) storeHalf2_check hk₂ hm34
  have hk₃ : AtEntry s₃ (s₀.gpr sb) m := by rw [AtEntry, k₃]; exact hk₂
  have d1₃ : ∀ j < 8, slotW s₃ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    rw [hh₃ j (by omega) (Or.inl (by simp only [d1Slot, d2Slot]; omega)), slotW_congr c₁ c₂ m₂,
      hh₁ j (by omega)]
  have d2₃ : HalfRel (fun j => slotW s₃ (d2Slot + j))
      (fun b => Spec.Camellia.flinv (S b).2 (E (m + 8 / 8))) := hq₂.congr fun j hj => sl₃ j hj
  -- FL on `D1`.
  obtain ⟨s₄, e₄, c₄, k₄, r₄, q₄, hh₄, -⟩ := loadHalf_step hp c₃ (Or.inl rfl) loadHalf1_check hk₃ hm34
  have hq₄ : HalfRel (Qs s₄) (fun b => (S b).1) := h1.congr fun j hj => by rw [q₄ j hj, d1₃ j hj]
  have hk₄ : AtEntry s₄ (s₀.gpr sb) m := by rw [AtEntry, k₄]; exact hk₃
  obtain ⟨s₅, e₅, c₅, k₅, r₅, m₅, hq₅⟩ := (flCode_step hp c₄ hk₄ (off := 0) (Or.inl rfl) (by omega) hm34 hq₄).1
  have hk₅ : AtEntry s₅ (s₀.gpr sb) m := by rw [AtEntry, k₅]; exact hk₄
  obtain ⟨s₆, e₆, c₆, k₆, r₆, q₆, sl₆, hh₆, -⟩ := storeHalf_step hp c₅ (Or.inl rfl) storeHalf1_check hk₅ hm34
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

/-- A step that changes only `t0` keeps `Ctx`. -/
theorem Ctx.t0 {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h1 _ _ => hg r fun h => h1 (by subst h; decide))
    (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
      simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

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

theorem ofNat_beq_zero {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v == 0) = decide (v = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
  · intro h; rw [h]; rfl

/-- `add x0, kp, #384`. -/
theorem setBound_ok (s : State) :
    ∃ s', runBlock isa [.addImm .x .x0 kp 384] s = some s' ∧
      s'.gpr .x0 = s.gpr kp + BitVec.ofNat 64 384 ∧ (∀ r, r ≠ .x0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x .x0 (s.gpr kp + BitVec.ofNat 64 384), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 384 < 4096 by decide), read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem Halves.congr {s s' : State} {S : Nat → BitVec 64 × BitVec 64} (h : Halves s S)
    (hq : ∀ j < 8, Qs s' j = Qs s j) (hs : ∀ k, slotW s' k = slotW s k) : Halves s' S :=
  ⟨h.1.congr hq, h.2.1.congr fun _ _ => hs _, h.2.2.congr fun _ _ => hs _⟩

/-- A step that changes only `x0` keeps everything. -/
theorem Ctx.flags {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ .x0 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r _ _ h3 => hg r h3) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
    simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

theorem entry_lt {g i : Nat} (hg : g ≤ 4) (hi : i ≤ 8 * g + 2) : 8 * keySlot + 64 * i < 2 ^ 64 := by
  rw [keySlot_eq]; omega

/-- The postwhitening's address stays in `x4`. -/
theorem Ctx.x4 {s₀ s : State} (hc : Ctx s₀ s) : s.gpr .x4 = s₀.gpr .x4 :=
  hc.keep _ (by decide) (by decide) (by decide)

/-- `sub t0, kp, x4`: whether `kp` is at the postwhitening's entry. -/
theorem endTest_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m ≤ 8 * g + 2) :
    ∃ s', runBlock isa [.sub .x t0 kp .x4] s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) m ∧
      (s'.gpr t0 == 0) = decide (m = 8 * g) ∧ (∀ j < 8, Qs s' j = Qs s j) ∧
      (∀ k, slotW s' k = slotW s k) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  obtain ⟨s', e', z', g', m', rd', wr'⟩ := subR_ok s t0 kp .x4
  have g'' : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r := g'
  refine ⟨s', e', hc.t0 g'' m' rd' wr', by rw [AtEntry, g'' _ (by decide)]; exact hk, ?_,
    fun j hj => g'' _ (q_ne_t0 j hj), fun k => by simp only [slotW, g'' sb (by decide), m']⟩
  rw [z', show s.gpr kp = _ from hk, hc.x4, hp.bound, show 512 * g = 64 * (8 * g) by omega,
    entry_beq _ (entry_lt hg4 hm) (entry_lt hg4 (by omega))]
  simp only [decide_eq_decide]; omega

/-- A group of six rounds, then FL and FLINV unless it is the last. -/
theorem group_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i : Nat} (hi : i < g) (hk : AtEntry s (s₀.gpr sb) (2 + 8 * i)) {S : Nat → BitVec 64 × BitVec 64}
    (hS : Halves s S) :
    WP isa groupBody s fun s' => Ctx s₀ s' ∧ Halves s' (fun b => group g E (S b) i) ∧
      AtEntry s' (s₀.gpr sb) (if i + 1 < g then 2 + 8 * (i + 1) else 8 * g) ∧
      (s'.gpr t0 == 0) = decide (i + 1 = g) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  let b := s₀.gpr sb
  -- The bound of the pairs.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := setBound_ok s
  have hc₁ : Ctx s₀ s₁ := hc.flags (fun r hr => o₁ r hr) m₁ rd₁ wr₁
  have hk₁ : AtEntry s₁ b (2 + 8 * i) := by rw [AtEntry, o₁ kp (by decide)]; exact hk
  have hrdi₁ : s₁.gpr .x0 = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 + 8 * i)) := by
    rw [r₁, show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * (2 + 8 * i) + 384 = 8 * keySlot + 64 * (8 + 8 * i) by omega]
  have hS₁ : Halves s₁ S := hS.congr (fun j hj => o₁ _ (fun h => by revert j; decide))
    (fun k => by simp only [slotW, m₁, o₁ sb (by decide)])
  unfold groupBody
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  -- The pairs.
  let Inv : Nat → State → Prop := fun n s' => ∃ p, n = 3 - p ∧ p < 3 ∧ Ctx s₀ s' ∧
    AtEntry s' b (2 + 8 * i + 2 * p) ∧ s'.gpr .x0 = s₁.gpr .x0 ∧
    Halves s' (fun b => pairsN E i p (S b))
  let Mid : State → Prop := fun s' => Ctx s₀ s' ∧ AtEntry s' b (8 + 8 * i) ∧
    Halves s' (fun b => pairsN E i 3 (S b))
  refine WP.seq (WP.mono (Q := Mid) (WP.loop Inv (fun n s' hs' => ?_) 3 s₁
    ⟨0, rfl, by omega, hc₁, by simpa using hk₁, rfl, by simpa [pairsN] using hS₁⟩) fun s₂ h₂ => ?_)
  · obtain ⟨p, rfl, hp3, hc', hk', hr', hS'⟩ := hs'
    obtain ⟨s'', e'', c'', k'', r'', S'', z''⟩ := pair_step hp.toKeyCtx hc' hk' (by omega) (by omega) hS'
    refine WP.of_runBlock ⟨s'', e'', ?_⟩
    have hz : (s''.gpr t0 == 0) = decide (p + 1 = 3) := by
      rw [z'', show s''.gpr kp = _ from k'', hr', hrdi₁, entry_beq b (entry_lt hg4 (by omega))
        (entry_lt hg4 (by omega))]
      simp only [decide_eq_decide]; omega
    have hS'' : Halves s'' (fun b => pairsN E i (p + 1) (S b)) := by
      simpa only [pairsN_succ, show 2 + 8 * i + 2 * p + 1 = 3 + 8 * i + 2 * p by omega] using S''
    by_cases hp2 : p + 1 = 3
    · refine .inl ⟨(eval_nonzero s'' t0).trans (by rw [hz]; simp [hp2]), c'', ?_, by rw [← hp2]; exact hS''⟩
      rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 8 + 8 * i by omega]
    · refine .inr ⟨(eval_nonzero s'' t0).trans (by rw [hz]; simp [hp2]), 3 - (p + 1), by omega, p + 1, rfl, by omega, c'',
        by rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 2 + 8 * i + 2 * (p + 1) by omega],
        by rw [r'', hr'], hS''⟩
  · obtain ⟨hc₂, hk₂, hS₂⟩ := h₂
    obtain ⟨s₃, e₃, hc₃, hk₃, hz₃, q₃, sl₃⟩ := endTest_ok hp hc₂ hk₂ (by omega)
    have hS₃ : Halves s₃ (fun b => pairsN E i 3 (S b)) := hS₂.congr q₃ sl₃
    refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
    refine WP.seq (WP.ite (!decide (8 + 8 * i = 8 * g)) ((eval_nonzero s₃ t0).trans (by rw [hz₃])) (fun ht => ?_)
      (fun hf => ?_))
    · have hlt : i + 1 < g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at ht; omega
      obtain ⟨s₄, e₄, c₄, k₄, -, S₄⟩ := fl_step hp.toKeyCtx hc₃ hk₃ (by omega) (by omega) hS₃
      refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
      have hk₄ : AtEntry s₄ b (2 + 8 * (i + 1)) := by
        rw [AtEntry, show s₄.gpr kp = _ from k₄, show 8 + 8 * i + 2 = 2 + 8 * (i + 1) by omega]
      obtain ⟨s₅, e₅, c₅, k₅, z₅, q₅, sl₅⟩ := endTest_ok hp c₄ hk₄ (by omega)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b =>
            (Spec.Camellia.fl (pairsN E i 3 (S b)).1 (E (8 + 8 * i)),
              Spec.Camellia.flinv (pairsN E i 3 (S b)).2 (E (8 + 8 * i + 1))) :=
          funext fun b => by
            rw [group_eq, show 8 + 8 * i + 1 = 9 + 8 * i by omega]; simp only [hlt, ↓reduceIte]
        rw [hG]
        exact S₄.congr q₅ sl₅
      · simp only [hlt, ↓reduceIte]; exact k₅
      · rw [z₅]; simp only [decide_eq_decide]; omega
    · have heq : i + 1 = g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hf; omega
      refine WP.of_runBlock ⟨s₃, rfl, ?_⟩
      obtain ⟨s₅, e₅, c₅, k₅, z₅, q₅, sl₅⟩ := endTest_ok hp hc₃ hk₃ (by omega)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b => pairsN E i 3 (S b) :=
          funext fun b => by rw [group_eq]; simp only [show ¬ i + 1 < g by omega, ↓reduceIte]
        rw [hG]
        exact hS₃.congr q₅ sl₅
      · simp only [show ¬ i + 1 < g by omega, ↓reduceIte]
        rw [show 8 * g = 8 + 8 * i by omega]; exact k₅
      · rw [z₅]; simp only [decide_eq_decide]; omega

end VG.Proof.Camellia.AArch64
