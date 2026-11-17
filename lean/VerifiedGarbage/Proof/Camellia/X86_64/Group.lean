module

public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Camellia.X86_64.Core
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Camellia.Layout
public import VerifiedGarbage.Proof.Camellia.X86_64.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym

/-! ### `Camellia.X86_64.Prologue`, which this module and modules that import it used -/

section

/-!
# Camellia ECB's prologue and epilogue on x86-64

Saving and restoring the callee-saved registers in their slots
(`save_ok`, `restore_ok`, by evaluation over names, as AES's), and setting
the masks of the layers (`setMasks_ok`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st imm setMasks)

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .rbx | 1 => .rbp | 2 => .r12 | 3 => .r13 | 4 => .r14 | _ => .r15

def saveCfg : Cfg := { base := sb, slots := tailSlot, ext := sb, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 6).find? (fun i => sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 6).all fun i => e.slot (savedSlot + i) == some i

theorem save_check : check (names 64) saveCfg (fun _ => none) saveRegs saveEnv savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none,
    slot := fun k => if savedSlot ≤ k ∧ k < savedSlot + 6 then some (k - savedSlot) else none }

def restorePost (e : Env Nat) : Bool := (List.range 6).all fun i => e.reg (sreg i) == some i

theorem restore_check :
    check (names 64) saveCfg (fun _ => none) restoreRegs restoreEnv restorePost = true := by
  decide +kernel

theorem saveCfg_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) : Ok saveCfg s :=
  Ok.of_region hw hb.symm (by simp only [saveCfg, slots]; omega_using []) (by simp [saveCfg, tailSlot_eq]) rfl

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 6, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * tailSlot⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ save_check
  let V : Nat → BitVec 64 := fun i => s.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [saveCfg] at hk)⟩
    simp only [saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (savedSlot + i) i (by simp [saveCfg, savedSlot, tailSlot]; omega_using [hi]) this
    rw [p.base] at h
    simp only [saveCfg, hb] at h
    exact h
  · have : (saveRegs.all fun i => i.dst != some r) = true := by simp [saveRegs, savedRegs, st, reduceInstrDst]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * tailSlot⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ restore_check
  let V : Nat → BitVec 64 := fun i => s₀.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [saveCfg] at hk)⟩
    simp only [restoreEnv] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hk'
      have := hs (k - savedSlot) (by omega_using [hk'])
      rw [show savedSlot + (k - savedSlot) = k by omega_using [hk']] at this
      simp only [NameRel, saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, fun r hr => p.other r ?_, ?_, p.rd, p.wr⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have : (restoreRegs.all fun i => i.dst != some r) = true := by
      have h0 := hr 0 (by omega_using []); have h1 := hr 1 (by omega_using []); have h2 := hr 2 (by omega_using [])
      have h3 := hr 3 (by omega_using []); have h4 := hr 4 (by omega_using []); have h5 := hr 5 (by omega_using [])
      simp only [sreg] at h0 h1 h2 h3 h4 h5
      simp [restoreRegs, savedRegs, movS, reduceInstrDst, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3,
        Ne.symm h4, Ne.symm h5]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

/-! ## The masks -/

/-- `mov t0, v; mov [sb + 8 k], t0`. -/
theorem setOne_ok {s : State} {b : Addr} {k : Nat} (v : BitVec 64) (hb : s.gpr sb = b)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa [imm t0 v, st k t0] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) v ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' : InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 := hw
  refine ⟨{ s.setReg t0 v with mem := s.mem.writeW (wordAddr b k) v }, ?_, rfl,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  simp only [imm, st, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, State.ea, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ sb_ne_t0,
    RegUpd.wr_setReg, ofInt_nat, hb, hw', ite_true, RegUpd.mem_setReg]

theorem setMasks_ok (ms : List (Nat × BitVec 64)) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : ∀ kv ∈ ms, kv.1 < keySlot)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setMasks ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * keySlot⟩] s.mem s'.mem := by
  induction ms generalizing s with
  | nil => exact ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | cons kv ms ih =>
    have hk0 : kv.1 < keySlot := hk kv List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := setOne_ok (k := kv.1) kv.2 hb ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [slots_eq, keySlot_eq] at *; omega_using [hk0])
        (by rw [keySlot_eq] at hk0; omega_using [hk0])⟩
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
        exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hk']) (by rw [keySlot_eq] at hk0; omega_using [hk0]) h) (by decide)
    refine ⟨s', by
      rw [show setMasks (kv :: ms) = [imm t0 kv.2, st kv.1 t0] ++ setMasks ms from rfl,
        runBlock_append', e₁, Option.bind_some, e'], fun x hx => ?_, fun k hk' hn => ?_,
      fun r hr => by rw [g' r hr, g₁ r hr], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [k' _ (by rw [slots_eq, keySlot_eq] at *; omega_using [hk0]) hnot, hslot _ (by rw [slots_eq, keySlot_eq] at *; omega_using [hk0]),
          ite_eq_left rfl]
      · exact v' x hx
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' k hk' hn.2, hslot k hk', ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      rw [m₁]
      simp only [Mem.writeW, Mem.write, wordAddr]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * kv.1 + 8 ≤ 8 * keySlot by omega_using [hk0]) _ (by simp only [Region.Contains]; omega_using [h]))

end VG.Proof.Camellia.X86_64

end

end

/-! ### `Camellia.X86_64.Keys`, which this module and modules that import it used -/

section

/-! ### `Camellia.X86_64.KeyChecks`, which this module and modules that import it used -/

section

/-!
# Bitslicing a subkey on x86-64, by evaluation

`keyOne d` loads the subkey at `[rdi + d]` into all eight state registers,
bitslices them as `toBs` does eight blocks' halves (`keyLoad`), and stores
the planes to the entry at `rsi` (`keyStore`). Both are checked over the
lane domain: the subkey is input word `d / 8` (words of `rdi`), and the
planes are input words `0 … 7` of the stores.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia (pos)

/-- The masks' slots below the table; the subkeys at `rdi`, of which `n` words are read. -/
def keyCfg (n : Nat) : Cfg := { base := sb, slots := keySlot, ext := .rdi, exts := n }

def keyLoad (d : Nat) : List Instr :=
  [.mov (q 0) (.mem (at_ .rdi d))] ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

def keyStore : List Instr := (List.range 8).map fun j => .store (slotAt .rsi j) (q j)

theorem keyOne_eq (d : Nat) : keyOne d = keyLoad d ++ keyStore ++ ([.alu .add .rsi (.imm 64)] : List Instr) := by
  simp only [keyOne, keyLoad, keyStore, List.append_assoc]

def keyEnv : Env (Nat × Nat) := linEnvG [] [] layerMasks

/-- Plane `j` of the subkey: bit `8 c + b` is bit `j` of its byte `pos c`. -/
def keyBsG (d j p : Nat) : List Nat := [64 * (d / 8) + 8 * pos (p / 8) + j]

theorem keyLoad0_check :
    check (lanes 64 7) (keyCfg 1) (linExt 0) (keyLoad 0) keyEnv
      (linPostG 7 (qOuts (keyBsG 0)) [] maskSlots keyEnv) = true := by
  decide +kernel

theorem keyLoad8_check :
    check (lanes 64 7) (keyCfg 2) (linExt 0) (keyLoad 8) keyEnv
      (linPostG 7 (qOuts (keyBsG 8)) [] maskSlots keyEnv) = true := by
  decide +kernel

/-- The entry at `rsi`. -/
def entryCfg : Cfg := { base := .rsi, slots := 8, ext := .rsi, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64

end

end

/-! ### `Camellia.X86_64.Crypt8`, which this module and modules that import it used -/

section

/-!
# The head and tail of eight blocks of bitsliced Camellia on x86-64

`head` loads and bitslices both halves of the eight blocks at `rdx` and
whitens them, and `tail` whitens, transposes and stores them back; between
them the groups of rounds (`group_wp`) run in a loop. `crypt8_ok` composes
them: each block becomes `cryptWords g E` of it.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)
open VG.Proof.Camellia (HalfRel WordRel pair group groups cryptWords toBsG fromBsG pos cpos)

theorem ok_data {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    Ok dataCfg s where
  slotIn k hk := by
    simp only [dataCfg] at hk ⊢
    rw [hc.rdx, hc.wr]; exact hp.dat k hk
  extIn k hk := by simp [dataCfg] at hk
  slots := by simp [dataCfg]
  sep k _ j hj := by simp [dataCfg] at hj

/-- A frame of the blocks keeps the scratch buffer. -/
theorem slotW_of_data {s₀ s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) (hb : s'.gpr sb = s.gpr sb) (hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem)
    {k : Nat} (hk : k < tailSlot) : slotW s' k = slotW s k := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  rw [tailSlot_eq] at hk
  simp only [slotW, wordAddr, hb, hc.base]
  refine hf.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [hc.rdx]
  refine (hp.sep.sub_right (VG.Offset.sub_base _ ?_)).symm
  rw [tailSlot_eq]; omega_arith

/-- A step that writes the blocks only. -/
theorem Ctx.data {s₀ s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem) : Ctx s₀ s' := by
  refine hc.step hrd hwr (fun r h1 _ _ => hg r h1) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [hc.rdx]) fun kv hkv => ?_
  have hlt : kv.1 < tailSlot := by
    simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;> rw [tailSlot_eq] <;>
      simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
  rw [slotW_of_data hp hc (hg _ (by decide)) hf hlt]
  exact hc.masks kv hkv

/-! ## The steps -/

/-- `loadWords h`. -/
theorem loadWords_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1)
    (hchk : check (lanes 64 10) dataCfg (linExt 0) (loadWords h) dataEnv
      (linPostG 10 (qOuts (loadG h)) [] (dataIns.map (·.1)) dataEnv) = true) :
    ∃ s', runBlock isa (loadWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ b < 8, Qs s' b = dataW s (2 * b + h)) ∧
      (∀ k < tailSlot, slotW s' k = slotW s k) ∧ (∀ k < 16, dataW s' k = dataW s k) := by
  unfold dataEnv at hchk
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_data hp hc) (dataW s)
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [dataIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      exact ⟨by simp only [dataCfg]; omega_arith, by omega_arith, rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [dataCfg] at hj)
  simp only [dataCfg] at hb' hkp f'
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (loadWords h).all fun i => i.dst != some r) =
      true := by rcases hh with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem := by
    simpa only [slotRegion, dataCfg] using f'
  refine ⟨s', h', hc.data hp rd' wr' hkeep hf, hkeep _ (by decide), hkeep _ (by decide), fun b hb => ?_,
    fun k hk => slotW_of_data hp hc (hkeep _ (by decide)) hf hk, fun k hk => ?_⟩
  · refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
    rw [Qs, ho (q b) (loadG h b) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
      p hp, loadG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp]
  · show s'.mem.readW (wordAddr (s'.gpr .rdx) k) 64 = _
    rw [hkeep .rdx (by decide)]
    exact hkp k (by simp only [dataIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩)
      hk

theorem mask_lt {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : kv.1 < keySlot := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

/-- A layer on the state registers over `bothEnv`, keeping the masks and both halves. -/
theorem lin_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) {is : List Instr} {G : Nat → Nat → List Nat}
    (hchk : check (lanes 64 12) layerCfg (linExt 24) is bothEnv
      (linPostG 12 (qOuts G) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true)
    (hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => is.all fun i => i.dst != some r) = true) :
    ∃ s', runBlock isa is s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (G j p)) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧ (∀ k < 16, dataW s' k = dataW s k) := by
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide),
    fun j hj p hp => ho (q j) (G j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
    fun j hj => hkp _ (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, keySlot]; omega_arith),
    fun k hk => dataW_of_scr hp hc (hkeep _ (by decide)) f' hk⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (mask_lt hkv)]
  exact hc.masks kv hkv

/-- `storeWords h`. -/
theorem storeWords_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1)
    (hchk : check (lanes 64 11) dataCfg (linExt 0) (storeWords h) storeEnv
      (linPostG 11 [] (storeOuts h) (otherWords h) storeEnv) = true) :
    ∃ s', runBlock isa (storeWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr = s.gpr ∧
      (∀ b < 8, dataW s' (2 * b + h) = Qs s b) ∧ (∀ b < 8, dataW s' (2 * b + (1 - h)) = dataW s (2 * b + (1 - h))) ∧
      (∀ k < tailSlot, slotW s' k = slotW s k) := by
  unfold storeEnv at hchk
  let W : Nat → BitVec 64 := fun i => if i < 8 then Qs s i else dataW s (i - 8)
  obtain ⟨s', h', -, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_data hp hc) W
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W, hi]⟩)
    (fun j i hji => by
      simp only [storeIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      exact ⟨by simp only [dataCfg]; omega_arith, by omega_arith, by simp only [W, show ¬ 8 + j < 8 by omega_arith, ↓reduceIte, show 8 + j - 8 = j by omega_arith]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [dataCfg] at hj)
  simp only [dataCfg] at hb' hkp hso f'
  have hall : ∀ r, ((storeWords h).all fun i => i.dst != some r) = true := fun r => by
    rcases hh with rfl | rfl <;> simp [storeWords, reduceInstrDst]
  have hg : s'.gpr = s.gpr := funext fun r => o' r (hall r)
  have hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem := by
    simpa only [slotRegion, dataCfg] using f'
  refine ⟨s', h', hc.data hp rd' wr' (fun r _ => by rw [hg]) hf, hg, fun b hb => ?_, fun b hb => ?_,
    fun k hk => slotW_of_data hp hc (by rw [hg]) hf hk⟩
  · refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
    show (s'.mem.readW (wordAddr (s'.gpr .rdx) _) 64).getLsbD p = _
    rw [hg, hso (2 * b + h) (idG b) (by simp only [storeOuts, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
      (by omega_arith) p hp, idG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp]
    simp [W, hb]
  · show s'.mem.readW (wordAddr (s'.gpr .rdx) _) 64 = _
    rw [hg]
    exact hkp _ (by simp only [otherWords, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩) (by omega_arith)

/-! ## Transposes -/

theorem toBs_rel {s s' : State} {d : Nat → BitVec 64}
    (h : ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (toBsG j p)) (hw : WordRel (Qs s) d) :
    HalfRel (Qs s') d :=
  Camellia.half_of_words (fun j hj p hp => by
    have := Camellia.pos_lt (show p / 8 < 8 by omega_arith)
    rw [h j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
      bitOf_word _ _ _ (by omega_arith), bothW_q s (by omega_arith)]) hw

theorem fromBs_rel {s s' : State} {d : Nat → BitVec 64}
    (h : ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (fromBsG j p)) (hq : HalfRel (Qs s) d) :
    WordRel (Qs s') d :=
  Camellia.words_of_half (fun b hb t ht => by
    have := Camellia.cpos_lt (show t / 8 < 8 by omega_arith)
    rw [h b hb t ht, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
      bitOf_word _ _ _ (by omega_arith), bothW_q s (by omega_arith)]) hq

/-- Block `b` at `rdx`. -/
abbrev blk (s : State) (b : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * b))

theorem dataW_byte (s : State) {b i j : Nat} (h : Nat) (hi : i < 8) (hj : j < 8) :
    (dataW s (2 * b + h)).getLsbD (8 * i + j) =
      (s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (8 * h + i))).getLsbD j := by
  rw [readW64_bit _ _ hi hj, wordAddr, addr_add, addr_add,
    show 8 * (2 * b + h) + i = 16 * b + (8 * h + i) by omega_arith]

theorem data_hi (s : State) : WordRel (fun b => dataW s (2 * b + 0))
    (fun b => (Spec.Camellia.decodeBlock (blk s b) >>> 64).setWidth 64) := fun b _ i hi j hj => by
  rw [dataW_byte s 0 hi hj, Camellia.byteOf_hi _ hi]
  simp [Spec.Camellia.blockAt]

theorem data_lo (s : State) : WordRel (fun b => dataW s (2 * b + 1))
    (fun b => (Spec.Camellia.decodeBlock (blk s b)).setWidth 64) := fun b _ i hi j hj => by
  rw [dataW_byte s 1 hi hj, Camellia.byteOf_lo _ hi]
  simp [Spec.Camellia.blockAt, Nat.add_comm]

theorem bothW_key (s : State) (j : Nat) : bothW s (24 + j) = keyW s j := by
  simp only [bothW, show ¬ 24 + j < 8 by omega_arith, show ¬ 24 + j < 24 by omega_arith, ↓reduceIte,
    show 24 + j - 24 = j by omega_arith]

theorem bothW_d2 (s : State) {j : Nat} (hj : j < 8) : bothW s (16 + j) = slotW s (d2Slot + j) := by
  simp only [bothW, show ¬ 16 + j < 8 by omega_arith, show 16 + j < 24 by omega_arith, ↓reduceIte,
    show d1Slot + (16 + j - 8) = d2Slot + j by simp only [d1Slot, d2Slot]; omega_arith]

/-- `mov kp, sb; add kp, 8 keySlot`. -/
theorem setKp_ok (s : State) :
    ∃ s', runBlock isa [movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] s = some s' ∧
      s'.gpr kp = s.gpr sb + BitVec.ofNat 64 (8 * keySlot) ∧ (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.map_some]; rfl, ?_, fun r hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The whitening. -/
theorem whiten_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa whiten s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      (∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s j).getLsbD p)) ∧
      (∀ j < 8, ∀ p < 64, (slotW s' (d1Slot + j)).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s j).getLsbD p)) ∧
      (∀ j < 8, ∀ p < 64, (slotW s' (d2Slot + j)).getLsbD p =
        ((slotW s (d2Slot + j)).getLsbD p ^^ (keyW s (8 + j)).getLsbD p)) := by
  obtain ⟨s', h', ho, hso, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 whiten_check
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => whiten.all fun i => i.dst != some r) =
      true := by decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), fun j hj p hp => ?_, fun j hj p hp => ?_, fun j hj p hp => ?_⟩
  · rw [hkp kv.1 (List.mem_map_of_mem hkv) (mask_lt hkv)]
    exact hc.masks kv hkv
  · rw [Qs, ho (q j) (keyXorG 0 j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      keyXorG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      Nat.add_assoc, bitOf_word _ _ _ hp, bothW_q s hj, Nat.zero_add, bothW_key]
  · rw [hso (d1Slot + j) (keyXorG 0 j) (List.mem_append_left _ (by
        simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) (by simp only [d1Slot, keySlot]; omega_arith) p hp,
      keyXorG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      Nat.add_assoc, bitOf_word _ _ _ hp, bothW_q s hj, Nat.zero_add, bothW_key]
  · rw [hso (d2Slot + j) (whiten2G j) (List.mem_append_right _ (by
        simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) (by simp only [d2Slot, keySlot]; omega_arith) p hp,
      whiten2G, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bothW_d2 s hj, show 32 + j = 24 + (8 + j) by omega_arith, bothW_key]

/-! ## The head -/

/-- The halves of the eight blocks after the prewhitening. -/
def headHalves (s : State) (E : Nat → BitVec 64) (b : Nat) : BitVec 64 × BitVec 64 :=
  ((Spec.Camellia.decodeBlock (blk s b) >>> 64).setWidth 64 ^^^ E 0,
    (Spec.Camellia.decodeBlock (blk s b)).setWidth 64 ^^^ E 1)

theorem head_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    ∃ s', runBlock isa head s₀ = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) 2 ∧
      Halves s' (headHalves s₀ E) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  have hc₀ : Ctx s₀ s₀ := Ctx.refl hp.masks
  let b := s₀.gpr sb
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  have hc₁ : Ctx s₀ s₁ := hc₀.step rd₁ wr₁ (fun r _ h2 _ => o₁ r h2) (by rw [m₁]; exact Frame.refl _ _)
    (fun kv hkv => by simp only [slotW, m₁, o₁ sb (by decide)]; exact hp.masks kv hkv)
  have hk₁ : AtEntry s₁ b 0 := by rw [AtEntry, k₁, Nat.mul_zero, Nat.add_zero]
  have hd₁ : ∀ k, dataW s₁ k = dataW s₀ k := fun k => by
    show s₁.mem.readW (wordAddr (s₁.gpr .rdx) k) 64 = _
    rw [m₁, o₁ .rdx (by decide)]
  -- `D2`.
  obtain ⟨s₂, e₂, c₂, k₂, -, q₂, -, d₂⟩ := loadWords_step hp.toKeyCtx hc₁ (Or.inr rfl) loadWords1_check
  have hk₂ : AtEntry s₂ b 0 := by rw [AtEntry, k₂]; exact hk₁
  obtain ⟨s₃, e₃, c₃, k₃, -, q₃, -, d₃⟩ := lin_step hp.toKeyCtx c₂ hk₂ (by omega_arith) toBs_check (by decide +kernel)
  have hk₃ : AtEntry s₃ b 0 := by rw [AtEntry, k₃]; exact hk₂
  have hD2 : HalfRel (Qs s₃) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b)).setWidth 64) :=
    toBs_rel q₃ fun b' hb i hi j hj => by rw [q₂ b' hb, hd₁]; exact data_lo s₀ b' hb i hi j hj
  obtain ⟨s₄, e₄, c₄, k₄, -, -, sl₄, hh₄, d₄⟩ :=
    storeHalf_step hp.toKeyCtx c₃ (Or.inr rfl) storeHalf2_check hk₃ (by omega_arith)
  have hk₄ : AtEntry s₄ b 0 := by rw [AtEntry, k₄]; exact hk₃
  -- `D1`.
  obtain ⟨s₅, e₅, c₅, k₅, -, q₅, sw₅, -⟩ := loadWords_step hp.toKeyCtx c₄ (Or.inl rfl) loadWords0_check
  have hk₅ : AtEntry s₅ b 0 := by rw [AtEntry, k₅]; exact hk₄
  obtain ⟨s₆, e₆, c₆, k₆, -, q₆, h₆, -⟩ := lin_step hp.toKeyCtx c₅ hk₅ (by omega_arith) toBs_check (by decide +kernel)
  have hk₆ : AtEntry s₆ b 0 := by rw [AtEntry, k₆]; exact hk₅
  have hD1 : HalfRel (Qs s₆) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b) >>> 64).setWidth 64) :=
    toBs_rel q₆ fun b' hb i hi j hj => by
      rw [q₅ b' hb, d₄ _ (by omega_arith), d₃ _ (by omega_arith), d₂ _ (by omega_arith), hd₁]
      exact data_hi s₀ b' hb i hi j hj
  have hS₆ : HalfRel (fun j => slotW s₆ (d2Slot + j)) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b)).setWidth 64) :=
    hD2.congr fun j hj => by
      have h1 := h₆ (8 + j) (by omega_arith)
      rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega_arith] at h1
      rw [h1, sw₅ _ (by simp only [tailSlot_eq, d2Slot]; omega_arith), sl₄ j hj]
  -- The whitening.
  obtain ⟨s₇, e₇, c₇, k₇, wq, w1, w2⟩ := whiten_step hp.toKeyCtx c₆ hk₆ (by omega_arith)
  have hK0 := c₆.keyRel hp.toKeyCtx hk₆ (e := 0) (by omega_arith)
  have hK1 := c₆.keyRel hp.toKeyCtx hk₆ (e := 1) (by omega_arith)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hK0 hK1
  obtain ⟨s₈, e₈, kp₈, o₈, m₈, rd₈, wr₈⟩ := addKp_ok s₇ 128 (by decide)
  have hs₈ : ∀ k, slotW s₈ k = slotW s₇ k := fun k => by simp only [slotW, m₈, o₈ sb (by decide)]
  refine ⟨s₈, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [head, runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      e₄, Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some]
    exact e₈
  · refine c₇.step rd₈ wr₈ (fun r _ h2 _ => o₈ r h2) (by rw [m₈]; exact Frame.refl _ _) fun kv hkv => ?_
    rw [hs₈]; exact c₇.masks kv hkv
  · rw [AtEntry, kp₈, k₇, show s₆.gpr kp = _ from hk₆, addr_add]
  · exact (HalfRel.xor_key hD1 hK0 wq).congr fun j hj => o₈ _ (q_ne_kp j hj)
  · exact (HalfRel.xor_key hD1 hK0 w1).congr fun j _ => hs₈ _
  · exact (HalfRel.xor_key hS₆ hK1 w2).congr fun j _ => hs₈ _

/-! ## The tail -/

theorem keyXor_bits {s s' : State} {off : Nat}
    (h : ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (keyXorG off j p)) :
    ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s (off + j)).getLsbD p) :=
  fun j hj p hp => by
    rw [h j hj p hp, keyXorG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bothW_q s hj, Nat.add_assoc, bothW_key]

theorem tail_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) (8 * g)) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa tail s = some s' ∧ Ctx s₀ s' ∧
      WordRel (fun b => dataW s' (2 * b + 0)) (fun b => (S b).2 ^^^ E (8 * g)) ∧
      WordRel (fun b => dataW s' (2 * b + 1)) (fun b => (S b).1 ^^^ E (8 * g + 1)) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  let b := s₀.gpr sb
  obtain ⟨hq, -, h2⟩ := hS
  have hK1 := hc.keyRel hp.toKeyCtx hk (e := 1) (by omega_arith)
  simp only [Nat.mul_one] at hK1
  -- The right halves.
  obtain ⟨s₁, e₁, c₁, k₁, -, q₁, h₁, -⟩ := lin_step hp.toKeyCtx hc hk (by omega_arith) keyXor8_check (by decide +kernel)
  have hk₁ : AtEntry s₁ b (8 * g) := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, -, q₂, h₂, -⟩ := lin_step hp.toKeyCtx c₁ hk₁ (by omega_arith) fromBs_check (by decide +kernel)
  have hk₂ : AtEntry s₂ b (8 * g) := by rw [AtEntry, k₂]; exact hk₁
  have hW1 : WordRel (Qs s₂) (fun b => (S b).1 ^^^ E (8 * g + 1)) :=
    fromBs_rel q₂ (HalfRel.xor_key hq hK1 (keyXor_bits q₁))
  obtain ⟨s₃, e₃, c₃, g₃, w₃, -, sl₃⟩ := storeWords_step hp.toKeyCtx c₂ (Or.inr rfl) storeWords1_check
  have hk₃ : AtEntry s₃ b (8 * g) := by rw [AtEntry, g₃]; exact hk₂
  -- The left halves.
  obtain ⟨s₄, e₄, c₄, k₄, -, q₄, -, d₄⟩ := lin_step hp.toKeyCtx c₃ hk₃ (by omega_arith) loadHalf2_check (by decide +kernel)
  have hk₄ : AtEntry s₄ b (8 * g) := by rw [AtEntry, k₄]; exact hk₃
  have hD2 : HalfRel (Qs s₄) (fun b => (S b).2) := h2.congr fun j hj =>
    BitVec.eq_of_getLsbD_eq fun p hp => by
      have e₂ := h₂ (8 + j) (by omega_arith)
      have e₁ := h₁ (8 + j) (by omega_arith)
      rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega_arith] at e₁ e₂
      rw [q₄ j hj p hp, loadHalfG, xorBits_cons, xorBits_nil,
        Bool.xor_false, bitOf_word _ _ _ hp, bothW_half s₃ (Or.inr rfl) hj,
        sl₃ _ (by simp only [tailSlot_eq, d2Slot]; omega_arith), e₂, e₁]
  obtain ⟨s₅, e₅, c₅, k₅, -, q₅, -, d₅⟩ := lin_step hp.toKeyCtx c₄ hk₄ (by omega_arith) keyXor0_check (by decide +kernel)
  have hk₅ : AtEntry s₅ b (8 * g) := by rw [AtEntry, k₅]; exact hk₄
  have hK0' := c₄.keyRel hp.toKeyCtx hk₄ (e := 0) (by omega_arith)
  simp only [Nat.mul_zero, Nat.add_zero] at hK0'
  obtain ⟨s₆, e₆, c₆, -, -, q₆, -, d₆⟩ := lin_step hp.toKeyCtx c₅ hk₅ (by omega_arith) fromBs_check (by decide +kernel)
  have hW0 : WordRel (Qs s₆) (fun b => (S b).2 ^^^ E (8 * g)) :=
    fromBs_rel q₆ (HalfRel.xor_key hD2 hK0' (by simpa only [Nat.zero_add] using keyXor_bits q₅))
  obtain ⟨s₇, e₇, c₇, -, w₇, o₇, -⟩ := storeWords_step hp.toKeyCtx c₆ (Or.inl rfl) storeWords0_check
  refine ⟨s₇, ?_, c₇, fun b' hb i hi j hj => ?_, fun b' hb i hi j hj => ?_⟩
  · rw [tail, runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some, e₄,
      Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some]
    exact e₇
  · show (dataW s₇ (2 * b' + 0)).getLsbD _ = _
    rw [w₇ b' hb]; exact hW0 b' hb i hi j hj
  · have := o₇ b' hb
    simp only [Nat.sub_zero] at this
    show (dataW s₇ (2 * b' + 1)).getLsbD _ = _
    rw [this, d₆ _ (by omega_arith), d₅ _ (by omega_arith), d₄ _ (by omega_arith), w₃ b' hb]
    exact hW1 b' hb i hi j hj

/-! ## The groups -/

theorem groups_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) 2) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    WP isa (.loop groupBody .ne) s fun s' => Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (8 * g) ∧
      Halves s' (fun b => groups g E (S b)) := by
  have hg0 : 0 < g := by rcases hp.hg with h | h <;> omega_arith
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = g - i ∧ i < g ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (2 + 8 * i) ∧ Halves s' (fun b => groupsN g E i (S b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) g s ⟨0, by omega_arith, hg0, hc, hk, by simpa [groupsN] using hS⟩
  obtain ⟨i, rfl, hi, hc', hk', hS'⟩ := hs'
  refine WP.mono (group_wp hp hc' hi hk' hS') fun s'' ⟨c'', S'', k'', z''⟩ => ?_
  simp only [← groupsN_succ] at S''
  by_cases he : i + 1 = g
  · refine .inl ⟨by simp [X86_64.eval, z'', he], c'', ?_, ?_⟩
    · simpa only [show ¬ i + 1 < g by omega_arith, ↓reduceIte] using k''
    · have hG : ∀ d, groupsN g E (i + 1) d = groups g E d := fun d => by rw [he]; rfl
      simpa only [hG] using S''
  · refine .inr ⟨by simp [X86_64.eval, z'', he], g - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, c'', ?_, S''⟩
    simpa only [show i + 1 < g by omega_arith, ↓reduceIte] using k''

/-! ## Eight blocks -/

theorem blk_of_words {s : State} {b : Nat} {hi lo : BitVec 64}
    (h0 : ∀ i < 8, ∀ j < 8, (dataW s (2 * b + 0)).getLsbD (8 * i + j) = (Camellia.byteOf hi i).getLsbD j)
    (h1 : ∀ i < 8, ∀ j < 8, (dataW s (2 * b + 1)).getLsbD (8 * i + j) = (Camellia.byteOf lo i).getLsbD j) :
    blk s b = Spec.Camellia.encodeBlock (hi ++ lo) := by
  apply Vector.ext
  intro i hi16
  rw [Camellia.encodeBlock_getElem _ _ hi16]
  simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
  split
  · rename_i h8
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← h0 i h8 j hj, dataW_byte s 0 h8 hj, show 8 * 0 + i = i by omega_arith]
  · rename_i h8
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← h1 (i - 8) (by omega_arith) j hj, dataW_byte s 1 (by omega_arith) hj, show 8 * 1 + (i - 8) = i by omega_arith]

/-- `crypt8`: each of the eight blocks at `rdx` becomes `cryptWords g E` of it. -/
theorem crypt8_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, k₁, S₁⟩ := head_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (groups_wp hp c₁ k₁ S₁) fun s₂ ⟨c₂, k₂, S₂⟩ => ?_)
  obtain ⟨s₃, e₃, c₃, w0, w1⟩ := tail_ok hp c₂ k₂ S₂
  refine WP.of_runBlock ⟨s₃, e₃, c₃, fun b hb => ?_⟩
  rw [cryptWords]
  refine (blk_of_words (fun i hi j hj => w0 b hb i hi j hj) (fun i hi j hj => w1 b hb i hi j hj)).trans ?_
  rfl

end VG.Proof.Camellia.X86_64

end

end

/-!
# The table of bitsliced subkeys on x86-64

`keyOne_step`: `keyOne d` bitslices the subkey at `[rdi + d]` (its eight
bytes, the most significant first: `wordAt`) into the table's entry at
`rsi`, every block's copy of it alike, and steps `rsi` to the next entry.
`encKeys_wp` and `decKeys_wp` build the table in the order the rounds use
the subkeys: for encryption the stored order, for decryption `decPerm`'s.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia (HalfRel WordRel pos)

/-- The table's entry `e` holds `k` for every block. -/
abbrev EntryOk (m : Mem) (b : Addr) (e : Nat) (k : BitVec 64) : Prop := HalfRel (entryW m b e) fun _ => k

theorem keyOne_step {s : State} {b : Addr} {d e : Nat} (hd : d = 0 ∨ d = 8)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hrsi : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hrdi : ∀ k < d / 8 + 1, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .rdi) k) 8)
    (hsep : ∀ k < keySlot, ∀ j < d / 8 + 1, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .rdi) j) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ (∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] s.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d)) := by
  rw [slots_eq] at hscr
  obtain hok : Ok (keyCfg (d / 8 + 1)) s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg, keySlot_eq] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => hrdi k (by simpa [keyCfg] using hk)
      slots := by simp [keyCfg, keySlot_eq]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; rw [hb]; exact hsep k hk j hj }
  obtain hchk : check (lanes 64 7) (keyCfg (d / 8 + 1)) (linExt 0) (keyLoad d) keyEnv
      (linPostG 7 (qOuts (keyBsG d)) [] maskSlots keyEnv) = true := by
    rcases hd with rfl | rfl
    · exact keyLoad0_check
    · exact keyLoad8_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkp₁, rd₁, wr₁, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .rdi) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by
      simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega_arith, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₁ hkp₁ f₁
  obtain hall₁ : ∀ r, r ∉ sboxWrites → ((keyLoad d).all fun i => i.dst != some r) = true := fun r hr => by
    obtain h := not_sboxWrites r hr
    have : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (keyLoad d).all fun i => i.dst != some r) =
        true := by rcases hd with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r h
  obtain k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s.gpr r := fun r hr => o₁ r (hall₁ r hr)
  -- The planes of the subkey.
  obtain hQ : HalfRel (Qs s₁) (fun _ => Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d)) := by
    obtain hw := wordRel_key s.mem (s.gpr .rdi + BitVec.ofNat 64 d)
    refine Camellia.half_of_words (W := fun _ => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 64)
      (fun j hj p hp => ?_) hw
    have := Camellia.pos_lt (show p / 8 < 8 by omega_arith)
    rw [Qs, ho₁ (q j) (keyBsG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ (by omega_arith)]
    rcases hd with rfl | rfl <;> rfl
  -- The stores.
  obtain hrsi₁ : s₁.gpr .rsi = s.gpr .rsi := k₁ .rsi (by decide)
  obtain hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hrsi₁, show s.gpr .rsi = _ from hrsi, wordAddr, addr_add]
        exact VG.Offset.contains_base b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  obtain hall₂ : ∀ r, (keyStore.all fun i => i.dst != some r) = true := fun r => by
    simp [keyStore, reduceInstrDst]
  obtain k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (hall₂ r)
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 64 (by decide)
  obtain he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    obtain h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hrsi₁, show s.gpr .rsi = _ from hrsi, addr_add]
  obtain ht1 : s₁.gpr t1 = s.gpr t1 := o₁ t1 (by rcases hd with rfl | rfl <;> decide +kernel)
  refine ⟨s₃, ?_, ?_, fun r h1 h2 => ?_, by rw [o₃ t1 (by decide), k₂, ht1], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun kv hkv => ?_,
    ?_, ?_⟩
  · rw [keyOne_eq, runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some]
    exact e₃
  · rw [kp₃, show s₂.gpr kp = s₁.gpr kp from k₂ _, show s₁.gpr kp = s.gpr kp from hrsi₁]
  · rw [o₃ r h2, k₂, k₁ r h1]
  · have hk : kv.1 < keySlot := mask_lt hkv
    show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    obtain h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hrsi₁, show s.gpr .rsi = _ from hrsi, hb, wordAddr]
      exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq] at hk ⊢; omega_arith)) (by rw [keySlot_eq] at hk; omega_arith)
        (by rw [keySlot_eq]; omega_arith)
    rw [m₃, o₃ sb (by decide), k₂, hb₁, h2, hkp₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · rw [m₃]
    refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hrsi₁, show s.gpr .rsi = _ from hrsi]
  · refine hQ.congr fun j hj => ?_
    show entryW s₃.mem b e j = _
    rw [m₃]; exact he₂ j hj

end VG.Proof.Camellia.X86_64

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)

/-! ## Steps of the pointers and the counter -/

theorem addImm_ok (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .add r (.imm v)] s = some s' ∧
      s'.gpr r = s.gpr r + v.signExtend 64 ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem subImm_ok (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .sub r (.imm v)] s = some s' ∧
      s'.gpr r = s.gpr r - v.signExtend 64 ∧ s'.zf = some (s.gpr r - v.signExtend 64 == 0) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, by rfl, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]


/-! ## The loops -/

/-- The scratch buffer at `b` and the schedule's 34 words at `sched`, apart. -/
structure KeyPre (s : State) (b sched : Addr) : Prop where
  base : s.gpr sb = b
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  sch : (⟨sched, 272⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 272 ≤ 2 ^ 64
  sep : Region.Disjoint ⟨sched, 272⟩ ⟨b, 8 * slots⟩

theorem KeyPre.congr {s s' : State} {b sched : Addr} (h : KeyPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KeyPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

theorem KeyPre.word {s : State} {b sched : Addr} (h : KeyPre s b sched) {w j : Nat} (hw : w + j < 34) :
    InRegions (s.rd ++ s.wr) (wordAddr (sched + BitVec.ofNat 64 (8 * w)) j) 8 :=
  ⟨_, h.sch, by rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)⟩

theorem KeyPre.wsep {s : State} {b sched : Addr} (h : KeyPre s b sched) {w j : Nat} (hw : w + j < 34)
    {k : Nat} (hk : k < slots) :
    Mem.Sep (wordAddr b k) 8 (wordAddr (sched + BitVec.ofNat 64 (8 * w)) j) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf hk
  refine h.sep.symm.sep (VG.Offset.contains_base b (by rw [slots_eq]; omega_arith) (by omega_arith)) ?_
  rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)

/-- The schedule is outside the scratch buffer. -/
theorem KeyPre.wordAt_eq {s : State} {b sched : Addr} (h : KeyPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨b, 8 * n⟩] m m') {w : Nat} (hw : w < 34) :
    Spec.Camellia.wordAt m' (sched + BitVec.ofNat 64 (8 * w)) =
      Spec.Camellia.wordAt m (sched + BitVec.ofNat 64 (8 * w)) := by
  refine wordAt_frame hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact (h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] m m')
    (hi : i < 34) (he : e < 34) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
  · exact VG.Offset.disjoint b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
      (by rw [keySlot_eq]; omega_arith)

/-- What the loops keep, after `k` of their `N` iterations: the subkeys `F`
in the entries before `e₀ + k`, `rdi` at word `wk k` of the schedule. -/
structure KeyInv (s₀ : State) (b sched : Addr) (e₀ N : Nat) (wk : Nat → Nat) (F : Nat → BitVec 64)
    (k : Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  rsi : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k))
  rdi : s.gpr .rdi = sched + BitVec.ofNat 64 (8 * wk k)
  cnt : s.gpr t1 = BitVec.ofNat 64 (N - k)
  ent : ∀ i < e₀ + k, EntryOk s.mem b i (F i)
  masks : MasksOk s
  frame : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop of `keyOne 0` and `op rdi, 8` (`f` on `rdi`), counted down in `t1`. -/
theorem keyLoop_wp {s₀ s : State} {b sched : Addr} {e₀ N : Nat} {wk : Nat → Nat} {F : Nat → BitVec 64}
    {op : AluOp} {f : Addr → Addr}
    (hop : ∀ s : State, ∃ s', runBlock isa [.alu op .rdi (.imm 8)] s = some s' ∧
      s'.gpr .rdi = f (s.gpr .rdi) ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (hN : e₀ + N ≤ 34) (hNw : N < 2 ^ 32)
    (hwk : ∀ k < N, wk k < 34)
    (hstep : ∀ k < N, f (sched + BitVec.ofNat 64 (8 * wk k)) = sched + BitVec.ofNat 64 (8 * wk (k + 1)))
    (hF : ∀ k < N, F (e₀ + k) = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * wk k)))
    {k : Nat} (hk : k < N) (hs : KeyInv s₀ b sched e₀ N wk F k s) :
    WP isa (.loop (.block (keyOne 0 ++ ([.alu op .rdi (.imm 8), .alu .sub t1 (.imm 1)] : List Instr))) .ne) s
      (KeyInv s₀ b sched e₀ N wk F N) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = N - k ∧ k < N ∧ KeyInv s₀ b sched e₀ N wk F k s)
    (fun n s hs => ?_) (N - k) s ⟨k, rfl, hk, hs⟩
  obtain ⟨k, rfl, hk, hi⟩ := hs
  have hfit := hi.pre.fit
  obtain hw := hwk k hk
  have hrdi := hi.rdi
  obtain ⟨s₁, e₁, kp₁, o₁, t₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre.base hi.pre.scr hi.rsi (by omega_arith)
    (fun j hj => by rw [hrdi]; exact hi.pre.word (by omega_arith))
    (fun j hj l hl => by rw [hrdi]; exact hi.pre.wsep (by omega_arith) (by rw [slots_eq, keySlot_eq] at *; omega_arith))
    hi.masks
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  obtain ⟨s₃, e₃, c₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₂ t1 1
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', e₁, Option.bind_some,
      show ([Instr.alu op .rdi (.imm 8), .alu .sub t1 (.imm 1)] : List Instr) =
        [.alu op .rdi (.imm 8)] ++ [.alu .sub t1 (.imm 1)] from rfl,
      runBlock_append', e₂, Option.bind_some, e₃], ?_⟩
  obtain ht₂ : s₂.gpr t1 = BitVec.ofNat 64 (N - k) := by rw [o₂ _ (by decide), t₁, hi.cnt]
  obtain hc₃ : s₃.gpr t1 = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [c₃, ht₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show N - k - 1 = N - (k + 1) by omega_arith]
  -- The new invariant.
  obtain hf₁₃ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k)), 64⟩] s.mem s₃.mem := by
    rw [m₃, m₂]; exact f₁
  obtain hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
    refine ⟨hi.pre.congr ?_ ?_ ?_, ?_, ?_, hc₃, fun i hi' => ?_, fun kv hkv => ?_, ?_, fun r h1 h2 h3 => ?_,
      by rw [rd₃, rd₂, rd₁, hi.rd], by rw [wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [rd₃, rd₂, rd₁]
    · rw [wr₃, wr₂, wr₁]
    · rw [o₃ _ (by decide), o₂ _ (by decide), kp₁, hi.rsi, addr_add,
        show 8 * keySlot + 64 * (e₀ + k) + 64 = 8 * keySlot + 64 * (e₀ + (k + 1)) by omega_arith]
    · rw [o₃ _ (by decide), r₂, o₁ _ (by decide) (by decide), hrdi, hstep k hk]
    · by_cases he : i = e₀ + k
      · subst he
        obtain hw' : Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 0) = F (e₀ + k) := by
          rw [hrdi, addr_add, Nat.add_zero, hF k hk]
          exact hi.pre.wordAt_eq (by rw [endSlot_eq, slots_eq]; decide) hi.frame hw
        rw [← hw']
        exact E₁.congr fun j _ => by
          show entryW s₃.mem b (e₀ + k) j = entryW s₁.mem b (e₀ + k) j
          rw [m₃, m₂]
      · refine (hi.ent i (by omega_arith)).congr fun j hj => ?_
        exact entryW_frame hf₁₃ (by omega_arith) (by omega_arith) he hj
    · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
      rw [m₃, m₂, o₃ _ (by decide), o₂ _ (by decide)]; exact m₁ kv hkv
    · refine hi.frame.trans ((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (by rw [m₃, m₂]; exact Frame.refl _ _))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega_arith)
      · exact VG.Offset.sub_base b (by rw [keySlot_eq, endSlot_eq]; omega_arith)
    · rw [o₃ r (fun h => h1 (by subst h; decide)), o₂ r h3, o₁ r h1 h2, hi.regs r h1 h2 h3]
  obtain hz : s₃.zf = some (decide (N - (k + 1) = 0)) := by
    rw [z₃, ht₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith
  by_cases hl : k + 1 = N
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show k + 1 = N from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega_arith, N - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, hinv⟩


/-! ## The tables -/

theorem movImm_ok (s : State) (r : Reg) (v : BitVec 64) :
    ∃ s', runBlock isa [.movImm64 r v] s = some s' ∧ s'.gpr r = v ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg r v, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec],
    by simp only [RegUpd.gpr_setReg_self], fun r' hr => by simp only [RegUpd.gpr_setReg_of_ne _ _ hr],
    rfl, rfl, rfl⟩

/-- What the table's construction leaves: entry `i` holds word `perm i` of the schedule. -/
structure KeysPost (s₀ : State) (b sched : Addr) (g : Nat) (perm : Nat → Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  ent : ∀ i < 8 * g + 2,
    EntryOk s.mem b i (Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * perm i)))
  masks : MasksOk s
  frame : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem add8 (x : Addr) {w : Nat} :
    x + BitVec.ofNat 64 (8 * w) + (8 : BitVec 32).signExtend 64 = x + BitVec.ofNat 64 (8 * (w + 1)) := by
  rw [show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl, addr_add,
    show 8 * w + 8 = 8 * (w + 1) by omega_arith]

theorem sub8 (x : Addr) {w : Nat} :
    x + BitVec.ofNat 64 (8 * (w + 1)) - (8 : BitVec 32).signExtend 64 = x + BitVec.ofNat 64 (8 * w) := by
  rw [show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl, VG.Offset.add_ofNat_sub _ (by omega_arith),
    show 8 * (w + 1) - 8 = 8 * w by omega_arith]

theorem encKeys_wp {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hrdi : s₀.gpr .rdi = sched) (hm : MasksOk s₀) :
    WP isa (encKeys g) s₀ (KeysPost s₀ b sched g id) := by
  obtain hg4 : g ≤ 4 := by omega_arith
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  obtain ⟨s₂, e₂, t₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s₁ t1 (BitVec.ofNat 64 (8 * g + 2))
  unfold encKeys
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_append']; simp only [tableSetup]; rw [show ([movR .rsi sb, .alu .add .rsi
      (.imm (BitVec.ofNat 32 (8 * keySlot)))] : List Instr) = [movR kp sb, .alu .add kp
      (.imm (BitVec.ofNat 32 (8 * keySlot)))] from rfl, e₁, Option.bind_some, e₂], ?_⟩)
  obtain hinv : KeyInv s₀ b sched 0 (8 * g + 2) id (fun i => Spec.Camellia.wordAt s₀.mem
      (sched + BitVec.ofNat 64 (8 * i))) 0 s₂ := by
    refine ⟨hk.congr ?_ ?_ ?_, ?_, ?_, ?_, fun i hi => by omega_arith, fun kv hkv => ?_, ?_, fun r h1 h2 _ => ?_,
      by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [o₂ _ (by decide), o₁ _ (by decide)]
    · rw [rd₂, rd₁]
    · rw [wr₂, wr₁]
    · rw [o₂ _ (by decide), k₁, hk.base]; simp
    · rw [o₂ _ (by decide), o₁ _ (by decide), hrdi]; simp
    · rw [t₂, Nat.sub_zero]
    · show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
      rw [m₂, m₁, o₂ _ (by decide), o₁ _ (by decide)]; exact hm kv hkv
    · rw [m₂, m₁]; exact Frame.refl _ _
    · rw [o₂ r (fun h => h1 (by subst h; decide)), o₁ r h2]
  refine WP.mono (keyLoop_wp (e₀ := 0) (N := 8 * g + 2) (wk := id) (f := fun x => x + (8 : BitVec 32).signExtend 64) (fun s => addImm_ok s .rdi 8) (by omega_arith) (by omega_arith) (fun k hk => by simp; omega_arith)
    (fun k _ => add8 sched) (fun k _ => by simp) (by omega_arith) hinv) fun s h => ?_
  exact ⟨h.pre, fun i hi => h.ent i (by omega_arith), h.masks, h.frame, h.regs, h.rd, h.wr⟩


/-- `keyOne_step` within the construction of a table from `s₀`. -/
theorem keyOne_inv {s₀ s : State} {b sched : Addr} {d e w : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hrsi : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hrdi : s.gpr .rdi = sched + BitVec.ofNat 64 (8 * w)) (hw : w + d / 8 < 34) (hm : MasksOk s)
    (hf : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ KeyPre s' b sched ∧
      s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + 1)) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧ Frame [⟨b, 8 * endSlot⟩] s₀.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (w + d / 8)))) ∧
      (∀ i < 34, i ≠ e → ∀ j < 8, entryW s'.mem b i j = entryW s.mem b i j) := by
  obtain ⟨s', e', k', o', t', rd', wr', m', f', E'⟩ := keyOne_step hd hk.base hk.scr hrsi he
    (fun j hj => by rw [hrdi]; exact hk.word (by omega_arith))
    (fun l hl j hj => by rw [hrdi]; exact hk.wsep (by omega_arith) (by rw [slots_eq, keySlot_eq] at *; omega_arith)) hm
  refine ⟨s', e', hk.congr (o' _ (by decide) (by decide)) rd' wr', ?_, o', t', rd', wr', m', ?_, ?_,
    fun i hi hie j hj => entryW_frame f' hi he hie hj⟩
  · rw [k', hrsi, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith]
  · refine hf.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega_arith)
    · exact VG.Offset.sub_base b (by rw [keySlot_eq, endSlot_eq]; omega_arith)
  · have hw' : Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d) =
        Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (w + d / 8))) := by
      rw [hrdi, addr_add, show 8 * w + d = 8 * (w + d / 8) by omega_arith]
      exact hk.wordAt_eq (by rw [endSlot_eq, slots_eq]; decide) hf hw
    rw [← hw']; exact E'


theorem decKeys_wp {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hrdi : s₀.gpr .rdi = sched) (hm : MasksOk s₀) :
    WP isa (decKeys g) s₀ (KeysPost s₀ b sched g (Camellia.decPerm g)) := by
  obtain hg4 : g ≤ 4 := by omega_arith
  obtain hg3 : 3 ≤ g := by omega_arith
  unfold decKeys
  -- `kw3`, `kw4` to entries 0 and 1.
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rdi (BitVec.ofNat 32 (64 * g))
  obtain hrdi₂ : s₂.gpr .rdi = sched + BitVec.ofNat 64 (8 * (8 * g)) := by
    rw [r₂, o₁ _ (by decide), hrdi, show (BitVec.ofNat 32 (64 * g)).signExtend 64 =
      BitVec.ofNat 64 (8 * (8 * g)) by rcases hg with rfl | rfl <;> rfl]
  obtain hk₂ : KeyPre s₂ b sched :=
    hk.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  obtain hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, m₁, o₂ _ (by decide), o₁ _ (by decide)]; exact hm kv hkv
  obtain hf₂ : Frame [⟨b, 8 * endSlot⟩] s₀.mem s₂.mem := by rw [m₂, m₁]; exact Frame.refl _ _
  obtain hrsi₂ : s₂.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * 0) := by
    rw [o₂ _ (by decide), k₁, hk.base]; simp
  obtain ⟨s₃, e₃, hk₃, rsi₃, o₃, t₃, rd₃, wr₃, hm₃, hf₃, E₃, -⟩ :=
    keyOne_inv (d := 0) (Or.inl rfl) hk₂ hrsi₂ (by omega_arith) hrdi₂ (by omega_arith) hm₂ hf₂
  obtain ⟨s₄, e₄, hk₄, rsi₄, o₄, t₄, rd₄, wr₄, hm₄, hf₄, E₄, P₄⟩ :=
    keyOne_inv (d := 8) (Or.inr rfl) hk₃ rsi₃ (by omega_arith) (by rw [o₃ _ (by decide) (by decide), hrdi₂])
      (by omega_arith) hm₃ hf₃
  obtain ⟨s₅, e₅, r₅, -, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rdi 8
  obtain ⟨s₆, e₆, t₆, o₆, m₆, rd₆, wr₆⟩ := movImm_ok s₅ t1 (BitVec.ofNat 64 (8 * g - 2))
  obtain hrdi₆ : s₆.gpr .rdi = sched + BitVec.ofNat 64 (8 * (8 * g - 1)) := by
    rw [o₆ _ (by decide), r₅, o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), hrdi₂]
    have := sub8 sched (w := 8 * g - 1)
    rwa [show 8 * g - 1 + 1 = 8 * g by omega_arith] at this
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append']
    simp only [tableSetup]
    rw [show ([movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] : List Instr) =
      [movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] from rfl, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some,
      show ([Instr.alu .sub .rdi (.imm 8), .movImm64 t1 (BitVec.ofNat 64 (8 * g - 2))] : List Instr) =
        [.alu .sub .rdi (.imm 8)] ++ [.movImm64 t1 (BitVec.ofNat 64 (8 * g - 2))] from rfl,
      runBlock_append', e₅, Option.bind_some, e₆], ?_⟩)
  -- The loop: entries 2 to `8 g - 1`.
  let F : Nat → BitVec 64 := fun i =>
    Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * Camellia.decPerm g i))
  obtain hF0 : F 0 = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (8 * g + 0 / 8))) := by
    simp [F, Camellia.decPerm]
  obtain hF1 : F 1 = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (8 * g + 8 / 8))) := by
    simp [F, Camellia.decPerm]
  obtain hinv : KeyInv s₀ b sched 2 (8 * g - 2) (fun k => 8 * g - 1 - k) F 0 s₆ := by
    refine ⟨hk₄.congr ?_ ?_ ?_, ?_, by rw [hrdi₆, Nat.sub_zero], by rw [t₆, Nat.sub_zero], fun i hi => ?_, fun kv hkv => ?_,
      by rw [m₆, m₅]; exact hf₄, fun r h1 h2 h3 => ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
      by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
    · rw [o₆ _ (by decide), o₅ _ (by decide)]
    · rw [rd₆, rd₅]
    · rw [wr₆, wr₅]
    · rw [o₆ _ (by decide), o₅ _ (by decide), rsi₄]
    · have hmem : s₆.mem = s₄.mem := by rw [m₆, m₅]
      rw [hmem]
      rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
      · rw [hF0]; exact E₃.congr fun j hj => P₄ 0 (by omega_arith) (by omega_arith) j hj
      · rw [hF1]; exact E₄
    · show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
      rw [m₆, m₅, o₆ _ (by decide), o₅ _ (by decide)]; exact hm₄ kv hkv
    · rw [o₆ r (fun h => h1 (by subst h; decide)), o₅ r h3, o₄ r h1 h2, o₃ r h1 h2, o₂ r h3, o₁ r h2]
  refine WP.seq (WP.mono (keyLoop_wp (e₀ := 2) (N := 8 * g - 2) (wk := fun k => 8 * g - 1 - k)
    (f := fun x => x - (8 : BitVec 32).signExtend 64) (fun s => ?_) (by omega_arith) (by omega_arith)
    (fun k hk => by omega_arith) (fun k hk => ?_) (fun k hk => ?_) (by omega_arith) hinv) fun s h => ?_)
  · obtain ⟨s', e', r', -, o', m', rd', wr'⟩ := subImm_ok s .rdi 8
    exact ⟨s', e', r', o', m', rd', wr'⟩
  · have := sub8 sched (w := 8 * g - 1 - (k + 1))
    rwa [show 8 * g - 1 - (k + 1) + 1 = 8 * g - 1 - k by omega_arith] at this
  · simp only [F, Camellia.decPerm, show ¬ 2 + k < 2 by omega_arith, show 2 + k < 8 * g by omega_arith, ↓reduceIte,
      show 8 * g + 1 - (2 + k) = 8 * g - 1 - k by omega_arith]
  -- `kw1`, `kw2` to entries `8 g` and `8 g + 1`.
  have hk₇ := h.pre
  obtain ⟨s₇, e₇, r₇, -, o₇, m₇, rd₇, wr₇⟩ := subImm_ok s .rdi 8
  obtain hrdi₇ : s₇.gpr .rdi = sched + BitVec.ofNat 64 (8 * 0) := by
    rw [r₇, h.rdi, show 8 * g - 1 - (8 * g - 2) = 0 + 1 by omega_arith, sub8]
  obtain hk₇' : KeyPre s₇ b sched := hk₇.congr (o₇ _ (by decide)) rd₇ wr₇
  obtain hm₇ : MasksOk s₇ := fun kv hkv => by
    show s₇.mem.readW (wordAddr (s₇.gpr sb) kv.1) 64 = kv.2
    rw [m₇, o₇ _ (by decide)]; exact h.masks kv hkv
  obtain hrsi₇ : s₇.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 * g)) := by
    rw [o₇ _ (by decide), h.rsi, show 2 + (8 * g - 2) = 8 * g by omega_arith]
  obtain ⟨s₈, e₈, hk₈, rsi₈, o₈, -, rd₈, wr₈, hm₈, hf₈, E₈, P₈⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₇' hrsi₇ (by omega_arith) hrdi₇ (by omega_arith) hm₇ (by rw [m₇]; exact h.frame)
  obtain ⟨s₉, e₉, hk₉, -, o₉, -, rd₉, wr₉, hm₉, hf₉, E₉, P₉⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₈ rsi₈ (by omega_arith) (by rw [o₈ _ (by decide) (by decide), hrdi₇])
      (by omega_arith) hm₈ hf₈
  refine WP.of_runBlock ⟨s₉, by
    rw [runBlock_append', runBlock_append', e₇, Option.bind_some, e₈, Option.bind_some, e₉],
    hk₉, fun i hi => ?_, hm₉, hf₉, fun r h1 h2 h3 => ?_, by rw [rd₉, rd₈, rd₇, h.rd],
    by rw [wr₉, wr₈, wr₇, h.wr]⟩
  · rcases (show i < 8 * g ∨ i = 8 * g ∨ i = 8 * g + 1 by omega_arith) with hi' | rfl | rfl
    · refine (h.ent i (by omega_arith)).congr fun j hj => ?_
      rw [P₉ i (by omega_arith) (by omega_arith) j hj, P₈ i (by omega_arith) (by omega_arith) j hj, m₇]
    · have hp : Camellia.decPerm g (8 * g) = 0 + 0 / 8 := by
        unfold Camellia.decPerm
        simp only [show ¬ 8 * g < 2 by omega_arith, show ¬ 8 * g < 8 * g by omega_arith, ↓reduceIte]; omega_arith
      rw [hp]; exact E₈.congr fun j hj => P₉ _ (by omega_arith) (by omega_arith) j hj
    · have hp : Camellia.decPerm g (8 * g + 1) = 0 + 8 / 8 := by
        unfold Camellia.decPerm
        simp only [show ¬ 8 * g + 1 < 2 by omega_arith, show ¬ 8 * g + 1 < 8 * g by omega_arith, ↓reduceIte]; omega_arith
      rw [hp]; exact E₉
  · rw [o₉ r h1 h2, o₈ r h1 h2, o₇ r h3, h.regs r h1 h2 h3]

end VG.Proof.Camellia.X86_64

end

end

/-! ### `Camellia.X86_64.Copy`, which only this module used -/

section

/-!
# Copying blocks on x86-64

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks of 16 bytes
from `rax` to `rbx` (areas that do not overlap), through `rbp`, counting
down `rcx`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (at_)

/-- `mov rbp, [rax + d]; mov [rbx + d], rbp`. -/
theorem copyWord_ok (s : State) (d : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rbp (.mem (at_ .rax d)), .store (at_ .rbx d) .rbp] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64
  refine ⟨{ s.setReg .rbp v with mem := s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d) v }, ?_, rfl,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64,
    State.ea, ofInt_nat, hr, ite_true, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ .rbp by decide), RegUpd.wr_setReg, hw]
  rfl

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = A + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = B + BitVec.ofNat 64 (16 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_using [], hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain hA0 := hA (2 * j) (by omega_using [hj])
  obtain hA1 := hA (2 * j + 1) (by omega_using [hj])
  obtain hB0 := hB (2 * j) (by omega_using [hj])
  obtain hB1 := hB (2 * j + 1) (by omega_using [hj])
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  obtain hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_using [hc8]) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s 0
    (by rw [hi.rd, hi.wr, hi.rax, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_using []]; exact hA0)
    (by rw [hi.wr, hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_using []]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ 8
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.rax, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_using []]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.rbx, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_using []]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rax 16
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rbx 16
  obtain ⟨s₅, e₅, c₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rcx 1
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.mov .rbp (.mem (at_ .rax 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr) =
      [.mov .rbp (.mem (at_ .rax 0)), .store (at_ .rbx 0) .rbp] ++
      ([.mov .rbp (.mem (at_ .rax 8)), .store (at_ .rbx 8) .rbp] ++
      ([.alu .add .rax (.imm 16)] ++ ([.alu .add .rbx (.imm 16)] ++ [.alu .sub .rcx (.imm 1)]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, runBlock_append', e₃,
      Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩
  obtain hn : 16 * c < 2 ^ 64 := by omega_using [hc8]
  obtain r1 : s₁.gpr .rbx = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rbx]
  obtain a1 : s₁.gpr .rax = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rax]
  obtain hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  obtain hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.rbx, hi.rax, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  obtain hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_using [hj]) hn)]
  obtain hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_using []]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_using []]
    · rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
        show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_using [hj]),
        show c - j - 1 = c - (j + 1) by omega_using []]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_using [hc8, hj, ht])]; omega_using [ht]), off_sub_toNat B h8 (by omega_using [hc8, hj, ht]), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_using [h8], hA₁ t (by omega_using [hj, ht]), hAs t (by omega_using [hj, ht])]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_using [h8])) (by omega_using [hc8, hj, ht]) (by omega_using []) (by omega_using [hc8, hj])), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_using [hc8, hj, ht])]; omega_using [h8]), off_sub_toNat B h0 (by omega_using [hc8, hj, ht]), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_using [h0], hAs t (by omega_using [hj, ht])]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_using [h0])) (by omega_using [hc8, hj, ht]) (by omega_using []) (by omega_using [hc8, hj]))]
          exact hi.copied t (by omega_using [h0])
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_using [h]))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_using [hj])), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_using [hj]))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  obtain hz : s₅.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_using [hc8]) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_using [hj]
  by_cases hl : j + 1 = c
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega_using [hj, hl], c - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hinv⟩

end VG.Proof.Camellia.X86_64

end

end


/-!
# A group of blocks of Camellia ECB on x86-64

`group_wp`: one iteration of the data loop copies the group's blocks (eight,
or the last one to seven) to the tail buffer, saves the data pointer, the
blocks left and the postwhitening's address in their slots, transforms the
tail buffer (`crypt8_ok`), reloads them, copies the blocks back and steps
to the next group.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)

theorem dataSlot_eq : dataSlot = 369 := rfl
theorem countSlot_eq : countSlot = 370 := rfl
theorem savedSlot_eq : savedSlot = 371 := rfl

/-! ## Small blocks -/

theorem cmpImm_ok (s : State) (r : Reg) (k : BitVec 32) {v K : Nat} (hr : s.gpr r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 64) (hk : (k.signExtend 64).toNat = K) :
    ∃ s', runBlock isa [.alu .cmp r (.imm k)] s = some s' ∧ s'.cf = some (decide (v < K)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r - k.signExtend 64) (decide ((s.gpr r).toNat < (k.signExtend 64).toNat))
    (subOverflow (s.gpr r) (k.signExtend 64) (s.gpr r - k.signExtend 64)), ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp [arithFlags, State.setFlags, hr, hk]; rw [Nat.mod_eq_of_lt (by simpa using hv)]

theorem cmpImmZ_ok (s : State) (r : Reg) (k : BitVec 32) :
    ∃ s', runBlock isa [.alu .cmp r (.imm k)] s = some s' ∧ s'.zf = some (s.gpr r - k.signExtend 64 == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r - k.signExtend 64) (decide ((s.gpr r).toNat < (k.signExtend 64).toNat))
    (subOverflow (s.gpr r) (k.signExtend 64) (s.gpr r - k.signExtend 64)), ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]

theorem movR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [movR d r] s = some s' ∧ s'.gpr d = s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.gpr r), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r' hr => by simp only [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl⟩
  simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]

theorem subSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.reg r)] s = some s' ∧ s'.zf = some true ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr r - s.gpr r) ((s.gpr r).toNat < (s.gpr r).toNat)
    (subOverflow (s.gpr r) (s.gpr r) (s.gpr r - s.gpr r))).setReg r (s.gpr r - s.gpr r), ?_, ?_,
    fun r' hr => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_setReg, RegUpd.zf_arithFlags, BitVec.sub_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `rcx := min(r8, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r8 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min v 8) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := movImm_ok s .rcx 8
  obtain ⟨s₂, e₂, f₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok s₁ .r8 8 (v := v) (by rw [o₁ _ (by decide), hr]) hv rfl
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([Instr.movImm64 .rcx 8, .alu .cmp .r8 (.imm 8)] : List Instr) =
      [.movImm64 .rcx 8] ++ [.alu .cmp .r8 (.imm 8)] from rfl, runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.ite (decide (v < 8)) (by simp [X86_64.eval, f₂]) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rcx .r8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => ?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
    · rw [r₃, g₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_arith)]
    · rw [o₃ r hr, g₂, o₁ r hr]
  · refine WP.of_runBlock ⟨s₂, rfl, ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [g₂, c₁, Nat.min_eq_right (by simp at h; omega_arith)]; rfl
    · rw [g₂, o₁ r hr]

/-- `mov [sb + 8 k], r`. -/
theorem stReg_ok {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa [st k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' : InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 := hw
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr r) }, ?_, rfl, rfl, rfl, rfl⟩
  simp only [st, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, State.ea, ofInt_nat, hb, hw', ite_true]

/-- `mov d, [sb + 8 k]`. -/
theorem movS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr b k) 8) :
    ∃ s', runBlock isa [movS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr' : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * k)) 8 := hr
  refine ⟨s.setReg d (slotW s k), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [movS, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.ea, ofInt_nat, hb, hr', ite_true, Option.map_some, slotW, wordAddr]

/-- `tailAddr r`. -/
theorem tailAddr_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa (tailAddr r) s = some s' ∧ s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * tailSlot) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s r sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ r (BitVec.ofNat 32 (8 * tailSlot))
  refine ⟨s₂, by rw [tailAddr, show ([movR r sb, .alu .add r (.imm (BitVec.ofNat 32 (8 * tailSlot)))] :
      List Instr) = [movR r sb] ++ [.alu .add r (.imm (BitVec.ofNat 32 (8 * tailSlot)))] from rfl,
      runBlock_append', e₁, Option.bind_some, e₂], ?_, fun r' h => by rw [o₂ r' h, o₁ r' h],
    by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  rw [r₂, r₁]; rfl

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_arith) (by omega_arith) h) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ layerMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ i < 8 * g + 2, EntryOk m b i (E i)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–52, 96–367 and 371–376. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 40⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot), 8 * 272⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 48⟩]

theorem ScrOk.frame {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b g E m' := by
  obtain hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk : 48 ≤ kv.1 ∧ kv.1 < 53 := by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_arith) (by omega_arith))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * keySlot + 64 * i + 8 * j) (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i)) (VG.Offset.sub b (by omega_arith) (by omega_arith))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b g E m' := by
  obtain hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * keySlot + 64 * i + 8 * j) (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    have : savedSlot = 371 := rfl
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i)) (VG.Offset.sub b (by omega_arith) (by omega_arith))

/-! ## The data loop -/

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n g : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  hg : g = 3 ∨ g = 4

/-- `copyBlocks` from `rax` to `rbx`, `rcx` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc8 : c ≤ 8)
    (hx : s.gpr .rax = X) (hy : s.gpr .rbx = Y) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc8 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega_arith, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (128 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 8 * k)
  lt : 8 * k < n
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n (8 * k) (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.X86_64.group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n g E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  rw [slots_eq] at hfit
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (128 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t, t < 16 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
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
  obtain inSlot : ∀ j < slots, InRegions s.wr (wordAddr b j) 8 := fun j hj =>
    ⟨_, hwS, VG.Offset.contains_base b (by rw [slots_eq] at hj ⊢; omega_arith) (by rw [slots_eq] at hj; omega_arith)⟩
  unfold Impl.Camellia.X86_64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r8 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .rax .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := tailAddr_ok s₂a .rbx
  obtain base₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), o₂a _ (by decide), o₁ _ (by decide), hi.base]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂ r h2, o₂a r h1, o₁ r h3]
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₂a, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc8
    (by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide), hi.rdx])
    (by rw [r₂, o₂a _ (by decide), o₁ _ (by decide), hi.base])
    (by rw [o₂ _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), base₂]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain g₃' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3]
  obtain sc₃ : ScrOk s₀ b g E s₃.mem := by
    refine hi.scr.frame hg4 (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b (Or.inl ?_) ?_ ?_ <;>
      (try simp only [tailSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega_arith
  -- The state to its slots, and `rdx` to the tail buffer.
  obtain inS₃ : ∀ j < slots, InRegions s₃.wr (wordAddr b j) 8 := fun j hj => by rw [wr₃']; exact inSlot j hj
  obtain hds : dataSlot < slots := by rw [dataSlot_eq, slots_eq]; decide
  obtain hcs : countSlot < slots := by rw [countSlot_eq, slots_eq]; decide
  obtain hes : endSlot < slots := by rw [endSlot_eq, slots_eq]; decide
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a⟩ := stReg_ok (k := dataSlot) .rdx base₃ (inS₃ _ hds)
  obtain ⟨s₄b, e₄b, m₄b, g₄b, rd₄b, wr₄b⟩ := stReg_ok (k := countSlot) .r8 (by rw [g₄a, base₃])
    (by rw [wr₄a]; exact inS₃ _ hcs)
  obtain ⟨s₄c, e₄c, m₄c, g₄c, rd₄c, wr₄c⟩ := stReg_ok (k := endSlot) .rdi (by rw [g₄b, g₄a, base₃])
    (by rw [wr₄b, wr₄a]; exact inS₃ _ hes)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := tailAddr_ok s₄c .rdx
  obtain base₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), g₄c, g₄b, g₄a, base₃]
  obtain rdx₄ : s₄.gpr .rdx = T := by rw [r₄, g₄c, g₄b, g₄a, base₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄c, wr₄b, wr₄a, wr₃']
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₄c, rd₄b, rd₄a, rd₃']
  obtain mem₄ : s₄.mem = ((s₃.mem.writeW (wordAddr b dataSlot) (s₃.gpr .rdx)).writeW (wordAddr b countSlot)
      (s₃.gpr .r8)).writeW (wordAddr b endSlot) (s₃.gpr .rdi) := by
    rw [m₄, m₄c, m₄b, m₄a, g₄b, g₄a]
  obtain f₄ : Frame [⟨b + BitVec.ofNat 64 (8 * endSlot), 24⟩] s₃.mem s₄.mem := by
    rw [mem₄]
    refine ((frame_writeW _ ?_).trans (frame_writeW _ ?_)).trans (frame_writeW _ ?_) <;>
      exact VG.Offset.sub b (by simp only [dataSlot_eq, countSlot_eq, endSlot_eq]; omega_arith)
        (by simp only [dataSlot_eq, countSlot_eq, endSlot_eq]; omega_arith)
  obtain slot₄ : ∀ j < slots, slotW s₄ j = if j = endSlot then s.gpr .rdi else if j = countSlot then
      s.gpr .r8 else if j = dataSlot then s.gpr .rdx else slotW s₃ j := fun j hj => by
    simp only [slotW, base₄, base₃, mem₄]
    rw [readW_slot_write _ hj hes, readW_slot_write _ hj hcs, readW_slot_write _ hj hds]
    rw [g₃' .rdi (by decide) (by decide) (by decide) (by decide), g₃' .r8 (by decide) (by decide) (by decide)
      (by decide), g₃' .rdx (by decide) (by decide) (by decide) (by decide)]
  obtain sc₄ : ScrOk s₀ b g E s₄.mem := by
    refine sc₃.frame hg4 f₄ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [endSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [saveState, show ([st dataSlot .rdx, st countSlot .r8, st endSlot .rdi] : List Instr) =
      [st dataSlot .rdx] ++ ([st countSlot .r8] ++ [st endSlot .rdi]) from rfl,
      runBlock_append', runBlock_append', e₄a, Option.bind_some, runBlock_append', e₄b, Option.bind_some,
      e₄c, Option.bind_some, e₄], ?_⟩)
  -- The eight blocks.
  obtain hcore : CorePre s₄ g E :=
    { scr := by rw [base₄, wr₄']; exact hwS
      dat := fun j hj => by rw [rdx₄, wr₄']; exact inT j hj
      sep := by rw [rdx₄, base₄]; exact VG.Offset.disjoint_base b (Nat.le_refl _) (by rw [tailSlot_eq]; omega_arith)
      fit := by rw [base₄, slots_eq]; exact hfit
      fitD := by rw [rdx₄, toNat_off b (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
      hg := hp.hg
      nk34 := by rcases hp.hg with h | h <;> omega_arith
      masks := sc₄.masks.ok base₄
      bound := by rw [slot₄ _ hes, ite_eq_left rfl, base₄, hi.rdi]
      keys := fun i hi' => by rw [base₄]; exact sc₄.keys i hi' }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₄]
  obtain rdx₅ : s₅.gpr .rdx = T := by rw [c₅.rdx, rdx₄]
  obtain f₅ : Frame [⟨b, 8 * keySlot⟩, ⟨T, 128⟩] s₄.mem s₅.mem := by
    have := c₅.frame; rw [base₄, rdx₄] at this; exact this
  have hT : T = b + BitVec.ofNat 64 (8 * tailSlot) := rfl
  obtain keepSlot : ∀ j, keySlot ≤ j → j < tailSlot → slotW s₅ j = slotW s₄ j := fun j h1 h2 => by
    simp only [slotW, base₅, base₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by omega_arith) (by rw [tailSlot_eq] at h2; omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by omega_arith)) (by rw [tailSlot_eq] at h2; omega_arith)
        (by rw [tailSlot_eq]; omega_arith)
  obtain sc₅ : ScrOk s₀ b g E s₅.mem := by
    refine sc₄.frame2 hg4 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    rcases ht with rfl | rfl <;> rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq] <;> omega_arith) (by rw [keySlot_eq] <;> omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq, tailSlot_eq] <;> omega_arith))
        (by rw [keySlot_eq] <;> omega_arith) (by rw [tailSlot_eq] <;> omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [keySlot_eq, savedSlot_eq] <;> omega_arith) (by rw [savedSlot_eq] <;> omega_arith)
    · rw [hT]; exact VG.Offset.disjoint b (Or.inl (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith))
        (by rw [savedSlot_eq] <;> omega_arith) (by rw [tailSlot_eq] <;> omega_arith)
  obtain vD : slotW s₅ dataSlot = A := by
    rw [keepSlot _ (by rw [dataSlot_eq, keySlot_eq]; omega_arith) (by rw [dataSlot_eq, tailSlot_eq]; omega_arith),
      slot₄ _ hds, ite_eq_right (by rw [dataSlot_eq, endSlot_eq]; omega_arith),
      ite_eq_right (by rw [dataSlot_eq, countSlot_eq]; omega_arith), ite_eq_left rfl, hi.rdx]
  obtain vC : slotW s₅ countSlot = BitVec.ofNat 64 v := by
    rw [keepSlot _ (by rw [countSlot_eq, keySlot_eq]; omega_arith) (by rw [countSlot_eq, tailSlot_eq]; omega_arith),
      slot₄ _ hcs, ite_eq_right (by rw [countSlot_eq, endSlot_eq]; omega_arith), ite_eq_left rfl, hi.r8]
  obtain vE : slotW s₅ endSlot = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [keepSlot _ (by rw [endSlot_eq, keySlot_eq]; omega_arith) (by rw [endSlot_eq, tailSlot_eq]; omega_arith),
      slot₄ _ hes, ite_eq_left rfl, hi.rdi]
  -- The state back from its slots.
  obtain wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  obtain rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₄']
  obtain inS₅ : ∀ j < slots, InRegions (s₅.rd ++ s₅.wr) (wordAddr b j) 8 := fun j hj => by
    rw [wr₅', rd₅']; exact inRd (inSlot j hj)
  obtain ⟨s₆a, e₆a, d₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := movS_ok (k := dataSlot) .rdx base₅ (inS₅ _ hds)
  obtain ⟨s₆b, e₆b, d₆b, o₆b, m₆b, rd₆b, wr₆b⟩ := movS_ok (k := countSlot) .r8
    (by rw [o₆a _ (by decide), base₅]) (by rw [rd₆a, wr₆a]; exact inS₅ _ hcs)
  obtain ⟨s₆, e₆, d₆, o₆, m₆, rd₆, wr₆⟩ := movS_ok (k := endSlot) .rdi
    (by rw [o₆b _ (by decide), o₆a _ (by decide), base₅]) (by rw [rd₆b, wr₆b, rd₆a, wr₆a]; exact inS₅ _ hes)
  obtain mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆b, m₆a]
  obtain rdx₆ : s₆.gpr .rdx = A := by
    rw [o₆ _ (by decide), o₆b _ (by decide), d₆a, ← vD]
  obtain r8₆ : s₆.gpr .r8 = BitVec.ofNat 64 v := by
    rw [o₆ _ (by decide), d₆b]; simp only [slotW, m₆a, o₆a _ (by decide : sb ≠ .rdx)]; exact vC
  obtain rdi₆ : s₆.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [d₆]; simp only [slotW, m₆b, m₆a, o₆b _ (by decide : sb ≠ .r8), o₆a _ (by decide : sb ≠ .rdx)]; exact vE
  obtain base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆b _ (by decide), o₆a _ (by decide), base₅]
  obtain g₆ : ∀ r, r ≠ .rdx → r ≠ .r8 → r ≠ .rdi → s₆.gpr r = s₅.gpr r := fun r h1 h2 h3 => by
    rw [o₆ r h3, o₆b r h2, o₆a r h1]
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [loadState, show ([movS .rdx dataSlot, movS .r8 countSlot, movS .rdi endSlot] : List Instr) =
      [movS .rdx dataSlot] ++ ([movS .r8 countSlot] ++ [movS .rdi endSlot]) from rfl,
      runBlock_append', e₆a, Option.bind_some, runBlock_append', e₆b, Option.bind_some, e₆], ?_⟩)
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r8₆ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := tailAddr_ok s₇ .rax
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈a .rbx .rdx
  refine WP.seq (WP.of_runBlock ⟨s₈, by rw [runBlock_append', e₈a, Option.bind_some, e₈], ?_⟩)
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆, wr₆b, wr₆a, wr₅']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆, rd₆b, rd₆a, rd₅']
  obtain g₈ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₈.gpr r = s₆.gpr r := fun r h1 h2 h3 => by
    rw [o₈ r h2, o₈a r h1, o₇ r h3]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc8
    (by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide), base₆])
    (by rw [r₈, o₈a _ (by decide), o₇ _ (by decide), rdx₆])
    (by rw [o₈ _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  obtain g₉' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₉.gpr r = s₆.gpr r :=
    fun r h1 h2 h3 h4 => by rw [g₉ r h1 h2 h3 h4, g₈ r h1 h2 h3]
  obtain base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide), base₆]
  obtain rdx₉ : s₉.gpr .rdx = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide), rdx₆]
  obtain r8₉ : s₉.gpr .r8 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), r8₆]
  obtain rdi₉ : s₉.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), rdi₆]
  obtain rsp₉ : s₉.gpr .rsp = s₀.gpr .rsp := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide),
      c₅.keep _ (by decide) (by decide) (by decide), o₄ _ (by decide), g₄c, g₄b, g₄a,
      g₃' _ (by decide) (by decide) (by decide) (by decide), hi.rsp]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₉ : ScrOk s₀ b g E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame hg4 f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [keySlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, endSlot_eq]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega_arith)
      · exact subS (by rw [slots_eq, tailSlot_eq] <;> omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, blk s₄ j = Spec.Camellia.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [rdx₄, addr_add, addr_add, addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    rw [f₄ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off b (Or.inr (by rw [endSlot_eq, tailSlot_eq]; omega_arith)) (by rw [tailSlot_eq]; omega_arith)
          (by decide) (by rw [endSlot_eq]; omega_arith))]
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [this, mem₂, addr_add, hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem D n (8 * k + c) (outF s₀.mem D g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [addr_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 128 * k) = s₅.gpr .rdx + BitVec.ofNat 64 (16 * ((i - 128 * k) / 16)) +
          BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [rdx₅, addr_add, addr_add, addr_add, show 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = i - 128 * k by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega_arith)
          · exact subS (by rw [slots_eq, tailSlot_eq] <;> omega_arith)) (by simp only; omega_arith) hin,
        f₄.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, endSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  unfold advance
  obtain ⟨s₁₀, e₁₀, cf₁₀, g₁₀, m₁₀, rd₁₀, wr₁₀⟩ := cmpImm_ok s₉ .r8 8 r8₉ hv rfl
  refine WP.seq (WP.of_runBlock ⟨s₁₀, e₁₀, ?_⟩)
  refine WP.ite (decide (v < 8)) (by simp [X86_64.eval, cf₁₀]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt' : v < 8 := by simpa using hlt
    obtain ⟨s₁₁, e₁₁, z₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := subSelf_ok s₁₀ .r8
    refine WP.of_runBlock ⟨s₁₁, e₁₁, .inl ⟨z₁₁, ?_⟩⟩
    obtain hn : 8 * k + c = n := by omega_arith
    refine ⟨by rw [o₁₁ _ (by decide), g₁₀, base₉], by rw [o₁₁ _ (by decide), g₁₀, rsp₉],
      by rw [m₁₁, m₁₀]; exact sc₉, fun i hi' => by rw [m₁₁, m₁₀, hdata i hi', hn], by rw [m₁₁, m₁₀]; exact fr,
      by rw [rd₁₁, rd₁₀, rd₉'], by rw [wr₁₁, wr₁₀, wr₉']⟩
  · have hge' : 8 ≤ v := by simpa using hge
    obtain hc : c = 8 := by omega_arith
    obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addImm_ok s₁₀ .rdx 128
    obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := subImm_ok s₁₁ .r8 8
    obtain r8₁₁ : s₁₁.gpr .r8 = BitVec.ofNat 64 v := by rw [o₁₁ _ (by decide), g₁₀, r8₉]
    obtain hz : s₁₂.zf = some (decide (v = 8)) := by
      rw [z₁₂, r8₁₁, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq hv (by decide)]
    refine WP.of_runBlock ⟨s₁₂, by
      rw [show ([Instr.alu .add .rdx (.imm 128), .alu .sub .r8 (.imm 8)] : List Instr) =
        [.alu .add .rdx (.imm 128)] ++ [.alu .sub .r8 (.imm 8)] from rfl, runBlock_append', e₁₁,
        Option.bind_some, e₁₂], ?_⟩
    obtain hm : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
    obtain base₁₂ : s₁₂.gpr sb = b := by rw [o₁₂ _ (by decide), o₁₁ _ (by decide), g₁₀, base₉]
    obtain rsp₁₂ : s₁₂.gpr .rsp = s₀.gpr .rsp := by rw [o₁₂ _ (by decide), o₁₁ _ (by decide), g₁₀, rsp₉]
    obtain rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉']
    obtain wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉']
    by_cases h8 : v = 8
    · refine .inl ⟨by rw [hz, h8]; rfl, base₁₂, rsp₁₂, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₂', wr₁₂'⟩
      intro i hi'
      rw [hm, hdata i hi', show 8 * k + c = n by omega_arith]
    · refine .inr ⟨by rw [hz]; simp [h8], base₁₂, rsp₁₂, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr,
        rd₁₂', wr₁₂'⟩
      · rw [o₁₂ _ (by decide), r₁₁, g₁₀, rdx₉, show (128 : BitVec 32).signExtend 64 = BitVec.ofNat 64 128 from rfl,
          addr_add, show 128 * k + 128 = 128 * (k + 1) by omega_arith]
      · rw [r₁₂, r8₁₁, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
          VG.Offset.ofNat_sub_ofNat hge', show v - 8 = n - 8 * (k + 1) by omega_arith]
      · rw [o₁₂ _ (by decide), o₁₁ _ (by decide), g₁₀, rdi₉]
      · rw [hm, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata

end VG.Proof.Camellia.X86_64
