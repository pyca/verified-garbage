module

import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Sm4.X86_64.Core
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `Sm4.X86_64.Group`, which this module and modules that import it used -/

section

/-! ### `Sm4.X86_64.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced round keys on x86-64

`keyOne_step`: `keyOne h` bitslices round key `2 m + h`, half `h` of the
64-bit word at `rdi`, into the table's entry at `rsi`, every block's copy of
it alike. `keys_wp` builds the table in the order the rounds use the round
keys: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia.X86_64 (linEnvG linPostG linG_ok)
open VG.Proof.Sm4 (WordRel readW64_bit getLsbD_scheduleAt)

/-- Round key `2 m + h`, half `h` of the 64-bit word `x`. -/
def rkWord (x : BitVec 64) (h : Nat) : Spec.Sm4.Word := (x >>> (32 * h)).setWidth 32

theorem keyStore_eq (h : Nat) : keyOne h = keyLoad h ++ keyStore := rfl

/-- Round key `2 m + h` from the word at `rdi` to the entry at `rsi`. -/
theorem keyOne_step {s : State} {b : Addr} {e h : Nat} (hh : h = 0 ∨ h = 1)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hrsi : s.gpr .rsi = b + BitVec.ofNat 64 (8 * tableSlot + 64 * e)) (he : e < 32)
    (hrdi : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .rdi) 0) 8)
    (hsep : ∀ k < 64, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .rdi) 0) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne h) s = some s' ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      s'.gpr t1 = s.gpr t1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * 64⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot + 64 * e), 64⟩] s.mem s'.mem ∧
      WordRel (entryW s'.mem b e) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .rdi) 0) 64) h) := by
  rw [slots_eq] at hscr
  obtain hok : Ok keyCfg s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => by simp only [keyCfg] at hk ⊢; obtain rfl : k = 0 := by omega_arith
                              exact hrdi
      slots := by simp [keyCfg]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; obtain rfl : j = 0 := by omega_arith
        rw [hb]; exact hsep k hk }
  obtain hchk : check (lanes 64 7) keyCfg (linExt 0) (keyLoad h) keyEnv
      (linPostG 7 (qOuts (keyBsG h)) [] keyMaskSlots keyEnv) = true := by
    rcases hh with rfl | rfl
    · exact keyLoad0_check
    · exact keyLoad1_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkp₁, rd₁, wr₁, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .rdi) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega_arith, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₁ hkp₁ f₁
  obtain hall₁ : ∀ r, r ∉ sboxWrites → ((keyLoad h).all fun i => i.dst != some r) = true := fun r hr => by
    have : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (keyLoad h).all fun i => i.dst != some r) =
        true := by rcases hh with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r (not_sboxWrites r hr)
  obtain k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s.gpr r := fun r hr => o₁ r (hall₁ r hr)
  -- The planes of the round key.
  obtain hQ : WordRel (Qs s₁) (fun _ => rkWord (s.mem.readW (wordAddr (s.gpr .rdi) 0) 64) h) := by
    intro b' hb' i hi j hj
    obtain hp : 16 * i + b' < 64 := by omega_arith
    rw [Qs, ho₁ (q j) (keyBsG h j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      _ hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 32 * h + 8 * (3 - (16 * i + b') / 16) + j = 64 * 0 + (32 * h + 8 * (3 - i) + j) by omega_arith,
      bitOf_word _ _ _ (by rcases hh with rfl | rfl <;> omega_arith), rkWord, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    simp only [show 8 * (3 - i) + j < 32 by omega_arith, decide_true, Bool.true_and]
    exact congrArg (BitVec.getLsbD _) (by omega_arith)
  -- The stores.
  obtain hrsi₁ : s₁.gpr .rsi = s.gpr .rsi := k₁ .rsi (by decide)
  obtain hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hrsi₁, hrsi, wordAddr, addr_add, tableSlot_eq]
        exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
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
  obtain k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (by simp [keyStore, reduceInstrDst])
  obtain he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    obtain h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hrsi₁, hrsi, addr_add]
  obtain ht1 : s₁.gpr t1 = s.gpr t1 := o₁ t1 (by rcases hh with rfl | rfl <;> decide +kernel)
  refine ⟨s₂, ?_, fun r hr => by rw [k₂, k₁ r hr], by rw [k₂, ht1], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun kv hkv => ?_,
    ?_, hQ.congr fun j hj => he₂ j hj⟩
  · rw [keyStore_eq, runBlock_app, e₁, Option.bind_some, e₂]
  · have hk : kv.1 < 64 := mask_lt hkv
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    obtain h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hrsi₁, hrsi, hb, wordAddr]
      rw [tableSlot_eq]
      exact VG.Offset.disjoint b (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    rw [k₂, hb₁, h2, hkp₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hrsi₁, hrsi]

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

theorem movImm_ok (s : State) (r : Reg) (v : BitVec 64) :
    ∃ s', runBlock isa [.movImm64 r v] s = some s' ∧ s'.gpr r = v ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg r v, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec],
    by simp only [RegUpd.gpr_setReg_self], fun r' hr => by simp only [RegUpd.gpr_setReg_of_ne _ _ hr],
    rfl, rfl, rfl⟩

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `rsi` before iteration `m`, as an offset in the scratch buffer. -/
def rsiAt : Dir → Nat → Nat
  | .encrypt, m => 8 * tableSlot + 128 * m
  | .decrypt, m => 8 * tableSlot - 64 + 64 * (32 - 2 * m)

/-- The operation stepping `rsi`. -/
def rsiOp : Dir → AluOp
  | .encrypt => .add
  | .decrypt => .sub

/-- `rsi` moves from `x` to `y`. -/
def RsiStep : Dir → Nat → Nat → Prop
  | .encrypt, x, y => y = x + 64
  | .decrypt, x, y => x = y + 64

/-- `op rsi, 64`. -/
theorem rsiStep_ok (dir : Dir) (s : State) {b : Addr} {x y : Nat} (hxy : RsiStep dir x y)
    (hrsi : s.gpr .rsi = b + BitVec.ofNat 64 x) :
    ∃ s', runBlock isa [.alu (rsiOp dir) .rsi (.imm 64)] s = some s' ∧
      s'.gpr .rsi = b + BitVec.ofNat 64 y ∧
      (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr'⟩ := addImm_ok s .rsi 64
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    rw [r', hrsi, show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl, addr_add,
      show y = x + 64 from hxy]
  · obtain ⟨s', e', r', -, o', m', rd', wr'⟩ := subImm_ok s .rsi 64
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    have hxy : x = y + 64 := hxy
    rw [r', hrsi, show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl,
      VG.Offset.add_ofNat_sub _ (by omega_arith), show x - 64 = y by omega_arith]

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
  obtain hi : 2 * m + h < 32 := by omega_arith
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
  rsi : s.gpr .rsi = b + BitVec.ofNat 64 (rsiAt dir m)
  rdi : s.gpr .rdi = sched + BitVec.ofNat 64 (8 * m)
  cnt : s.gpr t1 = BitVec.ofNat 64 (16 - m)
  ent : ∀ i < 2 * m, WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem sched).getD i 0)
  masks : MasksOk s
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₀.gpr r
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
  obtain hb : ∀ k < 128, m' (sched + BitVec.ofNat 64 k) = m (sched + BitVec.ofNat 64 k) := fun k hk =>
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
    ∃ s', runBlock isa (keyOne 0 ++ ([.alu (rsiOp dir) .rsi (.imm 64)] : List Instr) ++ keyOne 1 ++
        ([.alu (rsiOp dir) .rsi (.imm 64), .alu .add .rdi (.imm 8), .alu .sub t1 (.imm 1)] : List Instr)) s = some s' ∧
      KInv s₀ b sched dir (m + 1) s' ∧ s'.zf = some (decide (m + 1 = 16)) := by
  have hpre := hi.pre
  have hfit := hpre.fit
  obtain he0 := entOf_lt dir (show 2 * m < 32 by omega_arith)
  obtain he1 := entOf_lt dir (show 2 * m + 1 < 32 by omega_arith)
  obtain hsched : Spec.Sm4.scheduleAt s.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hpre.sched_eq hi.frame
  -- Round key `2 m`.
  obtain ⟨s₁, e₁, o₁, t₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (h := 0) (e := entOf dir (2 * m)) (Or.inl rfl)
    hpre.base hpre.scr (by rw [hi.rsi, rsiAt_ent dir hm]) he0 (by rw [hi.rdi]; exact hpre.rdiIn hm)
    (fun k hk => by rw [hi.rdi]; exact hpre.rdiSep hm hk) hi.masks
  rw [hi.rdi, rkWord_eq _ _ hm (by decide), hsched] at E₁
  obtain ⟨st1, st2⟩ := rsiAt_succ dir hm
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := rsiStep_ok dir s₁ (b := b) (x := rsiAt dir m)
    (y := 8 * tableSlot + 64 * entOf dir (2 * m + 1)) st1
    (by rw [o₁ _ (by decide), hi.rsi])
  obtain hpre₂ : SchedPre s₂ b sched :=
    hpre.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  obtain hrdi₂ : s₂.gpr .rdi = sched + BitVec.ofNat 64 (8 * m) := by
    rw [o₂ _ (by decide), o₁ _ (by decide), hi.rdi]
  obtain hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact m₁ kv hkv
  -- Round key `2 m + 1`.
  obtain ⟨s₃, e₃, o₃, t₃, rd₃, wr₃, m₃, f₃, E₃⟩ := keyOne_step (h := 1) (e := entOf dir (2 * m + 1)) (Or.inr rfl)
    hpre₂.base hpre₂.scr r₂ he1 (by rw [hrdi₂]; exact hpre₂.rdiIn hm)
    (fun k hk => by rw [hrdi₂]; exact hpre₂.rdiSep hm hk) hm₂
  obtain hfr₂ : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s₂.mem := by
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
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdi 8
  obtain ⟨s₆, e₆, c₆, z₆, o₆, m₆, rd₆, wr₆⟩ := subImm_ok s₅ t1 1
  obtain ht₅ : s₅.gpr t1 = BitVec.ofNat 64 (16 - m) := by
    rw [o₅ _ (by decide), o₄ _ (by decide), t₃, o₂ _ (by decide), t₁, hi.cnt]
  obtain hmem : s₆.mem = s₃.mem := by rw [m₆, m₅, m₄]
  obtain hb₆ : s₆.gpr sb = s₃.gpr sb := by rw [o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide)]
  obtain hf₃ : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s₃.mem := by
    refine hfr₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [tableEnd_eq]
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega_arith)
    · rw [tableSlot_eq]; exact VG.Offset.sub_base b (by omega_arith)
  refine ⟨s₆, ?_, ⟨hpre₂.congr (by rw [hb₆, o₃ _ (by decide)]) (by rw [rd₆, rd₅, rd₄, rd₃])
      (by rw [wr₆, wr₅, wr₄, wr₃]), by rw [o₆ _ (by decide), o₅ _ (by decide), r₄], ?_, ?_, fun i hi' => ?_,
      fun kv hkv => ?_, by rw [hmem]; exact hf₃, fun r h1 h2 h3 => ?_,
      by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩, ?_⟩
  · rw [runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃,
      Option.bind_some,
      show ([Instr.alu (rsiOp dir) .rsi (.imm 64), .alu .add .rdi (.imm 8), .alu .sub t1 (.imm 1)] : List Instr) =
        [.alu (rsiOp dir) .rsi (.imm 64)] ++ ([.alu .add .rdi (.imm 8)] ++ [.alu .sub t1 (.imm 1)]) from rfl,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [o₆ _ (by decide), r₅, o₄ _ (by decide), o₃ _ (by decide), hrdi₂,
      show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl, addr_add,
      show 8 * m + 8 = 8 * (m + 1) by omega_arith]
  · rw [c₆, ht₅, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show 16 - m - 1 = 16 - (m + 1) by omega_arith]
  · have hent : ∀ i' < 32, i' ≠ entOf dir (2 * m) → i' ≠ entOf dir (2 * m + 1) → ∀ j < 8,
        entryW s₆.mem b i' j = entryW s.mem b i' j := fun i' hi'' h0 h1 j hj => by
      rw [hmem, entryW_frame f₃ hi'' he1 h1 hj, m₂, entryW_frame f₁ hi'' he0 h0 hj]
    rcases (show i < 2 * m ∨ i = 2 * m ∨ i = 2 * m + 1 by omega_arith) with hlt | rfl | rfl
    · exact (hi.ent i hlt).congr fun j hj => hent _ (entOf_lt dir (by omega_arith))
        (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith)
        (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith) j hj
    · refine E₁.congr fun j hj => ?_
      rw [hmem, entryW_frame f₃ he0 he1 (fun h => by have := entOf_inj dir (by omega_arith) (by omega_arith) h; omega_arith) hj, m₂]
    · exact E₃.congr fun j hj => by rw [hmem]
  · show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
    rw [hmem, hb₆]; exact m₃ kv hkv
  · rw [o₆ r (fun h => h1 (by subst h; decide)), o₅ r h3, o₄ r h2, o₃ r h1, o₂ r h2, o₁ r h1, hi.regs r h1 h2 h3]
  · rw [z₆, ht₅, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega_arith

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

/-- What the table's construction leaves. -/
structure KeysPost (s₀ : State) (b sched : Addr) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched))
  masks : MasksOk s
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd)
  frame : Frame [⟨b, 8 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop's body. -/
def tableBody (dir : Dir) : List Instr :=
  keyOne 0 ++ ([.alu (rsiOp dir) .rsi (.imm 64)] : List Instr) ++ keyOne 1 ++
    [.alu (rsiOp dir) .rsi (.imm 64), .alu .add .rdi (.imm 8), .alu .sub t1 (.imm 1)]

theorem keyLoop_wp (dir : Dir) {s₀ s : State} {b sched : Addr} (hi : KInv s₀ b sched dir 0 s) :
    WP isa (.loop (.block (tableBody dir)) .ne) s (KInv s₀ b sched dir 16) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 16 - m ∧ m < 16 ∧ KInv s₀ b sched dir m s)
    (fun n s hs => ?_) 16 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := keyIter_ok dir hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h16 : m + 1 = 16
  · exact .inl ⟨by simp [X86_64.eval, z', h16], by rw [h16] at hi'; exact hi'⟩
  · exact .inr ⟨by simp [X86_64.eval, z', h16], 16 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

theorem keysGen_wp (dir : Dir) (k : Nat) (hk : 8 * k = rsiAt dir 0)
    (hse : (BitVec.ofNat 32 (8 * k)).signExtend 64 = BitVec.ofNat 64 (8 * k))
    {s₀ : State} {b sched : Addr} (hp : SchedPre s₀ b sched) (hrdi : s₀.gpr .rdi = sched) (hm : MasksOk s₀) :
    WP isa (.seq (.seq (.block (slotAddr .rsi k ++ ([.movImm64 t1 16] : List Instr))) (.loop (.block (tableBody dir)) .ne))
      (.block (slotAddr .rdi tableEnd))) s₀ (KeysPost s₀ b sched dir) := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s₀ .rsi k hse
  obtain ⟨s₂, e₂, t₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s₁ t1 16
  obtain hinv : KInv s₀ b sched dir 0 s₂ := by
    refine ⟨hp.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]),
      by rw [o₂ _ (by decide), r₁, hp.base, hk], by rw [o₂ _ (by decide), o₁ _ (by decide), hrdi]; simp,
      by rw [t₂]; rfl, fun i hi => by omega_arith, fun kv hkv => ?_, by rw [m₂, m₁]; exact Frame.refl _ _,
      fun r h1 h2 _ => by rw [o₂ r (fun h => h1 (by subst h; decide)), o₁ r h2], by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, m₁, o₂ _ (by decide), o₁ _ (by decide)]; exact hm kv hkv
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂],
    WP.mono (keyLoop_wp dir hinv) fun s h => ?_⟩))
  have hfit := h.pre.fit
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s .rdi tableEnd (by decide)
  refine WP.of_runBlock ⟨s₃, e₃, h.pre.congr (o₃ _ (by decide)) rd₃ wr₃, ⟨?_, ?_, fun e he => ?_⟩, fun kv hkv => ?_,
    by rw [r₃, h.pre.base], by rw [m₃]; exact h.frame, fun r h1 h2 h3 => by rw [o₃ r h3, h.regs r h1 h2 h3],
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
    (hrdi : s₀.gpr .rdi = sched) (hm : MasksOk s₀) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  cases dir
  · exact keysGen_wp .encrypt tableSlot (by simp [rsiAt]) (by decide) hp hrdi hm
  · exact keysGen_wp .decrypt (tableSlot + 8 * 31) (by simp [rsiAt, tableSlot_eq]) (by decide) hp hrdi hm

end VG.Proof.Sm4.X86_64

end

end

/-! ### `Sm4.X86_64.Prologue`, which this module and modules that import it used -/

section

/-!
# SM4's prologue and epilogue on x86-64

Saving and restoring the callee-saved registers in their slots
(`save_ok`, `restore_ok`, by evaluation over names, as AES's), and setting
the masks of the round keys' planes (`setMasks_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (ofInt_nat)
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st imm setMasks)

theorem savedSlot_eq : savedSlot = 384 := rfl
theorem sb_ne_t0 : sb ≠ t0 := by decide

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .rbx | 1 => .rbp | 2 => .r12 | 3 => .r13 | 4 => .r14 | _ => .r15

def saveCfg : Cfg := { base := sb, slots := slots, ext := sb, exts := 0 }

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
  Ok.of_region hw hb.symm (by simp only [saveCfg]; omega_using []) (by simp [saveCfg, slots_eq]) rfl

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 6, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem := by
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
    have h := p.rel.slot (savedSlot + i) i (by simp only [saveCfg, slots_eq, savedSlot_eq]; omega_using [hi]) this
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
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
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

theorem setMasksN_ok (N : Nat) (hN : N ≤ slots) (ms : List (Nat × BitVec 64)) {s : State} {b : Addr}
    (hb : s.gpr sb = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : ∀ kv ∈ ms, kv.1 < N)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setMasks ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * N⟩] s.mem s'.mem := by
  rw [slots_eq] at hN
  induction ms generalizing s with
  | nil => exact ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | cons kv ms ih =>
    have hk0 : kv.1 < N := hk kv List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := setOne_ok (k := kv.1) kv.2 hb ⟨_, hw, by
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
      rw [show setMasks (kv :: ms) = [imm t0 kv.2, st kv.1 t0] ++ setMasks ms from rfl,
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

theorem setMasks_ok (ms : List (Nat × BitVec 64)) {s : State} {b : Addr} (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : ∀ kv ∈ ms, kv.1 < tableSlot)
    (hnd : (ms.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setMasks ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ k < slots, k ∉ ms.map (·.1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * tableSlot⟩] s.mem s'.mem :=
  setMasksN_ok tableSlot (by rw [tableSlot_eq, slots_eq]; omega_using []) ms hb hw hk hnd

end VG.Proof.Sm4.X86_64

end

end

/-! ### `Sm4.X86_64.Copy`, which only this module used -/

section

/-!
# Copying blocks on x86-64

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks of 16 bytes
from `rax` to `rbx` (areas that do not overlap), through `rbp`, counting
down `rcx`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (writeW_readW_apply off_sub_toNat off_sub_not not_in_of_disjoint ofInt_nat)
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

theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c ≤ 16)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_using [], hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega_using [hj])
  have hA1 := hA (2 * j + 1) (by omega_using [hj])
  have hB0 := hB (2 * j) (by omega_using [hj])
  have hB1 := hB (2 * j + 1) (by omega_using [hj])
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_using [hc16]) ht
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
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have hn : 16 * c < 2 ^ 64 := by omega_using [hc16]
  have r1 : s₁.gpr .rbx = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rbx]
  have a1 : s₁.gpr .rax = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rax]
  have hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.rbx, hi.rax, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_using [hj]) hn)]
  have hinv : CopyInv A B c s₀ (j + 1) s₅ := by
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
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_using [hc16, hj, ht])]; omega_using [ht]), off_sub_toNat B h8 (by omega_using [hc16, hj, ht]), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_using [h8], hA₁ t (by omega_using [hj, ht]), hAs t (by omega_using [hj, ht])]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_using [h8])) (by omega_using [hc16, hj, ht]) (by omega_using []) (by omega_using [hc16, hj])), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_using [hc16, hj, ht])]; omega_using [h8]), off_sub_toNat B h0 (by omega_using [hc16, hj, ht]), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_using [h0], hAs t (by omega_using [hj, ht])]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_using [h0])) (by omega_using [hc16, hj, ht]) (by omega_using []) (by omega_using [hc16, hj]))]
          exact hi.copied t (by omega_using [h0])
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_using [h]))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_using [hj])), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_using [hj]))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₅.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_using [hc16]) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_using [hj]
  by_cases hl : j + 1 = c
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega_using [hj, hl], c - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hinv⟩

end VG.Proof.Sm4.X86_64

end

end


/-!
# A group of blocks of SM4 ECB on x86-64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(sixteen, or the last one to fifteen) to the tail buffer, transforms the
tail buffer (`crypt16_wp`), copies the blocks back and steps to the next
group.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (DInv ofInt_nat quads ofBlock outBlock)
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)


/-! ## Small blocks -/

theorem cmpImm_ok (s : State) (r : Reg) (k : BitVec 32) {v K : Nat} (hr : s.gpr r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 64) (hk : (k.signExtend 64).toNat = K) :
    ∃ s', runBlock isa [.alu .cmp r (.imm k)] s = some s' ∧ s'.cf = some (decide (v < K)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r - k.signExtend 64) (decide ((s.gpr r).toNat < (k.signExtend 64).toNat))
    (subOverflow (s.gpr r) (k.signExtend 64) (s.gpr r - k.signExtend 64)), ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp [arithFlags, State.setFlags, hr, hk]; rw [Nat.mod_eq_of_lt (by simpa using hv)]

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

/-- `rcx := min(r8, 16)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r8 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min v 16) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := movImm_ok s .rcx 16
  obtain ⟨s₂, e₂, f₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok s₁ .r8 16 (v := v) (by rw [o₁ _ (by decide), hr]) hv rfl
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([Instr.movImm64 .rcx 16, .alu .cmp .r8 (.imm 16)] : List Instr) =
      [.movImm64 .rcx 16] ++ [.alu .cmp .r8 (.imm 16)] from rfl, runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.ite (decide (v < 16)) (by simp [X86_64.eval, f₂]) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rcx .r8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => ?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
    · rw [r₃, g₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_using [h])]
    · rw [o₃ r hr, g₂, o₁ r hr]
  · refine WP.of_runBlock ⟨s₂, rfl, ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [g₂, c₁, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl
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

/-- The slots `ScrOk` reads: 48–50, the table (128–383) and 384–389. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 24⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 48⟩]

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : 48 ≤ kv.1 ∧ kv.1 < 51 := by
  simp [keyMasks] at hkv; rcases hkv with h | h | h <;> subst h <;> simp [evenSlot, oddSlot, grpSlot]

theorem ScrOk.frame {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b E m' := by
  have hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
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
  have hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
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

/-- `copyBlocks` from `rax` to `rbx`, `rcx` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc16 : c ≤ 16)
    (hx : s.gpr .rax = X) (hy : s.gpr .rbx = Y) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc16 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (256 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd)
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n (16 * k) (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Sm4.X86_64

end

end

/-! ### `Sm4.X86_64.Crypt16`, which this module and modules that import it used -/

section

/-!
# The transposes, and sixteen blocks of bitsliced SM4 on x86-64

`toBs_step` turns the sixteen blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt16_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)
open VG.Proof.Camellia.X86_64 (linEnvG linPostG linG_ok)
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
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  extIn k hk := by simp [bsCfg] at hk
  slots := by simp only [bsCfg, tableSlot_eq]; omega_arith
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
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  obtain ⟨s', h', -, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega_arith, by omega_arith, rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkp
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => toBs.all fun i => i.dst != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), fun w hw b hb i hi j hj => ?_⟩
  · rw [slotW, hb', hkp kv.1 (List.mem_map_of_mem hkv) (by have := mask_lt hkv; rw [tableSlot_eq]; omega_arith)]
    exact hc.masks kv hkv
  · have hp16 : 16 * i + b < 64 := by omega_arith
    have hmem := hso (64 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
        simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq]; omega_arith) _ hp16
    rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith] at hmem
    have ht : 8 * (4 * (w % 2) + i) + j < 64 := by omega_arith
    show (slotW s' (stateSlot w j)).getLsbD (16 * i + b) = _
    rw [slotW, hb', show stateSlot w j = 64 + (8 * w + j) by simp only [stateSlot]; omega_arith, hmem, toBsG,
      show (16 * i + b) % 16 = b by omega_arith, show (16 * i + b) / 16 = i by omega_arith, xorBits_cons, xorBits_nil,
      Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW64_bit _ _ (by omega_arith) hj]
    simp only [ofBlock]
    rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega_arith), byte_addr _ rfl, addr_add]
    rw [show 8 * (tailSlot + (2 * b + w / 2)) + (4 * (w % 2) + i) = 8 * tailSlot + 16 * b + (4 * w + i) by omega_arith]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ StRel s' X ∧
      ∀ b < 16, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  obtain ⟨s', h', -, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (64 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkp
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => fromBs.all fun i => i.dst != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have keep : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s' k = slotW s k := fun k hk => by
    have hk' : k < 128 := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega_arith
    rw [slotW, hb', hkp k hk (by rw [tableSlot_eq]; exact hk')]
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
    (hrdi : s₀.gpr .rdi = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) :
    WP isa crypt16 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 16, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, -, X₁⟩ := toBs_step hp (Ctx.refl hm)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hrdi₁ : s₁.gpr .rdi = s₁.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [c₁.keep _ (by decide) (by decide), c₁.base, hrdi]
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) c₁.masks hrdi₁ X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.X86_64

end

end

/-! ### `Sm4.X86_64.GroupStep`, which only this module used -/

section

/-!
# One group of blocks of SM4 ECB on x86-64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks to
the tail buffer, transforms them there (`crypt16_wp`), copies them back and
steps to the next group.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)
open VG.Proof.Sm4 (DInv ofInt_nat quads ofBlock outBlock not_contains_off toNat_off blockAt_getD)

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa Impl.Sm4.X86_64.group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n E (k + 1) s') := by
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
  unfold Impl.Sm4.X86_64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r8 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .rax .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := slotAddr_ok s₂a .rbx tailSlot (by decide)
  obtain base₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), o₂a _ (by decide), o₁ _ (by decide), hi.base]
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂ r h2, o₂a r h1, o₁ r h3]
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₂a, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide), hi.rdx])
    (by rw [r₂, o₂a _ (by decide), o₁ _ (by decide), hi.base])
    (by rw [o₂ _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain g₃' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame f₃' fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega_arith
  -- The sixteen blocks.
  obtain hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  obtain hrdi₃ : s₃.gpr .rdi = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hi.rdi, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) hrdi₃) fun s₄ ⟨c₄, b₄⟩ => ?_)
  obtain base₄ : s₄.gpr sb = b := by rw [c₄.base, base₃]
  obtain f₄ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₄.mem := by have := c₄.frame; rw [base₃] at this; exact this
  obtain g₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [c₄.keep r h1 h2, g₃' r (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))
      (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))]
  obtain sc₄ : ScrOk s₀ b E s₄.mem := by
    refine sc₃.frame2 f₄ (c₄.masks.at base₄) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
  -- The tail buffer back to the group's blocks.
  obtain r8₄ : s₄.gpr .r8 = BitVec.ofNat 64 v := by rw [g₄ _ (by decide) (by decide), hi.r8]
  obtain rdx₄ : s₄.gpr .rdx = A := by rw [g₄ _ (by decide) (by decide), hi.rdx]
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r8₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ => ?_))
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := slotAddr_ok s₅ .rax tailSlot (by decide)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₆a .rbx .rdx
  refine WP.seq (WP.of_runBlock ⟨s₆, by rw [runBlock_app, e₆a, Option.bind_some, e₆], ?_⟩)
  obtain mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₆a, m₅]
  obtain wr₄' : s₄.wr = s.wr := by rw [c₄.wr, wr₃']
  obtain rd₄' : s₄.rd = s.rd := by rw [c₄.rd, rd₃']
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅, wr₄']
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅, rd₄']
  obtain g₆ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₆.gpr r = s₄.gpr r := fun r h1 h2 h3 => by
    rw [o₆ r h2, o₆a r h1, o₅ r h3]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₆ _ (by decide), r₆a, o₅ _ (by decide), base₄])
    (by rw [r₆, o₆a _ (by decide), o₅ _ (by decide), rdx₄])
    (by rw [o₆ _ (by decide), o₆a _ (by decide), c₅])
    (fun t ht => by rw [rd₆', wr₆']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₆']; exact inA t ht) sepAT.symm) fun s₇ ⟨cp₇, f₇, g₇, rd₇, wr₇⟩ => ?_
  obtain g₇' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₇.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 => by rw [g₇ r h1 h2 h3 h4, g₆ r h1 h2 h3]
  obtain base₇ : s₇.gpr sb = b := by rw [g₇' _ (by decide) (by decide) (by decide) (by decide), base₄]
  obtain rdx₇ : s₇.gpr .rdx = A := by rw [g₇' _ (by decide) (by decide) (by decide) (by decide), rdx₄]
  obtain r8₇ : s₇.gpr .r8 = BitVec.ofNat 64 v := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), r8₄]
  obtain rdi₇ : s₇.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide), hi.rdi]
  obtain rsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide), hi.rsp]
  obtain wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆', hi.wr]
  obtain rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₇ : ScrOk s₀ b E s₇.mem := by
    refine (mem₆ ▸ sc₄).frame f₇ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₇ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₇.mem := by
    refine ((f₃'.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₆ ▸ f₇).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
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
  obtain hdata : DInv s₀.mem s₇.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega_arith]
      rw [e1, cp₇ _ (by omega_arith), mem₆, ite_eq_left (show i < 16 * (16 * k + c) by omega_arith),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega_arith, show i % 16 = (i - 256 * k) % 16 by omega_arith]
      obtain hj : (i - 256 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 256 * k) = s₄.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₄, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₄.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₄ _).getD _ 0 = _
      rw [b₄ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₇ _ hout, mem₆,
        f₄.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega_arith), ite_eq_left (show i < 16 * (16 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₇.mem := hi.frame.trans fr₇
  -- On to the next group.
  unfold advance
  obtain ⟨s₈, e₈, cf₈, g₈, m₈, rd₈, wr₈⟩ := cmpImm_ok s₇ .r8 16 r8₇ hv rfl
  refine WP.seq (WP.of_runBlock ⟨s₈, e₈, ?_⟩)
  refine WP.ite (decide (v < 16)) (by simp [X86_64.eval, cf₈]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt' : v < 16 := by simpa using hlt
    obtain ⟨s₉, e₉, z₉, o₉, m₉, rd₉, wr₉⟩ := subSelf_ok s₈ .r8
    refine WP.of_runBlock ⟨s₉, e₉, .inl ⟨z₉, ?_⟩⟩
    obtain hn : 16 * k + c = n := by omega_arith
    refine ⟨by rw [o₉ _ (by decide), g₈, base₇], by rw [o₉ _ (by decide), g₈, rsp₇],
      by rw [m₉, m₈]; exact sc₇, fun i hi' => by rw [m₉, m₈, hdata i hi', hn], by rw [m₉, m₈]; exact fr,
      by rw [rd₉, rd₈, rd₇'], by rw [wr₉, wr₈, wr₇']⟩
  · have hge' : 16 ≤ v := by simpa using hge
    obtain hc : c = 16 := by omega_arith
    obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := addImm_ok s₈ .rdx 256
    obtain ⟨s₁₀, e₁₀, r₁₀, z₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subImm_ok s₉ .r8 16
    obtain r8₉ : s₉.gpr .r8 = BitVec.ofNat 64 v := by rw [o₉ _ (by decide), g₈, r8₇]
    obtain hz : s₁₀.zf = some (decide (v = 16)) := by
      rw [z₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq hv (by decide)]
    refine WP.of_runBlock ⟨s₁₀, by
      rw [show ([Instr.alu .add .rdx (.imm 256), .alu .sub .r8 (.imm 16)] : List Instr) =
        [.alu .add .rdx (.imm 256)] ++ [.alu .sub .r8 (.imm 16)] from rfl, runBlock_app, e₉,
        Option.bind_some, e₁₀], ?_⟩
    obtain hm : s₁₀.mem = s₇.mem := by rw [m₁₀, m₉, m₈]
    obtain base₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, base₇]
    obtain rsp₁₀ : s₁₀.gpr .rsp = s₀.gpr .rsp := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rsp₇]
    obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₇']
    obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₇']
    by_cases h16 : v = 16
    · refine .inl ⟨by rw [hz, h16]; rfl, base₁₀, rsp₁₀, hm ▸ sc₇, ?_, hm ▸ fr, rd₁₀', wr₁₀'⟩
      intro i hi'
      rw [hm, hdata i hi', show 16 * k + c = n by omega_arith]
    · refine .inr ⟨by rw [hz]; simp [h16], base₁₀, rsp₁₀, ?_, ?_, by omega_arith, ?_, hm ▸ sc₇, ?_, hm ▸ fr,
        rd₁₀', wr₁₀'⟩
      · rw [o₁₀ _ (by decide), r₉, g₈, rdx₇, show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl,
          addr_add, show 256 * k + 256 = 256 * (k + 1) by omega_arith]
      · rw [r₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
          VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - 16 = n - 16 * (k + 1) by omega_arith]
      · rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rdi₇]
      · intro i hi'
        rw [hm, hdata i hi', show 16 * k + c = 16 * (k + 1) by omega_arith]

end VG.Proof.Sm4.X86_64

end

end


/-!
# SM4 ECB on x86-64: the whole function

`ecb_wp`: with the working space as an argument (`ecbX86_64`), `ecb dir`
saves the callee-saved registers, sets the masks, builds the table of round
keys in the order `dir` uses them, transforms the blocks a group at a time
(`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- The specification's direction. -/
def specDir : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86-64 with its working space at `rcx`. -/
def ecbX86_64 (dir : Dir) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)) (specDir dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st setMasks)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDir ecbX86_64 crypt_eq quads ofBlock outBlock)

theorem testSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (s.gpr r == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r &&& s.gpr r) false false, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_arithFlags, BitVec.and_self]

theorem dataLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop Impl.Sm4.X86_64.group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 16 * (k + 1), by have := d.lt; have := hk.lt; omega_arith,
      k + 1, rfl, d⟩

theorem sreg_ne (i : Nat) : sreg i ≠ .r9 ∧ sreg i ≠ .r8 ∧ sreg i ≠ .rdx := by
  unfold sreg; split <;> decide

theorem prologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .rcx = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] : List Instr) ++ saveRegs ++
        setMasks keyMasks) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r8 = s₀.gpr .rdx ∧ s.gpr .rdx = s₀.gpr .rsi ∧
      (∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .rdx → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .rcx
  obtain ⟨s₁b, e₁b, r₁b, o₁b, m₁b, rd₁b, wr₁b⟩ := movR_ok s₁a .r8 .rdx
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁b .rdx .rsi
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), o₁b _ (by decide), r₁a, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁, wr₁b, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁, wr₁b, wr₁a]; exact hw) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega_using [this])
    (by decide)
  obtain g₁ : ∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ .rdx → s₁.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [o₁ r h3, o₁b r h2, o₁a r h1]
  refine ⟨s₃, by
    rw [runBlock_app, runBlock_app, show ([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] : List Instr) =
      [movR sb .rcx] ++ ([movR .r8 .rdx] ++ [movR .rdx .rsi]) from rfl, runBlock_app, e₁a, Option.bind_some,
      runBlock_app, e₁b, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some, e₃],
    by rw [g₃ _ (by decide), g₂, hb₁], by rw [g₃ _ (by decide), g₂, o₁ _ (by decide), r₁b, o₁a _ (by decide)],
    by rw [g₃ _ (by decide), g₂, r₁, o₁b _ (by decide), o₁a _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [g₃ r h4, g₂, g₁ r h1 h2 h3], fun i hi => ?_, fun kv hkv => v₃ kv hkv, ?_,
    by rw [rd₃, rd₂, rd₁, rd₁b, rd₁a], by rw [wr₃, wr₂, wr₁, wr₁b, wr₁a]⟩
  · obtain ⟨n1, n2, n3⟩ := sreg_ne i
    rw [← g₁ _ n1 n2 n3, ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  · have hm1 : s₁.mem = s₀.mem := by rw [m₁, m₁b, m₁a]
    rw [← hm1]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_using [])

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j = blockFn sch (specDir dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDir, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDir, Spec.Sm4.decryptBlock, crypt_eq]; rfl

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86_64 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => gprPreserved s₀ s' ∧ (ecbX86_64 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, dRD, dRS, fitK, fitD, fitB⟩ := hp
  let b := s₀.gpr .rcx
  let D := s₀.gpr .rsi
  let n := (s₀.gpr .rdx).toNat
  let sched := s₀.gpr .rdi
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r8₁, rdx₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  obtain rdi₁ : s₁.gpr .rdi = sched := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ rdi₁ m₁) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem sched)
  obtain hsch : Spec.Sm4.scheduleAt s₁.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    hk₁.sched_eq' (Nat.le_refl _) f₁
  have hfitB := fitB
  rw [slots_eq] at hfitB
  obtain f₀₂ : Frame [⟨b, 8 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega_using [])⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  obtain sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨k₂.masks.at base₂, fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega_using [])
        (by rw [savedSlot_eq]; omega_using [hi])
  obtain data₂ : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi =>
    f₀₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS)
      (by simp only; omega) hi
  obtain fr₂ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]
  obtain r8₂ : s₂.gpr .r8 = s₀.gpr .rdx := by rw [k₂.regs _ (by decide) (by decide) (by decide), r8₁]
  obtain rdx₂ : s₂.gpr .rdx = D := by rw [k₂.regs _ (by decide) (by decide) (by decide), rdx₁]
  obtain rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- Any blocks?
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ .r8
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [z₃, r8₂]
    congr 1
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₃]) (fun h0 => ?_) (fun h0 => ?_)) fun s₄ d₄ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [g₃, base₂], by rw [g₃, rsp₂], by rw [m₃]; exact sc₂, fun i hi => by omega,
      by rw [m₃]; exact fr₂, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitB, fitD⟩ ⟨by rw [g₃, base₂], by rw [g₃, rsp₂],
      by rw [g₃, rdx₂]; simp, by rw [g₃, r8₂, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega_using [hn0],
      by rw [g₃, k₂.rdi], by rw [m₃]; exact sc₂, fun i hi => ?_, by rw [m₃]; exact fr₂, by rw [rd₃, rd₂],
      by rw [wr₃, wr₂]⟩
    rw [m₃, data₂ i hi, ite_eq_right (by omega_using [])]
  -- The epilogue.
  obtain ⟨s₅, e₅, rg₅, o₅, f₅, rd₅, wr₅⟩ := restore_ok (by rw [d₄.wr]; exact hwS) d₄.base d₄.scr.saved
  refine WP.of_runBlock ⟨s₅, e₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₅ 0 (by omega_using [])
    · exact rg₅ 1 (by omega_using [])
    · rw [o₅ _ (fun i hi => by unfold sreg; split <;> decide), d₄.rsp]
    · exact rg₅ 2 (by omega_using [])
    · exact rg₅ 3 (by omega_using [])
    · exact rg₅ 4 (by omega_using [])
    · exact rg₅ 5 (by omega_using [])
  · -- The return address is untouched.
    obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₅.mem :=
      d₄.frame.trans (f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩)
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · have hd₅ : DInv s₀.mem s₅.mem D n n (outF s₀.mem D E) := fun i hi => by
      rw [f₅.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dDS.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp only; omega) hi]
      exact d₄.data i hi
    show Spec.Sm4.blocksAt s₅.mem D n = _
    rw [blocksAt_of_dinv hd₅, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem _ D j

end VG.Proof.Sm4.X86_64
