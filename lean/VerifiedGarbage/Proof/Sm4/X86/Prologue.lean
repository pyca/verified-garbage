module

public import VerifiedGarbage.Proof.Sm4.X86.Core
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Sm4.X86.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced round keys on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/Group.lean`): `keyOne_step` bitslices the round
key at `ecx` (through slot 0) into the table's entry at `kp`, every block's
copy of it alike, and `keys_wp` builds the table in the order the rounds use
the round keys: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Bitslice (bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs movR addI subI movI at_ argOp)
open VG.Proof.Sm4 (getLsbD_scheduleAt)

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega_arith | (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

/-- The schedule at `sched`, apart from the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  sch : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨sched.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : BitVec 32} (h : SchedPre s b sched)
    (hb : s'.gpr sb = s.gpr sb) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- Round key `i` of the schedule at `sched`. -/
theorem SchedPre.keyIn {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (addr (sched + BitVec.ofNat 32 (4 * i)) 0) 4 :=
  ⟨_, h.sch, by
    have := h.schFit
    have := setWidth_toNat sched
    rw [addr, BitVec.add_zero, ← addr, addr_eq (by omega_arith)]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The word at round key `i` is round key `i`. -/
theorem key_word (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32) {i : Nat} (hi : i < 32) :
    m.readW (addr (sched + BitVec.ofNat 32 (4 * i)) 0) 32 =
      (Spec.Sm4.scheduleAt m (sched.setWidth 64)).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega_arith,
    getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith), readW32_bit _ _ (by omega_arith) (by omega_arith),
    addr, BitVec.add_zero, ← addr, addr_eq (by omega_arith), VG.Offset.add_add]

/-- The table's entry `e` at `b`. -/
theorem entry_addr {b : BitVec 32} {e j : Nat} :
    wordAddr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) j = wordAddr b (tableSlot + 8 * e + j) := by
  simp only [wordAddr, addr]
  rw [VG.Offset.add_add, show 4 * tableSlot + 32 * e + 4 * j = 4 * (tableSlot + 8 * e + j) by omega_arith]

/-- `mov eax, [ecx]; bswap eax; mov [edi], eax`. -/
theorem keyWord_ok (s : State) {b : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b)
    (h : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) 0) 4) :
    ∃ s', runBlock isa keyWord s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b 0) (bswap (s.mem.readW (addr (s.gpr .ecx) 0) 32)) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let x := s.mem.readW (addr (s.gpr .ecx) 0) 32
  let s₂ := (s.setReg .eax x).setReg .eax (bswap x)
  have hw₂ : InRegions s₂.wr (s₂.ea (VG.Impl.Aes.X86.slotAt sb 0)) 4 := by
    show InRegions s.wr (wordAddr (s₂.gpr sb) 0) 4
    rw [show s₂.gpr sb = b by
      simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ (show sb ≠ .eax by decide), hb]]
    exact hw.slot (by decide)
  refine ⟨{ s₂ with mem := s₂.mem.writeW (s₂.ea (VG.Impl.Aes.X86.slotAt sb 0)) (s₂.gpr .eax) }, ?_, ?_,
    fun r hr => by
      show s₂.gpr r = _
      simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl⟩
  · rw [keyWord, runBlock_cons, show exec (.mov .eax (.mem (at_ .ecx 0))) s = some (s.setReg .eax x) by
        simp [exec, readSrc, State.load32, at_, ea_mk, h, x], runStep_some, runBlock_cons,
      show exec (.bswap .eax) (s.setReg .eax x) = some s₂ by simp only [exec, RegUpd.gpr_setReg_self]; rfl,
      runStep_some, runBlock_cons]
    simp only [VG.Impl.Aes.X86.st, exec, State.store32, hw₂, ↓reduceIte, runStep_some, runBlock_nil]
  · show s.mem.writeW (s₂.ea (VG.Impl.Aes.X86.slotAt sb 0)) (s₂.gpr .eax) = _
    rw [RegUpd.gpr_setReg_self]
    congr 1
    show wordAddr (s₂.gpr sb) 0 = _
    simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ (show sb ≠ .eax by decide), hb]

/-- The round key at `ecx` to the entry at `kp`. -/
theorem keyOne_step {s : State} {b sched : BitVec 32} {e i : Nat} (hp : SchedPre s b sched)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) (he : e < 32)
    (hr : s.gpr .ecx = sched + BitVec.ofNat 32 (4 * i)) (hi : i < 32) :
    ∃ s', runBlock isa keyOne s = some s' ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨(b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)).setWidth 64, 32⟩, ⟨wordAddr b 0, 4⟩] s.mem s'.mem ∧
      W32.WordRel (entryW s'.mem b e) (fun _ => (Spec.Sm4.scheduleAt s.mem (sched.setWidth 64)).getD i 0) := by
  have hfit := hp.scr.fit
  rw [slots_eq] at hfit
  -- The word.
  obtain ⟨s₁, e₁, m₁, o₁, rd₁, wr₁⟩ := keyWord_ok s hp.base hp.scr (by rw [hr]; exact hp.keyIn hi)
  rw [hr, key_word _ hp.schFit hi] at m₁
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (by decide)
  have b₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hp.base]
  have w₀ : s₁.mem.readW (wordAddr b 0) 32 = bswap ((Spec.Sm4.scheduleAt s.mem (sched.setWidth 64)).getD i 0) := by
    rw [m₁, Mem.readW_writeW_self32]
  -- Its planes, to the entry.
  have hok : Ok entryCfg s₁ :=
    { slotIn := fun k hk => by
        simp only [entryCfg] at hk ⊢
        rw [wr₁, kp₁, hkp, entry_addr]
        exact hp.scr.slot (by rw [slots_eq, tableSlot_eq]; omega_arith)
      extIn := fun k hk => by
        simp only [entryCfg] at hk ⊢
        obtain rfl : k = 0 := by omega_arith
        rw [b₁, wr₁, rd₁]
        obtain ⟨r, hr, hc⟩ := hp.scr.slot (k := 0) (by decide)
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      fit := by
        simp only [entryCfg]; rw [kp₁, hkp, BitVec.toNat_add, BitVec.toNat_ofNat, tableSlot_eq]
        have := b.isLt
        rw [Nat.mod_eq_of_lt (show 384 + 32 * e < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      sep := fun k hk j hj => by
        simp only [entryCfg] at hk hj ⊢
        obtain rfl : j = 0 := by omega_arith
        rw [kp₁, hkp, entry_addr, b₁]
        exact slot_sep b (by rw [tableSlot_eq]; omega_arith) (by omega_arith) (by rw [tableSlot_eq]; omega_arith) }
  obtain ⟨s₂, e₂, hso₂, rd₂, wr₂, o₂, f₂⟩ := linear_ok keyPlanes_check hok (fun _ => s₁.mem.readW (wordAddr b 0) 32)
    (fun j i hji => by simp at hji)
    (fun j hj => by
      simp only [entryCfg] at hj ⊢
      obtain rfl : j = 0 := by omega_arith
      exact ⟨by omega_arith, by rw [b₁]⟩)
  simp only [entryCfg] at hso₂ f₂
  have hall₂ : ([Reg.eax, .ecx, .esp, .ebp, .esi, .edi].all fun r =>
      keyPlanes.all fun i => i.dst != some r) = true := by decide +kernel
  have k₂ : ∀ r ∈ [Reg.eax, .ecx, .esp, .ebp, .esi, .edi], s₂.gpr r = s₁.gpr r := fun r hr =>
    o₂ r (List.all_eq_true.mp hall₂ r hr)
  refine ⟨s₂, ?_, fun r h0 h1 h2 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun b' hb' i' hi' j hj => ?_⟩
  · rw [keyOne, runBlock_app, e₁, Option.bind_some, e₂]
  · rw [k₂ r (by revert h0 h1 h2; cases r <;> decide), o₁ r h0]
  · refine Frame.trans (fun x hx => ?_) (f₂.mono fun r hr => ?_)
    · rw [m₁]
      simp only [Mem.writeW, Mem.write]
      exact ite_eq_right fun h => hx _ (List.mem_cons_of_mem _ List.mem_cons_self) (by
        simp only [Region.Contains]; revert h; simp only [Nat.reduceDiv]; omega_arith)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [kp₁, hkp]; exact List.mem_cons_self
  · have hp' : 8 * i' + b' < 32 := by omega_arith
    have h := hso₂ j (keyBsG j) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) _ hp'
    rw [keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 8 * ((8 * i' + b') / 8) + j = 32 * 0 + (8 * i' + j) by omega_arith, bitOf_word _ _ _ (by omega_arith), w₀,
      bswap_bit _ hi' hj, kp₁, hkp, entry_addr] at h
    rw [entryW, h]

/-! ## The loop -/

/-- The entry of round key `i`: `i` for encryption, `31 - i` for decryption. -/
def entOf : Dir → Nat → Nat
  | .encrypt, i => i
  | .decrypt, i => 31 - i

/-- `kp` before iteration `m`, as an offset in the scratch buffer. -/
def kpAtIter : Dir → Nat → Nat
  | .encrypt, m => 4 * tableSlot + 32 * m
  | .decrypt, m => 4 * tableSlot - 32 + 32 * (32 - m)

/-- The instruction stepping `kp`. -/
def kpStep : Dir → Instr
  | .encrypt => addI kp 32
  | .decrypt => subI kp 32

/-- The loop's body. -/
def tableBody (dir : Dir) : List Instr :=
  keyOne ++ ([addI .ecx 4, kpStep dir, subI .ebp 1] : List Instr)

theorem keys_eq (dir : Dir) :
    keys dir = .seq (.block (([.mov .ecx (.mem (argOp 0))] : List Instr) ++
      kpAt (match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31) ++ ([movI .ebp 32] : List Instr)))
      (.loop (.block (tableBody dir)) .ne) := by
  cases dir <;> rfl

theorem kpAtIter_ent (dir : Dir) {m : Nat} (hm : m < 32) :
    kpAtIter dir m = 4 * tableSlot + 32 * entOf dir m := by
  cases dir <;> simp only [kpAtIter, entOf, tableSlot_eq] <;> omega_arith

theorem entOf_lt (dir : Dir) {i : Nat} (hi : i < 32) : entOf dir i < 32 := by cases dir <;> simp [entOf] <;> omega_arith

theorem entOf_inj (dir : Dir) {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : entOf dir i = entOf dir i') :
    i = i' := by cases dir <;> simp [entOf] at h <;> omega_arith

theorem entOf_entOf (dir : Dir) {e : Nat} (he : e < 32) : entOf dir (entOf dir e) = e := by
  cases dir <;> simp [entOf] <;> omega_arith

/-- `kp ± 32`. -/
theorem kpStep_ok (dir : Dir) (s : State) {b : BitVec 32} {m : Nat} (hm : m < 32)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)) :
    ∃ s', runBlock isa [kpStep dir] s = some s' ∧ s'.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir (m + 1)) ∧
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases dir
  · obtain ⟨s', e', r', -, o', m', rd', wr'⟩ := addI_ok s kp 32
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, VG.Offset.add_add]
    simp only [kpAtIter]; rw [show 4 * tableSlot + 32 * m + 32 = 4 * tableSlot + 32 * (m + 1) by omega_arith]
  · obtain ⟨s', e', r', -, o', m', rd', wr'⟩ := subI_ok s kp 32
    refine ⟨s', e', ?_, o', m', rd', wr'⟩
    simp only [kpAtIter] at hkp ⊢
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
      show 4 * tableSlot - 32 + 32 * (32 - m) = (4 * tableSlot - 32 + 32 * (32 - (m + 1))) + 32 by
        rw [tableSlot_eq]; omega_arith, ← VG.Offset.add_add, BitVec.add_sub_cancel]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e i : Nat}
    (hf : Frame [⟨(b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)).setWidth 64, 32⟩, ⟨wordAddr b 0, 4⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  rw [slots_eq] at hfit
  have hb := setWidth_toNat b
  rw [show (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)).setWidth 64 = wordAddr b (tableSlot + 8 * e) by
      simp only [wordAddr, addr]; rw [show 4 * (tableSlot + 8 * e) = 4 * tableSlot + 32 * e by omega_arith],
    slot_addr (b := b) (k := tableSlot + 8 * e) (by rw [tableSlot_eq]; omega_arith),
    slot_addr (b := b) (k := 0) (by omega_arith)] at hf
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega_arith)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [tableSlot_eq] at *
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The entries' and slot 0's frame is inside the table and the S-box's slots. -/
theorem entry_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 32) :
    ∀ r ∈ [(⟨(b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)).setWidth 64, 32⟩ : Region), ⟨wordAddr b 0, 4⟩],
      Region.Sub r ⟨b.setWidth 64, 4 * tableEnd⟩ := fun r hr => by
  rw [slots_eq] at hfit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [show (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)).setWidth 64 = addr b (4 * tableSlot + 32 * e) from rfl,
      addr_eq (by rw [tableSlot_eq]; omega_arith), tableSlot_eq, tableEnd_eq]
    exact VG.Offset.sub_base _ (by omega_arith)
  · rw [slot_addr (by omega_arith), tableEnd_eq]
    exact VG.Offset.sub_base _ (by omega_arith)

/-- What the loop keeps, after `m` of its 32 iterations. -/
structure KInv (s₀ : State) (b sched : BitVec 32) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : SchedPre s b sched
  kpv : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)
  ptr : s.gpr .ecx = sched + BitVec.ofNat 32 (4 * m)
  cnt : s.gpr .ebp = BitVec.ofNat 32 (32 - m)
  ent : ∀ i < m, W32.WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64)).getD i 0)
  frame : Frame [⟨b.setWidth 64, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ kp → r ≠ .ebp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The schedule is outside the scratch buffer. -/
theorem SchedPre.sched_eq {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨b.setWidth 64, 4 * n⟩] m m') :
    Spec.Sm4.scheduleAt m' (sched.setWidth 64) = Spec.Sm4.scheduleAt m (sched.setWidth 64) := by
  have hb : ∀ k < 128, m' (sched.setWidth 64 + BitVec.ofNat 64 k) = m (sched.setWidth 64 + BitVec.ofNat 64 k) :=
    fun k hk => hf.bytes (R := ⟨sched.setWidth 64, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_right (Region.sub_prefix (by omega_arith))) (by show 128 ≤ 2 ^ 64; omega_arith) hk
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith), hb (4 * i + 3) (by omega_arith)]

/-- One iteration: round key `m`. -/
theorem keyIter_ok (dir : Dir) {s₀ s : State} {b sched : BitVec 32} {m : Nat} (hm : m < 32)
    (hi : KInv s₀ b sched dir m s) :
    ∃ s', runBlock isa (tableBody dir) s = some s' ∧ KInv s₀ b sched dir (m + 1) s' ∧
      s'.zf = some (decide (m + 1 = 32)) := by
  have hpre := hi.pre
  have hfit := hpre.scr.fit
  have he := entOf_lt dir hm
  have hsched : Spec.Sm4.scheduleAt s.mem (sched.setWidth 64) = Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64) :=
    hpre.sched_eq (by rw [tableEnd_eq, slots_eq]; omega_arith) hi.frame
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, f₁, E₁⟩ := keyOne_step (e := entOf dir m) hpre
    (by rw [hi.kpv, kpAtIter_ent dir hm]) he hi.ptr hm
  rw [hsched] at E₁
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .ecx 4
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := kpStep_ok dir s₂ (b := b) hm
    (by rw [o₂ _ (by decide), o₁ _ (by decide) (by decide) (by decide), hi.kpv])
  obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ .ebp 1
  have hc₃ : s₃.gpr .ebp = BitVec.ofNat 32 (32 - m) := by
    rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide) (by decide), hi.cnt]
  have hmem : s₄.mem = s₁.mem := by rw [m₄, m₃, m₂]
  have hb₄ : s₄.gpr sb = s.gpr sb := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide) (by decide)]
  have hf₁ : Frame [⟨b.setWidth 64, 4 * tableEnd⟩] s₀.mem s₁.mem :=
    hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, entry_sub hfit he r hr⟩)
  refine ⟨s₄, ?_, ⟨hpre.congr hb₄ (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁]),
      by rw [o₄ _ (by decide), r₃], ?_, ?_, fun i hi' => ?_, by rw [hmem]; exact hf₁,
      fun r h0 h1 h2 h3 hk hl => by
        rw [o₄ r hl, o₃ r hk, o₂ r h2, o₁ r h0 h1 h3, hi.regs r h0 h1 h2 h3 hk hl],
      by rw [rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₄, wr₃, wr₂, wr₁, hi.wr]⟩, ?_⟩
  · rw [tableBody, runBlock_app, e₁, Option.bind_some,
      show ([addI .ecx 4, kpStep dir, subI .ebp 1] : List Instr) =
        [addI .ecx 4] ++ ([kpStep dir] ++ [subI .ebp 1]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide) (by decide) (by decide), hi.ptr,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Offset.add_add, show 4 * m + 4 = 4 * (m + 1) by omega_arith]
  · rw [c₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show 32 - m - 1 = 32 - (m + 1) by omega_arith]
  · rw [hmem]
    rcases (show i < m ∨ i = m by omega_arith) with hlt | rfl
    · exact (hi.ent i hlt).congr fun j hj => entryW_frame hfit f₁ (entOf_lt dir (by omega_arith)) he
        (fun h => by have := entOf_inj dir (by omega_arith) hm h; omega_arith) hj
    · exact E₁
  · rw [z₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      ofNat32_beq_zero (by omega_arith)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_arith

theorem keyLoop_wp (dir : Dir) {s₀ s : State} {b sched : BitVec 32} (hi : KInv s₀ b sched dir 0 s) :
    WP isa (.loop (.block (tableBody dir)) .ne) s (KInv s₀ b sched dir 32) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 32 - m ∧ m < 32 ∧ KInv s₀ b sched dir m s)
    (fun n s hs => ?_) 32 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := keyIter_ok dir hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h32 : m + 1 = 32
  · exact .inl ⟨by rw [eval_ne, z', h32]; rfl, by rw [h32] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h32], 32 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

/-- The round keys in the order the rounds use them. -/
def dirKeys (dir : Dir) (sch : Spec.Sm4.Schedule) (e : Nat) : Spec.Sm4.Word := sch.getD (entOf dir e) 0

/-- What the table's construction leaves. -/
structure KeysPost (s₀ : State) (b sched : BitVec 32) (dir : Dir) (s : State) : Prop where
  pre : SchedPre s b sched
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64)))
  frame : Frame [⟨b.setWidth 64, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ kp → r ≠ .ebp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `mov ecx, [esp + 4]`. -/
theorem ldArg_ok (s : State) (d : Reg) (i : Nat) (h : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov d (.mem (argOp i))] s = some s' ∧ s'.gpr d = s.mem.readW (s.ea (argOp i)) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d (s.mem.readW (s.ea (argOp i)) 32), by
    rw [runBlock_cons, show exec (.mov d (.mem (argOp i))) s = some (s.setReg d (s.mem.readW (s.ea (argOp i)) 32)) by
      simp [exec, readSrc, State.load32, h], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} (hp : SchedPre s₀ b sched)
    (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4)
    (hr : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  rw [keys_eq]
  let k := match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s₀ .ecx 0 harg
  obtain ⟨s₂a, e₂a, k₂a, o₂a, m₂a, rd₂a, wr₂a, -, -⟩ := movR_ok s₁ kp .edi
  obtain ⟨s₂, e₂, k₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₂a kp (BitVec.ofNat 32 (4 * k))
  obtain ⟨s₃, e₃, l₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .ebp 32
  have hinv : KInv s₀ b sched dir 0 s₃ := by
    refine ⟨hp.congr (by rw [o₃ _ (by decide), o₂ _ (by decide), o₂a _ (by decide), o₁ _ (by decide)])
        (by rw [rd₃, rd₂, rd₂a, rd₁]) (by rw [wr₃, wr₂, wr₂a, wr₁]),
      by have hb : s₀.gpr .edi = b := hp.base
         rw [o₃ _ (by decide), k₂, k₂a, o₁ _ (by decide), hb]; cases dir <;> rfl,
      by rw [o₃ _ (by decide), o₂ _ (by decide), o₂a _ (by decide), c₁, hr]; simp,
      by rw [l₃]; rfl, fun i hi => by omega_arith, by rw [m₃, m₂, m₂a, m₁]; exact Frame.refl _ _,
      fun r _ _ h2 _ hk hl => by rw [o₃ r hl, o₂ r hk, o₂a r hk, o₁ r h2], by rw [rd₃, rd₂, rd₂a, rd₁],
      by rw [wr₃, wr₂, wr₂a, wr₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, ?_, WP.mono (keyLoop_wp dir hinv) fun s h => ?_⟩)
  · rw [kpAt, show ([Instr.mov .ecx (.mem (argOp 0))] ++ [movR kp .edi, addI kp (BitVec.ofNat 32 (4 * k))] ++
        [movI .ebp 32] : List Instr) = [.mov .ecx (.mem (argOp 0))] ++ ([movR kp .edi] ++
          ([addI kp (BitVec.ofNat 32 (4 * k))] ++ [movI .ebp 32])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂a, Option.bind_some, runBlock_app, e₂,
      Option.bind_some, e₃]
  · refine ⟨h.pre, ⟨by rw [h.pre.base]; exact h.pre.scr, fun e he => ?_⟩, h.frame, h.regs, h.rd, h.wr⟩
    rw [h.pre.base]
    have := h.ent (entOf dir e) (entOf_lt dir he)
    rw [entOf_entOf dir he] at this
    exact this

end VG.Proof.Sm4.X86

end

end

/-!
# Slots, and saving and restoring registers, on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/Prologue.lean`): loads and stores of the
scratch buffer's slots through a base register (`ldSlot_ok`, `stSlot_ok`,
and lists of them), and the prologue and epilogue's saving and restoring
of the callee-saved registers (`save_ok`, `restore_ok`) in the slots from
`savedSlot`.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt movS st movR argOp at_)

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ := by
  rw [slot_addr (by omega_using [hfit, hk])]
  exact VG.Offset.sub_base _ (by omega_using [hk])

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hfit, hj]) (by omega_using [hfit, hk]) h) (by decide)

/-- `mov d, [n + 4 k]`, `n` holding `b`, a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.mov d (.mem (slotAt n k))] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov d (.mem (slotAt n k))) s = some (s.setReg d (s.mem.readW (wordAddr b k) 32)) by
    simp [exec, readSrc, State.load32, he, inRd (hw.slot hk)], runStep_some, runBlock_nil]

/-- `mov [n + 4 k], t`, `n` holding `b`, a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.store (slotAt n k) t] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [runBlock_cons]
  simp only [exec, State.store32, he, hw.slot hk, ↓reduceIte, runStep_some, runBlock_nil]

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .store (slotAt n x.1) x.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .mov x.1 (.mem (slotAt n x.2))) s = some s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .ebx

theorem savedRegs_eq : savedRegs = (List.range 4).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : BitVec 32} {k : Nat} (hw : ScrIn s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp k)) 4) (hb : s.mem.readW (s.ea (argOp k)) 32 = b) :
    ∃ s', runBlock isa (saveRegs k) s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ Saved s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax k ha
  rw [hb] at v₁
  let L : List (Nat × Reg) := (List.range 4).map fun i => (savedSlot + i, sreg i)
  have hL : savedRegs.map (fun (r, j) => Instr.store (slotAt .eax j) r) =
      L.map fun x => .store (slotAt .eax x.1) x.2 := by
    rw [savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 4).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, o₂, v₂⟩ := stW_list_ok .eax L s₁ v₁ (by rw [wr₁]; exact hw)
    (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, -, -⟩ := movR_ok s₂ .edi .eax
  refine ⟨s₃, ?_, by rw [r₃, g₂, v₁], fun r h0 h7 => by rw [o₃ r h7, g₂, o₁ r h0], fun i hi => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, ← m₁]; exact f₂, fun j hj => ?_⟩
  · rw [saveRegs, runBlock_app, runBlock_app, e₁, Option.bind_some, hL, e₂, Option.bind_some, e₃]
  · rw [m₃, v₂ (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩),
      o₁ _ (by revert i; decide)]
  · rw [m₃, o₂ j ?_ (by rw [savedSlot_eq] at hj; rw [slots_eq]; omega_using [hj]), m₁]
    rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_using [hj, h]

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .edi = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := [(.ebx, savedSlot), (.esi, savedSlot + 1), (.ebp, savedSlot + 3)]
  obtain ⟨s₁, e₁, m₁, rd₁, wr₁, o₁, v₁⟩ := ldW_list_ok .edi L s hb hw (by decide) (by decide)
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only [savedSlot_eq, slots_eq] <;> omega_using [])
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok s₁ .edi .edi (k := savedSlot + 2)
    (by rw [o₁ _ (by decide), hb]) (by rw [savedSlot_eq, slots_eq]; omega_using []) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, fun i hi => ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [show restoreRegs = (L.map fun x => .mov x.1 (.mem (slotAt .edi x.2))) ++
        [.mov .edi (.mem (slotAt .edi (savedSlot + 2)))] from rfl, runBlock_app, e₁, Option.bind_some, e₂]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
    · show s₂.gpr .ebx = _
      rw [o₂ _ (by decide), v₁ (.ebx, savedSlot) (by simp [L])]; exact hs 0 (by decide)
    · show s₂.gpr .esi = _
      rw [o₂ _ (by decide), v₁ (.esi, savedSlot + 1) (by simp [L])]; exact hs 1 (by decide)
    · rw [show sreg 2 = .edi from rfl, v₂, m₁]; exact hs 2 (by decide)
    · show s₂.gpr .ebp = _
      rw [o₂ _ (by decide), v₁ (.ebp, savedSlot + 3) (by simp [L])]; exact hs 3 (by decide)
  · rw [o₂ r (hr 2 (by decide)), o₁ r (by
      simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 0 (by decide), hr 1 (by decide), hr 3 (by decide)⟩)]

end VG.Proof.Sm4.X86
