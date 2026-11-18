module

public import VerifiedGarbage.Proof.Sm4.Arm.Prologue
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Impl.Sm4.Arm.Ecb
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Sm4.Arm.Crypt8`, which this module and modules that import it used -/

section

/-!
# The transposes, and eight blocks of bitsliced SM4 on ARMv7

`toBs_step` turns the eight blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt8_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR)
open VG.Proof.Sm4 (quads ofBlock outBlock getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (State.addr (s.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    KeyCtx s E where
  scr := by rw [hc.wr, hc.base]; exact hp.scr
  fit := by rw [hc.base]; exact hp.fit
  keys e he := by rw [hc.base]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem ok_bs {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) : Ok bsCfg s where
  slotIn k hk := by
    simp only [bsCfg, tableSlot_eq] at hk ⊢
    rw [hc.wr, hc.base]; exact slot_in hp.scr hp.fit (by rw [slots_eq]; omega_arith)
  extIn k hk := by simp [bsCfg] at hk
  slots := by have := hp.fit; simp only [bsCfg, hc.base]; rw [slots_eq] at this; rw [tableSlot_eq]; omega_arith
  sep k _ j hj := by simp [bsCfg] at hj

/-- The registers `Ctx` keeps but `kp`: `sb` alone. -/
theorem keep_sb (r : Reg) (h1 : r ∉ layerWrites) (h2 : r ≠ kp) : r = sb := by
  revert h1 h2; cases r <;> decide

/-- A block of the slots below the table that keeps `sb` keeps `Ctx`. -/
theorem Ctx.bs {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hsp (fun r h1 h2 => by rw [keep_sb r h1 h2]; exact hb) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base])

theorem byte_addr (b : BitVec 32) {k i n : Nat} (hn : 4 * k + i = n) (hfit : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k + BitVec.ofNat 64 i = State.addr b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add hfit, BitVec.add_assoc, ← BitVec.ofNat_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  have hfit := hp.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', -, hso, -, rd', wr', sp', -, f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega_arith, by omega_arith, rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso
  refine ⟨s', h', hc.bs rd' wr' sp' hb' f', fun w hw b hb i hi j hj => ?_⟩
  have hp8 : 8 * i + b < 32 := by omega_arith
  have hmem := hso (32 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
      simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega_arith, rfl⟩)
      (by rw [tableSlot_eq]; omega_arith) _ hp8
  rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith] at hmem
  have ht : 8 * i + j < 32 := by omega_arith
  show (slotW s' (stateSlot w j)).getLsbD (8 * i + b) = _
  rw [slotW, hb', show stateSlot w j = 32 + (8 * w + j) by simp only [stateSlot]; omega_arith, hmem, toBsG,
    show (8 * i + b) % 8 = b by omega_arith, show (8 * i + b) / 8 = i by omega_arith, xorBits_cons, xorBits_nil,
    Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW_bit _ _ hi hj]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega_arith), byte_addr _ rfl (by rw [tailSlot_eq]; omega_arith),
    BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * (tailSlot + (4 * b + w)) + i = 4 * tailSlot + 16 * b + (4 * w + i) by omega_arith]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ StRel s' X ∧
      ∀ b < 8, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  have hfit := hp.fit
  rw [slots_eq, ← hc.base] at hfit
  obtain ⟨s', h', -, hso, hkeep, rd', wr', sp', o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (32 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkeep
  have hall : (fromBs.all fun i => !clobbers i kp) = true := by decide +kernel
  refine ⟨s', h', hc.bs rd' wr' sp' hb' f', o' kp hall, fun w hw => (hX w hw).congr fun j hj => ?_, fun b hb => ?_⟩
  · show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
    have hm : stateSlot w j ∈ stateSlots := by
      simp only [stateSlots, List.mem_map, List.mem_range]
      exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩
    rw [slotW, hb', hkeep _ hm (by simp only [stateSlot, tableSlot_eq]; omega_arith)]
  apply Vector.ext
  intro k hk
  refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
  rw [getLsbD_outBlock' (X b) hk hj]
  have ht : 8 * (k % 4) + j < 32 := by omega_arith
  have hmem := hso (tailSlot + (4 * b + k / 4)) (fromBsG (4 * b + k / 4)) (by
      simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨4 * b + k / 4, by omega_arith, rfl⟩)
      (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
  rw [readW_bit _ _ (by omega_arith) hj, byte_addr _ rfl (by rw [tailSlot_eq]; omega_arith)] at hmem
  have e1 : 8 * (3 - (4 * b + k / 4) % 4) + (8 * (k % 4) + j) % 8 = 8 * (3 - k / 4) + j := by omega_arith
  have e2 : 8 * ((8 * (k % 4) + j) / 8) + (4 * b + k / 4) / 4 = 8 * (k % 4) + b := by omega_arith
  have hw : 3 - k / 4 < 4 := by omega_arith
  have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega_arith) j hj
  rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
  simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
  rw [hb', BitVec.add_assoc, ← BitVec.ofNat_add,
    show 4 * tailSlot + 16 * b + k = 4 * (tailSlot + (4 * b + k / 4)) + k % 4 by omega_arith,
    hmem, ← hbit, planes_eq]

/-- `crypt8`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt8_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) :
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, X₁⟩ := toBs_step hp (Ctx.refl s₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (rounds_wp .enc (hp.of_ctx c₁) X₁) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have c₀₂ := c₁.trans c₂
  obtain ⟨s₃, e₃, c₃, -, -, hout⟩ := fromBs_step hp c₀₂ X₂
  exact WP.of_runBlock ⟨s₃, e₃, c₃, hout⟩

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced round keys on ARMv7

`keyOne_step`: `keyOne` bitslices the round key at `r12` into the table's
entry at `kp`, every block's copy of it alike. `keys_wp` builds the table in
the order the rounds use the round keys: `rk₀ … rk₃₁` for encryption,
`rk₃₁ … rk₀` for decryption.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp)
open VG.Proof.Sm4 (getLsbD_scheduleAt)

/-- `ldr r0, [r12]; rev r0, r0`. -/
theorem keyWord_ok (s : State) (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 4) :
    ∃ s', runBlock isa keyWord s = some s' ∧
      s'.gpr (q 0) = rev (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 32) ∧
      (∀ r, r ≠ q 0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let x := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 0)) 32
  refine ⟨(s.setReg (q 0) x).setReg (q 0) (rev x), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl, rfl⟩
  rw [keyWord, runBlock_cons, exec_ldr (by decide) h, runStep_some, runBlock_cons,
    show exec (.rev (q 0) (q 0)) (s.setReg (q 0) x) = some ((s.setReg (q 0) x).setReg (q 0) (rev x)) by
      simp only [exec, RegUpd.gpr_setReg_self],
    runStep_some, runBlock_nil]

/-- The schedule at `sched`, apart from the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : (⟨State.addr b, 4 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 4 * slots ≤ 2 ^ 32
  sch : (⟨State.addr sched, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sched, 128⟩ ⟨State.addr b, 4 * slots⟩

theorem SchedPre.congr {s s' : State} {b sched : BitVec 32} (h : SchedPre s b sched)
    (hb : s'.gpr sb = s.gpr sb) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SchedPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- Round key `i` of the schedule at `sched`. -/
theorem SchedPre.keyIn {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (State.addr (sched + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4 :=
  ⟨_, h.sch, by
    have := h.schFit
    rw [BitVec.add_zero, addr_add (by omega_arith)]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The word at round key `i` is round key `i`. -/
theorem key_word (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32) {i : Nat} (hi : i < 32) :
    m.readW (State.addr (sched + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 =
      (Spec.Sm4.scheduleAt m (State.addr sched)).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [VG.Proof.Aes.getD_eq _ hi, show k = 8 * (k / 8) + k % 8 by omega_arith,
    getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith), readW_bit _ _ (by omega_arith) (by omega_arith),
    BitVec.add_zero, addr_add (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The table's entry `e` at `b`. -/
theorem entry_addr {b : BitVec 32} {e j : Nat} :
    wordAddr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) j = wordAddr b (tableSlot + 8 * e + j) := by
  simp only [wordAddr]
  rw [add_ofNat_ofNat, show 4 * tableSlot + 32 * e + 4 * j = 4 * (tableSlot + 8 * e + j) by omega_arith]

/-- The round key at `r12` to the entry at `kp`. -/
theorem keyOne_step {s : State} {b sched : BitVec 32} {e i : Nat} (hp : SchedPre s b sched)
    (hkp : s.gpr kp = b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)) (he : e < 32)
    (hr : s.gpr .r12 = sched + BitVec.ofNat 32 (4 * i)) (hi : i < 32) :
    ∃ s', runBlock isa keyOne s = some s' ∧
      (∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩] s.mem s'.mem ∧
      W32.WordRel (entryW s'.mem b e) (fun _ => (Spec.Sm4.scheduleAt s.mem (State.addr sched)).getD i 0) := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  -- The word.
  obtain ⟨s₁, e₁, x₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := keyWord_ok s (by rw [hr]; exact hp.keyIn hi)
  rw [hr, key_word _ hp.schFit hi] at x₁
  -- Its planes, to the entry.
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (by decide)
  have hok : Ok entryCfg s₁ :=
    { slotIn := fun k hk => by
        simp only [entryCfg] at hk ⊢
        rw [wr₁, kp₁, hkp, entry_addr]
        exact slot_in hp.scr hp.fit (by rw [slots_eq, tableSlot_eq]; omega_arith)
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by
        simp only [entryCfg]; rw [kp₁, hkp, BitVec.toNat_add, BitVec.toNat_ofNat, tableSlot_eq]
        have := b.isLt
        rw [Nat.mod_eq_of_lt (show 384 + 32 * e < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk := keyPlanes_check
  unfold keyEnv at hchk
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, sp₂, o₂, f₂, -, -⟩ := linG_ok hchk hok (fun _ => s₁.gpr (q 0))
    (fun r i hri => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hri
      obtain ⟨rfl, rfl⟩ := hri
      exact ⟨by decide, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv) (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hso₂ f₂
  have he₂ : ∀ j < 8, ∀ p < 32, (entryW s₂.mem b e j).getLsbD p = (rev (Vector.getD
      (Spec.Sm4.scheduleAt s.mem (State.addr sched)) i 0)).getLsbD (8 * (p / 8) + j) := fun j hj p hp => by
    have h := hso₂ j (keyBsG j) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) hj p hp
    rw [keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 8 * (p / 8) + j = 32 * 0 + (8 * (p / 8) + j) by omega_arith, bitOf_word _ _ _ (by omega_arith), x₁, kp₁, hkp,
      entry_addr] at h
    rw [entryW, h]
  have hall₂ : ([Reg.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .lr].all fun r =>
      keyPlanes.all fun i => !clobbers i r) = true := by decide +kernel
  refine ⟨s₂, ?_, fun r h0 h3 h11 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], ?_, ?_⟩
  · rw [keyOne, runBlock_app, e₁, Option.bind_some, e₂]
  · rw [o₂ r (List.all_eq_true.mp hall₂ r (by revert h0 h3 h11; cases r <;> decide)), o₁ r h0]
  · rw [← m₁]
    refine f₂.mono fun r hr => ?_
    simp only [slotRegion, List.mem_singleton] at hr; subst hr
    rw [kp₁, hkp]; exact List.mem_singleton_self _
  · intro b' hb' i' hi' j hj
    rw [he₂ j hj _ (by omega_arith), show (8 * i' + b') / 8 = i' by omega_arith, rev_bit _ hi' hj]

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
  | .encrypt => .dp .add kp kp (.imm 32)
  | .decrypt => .dp .sub kp kp (.imm 32)

/-- The loop's body. -/
def tableBody (dir : Dir) : List Instr :=
  keyOne ++ ([.dp .add .r12 .r12 (.imm 4), kpStep dir, .subs .lr .lr (.imm 1)] : List Instr)

theorem keys_eq (dir : Dir) :
    keys dir = .seq (.block [kpAt (match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31),
      .mov .lr (.imm 32)]) (.loop (.block (tableBody dir)) .ne) := by
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
      (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  cases dir
  · obtain ⟨s', e', r', o', m', rd', wr', sp'⟩ := addImm_ok s kp kp 32 (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr', sp'⟩
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_ofNat]
    simp only [kpAtIter]; rw [show 4 * tableSlot + 32 * m + 32 = 4 * tableSlot + 32 * (m + 1) by omega_arith]
  · obtain ⟨s', e', r', o', m', rd', wr', sp'⟩ := subImm_ok s kp kp 32 (by decide)
    refine ⟨s', e', ?_, o', m', rd', wr', sp'⟩
    simp only [kpAtIter] at hkp ⊢
    rw [r', hkp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
      show 4 * tableSlot - 32 + 32 * (32 - m) = (4 * tableSlot - 32 + 32 * (32 - (m + 1))) + 32 by
        rw [tableSlot_eq]; omega_arith, ← add_ofNat_ofNat, BitVec.add_sub_cancel]

/-- `subs d, n, #1`. -/
theorem subs1_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.subs d d (.imm 1)] s = some s' ∧ s'.gpr d = s.gpr d - 1 ∧ s'.z = (s.gpr d - 1 == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1), ?_, RegUpd.gpr_setReg_self _ _ _, by rw [RegUpd.z_setReg]; rfl,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d d (.imm 1)) s = some ((subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1)) by
    simp [exec, Op2.eval]; decide, runStep_some, runBlock_nil]

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e i : Nat}
    (hf : Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩] m m')
    (hi : i < 32) (he : e < 32) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  rw [slots_eq] at hfit
  have hb := addr_toNat b
  rw [addr_add (by rw [tableSlot_eq]; omega_arith)] at hf
  simp only [entryW]
  rw [slot_addr (by rw [tableSlot_eq]; omega_arith)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [tableSlot_eq]
  exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The table's entry `e` is inside the table. -/
theorem entry_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 32) :
    Region.Sub ⟨State.addr (b + BitVec.ofNat 32 (4 * tableSlot + 32 * e)), 32⟩ ⟨State.addr b, 4 * tableEnd⟩ := by
  rw [slots_eq] at hfit
  rw [addr_add (by rw [tableSlot_eq]; omega_arith), tableSlot_eq, tableEnd_eq]
  exact VG.Offset.sub_base _ (by omega_arith)

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- What the loop keeps, after `m` of its 32 iterations. -/
structure KInv (s₀ : State) (b sched : BitVec 32) (dir : Dir) (m : Nat) (s : State) : Prop where
  pre : SchedPre s b sched
  kpv : s.gpr kp = b + BitVec.ofNat 32 (kpAtIter dir m)
  ptr : s.gpr .r12 = sched + BitVec.ofNat 32 (4 * m)
  cnt : s.gpr .lr = BitVec.ofNat 32 (32 - m)
  ent : ∀ i < m, W32.WordRel (entryW s.mem b (entOf dir i))
    (fun _ => (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)).getD i 0)
  frame : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → r ≠ .r12 → r ≠ kp → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The schedule is outside the scratch buffer. -/
theorem SchedPre.sched_eq {s : State} {b sched : BitVec 32} (h : SchedPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨State.addr b, 4 * n⟩] m m') :
    Spec.Sm4.scheduleAt m' (State.addr sched) = Spec.Sm4.scheduleAt m (State.addr sched) := by
  have hb : ∀ k < 128, m' (State.addr sched + BitVec.ofNat 64 k) = m (State.addr sched + BitVec.ofNat 64 k) :=
    fun k hk => hf.bytes (R := ⟨State.addr sched, 128⟩) (fun r hr => by
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
      s'.z = decide (m + 1 = 32) := by
  have hpre := hi.pre
  have hfit := hpre.fit
  have he := entOf_lt dir hm
  have hsched : Spec.Sm4.scheduleAt s.mem (State.addr sched) = Spec.Sm4.scheduleAt s₀.mem (State.addr sched) :=
    hpre.sched_eq (by rw [tableEnd_eq, slots_eq]; omega_arith) hi.frame
  obtain ⟨s₁, e₁, o₁, rd₁, wr₁, sp₁, f₁, E₁⟩ := keyOne_step (e := entOf dir m) hpre
    (by rw [hi.kpv, kpAtIter_ent dir hm]) he hi.ptr hm
  rw [hsched] at E₁
  have ko : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → s₁.gpr r = s.gpr r := o₁
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₁ .r12 .r12 4 (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := kpStep_ok dir s₂ (b := b) hm
    (by rw [o₂ _ (by decide), ko kp (by decide) (by decide) (by decide), hi.kpv])
  obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := subs1_ok s₃ .lr
  have hc₃ : s₃.gpr .lr = BitVec.ofNat 32 (32 - m) := by
    rw [o₃ _ (by decide), o₂ _ (by decide), ko .lr (by decide) (by decide) (by decide), hi.cnt]
  have hmem : s₄.mem = s₁.mem := by rw [m₄, m₃, m₂]
  have hb₄ : s₄.gpr sb = s.gpr sb := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), ko sb (by decide) (by decide) (by decide)]
  have hf₁ : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s₁.mem :=
    hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact entry_sub hfit he⟩)
  refine ⟨s₄, ?_, ⟨hpre.congr hb₄ (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁]),
      by rw [o₄ _ (by decide), r₃], ?_, ?_, fun i hi' => ?_, by rw [hmem]; exact hf₁,
      fun r h0 h3 h11 h12 hk hl => by rw [o₄ r hl, o₃ r hk, o₂ r h12, ko r h0 h3 h11, hi.regs r h0 h3 h11 h12 hk hl],
      by rw [rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₄, wr₃, wr₂, wr₁, hi.wr], by rw [sp₄, sp₃, sp₂, sp₁, hi.sp]⟩, ?_⟩
  · rw [tableBody, runBlock_app, e₁, Option.bind_some,
      show ([.dp .add .r12 .r12 (.imm 4), kpStep dir, .subs .lr .lr (.imm 1)] : List Instr) =
        [.dp .add .r12 .r12 (.imm 4)] ++ ([kpStep dir] ++ [.subs .lr .lr (.imm 1)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rw [o₄ _ (by decide), o₃ _ (by decide), r₂, ko .r12 (by decide) (by decide) (by decide), hi.ptr,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_ofNat, show 4 * m + 4 = 4 * (m + 1) by omega_arith]
  · rw [c₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show 32 - m - 1 = 32 - (m + 1) by omega_arith]
  · rw [hmem]
    rcases (show i < m ∨ i = m by omega_arith) with hlt | rfl
    · exact (hi.ent i hlt).congr fun j hj => entryW_frame hfit f₁ (entOf_lt dir (by omega_arith)) he
        (fun h => by have := entOf_inj dir (by omega_arith) hm h; omega_arith) hj
    · exact E₁
  · rw [z₄, hc₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      ofNat32_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

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
  key : KeyCtx s (dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)))
  frame : Frame [⟨State.addr b, 4 * tableEnd⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ q 0 → r ≠ q 3 → r ≠ t1 → r ≠ .r12 → r ≠ kp → r ≠ .lr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- `mov d, #v` (`v` encodable). -/
theorem movImm_ok (s : State) (d : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.mov d (.imm v)] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d v, by
    rw [runBlock_cons, show exec (.mov d (.imm v)) s = some (s.setReg d v) by simp [exec, Op2.eval, hv],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} (hp : SchedPre s₀ b sched)
    (hr : s₀.gpr .r12 = sched) :
    WP isa (keys dir) s₀ (KeysPost s₀ b sched dir) := by
  rw [keys_eq]
  let k := match dir with | .encrypt => tableSlot | .decrypt => tableSlot + 8 * 31
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := kpAt_ok s₀ k (by cases dir <;> decide)
  obtain ⟨s₂, e₂, l₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movImm_ok s₁ .lr 32 (by decide)
  have hinv : KInv s₀ b sched dir 0 s₂ := by
    refine ⟨hp.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]),
      by rw [o₂ _ (by decide), k₁, hp.base]; cases dir <;> rfl,
      by rw [o₂ _ (by decide), o₁ _ (by decide), hr]; simp,
      by rw [l₂]; rfl, fun i hi => by omega_arith, by rw [m₂, m₁]; exact Frame.refl _ _,
      fun r _ _ _ _ hk hl => by rw [o₂ r hl, o₁ r hk], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (keyLoop_wp dir hinv) fun s h => ?_⟩)
  · rw [show ([kpAt k, .mov .lr (.imm 32)] : List Instr) = [kpAt k] ++ [.mov .lr (.imm 32)] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · refine ⟨h.pre, ⟨by rw [h.pre.base]; exact h.pre.scr, by rw [h.pre.base]; exact h.pre.fit, fun e he => ?_⟩,
      h.frame, h.regs, h.rd, h.wr, h.sp⟩
    rw [h.pre.base]
    have := h.ent (entOf dir e) (entOf_lt dir he)
    rw [entOf_entOf dir he] at this
    exact this

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.Copy`, which only this module used -/

section

/-!
# Copying blocks on ARMv7

As on AArch64: `copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `r0` to `r12` (areas that do not overlap), a word at a time
through `t0`, counting down `r3`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (t0)
open VG.Arm.Straight (add_ofNat_ofNat)
open VG.Proof.Sm4 (off_sub_toNat off_sub_not writeW_readW32_apply)

/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `ldr t0, [r0, #d]; str t0, [r1, #d]`: the copy's next word. -/
theorem copyWord_ok {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat} (hd : d < 16) (hd4 : d % 4 = 0)
    (hj : j < c) (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)) (h1 : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j))
    (hi : Copied (State.addr A) (State.addr B) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.ldr t0 .r0 d, .str t0 .r12 d] s = some s' ∧
      Copied (State.addr A) (State.addr B) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain eA : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr A + BitVec.ofNat 64 (16 * j + d) := by
    rw [h0, add_ofNat_ofNat, addr_add (by omega_arith)]
  obtain eB : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 (16 * j + d) := by
    rw [h1, add_ofNat_ofNat, addr_add (by omega_arith)]
  obtain h₁ : (s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32)).gpr .r12 = s.gpr .r12 :=
    RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine ⟨{ s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) with
      mem := s.mem.writeW (State.addr B + BitVec.ofNat 64 (16 * j + d))
        (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr (by omega_arith) (by rw [eA]; exact hr), eA, runStep_some, runBlock_cons,
      exec_str (by omega_arith) (by rw [h₁, eB]; exact hw), runStep_some, runBlock_nil, h₁, eB,
      RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega_arith
    obtain hAs : ∀ t < 16 * c, s.mem (State.addr A + BitVec.ofNat 64 t) = s₀.mem (State.addr A + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨State.addr A, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega_arith) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega_arith)]; omega_arith), off_sub_toNat _ h8 (by omega_arith),
        VG.Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega_arith, hAs t (by omega_arith)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact hi.copied t (by omega_arith)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (VG.Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega_arith) _
        (by simp only [Region.Contains]; omega_arith))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)
  dst : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 32 (c - j)
  cp : Copied (State.addr A) (State.addr B) c s₀ (16 * j) s
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem copyBlocks_wp {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hA : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 t) 4)
    (hB : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (State.addr B + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain rA : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h1 h2 => by
    rw [h1, h2]; exact hA _ (by omega_arith) (by omega_arith)
  obtain rB : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h2 => by
    rw [h2]; exact hB _ (by omega_arith) (by omega_arith)
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁, sp₁⟩ := copyWord_ok (d := 0) (by decide) (by decide) hj hfA hfB hsep
    (rA 0 (by decide) (by decide) s hi.rd hi.wr) (rB 0 (by decide) (by decide) s hi.wr) hi.src hi.dst
    (by simpa using hi.cp)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂, sp₂⟩ := copyWord_ok (d := 4) (by decide) (by decide) hj hfA hfB hsep
    (rA 4 (by decide) (by decide) s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr))
    (rB 4 (by decide) (by decide) s₁ (wr₁.trans hi.wr))
    (by rw [g₁ _ (by decide), hi.src]) (by rw [g₁ _ (by decide), hi.dst]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃, sp₃⟩ := copyWord_ok (d := 8) (by decide) (by decide) hj hfA hfB hsep
    (rA 8 (by decide) (by decide) s₂ (rd₂.trans (rd₁.trans hi.rd)) (wr₂.trans (wr₁.trans hi.wr)))
    (rB 8 (by decide) (by decide) s₂ (wr₂.trans (wr₁.trans hi.wr)))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.src]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.dst])
    c₂
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄, sp₄⟩ := copyWord_ok (d := 12) (by decide) (by decide) hj hfA hfB hsep
    (rA 12 (by decide) (by decide) s₃ (rd₃.trans (rd₂.trans (rd₁.trans hi.rd)))
      (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (rB 12 (by decide) (by decide) s₃ (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.src])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.dst]) c₃
  obtain g₄' : ∀ r, r ≠ t0 → s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r0 .r0 16 (by decide)
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ .r12 .r12 16 (by decide)
  obtain ⟨s₇, e₇, c₇, z₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := subs1_ok s₆ .r3
  refine WP.of_runBlock ⟨s₇, by
    rw [show ([Instr.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)] : List Instr) =
      [.ldr t0 .r0 0, .str t0 .r12 0] ++ ([.ldr t0 .r0 4, .str t0 .r12 4] ++ ([.ldr t0 .r0 8, .str t0 .r12 8] ++
      ([.ldr t0 .r0 12, .str t0 .r12 12] ++ ([.dp .add .r0 .r0 (.imm 16)] ++
      ([.dp .add .r12 .r12 (.imm 16)] ++ [.subs .r3 .r3 (.imm 1)]))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, e₇], ?_⟩
  obtain hc₇ : s₇.gpr .r3 = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [c₇, o₆ _ (by decide), o₅ _ (by decide), g₄' _ (by decide), hi.cnt,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      show c - j - 1 = c - (j + 1) by omega_arith]
  obtain hm : s₇.mem = s₄.mem := by rw [m₇, m₆, m₅]
  obtain hinv : CopyInv A B c s₀ (j + 1) s₇ := by
    refine ⟨?_, ?_, hc₇, ⟨fun t ht => ?_, by rw [hm]; exact c₄.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr],
      by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁, hi.sp]⟩
    · rw [o₇ _ (by decide), o₆ _ (by decide), a₅, g₄' _ (by decide), hi.src,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₇ _ (by decide), a₆, o₅ _ (by decide), g₄' _ (by decide), hi.dst,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm]; exact c₄.copied t (by omega_arith)
    · rw [o₇ r h3, o₆ r h2, o₅ r h1, g₄' r h4, hi.regs r h1 h2 h3 h4]
  obtain hz : s₇.z = decide (c - (j + 1) = 0) := by
    rw [z₇, ← c₇, hc₇, ofNat32_beq_zero (by omega_arith)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

end VG.Proof.Sm4.Arm

end

end


/-!
# A group of blocks of SM4 ECB on ARMv7

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_wp`), copies the blocks back and steps to the next group. The data
pointer and the blocks left live in their slots (`dSlot`, `nSlot`) between
the steps, which use every other register.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)

/-! ## Small blocks -/

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 32 v >>> 3 - 0 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.gpr n), by
    rw [runBlock_cons, show exec (movR d n) s = some (s.setReg d (s.gpr n)) by simp [movR, exec, Op2.eval],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `r3 := min(r2, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hn : s.gpr .r2 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r3 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg t0 (s.gpr .r2 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr t0) 0
  obtain e₂₃ : runBlock isa [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov t0 (lsrOp .r2 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp t0 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  obtain z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr t0 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  obtain o₃ : ∀ r, r ≠ t0 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_using [h])) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r3 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r3 .r2
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r2₃, Nat.min_eq_left (by simp at h; omega_using [h])]

/-- `subs d, n, m`. -/
theorem subsR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.subs d n (.reg m)] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      s'.z = (s.gpr n - s.gpr m == 0) ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m), ?_, RegUpd.gpr_setReg_self _ _ _,
    by rw [RegUpd.z_setReg]; rfl, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d n (.reg m)) s =
    some ((subFlags s (s.gpr n) (s.gpr m)).setReg d (s.gpr n - s.gpr m)) by simp [exec, Op2.eval],
    runStep_some, runBlock_nil]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h] : d < 2 ^ 32), Nat.mod_eq_of_lt h]

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨State.addr b + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_using [hfit, hhi, hk2])]
  exact hf.readW (VG.Offset.contains _ (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hhi, hk1, hk2])) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers, in the slots from `tableSlot` to `dSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, W32.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot dSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf hd (by omega_using []) (by rw [dSlot_eq, tableSlot_eq]; omega_using [he, hj])
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega_using [])
      (by rw [savedSlot_eq, dSlot_eq]; omega_using [hi])

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.gpr .r1 = D + BitVec.ofNat 32 (128 * k)
  np : s.gpr .r2 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.z = true ∧ GDone s₀ b D n E s') ∨
      (s'.z = false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := addr_toNat b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : State.addr A = State.addr D + BitVec.ofNat 64 (128 * k) := addr_add (by omega_arith)
  obtain hT : State.addr T = State.addr b + BitVec.ofNat 64 (4 * tailSlot) := addr_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr T + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr A + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨State.addr A, 16 * c⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨State.addr T, 16 * c⟩ ⟨State.addr b, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr T, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  obtain dT : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr T, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain dA : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr A, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  obtain dTab : (slotsRegion b tableSlot slots).Disjoint ⟨State.addr b, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by rw [tableSlot_eq, slots_eq]; omega_arith)
  obtain sub_ts : ∀ l u, tableSlot ≤ l → l ≤ u → u ≤ slots →
      (slotsRegion b l u).Sub (slotsRegion b tableSlot slots) :=
    fun l u h1 h2 h3 => VG.Offset.sub _ (by omega_arith) (by rw [slots_eq] at h3 ⊢; omega_arith)
  obtain subTab : (slotsRegion b tableSlot dSlot).Sub (slotsRegion b tableSlot slots) :=
    sub_ts _ _ (Nat.le_refl _) (by decide) (by decide)
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have r1₀ : s.gpr .r1 = A := hi.dp
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.np hv) fun s₁ ⟨r3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, sp₂a⟩ := movR_ok s₁ .r0 .r1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₂a .r12 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₂ r h12, o₂a r h0, o₁ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([movR .r0 .r1, tailAddr .r12] : List Instr) = [movR .r0 .r1] ++ [tailAddr .r12] from rfl,
      runBlock_app, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide) (by decide), r1₀]; simp [A],
      by rw [r₂, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  obtain f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₃.regs r h0 h12 h3 h4, g₂ r h0 h12 h3 h4]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left to their slots.
  unfold cryptSaved
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a, sp₄a, -, f₄a⟩ := stSlot_ok s₃ .r1 sb (k := dSlot) base₃ (by decide) hwS₃
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₄a .r2 sb (k := nSlot) (by rw [g₄a, base₃])
    (by decide) (by rw [wr₄a]; exact hwS₃)
  obtain r1₃ : s₃.gpr .r1 = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), r1₀]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.np]
  obtain fs : Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩] s₃.mem s₄.mem :=
    (f₄a.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  obtain hsub : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
  obtain dsTab : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b tableSlot dSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
      exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
        (by (try simp only [tableSlot_eq, dSlot_eq]); omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)
  obtain sc₄ : ScrOk s₀ b E s₄.mem := sc₃.frame hfit' fs dsTab
  obtain base₄ : s₄.gpr sb = b := by rw [g₄, g₄a, base₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄a, wr₃]
  obtain dp₄ : s₄.mem.readW (wordAddr b dSlot) 32 = A := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄a,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, r1₃]
  obtain np₄ : s₄.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄a, r2₃]
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([stS dSlot .r1, stS nSlot .r2] : List Instr) =
      [.str .r1 sb (4 * dSlot)] ++ [.str .r2 sb (4 * nSlot)] from rfl, runBlock_app, e₄a, Option.bind_some, e₄],
    ?_⟩))
  -- The eight blocks.
  obtain hkey : KeyCtx s₄ E :=
    { scr := by rw [base₄, wr₄']; exact hwS.mem
      fit := by rw [base₄]; exact hfit'
      keys := fun e he => by rw [base₄]; exact sc₄.keys e he }
  refine WP.seq (WP.mono (crypt8_wp hkey) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₄]
  obtain f₅ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₄.mem s₅.mem := by have := c₅.frame; rw [base₄] at this; exact this
  obtain keep₅ : ∀ j, tableSlot ≤ j → j < slots → s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => slot_keep hfit' (Nat.le_refl _) f₅
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTab) h1 h2
  obtain sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  obtain wr₅ : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [c₅.rd, rd₄, rd₄a, rd₃]
  obtain sp₅ : s₅.sp = s.sp := by rw [c₅.sp, sp₄, sp₄a, sp₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The data pointer and the blocks left back.
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a, sp₆a⟩ := ldSlot_ok s₅ .r1 sb (k := dSlot) base₅ (by decide) hwS₅
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := ldSlot_ok s₆a .r2 sb (k := nSlot)
    (by rw [o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆a]; exact hwS₅)
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([ldS .r1 dSlot, ldS .r2 nSlot] : List Instr) =
      [.ldr .r1 sb (4 * dSlot)] ++ [.ldr .r2 sb (4 * nSlot)] from rfl, runBlock_app, e₆a, Option.bind_some, e₆],
    ?_⟩
  obtain r1₆ : s₆.gpr .r1 = A := by rw [o₆ _ (by decide), r₆a, keep₅ _ (by decide) (by decide), dp₄]
  obtain r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 v := by rw [r₆, m₆a, keep₅ _ (by decide) (by decide), np₄]
  obtain base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆a _ (by decide), base₅]
  obtain mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆a]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅]
  obtain sp₆' : s₆.sp = s.sp := by rw [sp₆, sp₆a, sp₅]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r2₆ hv) fun s₇ ⟨r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ := movR_ok s₈a .r12 .r1
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  obtain g₈ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₈ r h12, o₈a r h0, o₇ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([tailAddr .r0, movR .r12 .r1] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [movR .r12 .r1] from rfl,
      runBlock_app, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆']
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆']
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈', wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₆]; simp [T],
      by rw [r₈, o₈a _ (by decide), o₇ _ (by decide) (by decide), r1₆]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  obtain f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  obtain g₉ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₉.regs r h0 h12 h3 h4, g₈ r h0 h12 h3 h4]
  obtain sc₉ : ScrOk s₀ b E s₉.mem := sc₅.frame hfit' f₉ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  obtain wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  obtain rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈']
  obtain sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Sm4.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
        ¬ r.Contains (State.addr b + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, dSlot_eq, nSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [dSlot_eq, nSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : State.addr D + BitVec.ofNat 64 i = State.addr A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₉.cp.copied _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : State.addr T + BitVec.ofNat 64 (i - 128 * k) =
          State.addr (s₅.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  -- On to the next group.
  obtain r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 v := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), r2₆]
  unfold advance
  refine WP.seq (WP.mono (groupCount_wp r2₉ hv) fun s₁₀ ⟨r3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁, sp₁₁⟩ := addImm_ok s₁₀ .r1 .r1 128 (by decide)
  obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂, sp₁₂⟩ := subsR_ok s₁₁ .r2 .r2 .r3
  refine WP.of_runBlock ⟨s₁₂, by
    rw [show ([.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)] : List Instr) =
      [.dp .add .r1 .r1 (.imm 128)] ++ [.subs .r2 .r2 (.reg .r3)] from rfl,
      runBlock_app, e₁₁, Option.bind_some, e₁₂], ?_⟩
  obtain zz : s₁₂.z = decide (v = c) := by
    rw [z₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
      ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
  obtain base₁₂ : s₁₂.gpr sb = b := by
    rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), base₆]
  obtain rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉, hi.rd]
  obtain wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, hi.wr]
  obtain sp₁₂' : s₁₂.sp = s₀.sp := by rw [sp₁₂, sp₁₁, sp₁₀, sp₉, hi.sp]
  obtain fr : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₁₂.mem := by
    rw [hmem]; exact hi.frame.trans fr₉
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₂, hmem ▸ sc₉, by have := hmem ▸ hdata; rwa [hn] at this, fr,
      rd₁₂', wr₁₂', sp₁₂'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₂, ?_, ?_, by omega_arith, hmem ▸ sc₉,
      by rw [hmem, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata, fr, rd₁₂', wr₁₂', sp₁₂'⟩
    · rw [o₁₂ _ (by decide), r₁₁, o₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide),
        r1₆]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
        VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

end VG.Proof.Sm4.Arm
