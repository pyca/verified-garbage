module

public import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Sm4.AArch64.Crypt16
public import VerifiedGarbage.Proof.Sm4.AArch64.Prologue
import VerifiedGarbage.Proof.Sm4.AArch64.KeyInit
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Sm4.AArch64.Keys
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.AArch64.Ecb

/-! ### `Sm4.AArch64.KeyLoop`, which only this module used -/

section

/-!
# The loop of the SM4 key schedule on AArch64

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's 64-bit words, byte-reversed (`rev`).
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_outBlock' ofInt_nat)

/-! ## Bytes -/

theorem rev64_bit (x : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    (rev64 x).getLsbD (8 * t + j) = x.getLsbD (8 * (7 - t) + j) := by
  rw [VG.AArch64.getLsbD_rev64 _ (by omega_arith)]
  exact congrArg x.getLsbD (by omega_arith)

/-- A byte of a word written. -/
theorem writeW_byte (m : Mem) (a : Addr) (v : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    ((m.writeW a v) (a + BitVec.ofNat 64 t)).getLsbD j = v.getLsbD (8 * t + j) := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_arith)]
  simp only [show t < 64 / 8 by omega_arith, ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]

/-- A byte outside a word written. -/
theorem writeW_other (m : Mem) (a x : Addr) (v : BitVec 64) (h : ¬ (x - a).toNat < 8) :
    (m.writeW a v) x = m x := by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h' => h (by simpa using h')

/-- A word written inside `R`. -/
theorem frame_writeW' {m : Mem} {a : Addr} {R : Region} (v : BitVec 64) (hs : Region.Sub ⟨a, 8⟩ R) :
    Frame [R] m (m.writeW a v) := VG.Proof.Sm4.frame_writeW v hs

/-! ## Single instructions -/

theorem bswapR_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.rev d d] s = some s' ∧ s'.gpr d = rev64 (s.gpr d) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (rev64 (s.gpr d)), by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x'],
    by simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq], fun r h => RegUpd.gpr_write_of_ne _ _ _ h,
    rfl, rfl, rfl⟩

/-- `str v, [r, #n]`. -/
theorem storeAt_ok (s : State) (r v : Reg) (n : Nat) (hn : n % 8 = 0 ∧ n < 32768)
    (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.str .x v r n] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr r + BitVec.ofNat 64 n) (s.gpr v) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨{ s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 n) (s.gpr v) }, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_str_x hn hw], rfl, rfl, rfl, rfl⟩

/-- A byte of the tail buffer's block `0`. -/
theorem tail_byte (s : State) {h t j : Nat} (hh : h < 2) (ht : t < 8) (hj : j < 8) :
    (slotW s (tailAt 0 h)).getLsbD (8 * t + j) = ((tailBlock s 0)[8 * h + t]'(by omega_arith)).getLsbD j := by
  rw [slotW, readW64_bit _ _ ht hj]
  simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, wordAddr, addr_add, tailAt]
  rw [show 8 * (tailSlot + 2 * 0 + h) + t = 8 * tailSlot + 16 * 0 + (8 * h + t) by omega_arith]

/-! ## The extraction -/

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian. -/
theorem extract_ok {s : State} {b S : Addr} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b)
    (hr8 : s.gpr .x1 = S + BitVec.ofNat 64 (16 * m))
    (hS : ∀ t < 2, InRegions s.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8)
    (hT : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr b (tailAt 0 t)) 8)
    (hsep : ∀ t < 2, Mem.Sep (wordAddr b (tailAt 0 t)) 8 (S + BitVec.ofNat 64 (16 * m)) 8) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0)[15 - t]'(by omega_arith)).getLsbD j) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := t0) (k := tailAt 0 1) (by simp only [tailAt, tailSlot_eq]; omega_arith)
    (by rw [hb]; exact hT 1 (by decide)) rfl
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := bswapR_ok s₁ t0
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeAt_ok s₂ .x1 t0 0 (by decide)
    (by rw [wr₂, wr₁, o₂ _ (by decide), o₁ _ (by decide), hr8, addr_add, Nat.add_zero]
        have := hS 0 (by decide); simpa using this)
  have hb₃ : s₃.gpr sb = b := by rw [g₃, o₂ _ (by decide), o₁ _ (by decide), hb]
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ldMask_ok (s := s₃) (r := t0) (k := tailAt 0 0)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, hb₃]; exact hT 0 (by decide)) rfl
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := bswapR_ok s₄ t0
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := storeAt_ok s₅ .x1 t0 8 (by decide)
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, o₅ _ (by decide), o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide),
          hr8, addr_add]; exact hS 1 (by decide))
  have hr8₅ : s₅.gpr .x1 = S + BitVec.ofNat 64 (16 * m) := by
    rw [o₅ _ (by decide), o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide), hr8]
  have hr8₂ : s₂.gpr .x1 = S + BitVec.ofNat 64 (16 * m) := by rw [o₂ _ (by decide), o₁ _ (by decide), hr8]
  have q1 : s₂.gpr t0 = rev64 (slotW s (tailAt 0 1)) := by rw [v₂, v₁]
  have q0 : s₅.gpr t0 = rev64 (slotW s (tailAt 0 0)) := by
    rw [v₅, v₄]
    simp only [slotW, m₃, m₂, m₁, hb₃, hb, hr8₂, addr_add, Nat.add_zero]
    rw [Mem.readW_writeW_sep (hsep 0 (by decide)) (by decide)]
  have hm6 : s₆.mem = (s.mem.writeW (S + BitVec.ofNat 64 (16 * m)) (rev64 (slotW s (tailAt 0 1)))).writeW
      (S + BitVec.ofNat 64 (16 * m + 8)) (rev64 (slotW s (tailAt 0 0))) := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁, hr8₅, q0, hr8₂, q1, addr_add, addr_add, Nat.add_zero]
  refine ⟨s₆, ?_, fun t ht j hj => ?_, ?_, fun r hr => ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [extract, show ([ldS t0 (tailAt 0 1), .rev t0 t0, .str .x t0 .x1 0, ldS t0 (tailAt 0 0), .rev t0 t0,
        .str .x t0 .x1 8] : List Instr) = [ldS t0 (tailAt 0 1)] ++ ([.rev t0 t0] ++ ([.str .x t0 .x1 0] ++
        ([ldS t0 (tailAt 0 0)] ++ ([.rev t0 t0] ++ [.str .x t0 .x1 8])))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [hm6]
    by_cases h8 : t < 8
    · rw [writeW_other _ _ _ _ (VG.Proof.Sm4.off_sub_not S (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)),
        ← addr_add, writeW_byte _ _ _ h8 hj, rev64_bit _ h8 hj, tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 1 + (7 - t) = 15 - t by omega_arith]
    · rw [show S + BitVec.ofNat 64 (16 * m + t) = S + BitVec.ofNat 64 (16 * m + 8) + BitVec.ofNat 64 (t - 8) by
          rw [addr_add, show 16 * m + 8 + (t - 8) = 16 * m + t by omega_arith], writeW_byte _ _ _ (by omega_arith) hj,
        rev64_bit _ (by omega_arith) hj, tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 0 + (7 - (t - 8)) = 15 - t by omega_arith]
  · rw [hm6]
    exact (frame_writeW' _ (VG.Offset.sub S (by omega_arith) (by omega_arith))).trans
      (frame_writeW' _ (VG.Offset.sub S (by omega_arith) (by omega_arith)))
  · rw [g₆, o₅ r hr, o₄ r hr, g₃, o₂ r hr, o₁ r hr]

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : Addr) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  x1 : s.gpr .x1 = S + BitVec.ofNat 64 (16 * m)
  x3 : s.gpr .x3 = b + BitVec.ofNat 64 (8 * tableEnd)
  kp : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  masks : MasksOk s
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b, 8 * slots⟩, ⟨S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : Addr) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  sch : (⟨S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 128⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitS : S.toNat + 128 ≤ 2 ^ 64

theorem ekIter_ok {s₀ : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  have hfit := hp.fit
  have hfitS := hp.fitS
  rw [slots_eq] at hfit
  have hc0 : Ctx s s := Ctx.refl hi.masks
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kp) hm hi.st
  obtain ⟨s₂, e₂, kp₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  have c₂ : Ctx s s₂ := c₁.kp o₂ m₂ rd₂ wr₂
  have X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kp₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  have base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  have r8₃ : s₃.gpr .x1 = S + BitVec.ofNat 64 (16 * m) := by rw [c₃.keep _ (by decide) (by decide), hi.x1]
  have wr₃ : s₃.wr = s₀.wr := by rw [c₃.wr, hi.wr]
  have rd₃ : s₃.rd = s₀.rd := by rw [c₃.rd, hi.rd]
  have inS : ∀ t < 2, InRegions s₃.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8 := fun t ht =>
    ⟨_, by rw [wr₃]; exact hp.sch, VG.Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  have inT : ∀ t < 2, InRegions (s₃.rd ++ s₃.wr) (wordAddr b (tailAt 0 t)) 8 := fun t ht =>
    ⟨_, List.mem_append_right _ (by rw [wr₃]; exact hp.scr), by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [tailAt, tailSlot_eq, slots_eq]; omega_arith)
        (by rw [tailAt, tailSlot_eq]; omega_arith)⟩
  have sepTS : ∀ k < slots, Region.Disjoint ⟨wordAddr b k, 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩ := fun k hk =>
    (hp.sep.sub_left (VG.Offset.sub_base S (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq] at hk ⊢; omega_arith)) |>.symm
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ r8₃ inS inT
    (fun t ht => fun x h1 h2 => sepTS _ (tailAt_lt (by decide) ht) x h1 (by
      simp only [Region.Contains] at h2 ⊢; omega_arith))
  have keep₄ : ∀ k < slots, slotW s₄ k = slotW s₃ k := fun k hk => by
    simp only [slotW, o₄ sb (by decide), base₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sepTS k hk) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .x1 .x1 (imm := 16) (by decide)
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := subR_ok s₅ t0 kp .x3
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have g₆' : ∀ r, r ≠ .x1 → r ≠ t0 → s₆.gpr r = s₃.gpr r := fun r h1 h2 => by rw [g₆ r h2, o₅ r h1, o₄ r h2]
  have base₆ : s₆.gpr sb = b := by rw [g₆' _ (by decide) (by decide), base₃]
  have keep₆ : ∀ k < slots, slotW s₆ k = slotW s₃ k := fun k hk => by
    rw [← keep₄ k hk]; simp only [slotW, mem₆, g₆' sb (by decide) (by decide), o₄ sb (by decide)]
  have kp₆ : AtEntry s₆ b (4 * (m + 1)) := by
    rw [AtEntry, g₆' _ (by decide) (by decide), kp₃, kp₂, k₁, show s.gpr kp = _ from hi.kp, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith]
  have rdi₆ : s₆.gpr .x3 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₆' _ (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.x3]
  have hent : ∀ (st : State) e j, entryW st.mem (st.gpr sb) e j = slotW st (tableSlot + 8 * e + j) := fun st e j => by
    simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]
  have key₃ := hi.keys.of_ctx c₃
  -- The schedule's bytes outside this iteration's.
  have old₆ : ∀ x, (∀ r ∈ [(⟨b, 8 * tableSlot⟩ : Region), ⟨S + BitVec.ofNat 64 (16 * m), 16⟩], ¬ r.Contains x 1) →
      s₆.mem x = s.mem x := fun x hx => by
    rw [mem₆, f₄ x (fun r hr => hx r (by simp at hr; simp [hr])),
      c₃.frame x (fun r hr => by simp at hr; subst hr; rw [hi.base]; exact hx _ (by simp))]
  refine ⟨s₆, ?_, ⟨base₆, ?_,
    rdi₆, kp₆, ⟨by rw [base₆, wr₆, wr₅, wr₄, wr₃]; exact hp.scr, by rw [base₆]; rw [slots_eq]; exact hfit,
      fun e he => (key₃.keys e he).congr fun j hj => by
        rw [hent s₆, hent s₃, keep₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith)]⟩,
    fun kv hkv => by rw [keep₆ _ (by have := mask_lt hkv; rw [slots_eq]; omega_arith)]; exact c₃.masks kv hkv,
    fun w hw => (X₃ w hw).congr fun j hj => keep₆ _ (by simp only [stateSlot, slots_eq]; omega_arith),
    fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_, by rw [rd₆, rd₅, rd₄, rd₃], by rw [wr₆, wr₅, wr₄, wr₃]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some,
      show ([.addImm .x .x1 .x1 16, .sub .x t0 kp .x3] : List Instr) =
        [.addImm .x .x1 .x1 16] ++ [.sub .x t0 kp .x3] from rfl, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [g₆ _ (by decide), r₅, o₄ _ (by decide), r8₃, addr_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega_arith
      have hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega_arith] at hB
      rw [mem₆, hB, T₃ 0 (by decide), getLsbD_outBlock' _ _ hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega_arith, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega_arith,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega_arith]
    · rw [old₆ _ (fun r hr => ?_)]
      · exact hi.sched i (by omega_arith) c hc j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro hc'
          exact hp.sep (S + BitVec.ofNat 64 (4 * i + c)) (VG.Offset.contains_base S (by omega_arith) (by omega_arith))
            (Region.sub_prefix (show 8 * tableSlot ≤ 8 * slots by rw [tableSlot_eq, slots_eq]; omega_arith) _ hc')
        · exact VG.Proof.Sm4.not_contains_off S (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    have h1 : s₆.mem.readW (wordAddr b (savedSlot + i)) 64 = s₃.mem.readW (wordAddr b (savedSlot + i)) 64 := by
      have := keep₆ _ hk; simp only [slotW, base₆, base₃] at this; exact this
    have h2 : s₃.mem.readW (wordAddr b (savedSlot + i)) 64 = s.mem.readW (wordAddr b (savedSlot + i)) 64 :=
      c₃.frame.readW (r := ⟨wordAddr b (savedSlot + i), 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hi.base, wordAddr]
        exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith))
        (by decide)
    rw [h1, h2]; exact hi.saved i hi'
  · rw [mem₆]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ⟨⟨S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base S (by omega_arith)
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), o₄ _ (by decide), kp₃, kp₂, k₁,
      show s.gpr kp = _ from hi.kp, c₃.keep _ (by decide) (by decide), hi.x3, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)]
    simp only [decide_eq_decide]; omega_arith

end VG.Proof.Sm4.AArch64

end

end


/-!
# The SM4 key schedule on AArch64: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyAArch64`),
`expandKey` saves the callee-saved registers, sets the masks, stores the
table of `CK`'s planes, bitslices sixteen copies of `MK ⊕ FK`, runs the
loop (`ekIter_ok`) and restores the registers; the schedule is the
specification's `expandKey`.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- The key schedule on AArch64 with its working space at `x2`. -/
def expandKeyAArch64 : Contract AArch64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let sched : Region := ⟨s.gpr .x1, 128⟩
    let scratch : Region := ⟨s.gpr .x2, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .x0).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (s.gpr .x1) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .x0))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (planeOf_rel fkWord_bit WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_wordAt ofInt_nat
  expandKeyAArch64)

/-! ## `MK ⊕ FK` in the tail buffer -/

theorem keyInit_bit (key : Spec.Sm4.Block) {w i j : Nat} (hi : i < 4) (hj : j < 8) :
    (keyInit key w).getLsbD (8 * (3 - i) + j) =
      ((key.getD (4 * w + i) 0).getLsbD j ^^ (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - i) + j)) := by
  rw [keyInit, BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi hj]

/-- Byte `i` of block `c` of the tail buffer, from its words. -/
theorem tailBlock_bit (s : State) {c i j : Nat} (hi : i < 16) (hj : j < 8) :
    ((tailBlock s c).getD i 0).getLsbD j = (slotW s (tailAt c (i / 8))).getLsbD (8 * (i % 8) + j) := by
  rw [slotW, readW64_bit _ _ (by omega_arith) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, wordAddr, addr_add, addr_add, tailAt]
  rw [show 8 * tailSlot + 16 * c + i = 8 * (tailSlot + 2 * c + i / 8) + i % 8 by omega_arith]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's 64-bit words `K h`. -/
theorem keyInit_rel {s : State} {key : Spec.Sm4.Block} {K : Nat → BitVec 64}
    (hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (K h).getLsbD (8 * t + j) = (key.getD (8 * h + t) 0).getLsbD j)
    (hT : ∀ c < 16, ∀ h < 2, slotW s (tailAt c h) = K h ^^^ fkWord h) :
    ∀ c < 16, ∀ w < 4, ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 3 - k / 8 < 4 := by omega_arith
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega_arith, keyInit_bit key (w := w) hi (by omega_arith)]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi (by omega_arith), tailBlock_bit s (c := c) (by omega_arith) (by omega_arith), hT c hc _ (by omega_arith),
    BitVec.getLsbD_xor, fkWord_bit (by omega_arith)]
  have e1 : 8 * ((4 * w + (3 - k / 8)) % 8) + k % 8 = 8 * (4 * (w % 2) + (3 - k / 8)) + k % 8 := by omega_arith
  rw [e1, hK _ (by omega_arith) _ (by omega_arith) _ (by omega_arith)]
  have h1 : 2 * ((4 * w + (3 - k / 8)) / 8) + (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) / 32 = w := by omega_arith
  have h2 : 8 * (3 - (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 32 / 8) +
      (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 8 = 8 * (3 - (3 - k / 8)) + k % 8 := by omega_arith
  have h3 : 8 * ((4 * w + (3 - k / 8)) / 8) + (4 * (w % 2) + (3 - k / 8)) = 4 * w + (3 - k / 8) := by omega_arith
  rw [h1, h2, h3]

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_ge : ∀ kv ∈ ckEntries, tableSlot ≤ kv.1 := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The slots are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' tableSlot 256 by decide +kernel]
  exact List.nodup_range'

theorem entryW_slot (s : State) (e j : Nat) : entryW s.mem (s.gpr sb) e j = slotW s (tableSlot + 8 * e + j) := by
  simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

/-- The code before the loop. -/
def ekHead : List Instr :=
  [movR sb .x2] ++ saveRegs ++ setSlots keyMasks ++ ckTable ++ loadHalf 0 ++
    loadHalf 1 ++ toBs ++ slotAddr .x3 tableEnd ++ slotAddr kp tableSlot

theorem ekHead_ok {s₀ : State} (hp : expandKeyAArch64.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (s₀.gpr .x2) (s₀.gpr .x1) (Spec.Sm4.blockAt s₀.mem (s₀.gpr .x0)) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .x2
  let S := s₀.gpr .x1
  let Kp := s₀.gpr .x0
  have hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hfitB := fitB
  rw [slots_eq] at hfitB
  -- The registers.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .x2
  have g₁ : ∀ r, r ≠ sb → s₁.gpr r = s₀.gpr r := o₁
  have hb₁ : s₁.gpr sb = b := r₁
  have mem₁ : s₁.mem = s₀.mem := m₁
  have wr₁' : s₁.wr = s₀.wr := wr₁
  have rd₁' : s₁.rd = s₀.rd := rd₁
  -- Saving, the masks and the table of `CK`.
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁']; exact hwB) hb₁
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁']; exact hwB) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega_arith) (by decide)
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, f₄⟩ := setSlotsN_ok tableEnd (by rw [tableEnd_eq, slots_eq]; omega_arith)
    ckEntries (b := b) (by rw [g₃ _ (by decide), g₂, hb₁]) (by rw [wr₃, wr₂, wr₁']; exact hwB) ckEntries_lt
    ckEntries_nodup
  have hb₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂, hb₁]
  have f₀₄ : Frame [⟨b, 8 * slots⟩] s₀.mem s₄.mem := by
    rw [← mem₁]
    refine f₂.trans ((f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)) <;>
      (simp only [List.mem_singleton] at hr; subst hr) <;>
      exact Region.sub_prefix (by simp only [tableSlot_eq, tableEnd_eq, slots_eq]; omega_arith)
  -- The key.
  have inK : ∀ h < 2, InRegions (s₄.rd ++ s₄.wr) (Kp + BitVec.ofNat 64 (8 * h)) 8 := fun h hh =>
    ⟨_, List.mem_append_left _ (by rw [rd₄, rd₃, rd₂, rd₁', hrd]; exact List.mem_singleton_self _),
      VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hKw : ∀ (m : Mem), Frame [⟨b, 8 * slots⟩] s₀.mem m → ∀ h < 2,
      m.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 :=
    fun m hf h hh => hf.readW (r := ⟨Kp, 16⟩) (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  have hrdi₄ : s₄.gpr .x0 = Kp := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂, g₁ _ (by decide)]
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loadHalf_ok 0 (by decide) hb₄ (by rw [wr₄, wr₃, wr₂, wr₁']; exact hwB)
    (by rw [hrdi₄]; exact inK 0 (by decide))
  have hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide), hb₄]
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, f₆⟩ := loadHalf_ok 1 (by decide) hb₅
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁']; exact hwB)
    (by rw [rd₅, wr₅, g₅ _ (by decide) (by decide), hrdi₄]; exact inK 1 (by decide))
  have hb₆ : s₆.gpr sb = b := by rw [g₆ _ (by decide) (by decide), hb₅]
  have f₀₆ : Frame [⟨b, 8 * slots⟩] s₀.mem s₆.mem := (f₀₄.trans f₅).trans f₆
  have hk₆ : ∀ k < slots, (∀ c < 16, ∀ h < 2, k ≠ tailAt c h) → slotW s₆ k = slotW s₄ k := fun k hk hn => by
    rw [k₆ k hk (fun c hc => hn c hc 1 (by decide)), k₅ k hk (fun c hc => hn c hc 0 (by decide))]
  have notTail : ∀ k, tableSlot ≤ k ∨ k < tailSlot → ∀ c < 16, ∀ h < 2, k ≠ tailAt c h := fun k hk c hc h hh => by
    simp only [tailAt, tailSlot_eq, tableSlot_eq] at hk ⊢; omega_arith
  have notCk : ∀ k, k < tableSlot ∨ tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; have := ckEntries_ge kv hkv; omega_arith
  have notMask : ∀ k, 51 ≤ k → k ∉ keyMasks.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := mask_range hkv; omega_arith
  -- The table and the masks.
  have hkey₆ : KeyCtx s₆ Spec.Sm4.ck :=
    { scr := by rw [hb₆, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁']; exact hwB
      fit := by rw [hb₆]; exact fitB
      keys := fun e he => (planeOf_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [entryW_slot, hk₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith) (notTail _ (Or.inl (by omega_arith))),
          v₄ _ (ckEntries_mem he hj)] }
  have hm₆ : MasksOk s₆ := fun kv hkv => by
    have := mask_range hkv
    rw [hk₆ _ (by rw [slots_eq]; omega_arith) (notTail _ (Or.inr (by rw [tailSlot_eq]; omega_arith))),
      k₄ _ (by rw [slots_eq]; omega_arith) (notCk _ (Or.inl (by rw [tableSlot_eq]; omega_arith))), v₃ kv hkv]
  -- The key, bitsliced.
  obtain ⟨s₇, e₇, c₇, kp₇, X₇⟩ := toBs_step hkey₆ (Ctx.refl hm₆)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := slotAddr_ok s₇ .x3 tableEnd (by decide)
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := slotAddr_ok s₈ kp tableSlot (by decide)
  have hb₇ : s₇.gpr sb = b := by rw [c₇.base, hb₆]
  have hb₉ : s₉.gpr sb = b := by rw [o₉ _ (by decide), o₈ _ (by decide), hb₇]
  have mem₉ : s₉.mem = s₇.mem := by rw [m₉, m₈]
  have g₉ : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x3 → s₉.gpr r = s₆.gpr r := fun r h1 h2 h3 => by
    rw [o₉ r h2, o₈ r h3, c₇.keep r h1 h2]
  have g₆' : ∀ r, r ∉ layerWrites → r ≠ sb → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    have ht0 : r ≠ t0 := fun h => h1 (by subst h; decide)
    have ht1 : r ≠ t1 := fun h => h1 (by subst h; decide)
    rw [g₆ r ht0 ht1, g₅ r ht0 ht1, g₄ r ht0, g₃ r ht0, g₂, g₁ r h2]
  have hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem Kp).getD (8 * h + t) 0).getLsbD j := fun h hh t ht j hj => by
    rw [readW64_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega_arith), addr_add]
  have hT : ∀ c < 16, ∀ h < 2, slotW s₆ (tailAt c h) = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h := by
    intro c hc h hh
    rcases (show h = 0 ∨ h = 1 by omega_arith) with rfl | rfl
    · rw [k₆ _ (tailAt_lt hc (by decide)) (fun c' _ h' => by simp only [tailAt] at h'; omega_arith), v₅ c hc, hrdi₄,
        hKw _ f₀₄ 0 (by decide)]
    · rw [v₆ c hc, g₅ _ (by decide) (by decide), hrdi₄, hKw _ (f₀₄.trans f₅) 1 (by decide)]
  have hst : StRel s₉ (fun _ => quads .key Spec.Sm4.ck 0 (keyInit (Spec.Sm4.blockAt s₀.mem Kp))) := fun w hw =>
    ((X₇ w hw).congr fun j _ => by simp only [planes, slotW, mem₉, hb₉, hb₇]).congr_right fun c hc =>
      (keyInit_rel hK hT c hc w hw).symm
  refine ⟨s₉, ?_, ⟨hb₉, ?_, ?_, ?_, ?_, ?_, hst, fun i hi => by omega_arith, fun i hi => ?_, ?_,
    by rw [rd₉, rd₈, c₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁'], by rw [wr₉, wr₈, c₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁']⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app,
      runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      ckTable, e₄, Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some, e₈,
      Option.bind_some, e₉]
  · rw [g₉ _ (by decide) (by decide) (by decide), g₆' _ (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · rw [o₉ _ (by decide), r₈, hb₇]
  · rw [AtEntry, r₉, o₈ _ (by decide), hb₇]; simp; rfl
  · exact (hkey₆.of_ctx c₇) |> fun h => ⟨by rw [wr₉, wr₈, hb₉, ← hb₇]; exact h.scr, by rw [hb₉, ← hb₇]; exact h.fit,
      fun e he => by rw [hb₉, ← hb₇, mem₉]; exact h.keys e he⟩
  · exact fun kv hkv => by simp only [slotW, mem₉, hb₉, ← hb₇]; exact c₇.masks kv hkv
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    have h7 : slotW s₇ (savedSlot + i) = slotW s₆ (savedSlot + i) := by
      simp only [slotW, hb₇, hb₆]
      refine c₇.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [hb₆, wordAddr]
      exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
    have h6 : slotW s₆ (savedSlot + i) = slotW s₂ (savedSlot + i) := by
      rw [hk₆ _ hk (notTail _ (Or.inl (by rw [tableSlot_eq, savedSlot_eq]; omega_arith))),
        k₄ _ hk (notCk _ (Or.inr (by rw [tableEnd_eq, savedSlot_eq]; omega_arith))),
        k₃ _ hk (notMask _ (by rw [savedSlot_eq]; omega_arith))]
    have h2 := sv₂ i hi
    rw [g₁ _ (sreg_ne i hi)] at h2
    show s₉.mem.readW (wordAddr b (savedSlot + i)) 64 = _
    rw [mem₉, ← hb₇, ← h2]
    have := h7.trans h6
    simp only [slotW, hb₇, show s₂.gpr sb = b by rw [g₂, hb₁]] at this
    rw [hb₇]; exact this
  · rw [mem₉]
    refine (f₀₆.trans (c₇.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hb₆]; exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)

/-! ## The loop and the whole function -/

theorem ekLoop_wp {s₀ s : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) (.nonzero .x t0)) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_nonzero, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_nonzero, z']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyAArch64.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyAArch64.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .x2
  let S := s₀.gpr .x1
  have hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwS : (⟨S, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  have pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)⟩)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [h₂.wr]; exact hwB) h₂.base h₂.saved
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  show Spec.Sm4.scheduleAt s₃.mem S = _
  rw [expandKey_eq]
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    Vector.getElem_ofFn, m₃]
  exact h₂.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

end VG.Proof.Sm4.AArch64
