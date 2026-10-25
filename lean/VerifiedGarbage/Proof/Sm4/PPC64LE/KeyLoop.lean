module
public import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Crypt16
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Prologue

import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyInit
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Sm4.PPC64LE.Keys
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit

/-!
# The loop of the SM4 key schedule on PPC64LE

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's 64-bit words, byte-reversed (`rev`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_outBlock' ofInt_nat)

/-! ## Bytes -/

theorem rev64_bit (x : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    (rev64 x).getLsbD (8 * t + j) = x.getLsbD (8 * (7 - t) + j) := by
  rw [show (rev64 x).getLsbD (8 * t + j) = x.getLsbD (8 * (7 - (8 * t + j) / 8) + (8 * t + j) % 8) from
    VG.byteRev64_getLsbD x (by omega_arith)]
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

/-- `li r12, n; stdbrx v, r4, r12`. -/
theorem storeRevAt_ok (s : State) (v : Reg) (n : Nat) (hv : v ≠ .r12) (hn : n < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.li .r12 n, .storeRev .d v .r4 .r12] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4 + BitVec.ofNat 64 n) (rev64 (s.gpr v)) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have u := Upd.write s .r12 (BitVec.ofNat 64 n)
  let s₁ := s.write .r12 (BitVec.ofNat 64 n)
  have h4 : s₁.gpr .r4 = s.gpr .r4 := u.other _ (by decide)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .r4 + s₁.gpr .r12) (rev64 (s₁.gpr v)) }, ?_, ?_, u.other,
    u.rd, u.wr⟩
  · have hw' : InRegions s₁.wr (s₁.gpr .r4 + s₁.gpr .r12) 8 := by rw [h4, u.gpr, u.wr]; exact hw
    simp only [runBlock_cons, exec_li hn, runStep_some]
    rw [exec_storeRev_d (show Reg.r4 ≠ .r0 by decide) hw', runStep_some, runBlock_nil]
  · show Mem.writeW _ _ _ = _
    rw [h4, u.gpr, u.other v hv, u.mem]

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
    (hr8 : s.gpr .r4 = S + BitVec.ofNat 64 (16 * m))
    (hS : ∀ t < 2, InRegions s.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8)
    (hT : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr b (tailAt 0 t)) 8)
    (hsep : ∀ t < 2, Mem.Sep (wordAddr b (tailAt 0 t)) 8 (S + BitVec.ofNat 64 (16 * m)) 8) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0)[15 - t]'(by omega_arith)).getLsbD j) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := t0) (k := tailAt 0 1) (by simp only [tailAt, tailSlot_eq]; omega_arith)
    (by rw [hb]; exact hT 1 (by decide)) rfl
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeRevAt_ok s₁ t0 0 (by decide) (by decide)
    (by rw [wr₁, o₁ _ (by decide), hr8, addr_add, Nat.add_zero]
        have := hS 0 (by decide); simpa using this)
  have hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), o₁ _ (by decide), hb]
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ldMask_ok (s := s₃) (r := t0) (k := tailAt 0 0)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) (by rw [rd₃, wr₃, rd₁, wr₁, hb₃]; exact hT 0 (by decide)) rfl
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := storeRevAt_ok s₄ t0 8 (by decide) (by decide)
    (by rw [wr₄, wr₃, wr₁, o₄ _ (by decide), g₃ _ (by decide), o₁ _ (by decide), hr8, addr_add]
        exact hS 1 (by decide))
  have hr8₄ : s₄.gpr .r4 = S + BitVec.ofNat 64 (16 * m) := by
    rw [o₄ _ (by decide), g₃ _ (by decide), o₁ _ (by decide), hr8]
  have hr8₁ : s₁.gpr .r4 = S + BitVec.ofNat 64 (16 * m) := by rw [o₁ _ (by decide), hr8]
  have q0 : s₄.gpr t0 = slotW s (tailAt 0 0) := by
    rw [v₄]
    simp only [slotW, m₃, m₁, hb₃, hb, hr8₁, addr_add, Nat.add_zero]
    rw [Mem.readW_writeW_sep (hsep 0 (by decide)) (by decide)]
  have hm6 : s₆.mem = (s.mem.writeW (S + BitVec.ofNat 64 (16 * m)) (rev64 (slotW s (tailAt 0 1)))).writeW
      (S + BitVec.ofNat 64 (16 * m + 8)) (rev64 (slotW s (tailAt 0 0))) := by
    rw [m₆, m₄, m₃, m₁, hr8₄, q0, hr8₁, v₁, addr_add, addr_add, Nat.add_zero]
  refine ⟨s₆, ?_, fun t ht j hj => ?_, ?_, fun r hr h12 => ?_, by rw [rd₆, rd₄, rd₃, rd₁],
    by rw [wr₆, wr₄, wr₃, wr₁]⟩
  · rw [extract, show ([ldS t0 (tailAt 0 1), .li .r12 0, .storeRev .d t0 .r4 .r12, ldS t0 (tailAt 0 0),
        .li .r12 8, .storeRev .d t0 .r4 .r12] : List Instr) = [ldS t0 (tailAt 0 1)] ++
        ([.li .r12 0, .storeRev .d t0 .r4 .r12] ++ ([ldS t0 (tailAt 0 0)] ++
        [.li .r12 8, .storeRev .d t0 .r4 .r12])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₆]
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
  · rw [g₆ r h12, o₄ r hr, g₃ r h12, o₁ r hr]

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : Addr) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r4 : s.gpr .r4 = S + BitVec.ofNat 64 (16 * m)
  r11 : s.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd)
  kr : AtEntry s b (4 * m)
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
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kr) hm hi.st
  obtain ⟨s₂, e₂, kr₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  have c₂ : Ctx s s₂ := c₁.kr o₂ m₂ rd₂ wr₂
  have X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kr₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  have base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  have r8₃ : s₃.gpr .r4 = S + BitVec.ofNat 64 (16 * m) := by rw [c₃.keep _ (by decide) (by decide), hi.r4]
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
    simp only [slotW, o₄ sb (by decide) (by decide), base₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sepTS k hk) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .r4 .r4 (imm := 16) (by decide)
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := subR_ok s₅ t0 kr .r11
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have g₆' : ∀ r, r ≠ .r4 → r ≠ t0 → r ≠ .r12 → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by rw [g₆ r h2, o₅ r h1, o₄ r h2 h3]
  have base₆ : s₆.gpr sb = b := by rw [g₆' _ (by decide) (by decide) (by decide), base₃]
  have keep₆ : ∀ k < slots, slotW s₆ k = slotW s₃ k := fun k hk => by
    rw [← keep₄ k hk]; simp only [slotW, mem₆, g₆' sb (by decide) (by decide) (by decide), o₄ sb (by decide) (by decide)]
  have kr₆ : AtEntry s₆ b (4 * (m + 1)) := by
    rw [AtEntry, g₆' _ (by decide) (by decide) (by decide), kr₃, kr₂, k₁, show s.gpr kr = _ from hi.kr, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith]
  have rdi₆ : s₆.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₆' _ (by decide) (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.r11]
  have hent : ∀ (st : State) e j, entryW st.mem (st.gpr sb) e j = slotW st (tableSlot + 8 * e + j) := fun st e j => by
    simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]
  have key₃ := hi.keys.of_ctx c₃
  -- The schedule's bytes outside this iteration's.
  have old₆ : ∀ x, (∀ r ∈ [(⟨b, 8 * tableSlot⟩ : Region), ⟨S + BitVec.ofNat 64 (16 * m), 16⟩], ¬ r.Contains x 1) →
      s₆.mem x = s.mem x := fun x hx => by
    rw [mem₆, f₄ x (fun r hr => hx r (by simp at hr; simp [hr])),
      c₃.frame x (fun r hr => by simp at hr; subst hr; rw [hi.base]; exact hx _ (by simp))]
  refine ⟨s₆, ?_, ⟨base₆, ?_,
    rdi₆, kr₆, ⟨by rw [base₆, wr₆, wr₅, wr₄, wr₃]; exact hp.scr, by rw [base₆]; rw [slots_eq]; exact hfit,
      fun e he => (key₃.keys e he).congr fun j hj => by
        rw [hent s₆, hent s₃, keep₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith)]⟩,
    fun kv hkv => by rw [keep₆ _ (by have := mask_lt hkv; rw [slots_eq]; omega_arith)]; exact c₃.masks kv hkv,
    fun w hw => (X₃ w hw).congr fun j hj => keep₆ _ (by simp only [stateSlot, slots_eq]; omega_arith),
    fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_, by rw [rd₆, rd₅, rd₄, rd₃], by rw [wr₆, wr₅, wr₄, wr₃]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some,
      show ([.addi .r4 .r4 16, .sub t0 kr .r11] : List Instr) =
        [.addi .r4 .r4 16] ++ [.sub t0 kr .r11] from rfl, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [g₆ _ (by decide), r₅, o₄ _ (by decide) (by decide), r8₃, addr_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
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
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), o₄ _ (by decide) (by decide), o₄ _ (by decide) (by decide), kr₃, kr₂, k₁,
      show s.gpr kr = _ from hi.kr, c₃.keep _ (by decide) (by decide), hi.r11, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)]
    simp only [decide_eq_decide]; omega_arith

end VG.Proof.Sm4.PPC64LE
