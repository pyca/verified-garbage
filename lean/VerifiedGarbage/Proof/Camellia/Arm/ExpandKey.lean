module

public import VerifiedGarbage.Proof.Camellia.Arm.KeyStore
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.Scratch
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Arm.KaKb
import VerifiedGarbage.Proof.Camellia.Arm.KeyLoad
import VerifiedGarbage.Proof.Camellia.Arm.KeyInit
import VerifiedGarbage.Proof.Camellia.Planes32
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Camellia's key schedule on ARMv7: the whole function

`expandKey_wp`: `expandKey` meets `expandKeyArm`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `revs_ok` byte-swaps them into numbers (`NumOf`), and
`stores_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Camellia (byteOf hiW loW rotHalf hi_eq lo_eq sigE kaD2 kaD3 kaD_eq klkr_halves
  schedule_of_stores subkeys_lt4 subkeys_length keyVals valNum)
open VG.Spec.Camellia (wordAt)

/-- The key schedule on ARMv7 with its working space at `r3`. -/
def expandKeyArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let sched : Region := ⟨State.addr (s.gpr .r2), 272⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 4 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 272 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4 * slots ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 16 ∨ (s.gpr .r1).toNat = 24 ∨ (s.gpr .r1).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem (State.addr (s.gpr .r2))
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s.gpr .r1).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 16 * i + j) := rfl

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (b S : BitVec 32) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem (State.addr S) (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨State.addr S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr
  sp : s.sp = s₈.sp

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {b S : BitVec 32} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hb : s₈.gpr sb = b) (hw : ScrIn s₈.wr b) (hS : SchedOut s₈ b S) (hks : ∀ k ∈ ks, k.1 < 4 ∧ k.2.1 < 128)
    (hkl : ks.length ≤ 34) (hX : ∀ v < 4, NumOf s₈ (valSlot v) (valNum key v))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ b S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉, sp₉⟩ := stores_ok (X := valNum key) ks 0 s₈ hb hw hS hks (by omega) hX
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉, sp₉⟩⟩
  · rw [hlen, schedule_of_stores (vs := keyVals key) (H := fun v => hiW ((keyVals key).getD v 0))
      (L := fun v => loW ((keyVals key).getD v 0)) (fun k hk => (hks k hk).1) (fun v _ => ⟨rfl, rfl⟩)
      (fun i hi j hj => by
        rw [b₉ i hi j hj]
        have hmem : ks.getD i (0, 0, true) ∈ ks := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
          exact List.getElem_mem hi
        have hk := hks _ hmem
        simp only [subHalf, valNum]
        split
        · rename_i h; rw [hi_eq _ _ hk.2, h]
        · rename_i h; rw [lo_eq _ _ hk.2]; simp only [Bool.not_eq_true] at h; rw [h]),
      Spec.Camellia.scheduleBytes, Proof.Camellia.scheduleWords_expandKey, ← hks']
    rfl
  · exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero]
      exact VG.Offset.sub_base _ (by omega)⟩

/-- After `KA` and `KB`: the four values in their slots, the schedule's
pointer and the key's length in theirs. -/
structure KeyMid (s₀ : State) (b : BitVec 32) (key : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  vals : ∀ v < 4, VW s (valSlot v) (hiW ((keyVals key).getD v 0), loW ((keyVals key).getD v 0))
  d : s.mem.readW (wordAddr b dSlot) 32 = s₀.gpr .r2
  n : s.mem.readW (wordAddr b nSlot) 32 = s₀.gpr .r1
  saved : Saved s₀ b s.mem
  frame : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The prologue, the key, and `KA` and `KB`. -/
theorem ekHead_wp {s₀ : State} (hp : expandKeyArm.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hcont : ∀ s, KeyMid s₀ (s₀.gpr .r3)
      (Spec.Camellia.bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) s → WP isa c s Q) :
    WP isa (.seq (.block (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
        (Impl.Camellia.sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)))
      (.seq loadKey (.seq (.block [slotAddr kp keySlot]) (.seq kaKb c)))) s₀ Q := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp
  generalize hb : s₀.gpr .r3 = b at fitB dKB dSB hwr hcont
  generalize hK : s₀.gpr .r0 = K at fitK dKB dKS hrd hcont
  generalize hL : (s₀.gpr .r1).toNat = len at fitK dKB dKS hrd hlen hcont
  have hw : ScrIn s₀.wr b := ⟨by rw [hwr]; simp, fitB⟩
  have hfitB := fitB
  rw [slots_eq] at hfitB
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, d₁, n₁, ent₁, f₁, rd₁, wr₁, sp₁⟩ := ekPrologue_ok hb hw
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyIn s₁ b K len := ⟨b₁, ⟨by rw [wr₁]; exact hw.mem, fitB⟩, by rw [g₁ _ (by decide) (by decide), hK],
    by rw [rd₁, hrd]; simp, fitK, dKB, by omega⟩
  have hkey : Spec.Camellia.bytesAt s₁.mem (State.addr K) len = Spec.Camellia.bytesAt s₀.mem (State.addr K) len :=
    Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨State.addr K, len⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by simp only; omega) hi
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp hk₁ hlen (by rw [g₁ _ (by decide) (by decide), ← hL]; simp)) fun s₂ h₂ => ?_)
  have hb₂ : s₂.gpr sb = b := by rw [h₂.regs _ (by decide) (by decide), b₁]
  let s₃ := s₂.setReg kp (s₂.gpr sb + BitVec.ofNat 32 (4 * keySlot))
  have e₃ : runBlock isa [slotAddr kp keySlot] s₂ = some s₃ := by
    rw [runBlock_cons, slotAddr, exec_addImm (by decide), runStep_some, runBlock_nil]
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have hb₃ : s₃.gpr sb = b := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = s₂.mem.readW (wordAddr b k) 32 := fun k => by
    rw [slotW, hb₃]; rfl
  -- The constants' table.
  have hkc : KeyCtx s₃ 6 sigE := by
    refine ⟨⟨by rw [hb₃, RegUpd.wr_setReg, h₂.wr, wr₁]; exact hw.mem, by rw [hb₃]; exact fitB⟩, by decide,
      fun i hi => (sigma_rel (sigE i)).congr fun j hj => ?_⟩
    rw [entryW_slot, hs₃, h₂.keep _ (by rw [keySlot_eq, slots_eq]; omega)
      (.inl (by rw [keySlot_eq, klSlot_eq]; omega)), ← ent₁ i hi j hj]
    rfl
  -- `KA` and `KB`.
  let key := Spec.Camellia.bytesAt s₁.mem (State.addr K) len
  obtain ⟨hKL1, hKL2, hKR1, hKR2⟩ := klkr_halves s₁.mem (State.addr K) hlen
  have vl : VW s₃ klSlot (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1) := by
    rw [hKL1, hKL2]; exact h₂.kl.congr fun j hj => slotW_setReg _ _ (by decide) _
  have vr : VW s₃ krSlot (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2) := by
    rw [hKR1, hKR2]; exact h₂.kr.congr fun j hj => slotW_setReg _ _ (by decide) _
  refine WP.seq (WP.mono (WP.sp (kaKb_wp hkc (by rw [AtEntry, RegUpd.gpr_setReg_self, hb₃, hb₂]; simp) vl vr))
    fun s₄ ⟨h₄, sp₄⟩ => hcont s₄ ?_)
  have hc := h₄.ctx
  have hb₄ : s₄.gpr sb = b := by rw [hc.base, hb₃]
  have keep₄ : ∀ k < slots, keySlot ≤ k → k ≠ grpSlot → k < tailSlot →
      s₄.mem.readW (wordAddr b k) 32 = s₁.mem.readW (wordAddr b k) 32 := fun k hk h1 h2 h3 => by
    have := hc.slot (by rw [hb₃]; exact fitB) hk h1 h2 (.inl h3)
    rw [slotW, hb₄, hs₃] at this
    rw [this, h₂.keep k hk (.inl (by rw [klSlot_eq]; rw [tailSlot_eq] at h3; omega))]
  have hka := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hkey' : key = Spec.Camellia.bytesAt s₀.mem (State.addr K) len := hkey
  rw [← hkey']
  refine ⟨hb₄, ⟨by rw [hc.wr, RegUpd.wr_setReg, h₂.wr, wr₁]; exact hw.mem, fitB⟩, fun v hv => ?_,
    by rw [keep₄ _ (by decide) (by decide) (by decide) (by decide), d₁],
    by rw [keep₄ _ (by decide) (by decide) (by decide) (by decide), n₁],
    fun i hi => ?_, ?_, by rw [hc.rd, RegUpd.rd_setReg, h₂.rd, rd₁], by rw [hc.wr, RegUpd.wr_setReg, h₂.wr, wr₁],
    by rw [sp₄, RegUpd.sp_setReg, h₂.sp, sp₁]⟩
  · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl
    · exact h₄.kl
    · exact h₄.kr
    · have := h₄.ka; rw [hka.1] at this; exact this
    · have := h₄.kb; rw [hka.2] at this; exact this
  · rw [keep₄ _ (by rw [savedSlot_eq, slots_eq]; omega) (by rw [savedSlot_eq, keySlot_eq]; omega)
      (by rw [savedSlot_eq, grpSlot_eq]; omega) (by rw [savedSlot_eq, tailSlot_eq]; omega)]
    exact sv₁ i hi
  · have f₃ : Frame [⟨State.addr b, 4 * slots⟩] s₃.mem s₄.mem := by
      have := hc.frame; rw [hb₃] at this
      exact this.sub fun r hr => ⟨_, List.mem_singleton_self _, ctx_sub_scr fitB r hr⟩
    exact f₁.trans (h₂.frame.trans f₃)


theorem saved_not_rev : ∀ i < 9, savedSlot + i ∉ revSlots := by decide +kernel

/-- The values byte-swapped, the subkeys stored, the registers restored. -/
theorem ekTail_wp {s₀ s : State} {b S : BitVec 32} {key : List Byte} {len : Nat} (h : KeyMid s₀ b key s)
    (hS2 : s₀.gpr .r2 = S) (hSw : (⟨State.addr S, 272⟩ : Region) ∈ s₀.wr) (hSf : S.toNat + 272 ≤ 2 ^ 32)
    (hSd : Region.Disjoint ⟨State.addr S, 272⟩ ⟨State.addr b, 4 * slots⟩) (hr1 : s₀.gpr .r1 = BitVec.ofNat 32 len)
    (hlen : len = 16 ∨ len = 24 ∨ len = 32) (hkl : key.length = len) :
    WP isa (.seq (.block (revValues ++ [ldS .r2 dSlot, ldS t0 nSlot, .cmp t0 (.imm 16)]))
      (.seq (.ite .eq (.block (storeSubkeys Impl.Camellia.subkeys128)) (.block (storeSubkeys Impl.Camellia.subkeys256)))
        (.block ([movR .r12 sb] ++ restoreRegs .r12)))) s fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Camellia.bytesAt s'.mem (State.addr S) (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
        Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key) := by
  have hfit := h.scr.fit
  obtain ⟨hnd, hlt⟩ := revSlots_facts
  -- The values, byte-swapped.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := revs_ok revSlots (s := s) h.base h.scr hnd hlt
  have hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide), h.base]
  have hX₁ : ∀ v < 4, NumOf s₁ (valSlot v) (valNum key v) := fun v hv => by
    have := num_of_rev (s' := s₁) (h.vals v hv) fun j hj => by
      simp only [slotW]
      rw [hb₁, h.base, v₁ (valSlot v + j) (mem_revSlots hv hj)]
    dsimp only at this
    exact this
  -- The schedule's pointer and the key's length.
  have hw₁ : ScrIn s₁.wr b := ⟨by rw [wr₁]; exact h.scr.mem, hfit⟩
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldSlot_ok s₁ .r2 sb (k := dSlot) hb₁ (by decide) hw₁
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := ldSlot_ok s₂ t0 sb (k := nSlot) (by rw [o₂ _ (by decide), hb₁])
    (by decide) (by rw [wr₂]; exact hw₁)
  let s₄ := subFlags s₃ (s₃.gpr t0) 16
  have e₄ := cmpImm_ok s₃ t0 (v := 16) (by decide)
  have hz₄ : s₄.z = decide (len = 16) := by
    rw [subFlags_z, v₃, m₂, k₁ nSlot (by decide) (by decide), h.n, hr1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      ofNat32_sub_beq (by omega) (by decide)]
  have hb₄ : s₄.gpr sb = b := by rw [subFlags_gpr, o₃ _ (by decide), o₂ _ (by decide), hb₁]
  have hm₄ : s₄.mem = s₁.mem := by rw [subFlags_mem, m₃, m₂]
  have hr2₄ : s₄.gpr .r2 = S := by
    rw [subFlags_gpr, o₃ _ (by decide), v₂, k₁ dSlot (by decide) (by decide), h.d, hS2]
  have wr₄ : s₄.wr = s.wr := by rw [subFlags_wr, wr₃, wr₂, wr₁]
  have hw₄ : ScrIn s₄.wr b := ⟨by rw [wr₄]; exact h.scr.mem, hfit⟩
  have hS₄ : SchedOut s₄ b S := ⟨hr2₄, by rw [wr₄, h.wr]; exact hSw, hSf, hSd⟩
  have hX₄ : ∀ v < 4, NumOf s₄ (valSlot v) (valNum key v) := fun v hv => (hX₁ v hv).congr fun j hj => by
    simp only [slotW, hb₄, hb₁, hm₄]
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [runBlock_app, revValues_eq, e₁, Option.bind_some, show ([ldS .r2 dSlot, ldS t0 nSlot, .cmp t0 (.imm 16)] :
      List Instr) = [.ldr .r2 sb (4 * dSlot)] ++ ([.ldr t0 sb (4 * nSlot)] ++ [.cmp t0 (.imm 16)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄], ?_⟩)
  -- The subkeys.
  have hk128 : ∀ k ∈ Impl.Camellia.subkeys128, k.1 < 4 ∧ k.2.1 < 128 := by decide
  have hk256 : ∀ k ∈ Impl.Camellia.subkeys256, k.1 < 4 ∧ k.2.1 < 128 := by decide
  refine WP.seq (WP.mono (Q := StoresPost s₄ b S len key)
    (WP.ite (decide (len = 16)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h16 => ?_) (fun h16 => ?_))
    fun s₅ h₅ => ?_)
  · have h16 : len = 16 := by simpa using h16
    exact stores_wp hb₄ hw₄ hS₄ hk128 (by rw [subkeys_length.1]; omega) hX₄
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hkl, ite_eq_left h16])
  · have h16 : len ≠ 16 := by simpa using h16
    exact stores_wp hb₄ hw₄ hS₄ hk256 (by rw [subkeys_length.2]) hX₄
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hkl, ite_eq_right h16])
  -- The epilogue.
  have hb₅ : s₅.gpr sb = b := by rw [h₅.regs _ (by decide) (by decide), hb₄]
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₅ .r12 sb
  have hsv : Saved s₀ b s₆.mem := fun i hi => by
    rw [m₆, hS₄.slot hfit h₅.frame (fun _ h => h) (by rw [savedSlot_eq, slots_eq]; omega), hm₄,
      k₁ (savedSlot + i) (by rw [savedSlot_eq, slots_eq]; omega) (saved_not_rev i hi)]
    exact h.saved i hi
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    ⟨by rw [wr₆, h₅.wr, wr₄]; exact h.scr.mem, hfit⟩ (by rw [r₆, hb₅]) hsv
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  rw [m₇, m₆]
  exact h₅.bytes

theorem expandKey_wp {s₀ : State} (hp : expandKeyArm.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ expandKeyArm.post s₀ s' := by
  have hp' := hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp'
  unfold expandKey
  refine ekHead_wp hp fun s h => ?_
  exact ekTail_wp h rfl (by rw [hwr]; simp) fitS dSB (by simp) hlen (by simp [Spec.Camellia.bytesAt])

end VG.Proof.Camellia.Arm
