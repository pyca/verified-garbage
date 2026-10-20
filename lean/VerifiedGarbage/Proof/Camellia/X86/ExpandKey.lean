module

public import VerifiedGarbage.Proof.Camellia.X86.KeyStore
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.X86.Prologue
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.X86.KaKb
import VerifiedGarbage.Proof.Camellia.X86.KeyLoad
import VerifiedGarbage.Proof.Camellia.X86.KeyInit
import VerifiedGarbage.Proof.Camellia.Planes32
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Camellia's key schedule on x86 (32-bit): the whole function

`expandKey_wp`: `expandKey` meets `expandKeyX86`, the shared contract with
the working space as the fourth argument. As on ARMv7
(`Proof/Camellia/Arm/ExpandKey.lean`): after the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `revs_ok` byte-swaps them into numbers (`NumOf`), and
`stores_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movS at_ argOp)
open VG.Proof.Camellia (byteOf hiW loW rotHalf hi_eq lo_eq sigE kaD2 kaD3 kaD_eq klkr_halves sigma_rel
  schedule_of_stores subkeys_length keyVals valNum)

/-- The key schedule on x86 with its working space as the fourth argument. -/
def expandKeyX86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sched : Region := ⟨(arg s 2).setWidth 64, 272⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 272 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem ((arg s 2).setWidth 64)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (arg s 1).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-! ## The arguments -/

theorem ekArg_eq (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) (i : Nat) (hi : i < 4) :
    argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  have hs := setWidth_toNat (s.gpr .esp)
  exact addr_eq (by omega)

/-- Argument `i` is in the arguments' region. -/
theorem ekArg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := setWidth_toNat (s.gpr .esp)
  rw [ekArg_eq s hfit i hi, ekArg_eq s hfit 0 (by decide)]
  exact VG.Offset.contains _ (by omega) (by omega) (by omega)

theorem ekArg_sub (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    Region.Sub ⟨argAddr s i, 4⟩ ⟨argAddr s 0, 16⟩ := by
  rw [ekArg_eq s hfit i hi, ekArg_eq s hfit 0 (by decide)]
  exact VG.Offset.sub _ (by omega) (by omega)

/-- `mov eax, [esp + 4 + 4 i]; cmp eax, 16`. -/
theorem cmpArg16_ok (s : State) (i : Nat) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .alu .cmp .eax (.imm 16)] s = some s' ∧
      s'.zf = some (s.mem.readW (s.ea (argOp i)) 32 - 16 == 0) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  let a := s₁.gpr .eax
  refine ⟨arithFlags s₁ (a - 16) (a.toNat < (16 : BitVec 32).toNat) (subOverflow a 16 (a - 16)), ?_,
    by rw [RegUpd.zf_arithFlags, show a = _ from v₁], fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr],
    by rw [RegUpd.mem_arithFlags, m₁], by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  rw [show ([.mov .eax (.mem (argOp i)), .alu .cmp .eax (.imm 16)] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.alu .cmp .eax (.imm 16)] from rfl, runBlock_app, e₁, Option.bind_some]
  rfl

/-! ## The subkeys' stores -/

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : BitVec 32) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem (S.setWidth 64) (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S.setWidth 64, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ .eax → r ≠ .ebx → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {b S : BitVec 32} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hb : s₈.gpr sb = b) (hw : ScrIn s₈.wr b) (hS : SchedOut s₈ b S) (hks : ∀ k ∈ ks, k.1 < 4 ∧ k.2.1 < 128)
    (hkl : ks.length ≤ 34) (hX : ∀ v < 4, NumOf s₈ (valSlot v) (valNum key v))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := stores_ok (X := valNum key) ks 0 s₈ hb hw hS hks (by omega) hX
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉⟩⟩
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

/-! ## The function -/

/-- After `KA` and `KB`: the four values in their slots. -/
structure KeyMid (s₀ : State) (b : BitVec 32) (key : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  esp : s.gpr .esp = s₀.gpr .esp
  scr : ScrIn s.wr b
  vals : ∀ v < 4, VW s (valSlot v) (hiW ((keyVals key).getD v 0), loW ((keyVals key).getD v 0))
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The prologue, the key, and `KA` and `KB`. -/
theorem ekHead_wp {s₀ : State} (hp : expandKeyX86.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hcont : ∀ s, KeyMid s₀ (arg s₀ 3)
      (Spec.Camellia.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat) s → WP isa c s Q) :
    WP isa (.seq (.block (saveRegs 3 ++ (Impl.Camellia.sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)))
      (.seq loadKey (.seq (.block (kpAt keySlot)) (.seq kaKb c)))) s₀ Q := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, hlen⟩ := hp
  let K := arg s₀ 0
  let len := (arg s₀ 1).toNat
  let b := arg s₀ 3
  have hw : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, ekArg_contains s₀ fitE hi⟩
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (ekArg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, ent₁, k₁, f₁, rd₁, wr₁⟩ :=
    ekPrologue_ok hw (argIn rfl rfl rfl 3 (by decide)) (by rw [ea_arg rfl]; rfl)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  have hkey : Spec.Camellia.bytesAt s₁.mem (K.setWidth 64) len = Spec.Camellia.bytesAt s₀.mem (K.setWidth 64) len :=
    Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨K.setWidth 64, len⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by simp only; omega) hi
  -- `KL` and `KR`.
  have hl₁ : LoadPre s₁ b K len :=
    { base := b₁, scr := ⟨by rw [wr₁]; exact hw.mem, fitB⟩, rd := by rw [rd₁, hrd]; simp [K, len],
      fit := fitK, sep := dKB, hlen := hlen,
      arg0 := argIn rd₁ wr₁ esp₁ 0 (by decide), arg0V := by rw [ea_arg esp₁, argR f₁ 0 (by decide)],
      arg1 := argIn rd₁ wr₁ esp₁ 1 (by decide),
      arg1V := by rw [ea_arg esp₁, argR f₁ 1 (by decide)]; simp [len],
      arg1Sep := by rw [ea_arg esp₁]; exact dAB.sub_left (ekArg_sub s₀ fitE (by decide)) }
  refine WP.seq (WP.mono (loadKey_wp hl₁) fun s₂ h₂ => ?_)
  have hb₂ : s₂.gpr sb = b := by rw [h₂.regs _ (by decide) (by decide), b₁]
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := kpAt_ok s₂ keySlot
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = s₂.mem.readW (wordAddr b k) 32 := fun k => by
    rw [slotW, hb₃, m₃]
  -- The constants' table.
  have hkc : KeyCtx s₃ 6 sigE := by
    refine ⟨⟨by rw [hb₃, wr₃, h₂.wr, wr₁]; exact hw.mem, by rw [hb₃]; exact fitB⟩, by decide,
      fun i hi => (sigma_rel (sigE i)).congr fun j hj => ?_⟩
    show slotW s₃ (keySlot + 16 * i + j) = _
    rw [hs₃, h₂.keep _ (by rw [keySlot_eq, slots_eq]; omega)
      (.inr (by rw [keySlot_eq, klSlot_eq]; omega))]
    exact ent₁ i hi j hj
  -- `KA` and `KB`.
  let key := Spec.Camellia.bytesAt s₁.mem (K.setWidth 64) len
  obtain ⟨hKL1, hKL2, hKR1, hKR2⟩ := klkr_halves s₁.mem (K.setWidth 64) hlen
  have hv₃ : ∀ a v, VW s₂ a v → VW s₃ a v := fun a v h => h.congr fun j _ => by
    rw [hs₃, slotW, hb₂]
  have vl : VW s₃ klSlot (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1) := by
    rw [hKL1, hKL2]; exact hv₃ _ _ h₂.kl
  have vr : VW s₃ krSlot (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2) := by
    rw [hKR1, hKR2]; exact hv₃ _ _ h₂.kr
  refine WP.seq (WP.mono (kaKb_wp hkc (by rw [AtEntry, kp₃, hb₃, hb₂]; simp) vl vr) fun s₄ h₄ => hcont s₄ ?_)
  have hc := h₄.ctx
  have hb₄ : s₄.gpr sb = b := by rw [hc.base, hb₃]
  have hka := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hkey' : key = Spec.Camellia.bytesAt s₀.mem (K.setWidth 64) len := hkey
  rw [← hkey']
  have esp₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [hc.keep _ (by decide) (by decide), o₃ _ (by decide), h₂.regs _ (by decide) (by decide), esp₁]
  refine ⟨hb₄, esp₄, ⟨by rw [hc.wr, wr₃, h₂.wr, wr₁]; exact hw.mem, fitB⟩, fun v hv => ?_, fun i hi => ?_, ?_,
    by rw [hc.rd, rd₃, h₂.rd, rd₁], by rw [hc.wr, wr₃, h₂.wr, wr₁]⟩
  · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl
    · exact h₄.kl
    · exact h₄.kr
    · have := h₄.ka; rw [hka.1] at this; exact this
    · have := h₄.kb; rw [hka.2] at this; exact this
  · have := hc.slot (by rw [hb₃]; exact fitB) (k := savedSlot + i) (by rw [savedSlot_eq, slots_eq]; omega)
      (by rw [savedSlot_eq, keySlot_eq]; omega) (by rw [savedSlot_eq, grpSlot_eq]; omega)
    rw [slotW, slotW, hb₄, hb₃, m₃, h₂.keep _ (by rw [savedSlot_eq, slots_eq]; omega)
      (.inr (by rw [savedSlot_eq, klSlot_eq]; omega))] at this
    rw [this]
    exact sv₁ i hi
  · have f₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₃.mem s₄.mem := by
      have := hc.frame; rw [hb₃] at this
      exact this.sub fun r hr => ⟨_, List.mem_singleton_self _, ctx_sub fitB r hr⟩
    rw [m₃] at f₃
    exact f₁.trans (h₂.frame.trans f₃)

theorem saved_not_rev : ∀ i < 4, savedSlot + i ∉ revSlots := by decide +kernel

/-- The values byte-swapped, the subkeys stored, the registers restored. -/
theorem ekTail_wp {s₀ s : State} (hp : expandKeyX86.pre s₀)
    (h : KeyMid s₀ (arg s₀ 3) (Spec.Camellia.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat) s) :
    WP isa (.seq (.block (revValues ++ ([.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 1)),
        .alu .cmp .eax (.imm 16)] : List Instr)))
      (.seq (.ite .e (.block (storeSubkeys Impl.Camellia.subkeys128)) (.block (storeSubkeys Impl.Camellia.subkeys256)))
        (.block restoreRegs))) s fun s' => abiPreserved s₀ s' ∧ expandKeyX86.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, hlen⟩ := hp
  let key := Spec.Camellia.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat
  let len := (arg s₀ 1).toNat
  let S := arg s₀ 2
  let b := arg s₀ 3
  have hkl : key.length = len := by simp [key, len, Spec.Camellia.bytesAt]
  have hfit := h.scr.fit
  have hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, ekArg_contains s₀ fitE hi⟩
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (ekArg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  obtain ⟨hnd, hlt⟩ := revSlots_facts
  -- The values, byte-swapped.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, f₁⟩ := revs_ok revSlots (s := s) h.base h.scr hnd hlt
  have hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide), h.base]
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [g₁ _ (by decide), h.esp]
  have hX₁ : ∀ v < 4, NumOf s₁ (valSlot v) (valNum key v) := fun v hv => by
    have := num_of_rev (s' := s₁) (h.vals v hv) fun j hj => by
      simp only [slotW]
      rw [hb₁, h.base, v₁ (valSlot v + j) (mem_revSlots hv hj)]
    dsimp only at this
    exact this
  have F₁ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₁.mem := h.frame.trans f₁
  -- The schedule's pointer and the key's length.
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok s₁ .edx 2
    (argIn (rd₁.trans h.rd) (wr₁.trans h.wr) esp₁ 2 (by decide))
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [o₂ _ (by decide), esp₁]
  obtain ⟨s₃, e₃, z₃, o₃, m₃, rd₃, wr₃⟩ := cmpArg16_ok s₂ 1
    (argIn (rd₂.trans (rd₁.trans h.rd)) (wr₂.trans (wr₁.trans h.wr)) esp₂ 1 (by decide))
  have hz₃ : s₃.zf = some (decide (len = 16)) := by
    rw [z₃, ea_arg esp₂, m₂, argR F₁ 1 (by decide), show arg s₀ 1 = BitVec.ofNat 32 len by simp [len],
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ofNat32_sub_beq (by omega) (by decide)]
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), o₂ _ (by decide), hb₁]
  have hm₃ : s₃.mem = s₁.mem := by rw [m₃, m₂]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, h.wr]
  have hw₃ : ScrIn s₃.wr b := .exact (by rw [wr₃', hwr]; simp [b]) hfit
  have hS₃ : SchedOut s₃ b S := ⟨by rw [o₃ _ (by decide), v₂, ea_arg esp₁, argR F₁ 2 (by decide)],
    by rw [wr₃', hwr]; simp [S], fitS, dSB⟩
  have hX₃ : ∀ v < 4, NumOf s₃ (valSlot v) (valNum key v) := fun v hv => (hX₁ v hv).congr fun j hj => by
    simp only [slotW, hb₃, hb₁, hm₃]
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, revValues_eq, e₁, Option.bind_some, show ([.mov .edx (.mem (argOp 2)),
      .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 16)] : List Instr) = [.mov .edx (.mem (argOp 2))] ++
      [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 16)] from rfl, runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  -- The subkeys.
  have hk128 : ∀ k ∈ Impl.Camellia.subkeys128, k.1 < 4 ∧ k.2.1 < 128 := by decide
  have hk256 : ∀ k ∈ Impl.Camellia.subkeys256, k.1 < 4 ∧ k.2.1 < 128 := by decide
  refine WP.seq (WP.mono (Q := StoresPost s₃ S len key)
    (WP.ite (decide (len = 16)) ((eval_e s₃).trans hz₃) (fun h16 => ?_) (fun h16 => ?_))
    fun s₅ h₅ => ?_)
  · have h16 : len = 16 := by simpa using h16
    exact stores_wp hb₃ hw₃ hS₃ hk128 (by rw [subkeys_length.1]; omega) hX₃
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hkl, ite_eq_left h16])
  · have h16 : len ≠ 16 := by simpa using h16
    exact stores_wp hb₃ hw₃ hS₃ hk256 (by rw [subkeys_length.2]) hX₃
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hkl, ite_eq_right h16])
  -- The epilogue.
  have hb₅ : s₅.gpr sb = b := by rw [h₅.regs _ (by decide) (by decide), hb₃]
  have hsv : Saved s₀ b s₅.mem := fun i hi => by
    rw [hS₃.slot hfit h₅.frame (fun _ h => h) (by rw [savedSlot_eq, slots_eq]; omega), hm₃,
      k₁ (savedSlot + i) (by rw [savedSlot_eq, slots_eq]; omega) (saved_not_rev i hi)]
    exact h.saved i hi
  obtain ⟨s₆, e₆, rg₆, o₆, m₆, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    (.exact (by rw [h₅.wr, wr₃', hwr]; simp [b]) hfit) hb₅ hsv
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), h₅.regs _ (by decide) (by decide), o₃ _ (by decide), esp₂]
  · rw [m₆, h₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dRS) (by decide), hm₃]
    exact F₁.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dRB) (by decide)
  · show Spec.Camellia.bytesAt s₆.mem (S.setWidth 64) _ = _
    rw [m₆]
    exact h₅.bytes

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86.pre s₀) :
    WP isa expandKey s₀ fun s' => abiPreserved s₀ s' ∧ expandKeyX86.post s₀ s' := by
  unfold expandKey
  exact ekHead_wp hp fun s h => ekTail_wp hp h

end VG.Proof.Camellia.X86
