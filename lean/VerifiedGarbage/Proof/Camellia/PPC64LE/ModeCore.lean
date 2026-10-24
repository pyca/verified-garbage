module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Camellia.PPC64LE.PreparedBody
import VerifiedGarbage.Proof.Camellia.PPC64LE.PreparedVerified
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# Camellia's core for the modes on PPC64LE

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key the number of rounds and the
schedule's words, its cipher `Spec.Camellia.cipher` under them for
encryption and `Spec.Camellia.invCipher` for decryption. The key's
arguments are the schedule at `r3` and the number of rounds in `r28`, which
the modes keep (`KeptBut`); it is ready when the masks and the table of
subkeys in `d`'s order are in the core's slots (`ReadyAt`) and `r28` still
holds the number of rounds.

`prepare` and `crypt` run the bodies of `vg_camellia_prepare_keys` and
`vg_camellia_crypt_prepared` (`prepareBody_wp`, `cryptBody_wp`) from the
state narrowed to the schedule and the functions' 414 slots (`WP.narrow`);
the registers the bodies do not write (`prepWrites`, `cryptWrites`, by
`WP.keep`) hold meanwhile the values the core must keep.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.Mode

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Camellia.PPC64LE VG.Proof.Camellia.PPC64LE
open VG.Impl.Modes.PPC64LE (mov)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList blockFn)

/-- The number of rounds in `r28` and the schedule at `r3`, outside the
regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .r3 = p ∧ s.gpr .r28 = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The table of the subkeys of `k`'s rounds and words in the order of `d`,
and the number of rounds in `r28`. -/
def Ready (d : Dir) (s : State) (B : Addr) (_ : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ReadyAt d k.1 s.mem B k.2 ∧ s.gpr .r28 = BitVec.ofNat 64 k.1

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : 48 ≤ kv.1 ∧ kv.1 < 53 := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

theorem toNat_rounds {R : Nat} (h : R = 18 ∨ R = 24) : (BitVec.ofNat 64 R).toNat = R := by
  rcases h with rfl | rfl <;> rfl

/-- The table survives what writes only bytes from the tail buffer on. -/
theorem readyAt_congr {d : Dir} {R : Nat} {m m' : Mem} {B : Addr} {w : List (BitVec 64)} (hR : R = 18 ∨ R = 24)
    (h : ReadyAt d R m B w)
    (hw : ∀ o, o + 8 ≤ 8 * tailSlot → m'.readW (B + BitVec.ofNat 64 o) 64 = m.readW (B + BitVec.ofNat 64 o) 64) :
    ReadyAt d R m' B w := by
  obtain ⟨hm, he⟩ := h
  have hg4 : R / 6 ≤ 4 := by omega
  refine ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩
  · have hk := mask_range hkv
    rw [← hm kv hkv]
    exact hw (8 * kv.1) (by rw [tailSlot_eq]; omega)
  · exact hw (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega)

/-- A word of the core's slots before the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {o : Nat} (ho : o + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (blkRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 o, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (show o + 8 ≤ 8 * slots by rw [slots_eq]; rw [tailSlot_eq] at ho; omega))
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 o, 8⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 4 * 4 * 1⟩
    exact VG.Offset.disjoint B (by simp only [tailSlot_eq] at ho ⊢; omega)
      (by simp only [tailSlot_eq] at ho; omega) (by simp only [tailSlot_eq]; omega)

theorem ready_frame {dir : Dir} {s s' : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)}
    {rs : List Region} (h : Ready dir s B ws k) (hk : KeptBut s s') (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (blkRegion (dirCore dir) B)) :
    Ready dir s' B ws k := by
  obtain ⟨hR, hr, h28⟩ := h
  refine ⟨hR, readyAt_congr hR hr fun o ho => ?_, by rw [hk .r28 (by decide) (by decide) (by decide) (by decide), h28]⟩
  exact hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint ho (hd r hr)) (by decide)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hk : KeptBut s s') (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hk.r3, hp], by rw [hk .r28 (by decide) (by decide) (by decide) (by decide), h28],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The cipher on a block in memory: its block function. -/
theorem dirCipher_bytes (d : Dir) (K : Spec.Camellia.Subkeys) (m : Mem) (p : Addr) :
    dirCipher d K (Spec.Aes.bytesAt m p 16) = (blockFn K (specDir d) (Spec.Camellia.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList]; rfl

/-! ## The bodies, narrowed -/

/-- The registers `vg_camellia_prepare_keys`'s body writes. -/
def prepWrites : List Reg :=
  [.r3, .r4, .r7, .r8, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
   .r27, .r28, .r29, .r30, .r31]

/-- The registers `vg_camellia_crypt_prepared`'s body writes. -/
def cryptWrites : List Reg :=
  [.r0, .r3, .r4, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25,
   .r26, .r27, .r28, .r29, .r30, .r31]

theorem prep_writes : writesOnly prepWrites prepareKeys = true := by lit_decide
theorem prep_noCalls : prepareKeys.noCalls = true := by lit_decide
theorem prep_noFrames : prepareKeys.noFrames = true := by lit_decide
theorem crypt_writes : writesOnly cryptWrites cryptPrepared = true := by lit_decide
theorem crypt_noCalls : cryptPrepared.noCalls = true := by lit_decide
theorem crypt_noFrames : cryptPrepared.noFrames = true := by lit_decide

/-- The registers the core keeps are `r3`, `r2` or restored by the bodies. -/
theorem kept_cases : ∀ r ∈ kept, r = .r3 ∨ r = .r2 ∨ ∃ i < 18, sreg i = r := by decide

theorem dirOf_dirBit (d : Dir) : dirOf (BitVec.ofNat 64 (dirBit d)) = d := by cases d <;> rfl

theorem dirBit_lt (d : Dir) : dirBit d < 2 ^ 15 := by cases d <;> decide

theorem slots_le (d : Dir) : slots ≤ (dirCore d).total := by simp [dirCore, modeSlots]

/-- The functions' slots, as a region of the writable ones. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hS : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, hS.wr, 0, by simp, by have := slots_le d; simp only; omega⟩

theorem sreg_not_parked : ∀ i < 18, sreg i ∉ [Reg.r0, .r4, .r5, .r6, .r9, .r10, .r11, .r12] := by decide

theorem sreg_not_crypt : ∀ i < 18, sreg i ∉ [Reg.r3, .r4, .r5, .r6, .r10, .r11, .r12] := by decide

theorem sreg_ne_r3_r5 : ∀ i < 18, sreg i ≠ .r3 ∧ sreg i ≠ .r5 := by decide

/-! ## The preparation -/

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .r5 = B) (hS : ScrIn s B (dirCore d).total)
    (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B rs k ∧ s'.gpr .r5 = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, hdis⟩ := hk
  have hfB : B.toNat + 8 * slots ≤ 2 ^ 64 := by have := hS.fit; have := slots_le d; omega
  have dSS : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hm).sub_right (Region.sub_prefix (by have := slots_le d; omega))
  -- The arguments, and the values to keep in registers the body does not write.
  let s₁ := (((((((s.write .r6 (s.gpr .r5)).write .r4 (s.gpr .r28)).write .r5 (BitVec.ofNat 64 (dirBit d))).write
    .r9 (s.gpr .r29)).write .r10 (s.gpr .r30)).write .r11 (s.gpr .r31)).write .r12 (s.gpr .r3)).write .r0 (s.gpr .r28)
  have e₁ : runBlock isa [mov .r6 .r5, mov .r4 .r28, .li .r5 (dirBit d), mov .r9 .r29, mov .r10 .r30,
      mov .r11 .r31, mov .r12 .r3, mov .r0 .r28] s = some s₁ := by
    simp only [mov, runBlock_cons, exec_or_self, exec_li (dirBit_lt d), runStep_some, runBlock_nil]
    simp only [s₁, gpr_write]; rfl
  have g₁ : ∀ r, r ∉ [Reg.r0, .r4, .r5, .r6, .r9, .r10, .r11, .r12] → s₁.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₁, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]
  have v₁ : s₁.gpr .r6 = B ∧ s₁.gpr .r4 = BitVec.ofNat 64 k.1 ∧ s₁.gpr .r5 = BitVec.ofNat 64 (dirBit d) ∧
      s₁.gpr .r9 = s.gpr .r29 ∧ s₁.gpr .r10 = s.gpr .r30 ∧ s₁.gpr .r11 = s.gpr .r31 ∧
      s₁.gpr .r12 = s.gpr .r3 ∧ s₁.gpr .r0 = s.gpr .r28 ∧ s₁.gpr .r3 = p := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s₁, gpr_write, hB, h28, hp]
  obtain ⟨r6₁, r4₁, r5₁, r9₁, r10₁, r11₁, r12₁, r0₁, r3₁⟩ := v₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hS₁ : ScrIn s₁ B (dirCore d).total := ⟨hS.wr, hS.fit⟩
  -- The body, narrowed to the schedule and the functions' slots.
  let N := s₁.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]
  have w := prepareBody_wp (s₀ := N) (by simp [N, r3₁]) (by simp [N, r6₁]) (by simpa [N, r3₁, r6₁] using dSS)
    (by simpa [N, r3₁] using hfit) (by simpa [N, r6₁] using hfB) (by simp [N, r4₁, toNat_rounds hR, hR])
  have hc : Covers ([⟨p, 272⟩] ++ [⟨B, 8 * slots⟩]) (s₁.rd ++ s₁.wr) :=
    Covers.append (Covers.of_mem fun r hr => by simp at hr; subst hr; exact hin)
      (ws_covers hS₁)
  refine WP.seq (WP.narrow (WP.keep prepWrites w prep_writes prep_noCalls) hc (ws_covers hS₁)
    (fun s₂ rd₂ wr₂ _ f₂ ⟨⟨sv₂, tab₂⟩, kp₂⟩ => ?_) prep_noFrames)
  have k₂ : ∀ r, r ∉ prepWrites → s₂.gpr r = s₁.gpr r := fun r hr => by
    simpa [N] using kp₂.gpr hr
  -- The kept values back.
  let s₃ := (((((s₂.write .r5 (s₂.gpr .r6)).write .r3 (s₂.gpr .r12)).write .r28 (s₂.gpr .r0)).write .r29
    (s₂.gpr .r9)).write .r30 (s₂.gpr .r10)).write .r31 (s₂.gpr .r11)
  refine WP.of_runBlock ⟨s₃, by
    simp only [mov, runBlock_cons, exec_or_self, runStep_some, runBlock_nil]
    simp only [s₃, gpr_write]; rfl, ?_⟩
  have g₃ : ∀ r, r ∉ [Reg.r3, .r5, .r28, .r29, .r30, .r31] → s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₃, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  have kp : ∀ r, r ∈ [Reg.r0, .r6, .r9, .r10, .r11, .r12, .r2] → s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂ r (by revert hr; decide +revert)
  have v₃ : s₃.gpr .r5 = B ∧ s₃.gpr .r3 = s.gpr .r3 ∧ s₃.gpr .r28 = s.gpr .r28 ∧ s₃.gpr .r29 = s.gpr .r29 ∧
      s₃.gpr .r30 = s.gpr .r30 ∧ s₃.gpr .r31 = s.gpr .r31 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s₃, gpr_write] <;> simp
    · rw [kp .r6 (by simp), r6₁]
    · rw [kp .r12 (by simp), r12₁]
    · rw [kp .r0 (by simp), r0₁]
    · rw [kp .r9 (by simp), r9₁]
    · rw [kp .r10 (by simp), r10₁]
    · rw [kp .r11 (by simp), r11₁]
  have m₃ : s₃.mem = s₂.mem := rfl
  refine ⟨⟨hR, ?_, by rw [v₃.2.2.1, h28]⟩, v₃.1, fun r hr => ?_, ?_, by rw [show s₃.rd = s₂.rd from rfl, rd₂]; rfl,
    by rw [show s₃.wr = s₂.wr from rfl, wr₂]; rfl⟩
  · rw [m₃, hws]
    have := readyAt_of_words tab₂
    simp only [N, State.withRegions_gpr, State.withRegions_mem, r4₁, r6₁, r5₁, r3₁, toNat_rounds hR,
      dirOf_dirBit] at this
    exact this
  · rcases kept_cases r hr with rfl | rfl | ⟨i, hi, rfl⟩
    · exact v₃.2.1
    · rw [g₃ _ (by decide), kp .r2 (by simp), g₁ _ (by decide)]
    · by_cases h28 : sreg i = .r28
      · rw [h28]; exact v₃.2.2.1
      by_cases h29 : sreg i = .r29
      · rw [h29]; exact v₃.2.2.2.1
      by_cases h30 : sreg i = .r30
      · rw [h30]; exact v₃.2.2.2.2.1
      by_cases h31 : sreg i = .r31
      · rw [h31]; exact v₃.2.2.2.2.2
      have hs := sreg_not_parked i hi
      rw [g₃ _ (by simp [h28, h29, h30, h31, (sreg_ne_r3_r5 i hi).1, (sreg_ne_r3_r5 i hi).2]), ← g₁ _ hs]
      simpa [N] using sv₂ i hi
  · exact f₂

/-! ## A batch -/

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .r5 = B) (hS : ScrIn s B (dirCore d).total) (hr : Ready d s B ws k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr .r5 = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready d s' B ws k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hR, hrd, h28⟩ := hr
  have hfB : B.toNat + 8 * slots ≤ 2 ^ 64 := by have := hS.fit; have := slots_le d; omega
  -- The arguments, and the values to keep in registers the body does not write.
  let s₁ := ((((((s.write .r12 (s.gpr .r3)).write .r3 (s.gpr .r28)).write .r4 (s.gpr .r5)).write .r5
    (s.gpr .r28)).write .r6 (s.gpr .r29)).write .r10 (s.gpr .r30)).write .r11 (s.gpr .r31)
  have e₁ : runBlock isa [mov .r12 .r3, mov .r3 .r28, mov .r4 .r5, mov .r5 .r28, mov .r6 .r29, mov .r10 .r30,
      mov .r11 .r31] s = some s₁ := by
    simp only [mov, runBlock_cons, exec_or_self, runStep_some, runBlock_nil]
    simp only [s₁, gpr_write]; rfl
  have g₁ : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r10, .r11, .r12] → s₁.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₁, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]
  have v₁ : s₁.gpr .r12 = s.gpr .r3 ∧ s₁.gpr .r3 = BitVec.ofNat 64 k.1 ∧ s₁.gpr .r4 = B ∧
      s₁.gpr .r5 = BitVec.ofNat 64 k.1 ∧ s₁.gpr .r6 = s.gpr .r29 ∧ s₁.gpr .r10 = s.gpr .r30 ∧
      s₁.gpr .r11 = s.gpr .r31 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s₁, gpr_write, hB, h28]
  obtain ⟨r12₁, r3₁, r4₁, r5₁, r6₁, r10₁, r11₁⟩ := v₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hS₁ : ScrIn s₁ B (dirCore d).total := ⟨hS.wr, hS.fit⟩
  -- The body, narrowed to the functions' slots.
  let N := s₁.withRegions [] [⟨B, 8 * slots⟩]
  have w := cryptBody_wp (s₀ := N) (by simp [N, r4₁]) (by simpa [N, r4₁] using hfB)
    (by simp [N, r3₁, toNat_rounds hR, hR]) (w := k.2) (d := d)
    (by have m₁ : s₁.mem = s.mem := rfl; simpa [N, r3₁, r4₁, toNat_rounds hR, m₁] using hrd)
  refine WP.seq (WP.narrow (WP.keep cryptWrites w crypt_writes crypt_noCalls) (Covers.right (ws_covers hS₁))
    (ws_covers hS₁) (fun s₂ rd₂ wr₂ _ f₂ ⟨⟨sv₂, rdy₂, _, _, _, b₂, blk₂⟩, kp₂⟩ => ?_) crypt_noFrames)
  have k₂ : ∀ r, r ∉ cryptWrites → s₂.gpr r = s₁.gpr r := fun r hr => by
    simpa [N] using kp₂.gpr hr
  have kp : ∀ r, r ∈ [Reg.r5, .r6, .r10, .r11, .r12, .r2] → s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂ r (by revert hr; decide +revert)
  have r8₂ : s₂.gpr .r8 = B := by simpa [N, r4₁, Impl.Aes.PPC64LE.sb] using b₂
  -- The kept values back.
  let s₃ := (((((s₂.write .r28 (s₂.gpr .r5)).write .r5 (s₂.gpr .r8)).write .r3 (s₂.gpr .r12)).write .r29
    (s₂.gpr .r6)).write .r30 (s₂.gpr .r10)).write .r31 (s₂.gpr .r11)
  refine WP.of_runBlock ⟨s₃, by
    simp only [mov, runBlock_cons, exec_or_self, runStep_some, runBlock_nil]
    simp only [s₃, gpr_write]; rfl, ?_⟩
  have g₃ : ∀ r, r ∉ [Reg.r3, .r5, .r28, .r29, .r30, .r31] → s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₃, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  have v₃ : s₃.gpr .r5 = B ∧ s₃.gpr .r3 = s.gpr .r3 ∧ s₃.gpr .r28 = s.gpr .r28 ∧ s₃.gpr .r29 = s.gpr .r29 ∧
      s₃.gpr .r30 = s.gpr .r30 ∧ s₃.gpr .r31 = s.gpr .r31 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s₃, gpr_write] <;> simp
    · exact r8₂
    · rw [kp .r12 (by simp), r12₁]
    · rw [kp .r5 (by simp), r5₁, h28]
    · rw [kp .r6 (by simp), r6₁]
    · rw [kp .r10 (by simp), r10₁]
    · rw [kp .r11 (by simp), r11₁]
  have m₃ : s₃.mem = s₂.mem := rfl
  have e0 : blkAddr (dirCore d) B 0 = B + BitVec.ofNat 64 (8 * tailSlot + 16 * 0) := by
    simp [blkAddr, slotA, dirCore]
  refine ⟨v₃.1, fun r hr => ?_, ⟨hR, ?_, by rw [v₃.2.2.1, h28]⟩, f₂, fun j hj => ?_,
    by rw [show s₃.rd = s₂.rd from rfl, rd₂]; rfl, by rw [show s₃.wr = s₂.wr from rfl, wr₂]; rfl⟩
  · rcases kept_cases r hr with rfl | rfl | ⟨i, hi, rfl⟩
    · exact v₃.2.1
    · rw [g₃ _ (by decide), kp .r2 (by simp), g₁ _ (by decide)]
    · by_cases h28 : sreg i = .r28
      · rw [h28]; exact v₃.2.2.1
      by_cases h29 : sreg i = .r29
      · rw [h29]; exact v₃.2.2.2.1
      by_cases h30 : sreg i = .r30
      · rw [h30]; exact v₃.2.2.2.2.1
      by_cases h31 : sreg i = .r31
      · rw [h31]; exact v₃.2.2.2.2.2
      have hs := sreg_not_crypt i hi
      rw [g₃ _ (by simp [h28, h29, h30, h31, (sreg_ne_r3_r5 i hi).1, (sreg_ne_r3_r5 i hi).2]), ← g₁ _ hs]
      simpa [N] using sv₂ i hi
  · rw [m₃]
    simpa [N, r3₁, r4₁, toNat_rounds hR] using rdy₂
  · obtain rfl : j = 0 := by simpa [dirCore] using hj
    have hb := blk₂ 0 (by omega)
    simp only [N, State.withRegions_mem, State.withRegions_gpr, r3₁, r4₁, toNat_rounds hR] at hb
    rw [show 4 * (dirCore d).bw = 16 from rfl, e0, dirCipher_bytes, bytesAt_eq_blockAt, m₃, hb]
    rfl

/-- Camellia's core meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, dirCore]
  layout := ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩
  keyArgs_congr h e r _ f := keyArgs_congr h e r f
  ready_frame h e _ _ f _ hd := ready_frame h e f hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Camellia.PPC64LE.Mode
