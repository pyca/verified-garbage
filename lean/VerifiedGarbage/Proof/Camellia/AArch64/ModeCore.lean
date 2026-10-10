import VerifiedGarbage.Proof.Camellia.AArch64.Ecb
import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
import VerifiedGarbage.Proof.Camellia.CtrCipher

/-!
# Camellia's core for the modes on AArch64

`modeCoreSpec`: Camellia's core (`Impl.Camellia.AArch64.modeCore`) meets
what the modes need of a core (`Proof.Modes.AArch64.CoreSpec`), with the key
the number of rounds and the schedule's words, its cipher
`Spec.Camellia.cipher` under them, and the key ready when the masks and the
table of subkeys in encryption order are in the scratch buffer and `x4`
holds the address of the postwhitening's entry (which the modes do not
write).
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (sb t0 kp)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec modeRegs eval_zero)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt cipher_bytes)

/-- The number of rounds in `x1` and the schedule at `x0`, outside the
regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ s.gpr .x1 = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The masks, the table of subkeys in encryption order, and the address of
its postwhitening entry in `x4`. -/
def Ready (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ MasksAt s.mem B ∧ (∀ i < 8 * (k.1 / 6) + 2, EntryOk s.mem B i (k.2.getD i 0)) ∧
    s.gpr .x4 = B + BitVec.ofNat 64 (8 * keySlot + 512 * (k.1 / 6))

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : 48 ≤ kv.1 ∧ kv.1 < 53 := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (bufRegion modeCore B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (by simp only [modeCore, tailSlot_eq] at hd ⊢; omega))
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 128⟩
    exact VG.Offset.disjoint B (by simp only [tailSlot_eq] at hd ⊢; omega)
      (by simp only [tailSlot_eq] at hd; omega) (by simp only [tailSlot_eq]; omega)

theorem ready_frame {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region} (h : Ready s B k)
    (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (bufRegion modeCore B))
    (hg : ∀ r, r ∉ modeRegs modeCore → s'.gpr r = s.gpr r) : Ready s' B k := by
  obtain ⟨hR, hm, he, hx4⟩ := h
  have hR' : ∀ d, d + 8 ≤ 8 * tailSlot →
      s'.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 (hd r hr)) (by decide)
  have hg4 : k.1 / 6 ≤ 4 := by omega
  refine ⟨hR, fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_, ?_⟩
  · have hk := mask_range hkv
    rw [← hm kv hkv]
    exact hR' (8 * kv.1) (by rw [tailSlot_eq]; omega)
  · exact hR' (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega)
  · rw [hg .x4 (by decide), hx4]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ modeCore.keyRegs, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hx1, hR, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], by rw [hr .x1 (List.mem_cons_of_mem _ List.mem_cons_self), hx1],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

theorem permOf_encrypt (g i : Nat) : permOf .encrypt g i = i := rfl

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hR : (⟨B, 8 * modeCore.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧
      s'.gpr modeCore.dataReg = s.gpr modeCore.dataReg ∧ s'.gpr modeCore.leftReg = s.gpr modeCore.leftReg ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hx1, hRr, hws, hin, hfit, hdis⟩ := hk
  simp only at hx1 hRr hws
  have hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr := hs.wr
  obtain ⟨s₁, e₁, mk₁, g₁, rd₁, wr₁, f₁⟩ := setSlots_ok hw hB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ t0 .x1 (imm := 18) (by decide)
  have hz : isa.eval (.zero .x t0) s₂ = some (decide (R = 18)) := by
    rw [eval_zero, r₂, g₁ _ (by decide), hx1, VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  have hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ := hdis _ hR
  have b₂ : s₂.gpr sb = B := by rw [o₂ _ (by decide), g₁ _ (by decide), hB]
  have hpre : KeyPre s₂ B p := ⟨b₂, by rw [wr₂, wr₁]; exact hw, hs.fit,
    List.mem_append_left _ (by rw [rd₂, rd₁]; exact hin), hfit, hsep⟩
  have x0₂ : s₂.gpr .x0 = p := by rw [o₂ _ (by decide), g₁ _ (by decide), hp]
  have mk₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact mk₁ kv hkv
  show WP isa (.seq (.block (setSlots layerMasks ++ ([.subImm .x t0 .x1 18] : List Instr)))
    (.ite (.zero .x t0) (keys .encrypt 3) (keys .encrypt 4))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  refine WP.mono (M := isa) (Q := fun s' => KeysPost s₂ B p g (permOf .encrypt g) s' ∧
      s'.gpr .x4 = B + BitVec.ofNat 64 (8 * keySlot + 512 * g))
    (WP.ite (decide (R = 18)) hz (fun h => ?_) (fun h => ?_)) fun s₃ ⟨k₃, x4₃⟩ => ?_
  · obtain rfl : g = 3 := by simp at h; omega
    exact keys_wp .encrypt (Or.inl rfl) hpre x0₂ mk₂
  · obtain rfl : g = 4 := by simp at h; omega
    exact keys_wp .encrypt (Or.inr rfl) hpre x0₂ mk₂
  have b₃ : s₃.gpr sb = B := k₃.pre.base
  have keep : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → r ≠ .x4 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [k₃.regs r h1 h2 h3 h4, o₂ r h5, g₁ r h5]
  have hcore : ∀ {n : Nat}, n ≤ tailSlot + 16 → Region.Sub ⟨B, 8 * n⟩ (coreRegion modeCore B) := fun h =>
    Region.sub_prefix (by simp only [modeCore]; omega)
  refine ⟨⟨hRr, k₃.masks.at b₃, fun i hi => ?_, by rw [x4₃, hgR]⟩, b₃,
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide), ?_,
    by rw [k₃.rd, rd₂, rd₁], by rw [k₃.wr, wr₂, wr₁]⟩
  · rw [hgR] at hi
    have := k₃.ent i hi
    rw [permOf_encrypt, m₂] at this
    have hl : i < Spec.Camellia.scheduleLength R := by simp only [Spec.Camellia.scheduleLength]; omega
    rw [hws, schedWords_getD _ _ hl]
    rw [wordAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep.sub_left (VG.Offset.sub_base p (by simp only [Spec.Camellia.scheduleLength] at hl; omega))).sub_right
        (Region.sub_prefix (by rw [keySlot_eq, slots_eq]; omega))] at this
    exact this
  · have kf := k₃.frame
    rw [m₂] at kf
    exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hcore (by rw [keySlot_eq, tailSlot_eq]; omega)⟩).trans
      (kf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hcore (by rw [endSlot_eq, tailSlot_eq]; omega)⟩)

theorem crypt_wp {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hr : Ready s B k) :
    WP isa modeCore.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr modeCore.dataReg = s.gpr modeCore.dataReg ∧ s'.gpr modeCore.leftReg = s.gpr modeCore.leftReg ∧
      Ready s' B k ∧ Frame [coreRegion modeCore B] s.mem s'.mem ∧
      (∀ j < modeCore.G, Spec.Aes.bytesAt s'.mem (bufAddr modeCore B j) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr modeCore B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRr, hm, he, hx4⟩ := hr
  simp only at hRr he hx4 ⊢
  let g := R / 6
  have hg : g = 3 ∨ g = 4 := by omega
  have hcore : CorePre s g (fun i => ws.getD i 0) :=
    { scr := by rw [hB]; exact hs.wr
      fit := by rw [hB]; exact hs.fit
      nk34 := by omega
      masks := hm.ok hB
      keys := fun i hi => by rw [hB]; exact he i hi
      hg := hg
      bound := by rw [hx4, hB] }
  refine WP.mono (crypt8_ok hcore) fun s₁ ⟨c₁, b₁⟩ => ?_
  have base₁ : s₁.gpr sb = B := by rw [c₁.base, hB]
  have f₁ : Frame (ctxRegions B) s.mem s₁.mem := by have := c₁.frame; rw [hB] at this; exact this
  have keepK : ∀ d, 8 * keySlot ≤ d → d + 8 ≤ 8 * tailSlot →
      s₁.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 =>
    f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint_base B h1 (by rw [tailSlot_eq] at h2; omega)
      · exact VG.Offset.disjoint B (Or.inl h2) (by rw [tailSlot_eq] at h2; omega) (by rw [tailSlot_eq]; omega))
      (by decide)
  refine ⟨base₁, c₁.keep _ (by decide) (by decide) (by decide), c₁.keep _ (by decide) (by decide) (by decide),
    ⟨hRr, c₁.masks.at base₁, fun i hi' => (he i hi').congr fun j hj => ?_,
      by rw [c₁.keep _ (by decide) (by decide) (by decide), hx4]⟩, ?_, fun j hj => ?_, c₁.rd, c₁.wr⟩
  · have hg4 : g ≤ 4 := by omega
    exact keepK _ (by omega) (by rw [keySlot_eq, tailSlot_eq]; omega)
  · refine f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [modeCore]; rw [keySlot_eq, tailSlot_eq]; omega)
    · exact VG.Offset.sub_base B (by simp only [modeCore]; omega)
  · have hj8 : j < 8 := hj
    have ha : bufAddr modeCore B j = B + BitVec.ofNat 64 (8 * tailSlot + 16 * j) := rfl
    have e1 := b₁ j hj8
    simp only [blk, base₁, hB] at e1
    rw [ha, cipher_bytes hRr, bytesAt_eq_blockAt, e1]

/-- Camellia's core meets what the modes need. -/
def modeCoreSpec : CoreSpec modeCore where
  Key := Nat × List (BitVec 64)
  cipher k := Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Camellia.cipher]
  layout := ⟨by decide, by decide, by decide, by decide, by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr := keyArgs_congr
  ready_frame := ready_frame
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Camellia.AArch64
