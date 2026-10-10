import VerifiedGarbage.Proof.Sm4.X86_64.GroupStep
import VerifiedGarbage.Proof.Modes.X86_64.Core
import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
import VerifiedGarbage.Spec.Sm4.Ctr

/-!
# SM4's core for the modes on x86-64

`modeCoreSpec`: SM4's core (`Impl.Sm4.X86_64.modeCore`) meets what the
modes need of a core (`Proof.Modes.X86_64.CoreSpec`), with the key a
schedule, its cipher `Spec.Sm4.cipher`, and the key ready when the masks
and the table of round keys in encryption order are in the scratch buffer.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (sb t0)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec)
open VG.Proof.Sm4 (crypt_eq)
open VG.Spec.Aes (bytesAt)

/-- The schedule at `rdi`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Sm4.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r

/-- The masks and the table of round keys in encryption order. -/
def Ready (m : Mem) (B : Addr) (k : Spec.Sm4.Schedule) : Prop :=
  MasksAt m B ∧ ∀ e < 32, VG.Proof.Sm4.WordRel (entryW m B e) fun _ => dirKeys .encrypt k e

theorem scheduleAt_congr {m m' : Mem} {p : Addr}
    (hb : ∀ k < 128, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    Spec.Sm4.scheduleAt m' p = Spec.Sm4.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega), hb (4 * i + 1) (by omega), hb (4 * i + 2) (by omega), hb (4 * i + 3) (by omega)]

theorem bytesAt_eq_blockAt (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Sm4.blockAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 h2
  simp [bytesAt, Spec.Sm4.blockAt]

theorem ofFn_toList (v : Spec.Sm4.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

theorem dirKeys_encrypt (k : Spec.Sm4.Schedule) : dirKeys .encrypt k = fun i => k.getD i 0 := rfl

theorem cipher_bytes (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    Spec.Sm4.cipher k (bytesAt m p 16) =
      (outBlock (quads .enc (dirKeys .encrypt k) 8 (ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  rw [Spec.Sm4.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.encryptBlock, crypt_eq, dirKeys_encrypt]

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tableEnd)
    (hout : d + 8 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ d) {r : Region}
    (hr : Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (bufRegion modeCore B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B hd)
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint B (by simp only [modeCore, tailSlot_eq] at hout ⊢; omega)
      (by simp only [tableEnd_eq] at hd; omega) (by simp only [modeCore, tailSlot_eq]; omega)

theorem ready_frame {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {rs : List Region} (h : Ready m B k)
    (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion modeCore B) r ∨ Region.Sub r (bufRegion modeCore B)) :
    Ready m' B k := by
  have hR : ∀ d, d + 8 ≤ 8 * tableEnd → (d + 8 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ d) →
      m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 h2 (hd r hr)) (by decide)
  refine ⟨fun kv hkv => ?_, fun e he => (h.2 e he).congr fun j hj => ?_⟩
  · have := mask_range hkv
    rw [← h.1 kv hkv]
    exact hR (8 * kv.1) (by rw [tableEnd_eq]; omega) (.inl (by rw [tailSlot_eq]; omega))
  · exact hR (8 * tableSlot + 64 * e + 8 * j) (by rw [tableEnd_eq, tableSlot_eq]; omega)
      (.inr (by rw [tailSlot_eq, tableSlot_eq]; omega))

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ modeCore.keyRegs, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega) hi).symm

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hR : (⟨B, 8 * modeCore.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa modeCore.prepare s fun s' => Ready s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr modeCore.dataReg = s.gpr modeCore.dataReg ∧ s'.gpr modeCore.leftReg = s.gpr modeCore.leftReg ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr := hs.wr
  obtain ⟨s₁, e₁, v₁, -, g₁, rd₁, wr₁, f₁⟩ := setMasks_ok (b := B) keyMasks hB hw
    (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega) (by decide)
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 8 * slots⟩ := hdis _ hR
  have hsch : Spec.Sm4.scheduleAt s₁.mem p = Spec.Sm4.scheduleAt s.mem p :=
    scheduleAt_congr fun i hi => f₁.bytes (R := ⟨p, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_right (Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega))) (by show 128 ≤ 2 ^ 64; omega) hi
  have b₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hB]
  have hpre : SchedPre s₁ B p := ⟨b₁, by rw [wr₁]; exact hw, by have := hs.fit; exact this,
    List.mem_append_left _ (by rw [rd₁]; exact hin), hfit, hsep⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.mono (keys_wp .encrypt hpre (by rw [g₁ _ (by decide), hp]) v₁) fun s₂ k₂ => ?_
  have b₂ : s₂.gpr sb = B := k₂.pre.base
  have keep : ∀ r, r ∉ sboxWrites → r ≠ .rsi → r ≠ .rdi → r ≠ t0 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [k₂.regs r h1 h2 h3, g₁ r h4]
  refine ⟨⟨k₂.masks.at b₂, fun e he => ?_⟩, b₂, keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide), keep _ (by decide) (by decide) (by decide) (by decide),
    ?_, by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁]⟩
  · have := k₂.key.keys e he
    rw [b₂, hsch] at this
    exact this
  · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableSlot_eq]; show 8 * 128 ≤ 8 * tableEnd; rw [tableEnd_eq]; omega)⟩).trans
      k₂.frame

theorem crypt_wp {s : State} {B : Addr} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B modeCore.total) (hr : Ready s.mem B k) :
    WP isa modeCore.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr modeCore.dataReg = s.gpr modeCore.dataReg ∧ s'.gpr modeCore.leftReg = s.gpr modeCore.leftReg ∧
      Ready s'.mem B k ∧
      Frame [coreRegion modeCore B] s.mem s'.mem ∧
      (∀ j < modeCore.G, bytesAt s'.mem (bufAddr modeCore B j) 16 =
        Spec.Sm4.cipher k (bytesAt s.mem (bufAddr modeCore B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s .rdi tableEnd (by decide)
  have b₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide), hB]
  have hkey : KeyCtx s₁ (dirKeys .encrypt k) :=
    { scr := by rw [b₁, wr₁]; exact hs.wr
      fit := by rw [b₁]; exact hs.fit
      keys := fun e he => by rw [b₁, m₁]; exact hr.2 e he }
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.mono (crypt16_wp hkey ((show MasksAt s₁.mem B by rw [m₁]; exact hr.1).ok b₁) (by rw [r₁, b₁, hB])) fun s₂ ⟨c₂, b₂⟩ => ?_
  have base₂ : s₂.gpr sb = B := by rw [c₂.base, b₁]
  have f₂ : Frame [⟨B, 8 * tableSlot⟩] s₁.mem s₂.mem := by have := c₂.frame; rw [b₁] at this; exact this
  have f₀₂ : Frame [coreRegion modeCore B] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by show 8 * tableSlot ≤ 8 * tableEnd; rw [tableSlot_eq, tableEnd_eq]; omega)⟩
  refine ⟨base₂, by rw [c₂.keep _ (by decide) (by decide), o₁ _ (by decide)],
    by rw [c₂.keep _ (by decide) (by decide), o₁ _ (by decide)], by rw [c₂.keep _ (by decide) (by decide), o₁ _ (by decide)],
    ⟨c₂.masks.at base₂, ?_⟩, f₀₂,
    fun j hj => ?_, by rw [c₂.rd, rd₁], by rw [c₂.wr, wr₁]⟩
  · intro e he
    refine (hr.2 e he).congr fun i hi => ?_
    rw [← m₁]
    refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base B (by omega) (by rw [tableSlot_eq]; omega)
  · have hj' : j < 16 := hj
    have e₁ := b₂ j hj'
    simp only [tailBlock, base₂, b₁] at e₁
    have ha : bufAddr modeCore B j = B + BitVec.ofNat 64 (8 * tailSlot + 16 * j) := rfl
    rw [ha, cipher_bytes, bytesAt_eq_blockAt, ← m₁, e₁]

/-- SM4's core meets what the modes need. -/
def modeCoreSpec : CoreSpec modeCore where
  Key := Spec.Sm4.Schedule
  cipher := Spec.Sm4.cipher
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Sm4.cipher]
  layout := ⟨by decide, by decide, by decide, by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr := keyArgs_congr
  ready_frame := ready_frame
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

end VG.Proof.Sm4.X86_64
