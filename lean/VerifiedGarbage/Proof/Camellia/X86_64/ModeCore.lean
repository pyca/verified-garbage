import VerifiedGarbage.Proof.Camellia.X86_64.Ecb
import VerifiedGarbage.Proof.Modes.X86_64.Core
import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Spec.Camellia.Cbc

/-!
# Camellia's core for the modes on x86-64

`modeCoreSpec`: Camellia's core (`Impl.Camellia.X86_64.modeCore`) meets
what the modes need of a core (`Proof.Modes.X86_64.CoreSpec`), with the key
the number of rounds and the schedule's words, its cipher
`Spec.Camellia.cipher` under them, and the key ready when the masks and the
table of subkeys in encryption order are in the scratch buffer and `rdi`
holds the address of the postwhitening's entry (which the modes do not
write).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (sb t0 setMasks st movS)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec modeRegs of_not_modeRegs)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList encryptWith_eq
  decryptWith_eq dirPerm_lt)

/-- The number of rounds in `rsi` and the schedule at `rdi`, outside the
regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ s.gpr .rsi = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The masks, the table of subkeys in the order of `d`, and the address of
its postwhitening entry in `rdi`. -/
def Ready (d : Dir) (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ MasksAt s.mem B ∧
    (∀ i < 8 * (k.1 / 6) + 2, EntryOk s.mem B i (k.2.getD (permOf d (k.1 / 6) i) 0)) ∧
    s.gpr .rdi = B + BitVec.ofNat 64 (8 * keySlot + 512 * (k.1 / 6))

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (by simp only [dirCore, tailSlot_eq] at hd ⊢; omega))
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint B (by simp only [dirCore, tailSlot_eq] at hd ⊢; omega)
      (by simp only [tailSlot_eq] at hd; omega) (by simp only [dirCore, tailSlot_eq]; omega)

theorem ready_frame {d : Dir} {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready d s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (bufRegion (dirCore d) B))
    (hg : ∀ r, r ∉ modeRegs (dirCore d) → s'.gpr r = s.gpr r) : Ready d s' B k := by
  obtain ⟨hR, hm, he, hrdi⟩ := h
  have hR' : ∀ d, d + 8 ≤ 8 * tailSlot →
      s'.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 (hd r hr)) (by decide)
  have hg4 : k.1 / 6 ≤ 4 := by omega
  refine ⟨hR, fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_, ?_⟩
  · have hk : 48 ≤ kv.1 ∧ kv.1 < 53 := by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
    rw [← hm kv hkv]
    exact hR' (8 * kv.1) (by rw [tailSlot_eq]; omega)
  · exact hR' (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega)
  · rw [hg .rdi (by simp only [modeRegs, dirCore]; decide), hrdi]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi, .rsi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hrsi, hR, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], by rw [hr .rsi (List.mem_cons_of_mem _ List.mem_cons_self), hrsi],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hrsi, hRr, hws, hin, hfit, hdis⟩ := hk
  simp only at hrsi hRr hws
  have hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr := hs.wr
  obtain ⟨s₁, e₁, v₁, -, g₁, rd₁, wr₁, f₁⟩ := setMasks_ok layerMasks hB hw
    (fun kv hkv => by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot, keySlot]) (by decide)
  obtain ⟨s₂, e₂, z₂, g₂, m₂, rd₂, wr₂⟩ := cmpImmZ_ok s₁ .rsi 18
  have hz : s₂.zf = some (decide (R = 18)) := by
    rw [z₂, g₁ _ (by decide), hrsi, show (18 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  have hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ := hdis _ hR
  have b₂ : s₂.gpr sb = B := by rw [g₂, g₁ _ (by decide), hB]
  have hpre : KeyPre s₂ B p := ⟨b₂, by rw [wr₂, wr₁]; exact hw, hs.fit,
    List.mem_append_left _ (by rw [rd₂, rd₁]; exact hin), hfit, hsep⟩
  have rdi₂ : s₂.gpr .rdi = p := by rw [g₂, g₁ _ (by decide), hp]
  have mk₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, g₂]; exact v₁ kv hkv
  show WP isa (.seq (.block (setMasks layerMasks ++ ([.alu .cmp .rsi (.imm 18)] : List Instr)))
    (.ite .e (keys d 3) (keys d 4))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  refine WP.mono (M := isa) (Q := fun s' => KeysPost s₂ B p g (permOf d g) s' ∧
      s'.gpr .rdi = B + BitVec.ofNat 64 (8 * keySlot + 512 * g))
    (WP.ite (decide (R = 18)) (by simp [X86_64.eval, hz]) (fun h => ?_) (fun h => ?_)) fun s₃ ⟨k₃, rdi₃⟩ => ?_
  · obtain rfl : g = 3 := by simp at h; omega
    exact keys_wp d (Or.inl rfl) hpre rdi₂ mk₂
  · obtain rfl : g = 4 := by simp at h; omega
    exact keys_wp d (Or.inr rfl) hpre rdi₂ mk₂
  have b₃ : s₃.gpr sb = B := k₃.pre.base
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → r ≠ t0 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [k₃.regs r h1 h2 h3, g₂, g₁ r h4]
  have hcore : ∀ {n : Nat}, n ≤ tailSlot + 16 → Region.Sub ⟨B, 8 * n⟩ (coreRegion (dirCore d) B) := fun h =>
    Region.sub_prefix (by simp only [dirCore]; omega)
  refine ⟨⟨hRr, k₃.masks.at b₃, fun i hi => ?_, by rw [rdi₃, hgR]⟩, b₃,
    keep _ (by decide) (by decide) (by decide) (by decide), keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide), ?_, by rw [k₃.rd, rd₂, rd₁], by rw [k₃.wr, wr₂, wr₁]⟩
  · rw [hgR] at hi
    have := k₃.ent i hi
    rw [m₂] at this
    have hp' : permOf d g i < 8 * g + 2 := dirPerm_lt (specDir d) hi
    have hl : permOf d g i < Spec.Camellia.scheduleLength R := by simp only [Spec.Camellia.scheduleLength]; omega
    show EntryOk s₃.mem B i (ws.getD (permOf d (R / 6) i) 0)
    rw [hgR, hws, schedWords_getD _ _ hl]
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

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The cipher on a block in memory: `crypt8`'s words. -/
theorem dirCipher_bytes (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) (ws : List (BitVec 64)) (m : Mem) (p : Addr) :
    dirCipher d (Spec.Camellia.subkeysOfWords R ws) (Spec.Aes.bytesAt m p 16) =
      (Spec.Camellia.encodeBlock (cryptWords (R / 6) (fun i => ws.getD (permOf d (R / 6) i) 0)
        (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt m p)))).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Camellia.encryptBlock,
      encryptWith_eq hR]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Camellia.decryptBlock,
      decryptWith_eq hR]; rfl

/-- The masks and the table below the postwhitening's entry, through a
change of memory that keeps the words below it. -/
theorem keys_of_words {m m' : Mem} {B : Addr} {g : Nat} {E : Nat → BitVec 64} (hg : g ≤ 4)
    (hm : MasksAt m B) (he : ∀ i < 8 * g + 2, EntryOk m B i (E i))
    (hw : ∀ d, d + 8 ≤ 8 * endSlot → m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64) :
    MasksAt m' B ∧ ∀ i < 8 * g + 2, EntryOk m' B i (E i) := by
  refine ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩
  · have hk : 48 ≤ kv.1 ∧ kv.1 < 53 := by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
    rw [← hm kv hkv]
    exact hw (8 * kv.1) (by rw [endSlot_eq]; omega)
  · exact hw (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, endSlot_eq]; omega)

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready d s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Ready d s' B k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRr, hm, he, hrdi⟩ := hr
  simp only at hRr he hrdi ⊢
  let g := R / 6
  have hg : g = 3 ∨ g = 4 := by omega
  have hg4 : g ≤ 4 := by omega
  let E : Nat → BitVec 64 := fun i => ws.getD (permOf d g i) 0
  let T := B + BitVec.ofNat 64 (8 * tailSlot)
  have hfit : B.toNat + 8 * slots ≤ 2 ^ 64 := hs.fit
  have hwS : (⟨B, 8 * slots⟩ : Region) ∈ s.wr := hs.wr
  rw [slots_eq] at hfit
  have inSlot : ∀ j < slots, InRegions s.wr (wordAddr B j) 8 := fun j hj =>
    ⟨_, hwS, VG.Offset.contains_base B (by rw [slots_eq] at hj ⊢; omega) (by rw [slots_eq] at hj; omega)⟩
  have hds : dataSlot < slots := by rw [dataSlot_eq, slots_eq]; decide
  have hcs : countSlot < slots := by rw [countSlot_eq, slots_eq]; decide
  have hes : endSlot < slots := by rw [endSlot_eq, slots_eq]; decide
  -- The state to its slots, and `rdx` to the tail buffer.
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a⟩ := stReg_ok (k := dataSlot) .rdx hB (inSlot _ hds)
  obtain ⟨s₄b, e₄b, m₄b, g₄b, rd₄b, wr₄b⟩ := stReg_ok (k := countSlot) .r8 (by rw [g₄a, hB])
    (by rw [wr₄a]; exact inSlot _ hcs)
  obtain ⟨s₄c, e₄c, m₄c, g₄c, rd₄c, wr₄c⟩ := stReg_ok (k := endSlot) .rdi (by rw [g₄b, g₄a, hB])
    (by rw [wr₄b, wr₄a]; exact inSlot _ hes)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := tailAddr_ok s₄c .rdx
  have base₄ : s₄.gpr sb = B := by rw [o₄ _ (by decide), g₄c, g₄b, g₄a, hB]
  have rdx₄ : s₄.gpr .rdx = T := by rw [r₄, g₄c, g₄b, g₄a, hB]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄c, wr₄b, wr₄a]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₄c, rd₄b, rd₄a]
  have g₄ : ∀ r, r ≠ .rdx → s₄.gpr r = s.gpr r := fun r h => by rw [o₄ r h, g₄c, g₄b, g₄a]
  have mem₄ : s₄.mem = ((s.mem.writeW (wordAddr B dataSlot) (s.gpr .rdx)).writeW (wordAddr B countSlot)
      (s.gpr .r8)).writeW (wordAddr B endSlot) (s.gpr .rdi) := by
    rw [m₄, m₄c, m₄b, m₄a, g₄b, g₄a]
  have f₄ : Frame [⟨B + BitVec.ofNat 64 (8 * endSlot), 24⟩] s.mem s₄.mem := by
    rw [mem₄]
    refine ((frame_writeW _ ?_).trans (frame_writeW _ ?_)).trans (frame_writeW _ ?_) <;>
      exact VG.Offset.sub B (by simp only [dataSlot_eq, countSlot_eq, endSlot_eq]; omega)
        (by simp only [dataSlot_eq, countSlot_eq, endSlot_eq]; omega)
  have slot₄ : ∀ j < slots, slotW s₄ j = if j = endSlot then s.gpr .rdi else if j = countSlot then
      s.gpr .r8 else if j = dataSlot then s.gpr .rdx else s.mem.readW (wordAddr B j) 64 := fun j hj => by
    simp only [slotW, base₄, mem₄]
    rw [readW_slot_write _ hj hes, readW_slot_write _ hj hcs, readW_slot_write _ hj hds]
  have below₄ : ∀ d, d + 8 ≤ 8 * endSlot →
      s₄.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint B (Or.inl hd) (by rw [endSlot_eq] at hd; omega)
        (by rw [endSlot_eq]; omega)) (by decide)
  obtain ⟨hm₄, he₄⟩ := keys_of_words hg4 hm he below₄
  have tail₄ : ∀ j < 8, Spec.Camellia.blockAt s₄.mem (T + BitVec.ofNat 64 (16 * j)) =
      Spec.Camellia.blockAt s.mem (T + BitVec.ofNat 64 (16 * j)) := fun j hj => by
    apply Vector.ext; intro i hi
    simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
    refine f₄ _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [T] at hc
    rw [addr_add, addr_add] at hc
    exact Proof.Camellia.not_contains_off B (Or.inr (by rw [endSlot_eq, tailSlot_eq]; omega))
      (by rw [tailSlot_eq]; omega) (by decide) (by rw [endSlot_eq]; omega) hc
  -- The eight blocks.
  have hcore : CorePre s₄ g E :=
    { scr := by rw [base₄, wr₄']; exact hwS
      dat := fun j hj => by
        rw [rdx₄, wr₄']
        refine ⟨_, hwS, ?_⟩
        simp only [T, wordAddr]
        rw [addr_add]
        exact VG.Offset.contains_base B (by rw [slots_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)
      sep := by rw [rdx₄, base₄]; exact VG.Offset.disjoint_base B (Nat.le_refl _) (by rw [tailSlot_eq]; omega)
      fit := by rw [base₄, slots_eq]; exact hfit
      fitD := by rw [rdx₄, Proof.Camellia.toNat_off B (by rw [tailSlot_eq]; omega), tailSlot_eq]; omega
      hg := hg
      nk34 := by omega
      masks := hm₄.ok base₄
      bound := by rw [slot₄ _ hes, ite_eq_left rfl, base₄, hrdi]
      keys := fun i hi' => by rw [base₄]; exact he₄ i hi' }
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [saveState, show ([st dataSlot .rdx, st countSlot .r8, st endSlot .rdi] : List Instr) =
      [st dataSlot .rdx] ++ ([st countSlot .r8] ++ [st endSlot .rdi]) from rfl,
      runBlock_append', runBlock_append', e₄a, Option.bind_some, runBlock_append', e₄b, Option.bind_some,
      e₄c, Option.bind_some, e₄], ?_⟩)
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, b₅⟩ => ?_)
  have base₅ : s₅.gpr sb = B := by rw [c₅.base, base₄]
  have rdx₅ : s₅.gpr .rdx = T := by rw [c₅.rdx, rdx₄]
  have f₅ : Frame [⟨B, 8 * keySlot⟩, ⟨T, 128⟩] s₄.mem s₅.mem := by
    have := c₅.frame; rw [base₄, rdx₄] at this; exact this
  have keepSlot : ∀ d, 8 * keySlot ≤ d → d + 8 ≤ 8 * tailSlot →
      s₅.mem.readW (B + BitVec.ofNat 64 d) 64 = s₄.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 =>
    f₅.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint_base B h1 (by rw [tailSlot_eq] at h2; omega)
      · exact VG.Offset.disjoint B (Or.inl h2) (by rw [tailSlot_eq] at h2; omega) (by rw [tailSlot_eq]; omega))
      (by decide)
  have vS : ∀ j, j = dataSlot ∨ j = countSlot ∨ j = endSlot →
      s₅.mem.readW (wordAddr B j) 64 = slotW s₄ j := fun j hj => by
    simp only [slotW, base₄, wordAddr]
    exact keepSlot (8 * j) (by rcases hj with rfl | rfl | rfl <;> simp [dataSlot_eq, countSlot_eq, endSlot_eq, keySlot_eq])
      (by rcases hj with rfl | rfl | rfl <;> simp [dataSlot_eq, countSlot_eq, endSlot_eq, tailSlot_eq])
  -- The state back from its slots.
  have wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  have rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₄']
  have inS₅ : ∀ j < slots, InRegions (s₅.rd ++ s₅.wr) (wordAddr B j) 8 := fun j hj => by
    rw [wr₅', rd₅']; exact Proof.Camellia.X86_64.inRd (inSlot j hj)
  obtain ⟨s₆a, e₆a, d₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := movS_ok (k := dataSlot) .rdx base₅ (inS₅ _ hds)
  obtain ⟨s₆b, e₆b, d₆b, o₆b, m₆b, rd₆b, wr₆b⟩ := movS_ok (k := countSlot) .r8
    (by rw [o₆a _ (by decide), base₅]) (by rw [rd₆a, wr₆a]; exact inS₅ _ hcs)
  obtain ⟨s₆, e₆, d₆, o₆, m₆, rd₆, wr₆⟩ := movS_ok (k := endSlot) .rdi
    (by rw [o₆b _ (by decide), o₆a _ (by decide), base₅]) (by rw [rd₆b, wr₆b, rd₆a, wr₆a]; exact inS₅ _ hes)
  have mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆b, m₆a]
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (by decide), o₆b _ (by decide), o₆a _ (by decide), base₅]
  have rdx₆ : s₆.gpr .rdx = s.gpr .rdx := by
    rw [o₆ _ (by decide), o₆b _ (by decide), d₆a]
    show s₅.mem.readW (wordAddr (s₅.gpr sb) dataSlot) 64 = _
    rw [base₅, vS _ (.inl rfl), slot₄ _ hds, ite_eq_right (by rw [dataSlot_eq, endSlot_eq]; omega),
      ite_eq_right (by rw [dataSlot_eq, countSlot_eq]; omega), ite_eq_left rfl]
  have r8₆ : s₆.gpr .r8 = s.gpr .r8 := by
    rw [o₆ _ (by decide), d₆b]
    show s₆a.mem.readW (wordAddr (s₆a.gpr sb) countSlot) 64 = _
    rw [m₆a, o₆a _ (by decide), base₅, vS _ (.inr (.inl rfl)), slot₄ _ hcs,
      ite_eq_right (by rw [countSlot_eq, endSlot_eq]; omega), ite_eq_left rfl]
  have rdi₆ : s₆.gpr .rdi = s.gpr .rdi := by
    rw [d₆]
    show s₆b.mem.readW (wordAddr (s₆b.gpr sb) endSlot) 64 = _
    rw [m₆b, m₆a, o₆b _ (by decide), o₆a _ (by decide), base₅, vS _ (.inr (.inr rfl)), slot₄ _ hes, ite_eq_left rfl]
  have g₆ : ∀ r, r ≠ .rdx → r ≠ .r8 → r ≠ .rdi → s₆.gpr r = s₅.gpr r := fun r h1 h2 h3 => by
    rw [o₆ r h3, o₆b r h2, o₆a r h1]
  have hcoreR : ∀ {o n : Nat}, o + n ≤ 8 * (tailSlot + 16) →
      Region.Sub ⟨B + BitVec.ofNat 64 o, n⟩ (coreRegion (dirCore d) B) := fun h =>
    VG.Offset.sub_base B (by simp only [dirCore]; omega)
  refine WP.of_runBlock ⟨s₆, by
    rw [loadState, show ([movS .rdx dataSlot, movS .r8 countSlot, movS .rdi endSlot] : List Instr) =
      [movS .rdx dataSlot] ++ ([movS .r8 countSlot] ++ [movS .rdi endSlot]) from rfl,
      runBlock_append', e₆a, Option.bind_some, runBlock_append', e₆b, Option.bind_some, e₆],
    base₆, ?_, rdx₆, r8₆, ⟨hRr, ?_, ?_, by rw [rdi₆, hrdi]⟩, ?_, fun j hj => ?_,
    by rw [rd₆, rd₆b, rd₆a, rd₅'], by rw [wr₆, wr₆b, wr₆a, wr₅']⟩
  · rw [g₆ _ (by decide) (by decide) (by decide), c₅.keep _ (by decide) (by decide) (by decide),
      g₄ _ (by decide)]
  · rw [mem₆]; exact c₅.masks.at base₅
  · intro i hi'
    refine (he₄ i hi').congr fun j hj => ?_
    rw [mem₆]
    exact keepSlot _ (by omega) (by rw [keySlot_eq, tailSlot_eq]; omega)
  · rw [mem₆]
    refine (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr
        exact hcoreR (by rw [endSlot_eq, tailSlot_eq]; omega)⟩).trans
      (f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Region.sub_prefix (by simp only [dirCore]; rw [keySlot_eq, tailSlot_eq]; omega)
        · exact hcoreR (by rw [tailSlot_eq])⟩)
  · have hj8 : j < 8 := hj
    have ha : bufAddr (dirCore d) B j = T + BitVec.ofNat 64 (16 * j) := by
      simp only [bufAddr, dirCore, T]; rw [addr_add]
    have e5 := b₅ j hj8
    simp only [Proof.Camellia.X86_64.blk, rdx₅, rdx₄] at e5
    rw [ha, dirCipher_bytes d hRr, bytesAt_eq_blockAt, mem₆, e5, tail₄ j hj8]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr := keyArgs_congr
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- Camellia's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Camellia.X86_64
